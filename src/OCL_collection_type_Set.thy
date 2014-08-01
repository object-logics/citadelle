(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_collection_type_Set.thy --- Library definitions.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2014 Université Paris-Sud, France
 *               2013-2014 IRT SystemX, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id:$ *)

header{* ... *}

theory  OCL_collection_type_Set
imports OCL_basic_type
begin

no_notation None ("\<bottom>")
section{* Complex Types: The Set-Collection Type (I) Core *}

subsection{* The Construction of the Set Type *}

text{* The core of an own type construction is done via a type
  definition which provides the raw-type @{text "'\<alpha> Set_0"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. *}

typedef '\<alpha> Set_0 ="{X::('\<alpha>\<Colon>null) set option option. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by (rule_tac x="bot" in exI, simp)

instantiation   Set_0  :: (null)bot
begin

   definition bot_Set_0_def: "(bot::('a::null) Set_0) \<equiv> Abs_Set_0 None"

   instance proof show "\<exists>x\<Colon>'a Set_0. x \<noteq> bot"
                  apply(rule_tac x="Abs_Set_0 \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Set_0_def)
                  apply(subst Abs_Set_0_inject)
                    apply(simp_all add: bot_Set_0_def
                                        null_option_def bot_option_def)
                  done
            qed
end

instantiation   Set_0  :: (null)null
begin

   definition null_Set_0_def: "(null::('a::null) Set_0) \<equiv> Abs_Set_0 \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null) Set_0) \<noteq> bot"
                  apply(simp add:null_Set_0_def bot_Set_0_def)
                  apply(subst Abs_Set_0_inject)
                    apply(simp_all add: bot_Set_0_def
                                        null_option_def bot_option_def)
                  done
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Set  = "('\<AA>, '\<alpha> Set_0) val"

subsection{* As a Motivation: Type-Extensions as Sets*}

text{* Our notion of typed set goes beyond the usual notion of a finite executable set and
is powerful enough to capture \emph{the extension of a type} in UML and OCL. This means
we can have in Featherweight OCL Sets containing all possible elements of a type, not only
those (finite) ones representable in a state. This holds for base types as well as class types,
although the notion for class-types --- involving object id's not occuring in a state ---
requires some care.

In a world with @{term invalid} and @{term null}, there are two notions extensions possible:
\begin{enumerate}
\item the set of all \emph{defined} values of a type @{term T}
      (for which we will introduce the constant  @{term T})
\item the set of all \emph{valid} values of a type @{term T}, so including @{term null}
      (for which we will introduce the constant  @{term T\<^sub>n\<^sub>u\<^sub>l\<^sub>l}).
\end{enumerate}
*}

text{* We define the set extensions for the base type @{term Integer} as follows: *}
definition Integer :: "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Integer \<equiv> (\<lambda> \<tau>. (Abs_Set_0 o Some o Some)  ((Some o Some) ` (UNIV::int set)))"

definition Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l :: "('\<AA>,Integer\<^sub>b\<^sub>a\<^sub>s\<^sub>e) Set"
where     "Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l \<equiv> (\<lambda> \<tau>. (Abs_Set_0 o Some o Some)  (Some ` (UNIV::int option set)))"

lemma Integer_defined : "\<delta> Integer = true"
apply(rule ext, auto simp: Integer_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set_0_inject bot_option_def bot_Set_0_def null_Set_0_def null_option_def)

lemma Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l_defined : "\<delta> Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l = true"
apply(rule ext, auto simp: Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l_def defined_def false_def true_def
                           bot_fun_def null_fun_def null_option_def)
by(simp_all add: Abs_Set_0_inject bot_option_def bot_Set_0_def null_Set_0_def null_option_def)

text{* This allows the theorems:

      @{text "\<tau> \<Turnstile> \<delta> x  \<Longrightarrow> \<tau> \<Turnstile> (Integer->includes(x))"}
      @{text "\<tau> \<Turnstile> \<delta> x  \<Longrightarrow> \<tau> \<Turnstile> Integer  \<triangleq> (Integer->including(x))"}

and

      @{text "\<tau> \<Turnstile> \<upsilon> x  \<Longrightarrow> \<tau> \<Turnstile> (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l->includes(x))"}
      @{text "\<tau> \<Turnstile> \<upsilon> x  \<Longrightarrow> \<tau> \<Turnstile> Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l  \<triangleq> (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l->including(x))"}

which characterize the infiniteness of these sets by a recursive property on these sets.
*}

subsection{* Validity and Definedness Properties *}

text{* Every element in a defined set is valid. *}

lemma Set_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot"
apply(insert Rep_Set_0 [of "X \<tau>"], simp)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Set_0_def null_Set_0_def null_fun_def
           split:split_if_asm)
 apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = bot"])
 apply(subst Abs_Set_0_inject[symmetric], rule Rep_Set_0, simp)
 apply(simp add: Rep_Set_0_inverse bot_Set_0_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = null"])
apply(subst Abs_Set_0_inject[symmetric], rule Rep_Set_0, simp)
apply(simp add: Rep_Set_0_inverse  null_option_def)
by (simp add: bot_option_def)

lemma Set_inv_lemma' :
 assumes x_def : "\<tau> \<Turnstile> \<delta> X"
     and e_mem : "e \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
   shows "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)"
 apply(rule Set_inv_lemma[OF x_def, THEN ballE[where x = e]])
  apply(simp add: foundation18')
by(simp add: e_mem)

lemma abs_rep_simp' :
 assumes S_all_def : "\<tau> \<Turnstile> \<delta> S"
   shows "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by(simp add: false_def true_def)
 show ?thesis
  apply(insert S_all_def, simp add: OclValid_def defined_def)
  apply(rule mp[OF Abs_Set_0_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau>
                                                    then false \<tau> else true \<tau>) = true \<tau> \<longrightarrow>
                                                   Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]],
        rename_tac S')
   apply(simp add: Abs_Set_0_inverse discr_eq_false_true)
   apply(case_tac S') apply(simp add: bot_fun_def bot_Set_0_def)+
   apply(rename_tac S'', case_tac S'') apply(simp add: null_fun_def null_Set_0_def)+
 done
qed

lemma S_lift' :
 assumes S_all_def : "(\<tau> :: '\<AA> st) \<Turnstile> \<delta> S"
   shows "\<exists>S'. (\<lambda>a (_::'\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = (\<lambda>a (_::'\<AA> st). \<lfloor>a\<rfloor>) ` S'"
  apply(rule_tac x = "(\<lambda>a. \<lceil>a\<rceil>) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>" in exI)
  apply(simp only: image_comp[symmetric])
  apply(simp add: comp_def)
  apply(rule image_cong, fast)
  (* *)
  apply(drule Set_inv_lemma'[OF S_all_def])
by(case_tac x, (simp add: bot_option_def foundation18')+)

lemma invalid_set_OclNot_defined [simp,code_unfold]:"\<delta>(invalid::('\<AA>,'\<alpha>::null) Set) = false" by simp
lemma null_set_OclNot_defined [simp,code_unfold]:"\<delta>(null::('\<AA>,'\<alpha>::null) Set) = false"
by(simp add: defined_def null_fun_def)
lemma invalid_set_valid [simp,code_unfold]:"\<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set) = false"
by simp
lemma null_set_valid [simp,code_unfold]:"\<upsilon>(null::('\<AA>,'\<alpha>::null) Set) = true"
apply(simp add: valid_def null_fun_def bot_fun_def bot_Set_0_def null_Set_0_def)
apply(subst Abs_Set_0_inject,simp_all add: null_option_def bot_option_def)
done

text{* ... which means that we can have a type @{text "('\<AA>,('\<AA>,('\<AA>) Integer) Set) Set"}
corresponding exactly to Set(Set(Integer)) in OCL notation. Note that the parameter
@{text "'\<AA>"} still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties
independently from a concrete class diagram. *}

subsection{* Constants on Sets *}
definition mtSet::"('\<AA>,'\<alpha>::null) Set"  ("Set{}")
where     "Set{} \<equiv> (\<lambda> \<tau>.  Abs_Set_0 \<lfloor>\<lfloor>{}::'\<alpha> set\<rfloor>\<rfloor> )"


lemma mtSet_defined[simp,code_unfold]:"\<delta>(Set{}) = true"
apply(rule ext, auto simp: mtSet_def defined_def null_Set_0_def
                           bot_Set_0_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Set_0_inject bot_option_def null_Set_0_def null_option_def)

lemma mtSet_valid[simp,code_unfold]:"\<upsilon>(Set{}) = true"
apply(rule ext,auto simp: mtSet_def valid_def null_Set_0_def
                          bot_Set_0_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Set_0_inject bot_option_def null_Set_0_def null_option_def)

lemma mtSet_rep_set: "\<lceil>\<lceil>Rep_Set_0 (Set{} \<tau>)\<rceil>\<rceil> = {}"
 apply(simp add: mtSet_def, subst Abs_Set_0_inverse)
by(simp add: bot_option_def)+

lemma [simp,code_unfold]: "const Set{}"
by(simp add: const_def mtSet_def)


text{* Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid. *}

section{* Complex Types: The Set-Collection Type (II) Library *}

text{* This part provides a collection of operators for the Set type. *}

subsection{* Computational Operations on Set *}

subsubsection{* Definition *}

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>  \<union> {y \<tau>} \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclIncluding   ("_->including'(_')")

interpretation OclIncluding : binop_infra2 OclIncluding "\<lambda>x y. Abs_Set_0\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 x\<rceil>\<rceil> \<union> {y}\<rfloor>\<rfloor>"
proof -  
 have A : "None \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" 
          by(simp add: null_option_def bot_option_def)
 have C : "\<And>x y. x \<noteq> \<bottom> \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> \<bottom>  \<Longrightarrow>
           \<lfloor>\<lfloor>insert y \<lceil>\<lceil>Rep_Set_0 x\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(auto intro!:Set_inv_lemma[simplified OclValid_def 
                                        defined_def false_def true_def null_fun_def bot_fun_def])          
         show "binop_infra2 OclIncluding (\<lambda>x y. Abs_Set_0\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 x\<rceil>\<rceil> \<union> {y}\<rfloor>\<rfloor>)"
         apply unfold_locales  
         apply(auto simp:OclIncluding_def bot_option_def null_option_def null_Set_0_def bot_Set_0_def)
         apply(erule_tac Q="Abs_Set_0\<lfloor>\<lfloor>insert y \<lceil>\<lceil>Rep_Set_0 x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set_0 None" in contrapos_pp)
         apply(subst Abs_Set_0_inject[OF C A])
         apply(simp_all add:  null_Set_0_def bot_Set_0_def bot_option_def)
         apply(erule_tac Q="Abs_Set_0\<lfloor>\<lfloor>insert y \<lceil>\<lceil>Rep_Set_0 x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Set_0 \<lfloor>None\<rfloor>" in contrapos_pp)
         apply(subst Abs_Set_0_inject[OF C B])
         apply(simp_all add:  null_Set_0_def bot_Set_0_def bot_option_def)
         done
qed

(*
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(simp add: null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
           \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have D: "(\<tau> \<Turnstile> \<delta>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->including(x)))"
          apply(subst OclIncluding_def, subst OclValid_def, subst defined_def)
          apply(auto simp: OclValid_def null_Set_0_def bot_Set_0_def null_fun_def bot_fun_def)
           apply(frule Abs_Set_0_inject[OF C A, simplified OclValid_def, THEN iffD1],
                 simp_all add: bot_option_def)
          apply(frule Abs_Set_0_inject[OF C B, simplified OclValid_def, THEN iffD1],
                simp_all add: bot_option_def)
          done
*)

syntax
  "_OclFinset" :: "args => ('\<AA>,'a::null) Set"    ("Set{(_)}")
translations
  "Set{x, xs}" == "CONST OclIncluding (Set{xs}) x"
  "Set{x}"     == "CONST OclIncluding (Set{}) x "

definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclExcluding x y = (\<lambda> \<tau>.  if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> - {y \<tau>} \<rfloor>\<rfloor>
                                     else \<bottom> )"
notation   OclExcluding   ("_->excluding'(_')")

definition OclIncludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludes x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then \<lfloor>\<lfloor>(y \<tau>) \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                     else \<bottom>  )"
notation   OclIncludes    ("_->includes'(_')" (*[66,65]65*))

definition OclExcludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludes x y = (not(OclIncludes x y))"
notation   OclExcludes    ("_->excludes'(_')" (*[66,65]65*))

text{* The case of the size definition is somewhat special, we admit
explicitly in Featherweight OCL the possibility of infinite sets. For
the size definition, this requires an extra condition that assures
that the cardinality of the set is actually a defined integer. *}

definition OclSize     :: "('\<AA>,'\<alpha>::null)Set \<Rightarrow> '\<AA> Integer"
where     "OclSize x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> finite(\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>)
                             then \<lfloor>\<lfloor> int(card \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<rfloor>\<rfloor>
                             else \<bottom> )"
notation  (* standard ascii syntax *)
           OclSize        ("_->size'(')" (*[66]*))

text{* The following definition follows the requirement of the
standard to treat null as neutral element of sets. It is
a well-documented exception from the general strictness
rule and the rule that the distinguished argument self should
be non-null. *}
definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((\<upsilon> x and not (\<delta> x)) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty'(')" (*[66]*))

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty'(')" (*[66]*))

(* Slight breach of naming convention in order to avoid naming conflict on constant.*)
definition OclANY   :: "[('\<AA>,'\<alpha>::null) Set] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclANY x = (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau>
                            then if (\<delta> x and OclNotEmpty x) \<tau> = true \<tau>
                                 then SOME y. y \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>
                                 else null \<tau>
                            else \<bottom> )"
notation   OclANY   ("_->any'(')")

(* actually, this definition covers only: X->any(true) of the standard, which foresees
a (totally correct) high-level definition
source->any(iterator | body) =
source->select(iterator | body)->asSequence()->first(). Since we don't have sequences,
we have to go for a direct---restricted---definition. *)


text{* The definition of OclForall mimics the one of @{term "OclAnd"}:
OclForall is not a strict operation. *}
definition OclForall     :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall S P = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau>
                                 then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = false \<tau>)
                                      then false \<tau>
                                      else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = invalid \<tau>)
                                           then invalid \<tau>
                                           else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = null \<tau>)
                                                then null \<tau>
                                                else true \<tau>
                                 else \<bottom>)"
syntax
  "_OclForall" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forAll'(_|_')")
translations
  "X->forAll(x | P)" == "CONST OclForall X (%x. P)"

text{* Like OclForall, OclExists is also not strict. *}
definition OclExists     :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclExists S P = not(OclForall S (\<lambda> X. not (P X)))"

syntax
  "_OclExist" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->exists'(_|_')")
translations
  "X->exists(x | P)" == "CONST OclExists X (%x. P)"

definition OclIterate :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<beta>::null)val,
                             ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where "OclIterate S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>
                                  then (Finite_Set.fold (F) (A) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))\<tau>
                                  else \<bottom>)"
syntax
  "_OclIterate"  :: "[('\<AA>,'\<alpha>::null) Set, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate'(_;_=_ | _')" (*[71,100,70]50*))
translations
  "X->iterate(a; x = A | P)" == "CONST OclIterate X A (%a. (% x. P))"

definition OclSelect :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>)Set"
where "OclSelect S P = (\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau>
                              then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = invalid \<tau>)
                                   then invalid \<tau>
                                   else Abs_Set_0 \<lfloor>\<lfloor>{x\<in>\<lceil>\<lceil> Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}\<rfloor>\<rfloor>
                              else invalid \<tau>)"
syntax
  "_OclSelect" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->select'(_|_')")
translations
  "X->select(x | P)" == "CONST OclSelect X (% x. P)"

definition OclReject :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>::null)Set"
where "OclReject S P = OclSelect S (not o P)"
syntax
  "_OclReject" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->reject'(_|_')")
translations
  "X->reject(x | P)" == "CONST OclReject X (% x. P)"

subsubsection{* Definition (futur operators) *}

consts (* abstract set collection operations *)
    OclCount       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Integer"
    OclSum         :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"
    OclIncludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclExcludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclComplement  :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclUnion       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclIntersection:: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"

notation
    OclCount       ("_->count'(_')" (*[66,65]65*))
notation
    OclSum         ("_->sum'(')" (*[66]*))
notation
    OclIncludesAll ("_->includesAll'(_')" (*[66,65]65*))
notation
    OclExcludesAll ("_->excludesAll'(_')" (*[66,65]65*))
notation
    OclComplement  ("_->complement'(')")
notation
    OclUnion       ("_->union'(_')"          (*[66,65]65*))
notation
    OclIntersection("_->intersection'(_')"   (*[71,70]70*))

subsection{* Validity and Definedness Properties *}

subsubsection{* OclIncluding *}

lemma OclIncluding_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->including(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(simp add: null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
           \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have D: "(\<tau> \<Turnstile> \<delta>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->including(x)))"
          apply(subst OclIncluding_def, subst OclValid_def, subst defined_def)
          apply(auto simp: OclValid_def null_Set_0_def bot_Set_0_def null_fun_def bot_fun_def)
           apply(frule Abs_Set_0_inject[OF C A, simplified OclValid_def, THEN iffD1],
                 simp_all add: bot_option_def)
          apply(frule Abs_Set_0_inject[OF C B, simplified OclValid_def, THEN iffD1],
                simp_all add: bot_option_def)
          done
show ?thesis by(auto dest:D intro:E)
qed



lemma OclIncluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->including(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have D: "(\<tau> \<Turnstile> \<upsilon>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->including(x)))"
          by(simp add: foundation20 OclIncluding_defined_args_valid)
show ?thesis by(auto dest:D intro:E)
qed

lemma OclIncluding_defined_args_valid'[simp,code_unfold]:
"\<delta>(X->including(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclIncluding_defined_args_valid foundation10 defined_and_I)

lemma OclIncluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->including(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclIncluding_valid_args_valid foundation10 defined_and_I)


subsubsection{* OclExcluding *}

lemma OclExcluding_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->excluding(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(simp add: null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
           \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have D: "(\<tau> \<Turnstile> \<delta>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->excluding(x)))"
          apply(subst OclExcluding_def, subst OclValid_def, subst defined_def)
          apply(auto simp: OclValid_def null_Set_0_def bot_Set_0_def null_fun_def bot_fun_def)
           apply(frule Abs_Set_0_inject[OF C A, simplified OclValid_def, THEN iffD1],
                 simp_all add: bot_option_def)
          apply(frule Abs_Set_0_inject[OF C B, simplified OclValid_def, THEN iffD1],
                simp_all add: bot_option_def)
          done
show ?thesis by(auto dest:D intro:E)
qed


lemma OclExcluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excluding(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have D: "(\<tau> \<Turnstile> \<upsilon>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->excluding(x)))"
          by(simp add: foundation20 OclExcluding_defined_args_valid)
show ?thesis by(auto dest:D intro:E)
qed


lemma OclExcluding_valid_args_valid'[simp,code_unfold]:
"\<delta>(X->excluding(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclExcluding_defined_args_valid foundation10 defined_and_I)


lemma OclExcluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excluding(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclExcluding_valid_args_valid foundation10 defined_and_I)

subsubsection{* OclIncludes *}

lemma OclIncludes_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->includes(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A: "(\<tau> \<Turnstile> \<delta>(X->includes(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncludes_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have B: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->includes(x)))"
          by(auto simp: OclIncludes_def OclValid_def true_def false_def StrongEq_def
                           defined_def invalid_def valid_def bot_fun_def null_fun_def
                           bot_option_def null_option_def
                     split: bool.split_asm HOL.split_if_asm option.split)
show ?thesis by(auto dest:A intro:B)
qed

lemma OclIncludes_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->includes(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A: "(\<tau> \<Turnstile> \<upsilon>(X->includes(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncludes_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have B: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->includes(x)))"
          by(auto simp: OclIncludes_def OclValid_def true_def false_def StrongEq_def
                           defined_def invalid_def valid_def bot_fun_def null_fun_def
                           bot_option_def null_option_def
                     split: bool.split_asm HOL.split_if_asm option.split)
show ?thesis by(auto dest:A intro:B)
qed

lemma OclIncludes_valid_args_valid'[simp,code_unfold]:
"\<delta>(X->includes(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclIncludes_defined_args_valid foundation10 defined_and_I)

lemma OclIncludes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->includes(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclIncludes_valid_args_valid foundation10 defined_and_I)

subsubsection{* OclExcludes *}

lemma OclExcludes_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->excludes(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (metis (hide_lams, no_types)
     OclExcludes_def OclAnd_idem OclOr_def OclOr_idem defined_not_I OclIncludes_defined_args_valid)

lemma OclExcludes_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excludes(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
by (metis (hide_lams, no_types)
     OclExcludes_def OclAnd_idem OclOr_def OclOr_idem valid_not_I OclIncludes_valid_args_valid)

lemma OclExcludes_valid_args_valid'[simp,code_unfold]:
"\<delta>(X->excludes(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclExcludes_defined_args_valid foundation10 defined_and_I)

lemma OclExcludes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excludes(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:OclExcludes_valid_args_valid foundation10 defined_and_I)

subsubsection{* OclSize *}

lemma OclSize_defined_args_valid: "\<tau> \<Turnstile> \<delta> (X->size()) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
by(auto simp: OclSize_def OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def bot_fun_def null_fun_def
        split: bool.split_asm HOL.split_if_asm option.split)

lemma OclSize_infinite:
assumes non_finite:"\<tau> \<Turnstile> not(\<delta>(S->size()))"
shows   "(\<tau> \<Turnstile> not(\<delta>(S))) \<or> \<not> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
apply(insert non_finite, simp)
apply(rule impI)
apply(simp add: OclSize_def OclValid_def defined_def)
apply(case_tac "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>",
      simp_all add:null_fun_def null_option_def bot_fun_def bot_option_def)
done

lemma "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->size())"
by(simp add: OclSize_def OclValid_def defined_def bot_fun_def false_def true_def)

lemma size_defined:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> (X->size()) = \<delta> X"
 apply(rule ext, simp add: cp_defined[of "X->size()"] OclSize_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

lemma size_defined':
 assumes X_finite: "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "(\<tau> \<Turnstile> \<delta> (X->size())) = (\<tau> \<Turnstile> \<delta> X)"
 apply(simp add: cp_defined[of "X->size()"] OclSize_def OclValid_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

subsubsection{* OclIsEmpty *}

lemma OclIsEmpty_defined_args_valid:"\<tau> \<Turnstile> \<delta> (X->isEmpty()) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
  apply(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
                   bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def
             split: split_if_asm)
  apply(case_tac "(X->size() \<doteq> \<zero>) \<tau>", simp add: bot_option_def, simp, rename_tac x)
  apply(case_tac x, simp add: null_option_def bot_option_def, simp)
  apply(simp add: OclSize_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def)
by (metis (hide_lams, no_types)
          OCL_core.bot_fun_def OclValid_def defined_def foundation2 invalid_def)

lemma "\<tau> \<Turnstile> \<delta> (null->isEmpty())"
by(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
              bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def null_is_valid
        split: split_if_asm)

lemma OclIsEmpty_infinite: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->isEmpty())"
  apply(auto simp: OclIsEmpty_def OclValid_def defined_def valid_def false_def true_def
                   bot_fun_def null_fun_def OclAnd_def OclOr_def OclNot_def
             split: split_if_asm)
  apply(case_tac "(X->size() \<doteq> \<zero>) \<tau>", simp add: bot_option_def, simp, rename_tac x)
  apply(case_tac x, simp add: null_option_def bot_option_def, simp)
by(simp add: OclSize_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def bot_fun_def false_def true_def invalid_def)

subsubsection{* OclNotEmpty *}

lemma OclNotEmpty_defined_args_valid:"\<tau> \<Turnstile> \<delta> (X->notEmpty()) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> X"
by (metis (hide_lams, no_types) OclNotEmpty_def OclNot_defargs OclNot_not foundation6 foundation9
                                OclIsEmpty_defined_args_valid)

lemma "\<tau> \<Turnstile> \<delta> (null->notEmpty())"
by (metis (hide_lams, no_types) OclNotEmpty_def OclAnd_false1 OclAnd_idem OclIsEmpty_def
                                OclNot3 OclNot4 OclOr_def defined2 defined4 transform1 valid2)

lemma OclNotEmpty_infinite: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<not> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->notEmpty())"
 apply(simp add: OclNotEmpty_def)
 apply(drule OclIsEmpty_infinite, simp)
by (metis OclNot_defargs OclNot_not foundation6 foundation9)

lemma OclNotEmpty_has_elt : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                          \<tau> \<Turnstile> X->notEmpty() \<Longrightarrow>
                          \<exists>e. e \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 apply(simp add: OclNotEmpty_def OclIsEmpty_def deMorgan1 deMorgan2, drule foundation5)
 apply(subst (asm) (2) OclNot_def,
       simp add: OclValid_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def
            split: split_if_asm)
  prefer 2
  apply(simp add: invalid_def bot_option_def true_def)
 apply(simp add: OclSize_def valid_def split: split_if_asm,
       simp_all add: false_def true_def bot_option_def bot_fun_def OclInt0_def)
by (metis equals0I)

subsubsection{* OclANY *}

lemma OclANY_defined_args_valid: "\<tau> \<Turnstile> \<delta> (X->any()) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
by(auto simp: OclANY_def OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def bot_fun_def null_fun_def OclAnd_def
        split: bool.split_asm HOL.split_if_asm option.split)

lemma "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> X->isEmpty() \<Longrightarrow> \<not> \<tau> \<Turnstile> \<delta> (X->any())"
 apply(simp add: OclANY_def OclValid_def)
 apply(subst cp_defined, subst cp_OclAnd, simp add: OclNotEmpty_def, subst (1 2) cp_OclNot,
       simp add: cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_defined[symmetric],
       simp add: false_def true_def)
by(drule foundation20[simplified OclValid_def true_def], simp)

lemma OclANY_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->any())) = (\<tau> \<Turnstile> \<upsilon> X)"
proof -
 have A: "(\<tau> \<Turnstile> \<upsilon>(X->any())) \<Longrightarrow> ((\<tau> \<Turnstile>(\<upsilon> X)))"
          by(auto simp: OclANY_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have B: "(\<tau> \<Turnstile>(\<upsilon> X)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->any()))"
           apply(auto simp: OclANY_def OclValid_def true_def false_def StrongEq_def
                            defined_def invalid_def valid_def bot_fun_def null_fun_def
                            bot_option_def null_option_def null_is_valid
                            OclAnd_def
                      split: bool.split_asm HOL.split_if_asm option.split)
           apply(frule Set_inv_lemma[OF foundation16[THEN iffD2], OF conjI], simp)
           apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau>")
            prefer 2
            apply (metis (hide_lams, no_types) OclValid_def foundation16)
           apply(simp add: true_def,
                 drule OclNotEmpty_has_elt[simplified OclValid_def true_def], simp)
          by(erule exE,
             insert someI2[where Q = "\<lambda>x. x \<noteq> \<bottom>" and P = "\<lambda>y. y \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"],
             simp)
 show ?thesis by(auto dest:A intro:B)
qed

lemma OclANY_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->any()) = (\<upsilon> X)"
by(auto intro!: OclANY_valid_args_valid transform2_rev)

(* and higher order ones : forall, exists, iterate, select, reject... *)

subsection{* Execution with Invalid or Null or Infinite Set as Argument *}


subsubsection{* OclIncluding *}

lemma OclIncluding_invalid[simp,code_unfold]:"(invalid->including(x)) = invalid"
by(simp add: bot_fun_def OclIncluding_def invalid_def defined_def valid_def false_def true_def)

lemma OclIncluding_invalid_args[simp,code_unfold]:"(X->including(invalid)) = invalid"
by(simp add: OclIncluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma OclIncluding_null[simp,code_unfold]:"(null->including(x)) = invalid"
by(simp add: OclIncluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)


subsubsection{* OclExcluding *}

lemma OclExcluding_invalid[simp,code_unfold]:"(invalid->excluding(x)) = invalid"
by(simp add: bot_fun_def OclExcluding_def invalid_def defined_def valid_def false_def true_def)

lemma OclExcluding_invalid_args[simp,code_unfold]:"(X->excluding(invalid)) = invalid"
by(simp add: OclExcluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma OclExcluding_null[simp,code_unfold]:"(null->excluding(x)) = invalid"
by(simp add: OclExcluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

subsubsection{* OclIncludes *}

lemma OclIncludes_invalid[simp,code_unfold]:"(invalid->includes(x)) = invalid"
by(simp add: bot_fun_def OclIncludes_def invalid_def defined_def valid_def false_def true_def)

lemma OclIncludes_invalid_args[simp,code_unfold]:"(X->includes(invalid)) = invalid"
by(simp add: OclIncludes_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma OclIncludes_null[simp,code_unfold]:"(null->includes(x)) = invalid"
by(simp add: OclIncludes_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

subsubsection{* OclExcludes *}

lemma OclExcludes_invalid[simp,code_unfold]:"(invalid->excludes(x)) = invalid"
by(simp add: OclExcludes_def OclNot_def, simp add: invalid_def bot_option_def)

lemma OclExcludes_invalid_args[simp,code_unfold]:"(X->excludes(invalid)) = invalid"
by(simp add: OclExcludes_def OclNot_def, simp add: invalid_def bot_option_def)

lemma OclExcludes_null[simp,code_unfold]:"(null->excludes(x)) = invalid"
by(simp add: OclExcludes_def OclNot_def, simp add: invalid_def bot_option_def)

subsubsection{* OclSize *}

lemma OclSize_invalid[simp,code_unfold]:"(invalid->size()) = invalid"
by(simp add: bot_fun_def OclSize_def invalid_def defined_def valid_def false_def true_def)

lemma OclSize_null[simp,code_unfold]:"(null->size()) = invalid"
by(rule ext,
   simp add: bot_fun_def null_fun_def null_is_valid OclSize_def
             invalid_def defined_def valid_def false_def true_def)

subsubsection{* OclIsEmpty *}

lemma OclIsEmpty_invalid[simp,code_unfold]:"(invalid->isEmpty()) = invalid"
by(simp add: OclIsEmpty_def)

lemma OclIsEmpty_null[simp,code_unfold]:"(null->isEmpty()) = true"
by(simp add: OclIsEmpty_def)

subsubsection{* OclNotEmpty *}

lemma OclNotEmpty_invalid[simp,code_unfold]:"(invalid->notEmpty()) = invalid"
by(simp add: OclNotEmpty_def)

lemma OclNotEmpty_null[simp,code_unfold]:"(null->notEmpty()) = false"
by(simp add: OclNotEmpty_def)

subsubsection{* OclANY *}

lemma OclANY_invalid[simp,code_unfold]:"(invalid->any()) = invalid"
by(simp add: bot_fun_def OclANY_def invalid_def defined_def valid_def false_def true_def)

lemma OclANY_null[simp,code_unfold]:"(null->any()) = null"
by(simp add: OclANY_def false_def true_def)

subsubsection{* OclForall *}

lemma OclForall_invalid[simp,code_unfold]:"invalid->forAll(a| P a) = invalid"
by(simp add: bot_fun_def invalid_def OclForall_def defined_def valid_def false_def true_def)

lemma OclForall_null[simp,code_unfold]:"null->forAll(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclForall_def defined_def valid_def false_def true_def)

subsubsection{* OclExists *}

lemma OclExists_invalid[simp,code_unfold]:"invalid->exists(a| P a) = invalid"
by(simp add: OclExists_def)

lemma OclExists_null[simp,code_unfold]:"null->exists(a | P a) = invalid"
by(simp add: OclExists_def)

subsubsection{* OclIterate *}

lemma OclIterate_invalid[simp,code_unfold]:"invalid->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

lemma OclIterate_null[simp,code_unfold]:"null->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)


lemma OclIterate_invalid_args[simp,code_unfold]:"S->iterate(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate_def defined_def valid_def false_def true_def)

text{* An open question is this ... *}
lemma (*OclIterate_null_args[simp,code_unfold]:*) "S->iterate(a; x = null | P a x) = invalid"
oops
(* In the definition above, this does not hold in general.
       And I believe, this is how it should be ... *)

lemma OclIterate_infinite:
assumes non_finite: "\<tau> \<Turnstile> not(\<delta>(S->size()))"
shows "(OclIterate S A F) \<tau> = invalid \<tau>"
apply(insert non_finite [THEN OclSize_infinite])
apply(subst (asm) foundation9, simp)
by(metis OclIterate_def OclValid_def invalid_def)

subsubsection{* OclSelect *}

lemma OclSelect_invalid[simp,code_unfold]:"invalid->select(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclSelect_def defined_def valid_def false_def true_def)

lemma OclSelect_null[simp,code_unfold]:"null->select(a | P a) = invalid"
by(simp add: bot_fun_def invalid_def OclSelect_def defined_def valid_def false_def true_def)

subsubsection{* OclReject *}

lemma OclReject_invalid[simp,code_unfold]:"invalid->reject(a | P a) = invalid"
by(simp add: OclReject_def)

lemma OclReject_null[simp,code_unfold]:"null->reject(a | P a) = invalid"
by(simp add: OclReject_def)

subsection{* Context Passing *}

lemma cp_OclIncluding:
"(X->including(x)) \<tau> = ((\<lambda> _. X \<tau>)->including(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncluding_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclExcluding:
"(X->excluding(x)) \<tau> = ((\<lambda> _. X \<tau>)->excluding(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclExcluding_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclIncludes:
"(X->includes(x)) \<tau> = ((\<lambda> _. X \<tau>)->includes(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclIncludes1:
"(X->includes(x)) \<tau> = (X->includes(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclExcludes:
"(X->excludes(x)) \<tau> = ((\<lambda> _. X \<tau>)->excludes(\<lambda> _. x \<tau>)) \<tau>"
by(simp add: OclExcludes_def OclNot_def, subst cp_OclIncludes, simp)

lemma cp_OclSize: "X->size() \<tau> = ((\<lambda>_. X \<tau>)->size()) \<tau>"
by(simp add: OclSize_def cp_defined[symmetric])

lemma cp_OclIsEmpty: "X->isEmpty() \<tau> = ((\<lambda>_. X \<tau>)->isEmpty()) \<tau>"
 apply(simp only: OclIsEmpty_def)
 apply(subst (2) cp_OclOr,
       subst cp_OclAnd,
       subst cp_OclNot,
       subst cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r)
by(simp add: cp_defined[symmetric] cp_valid[symmetric] cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[symmetric]
             cp_OclSize[symmetric] cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])

lemma cp_OclNotEmpty: "X->notEmpty() \<tau> = ((\<lambda>_. X \<tau>)->notEmpty()) \<tau>"
 apply(simp only: OclNotEmpty_def)
 apply(subst (2) cp_OclNot)
by(simp add: cp_OclNot[symmetric] cp_OclIsEmpty[symmetric])

lemma cp_OclANY: "X->any() \<tau> = ((\<lambda>_. X \<tau>)->any()) \<tau>"
 apply(simp only: OclANY_def)
 apply(subst (2) cp_OclAnd)
by(simp only: cp_OclAnd[symmetric] cp_defined[symmetric] cp_valid[symmetric]
              cp_OclNotEmpty[symmetric])

lemma cp_OclForall:
"(S->forAll(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->forAll(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclForall_def cp_defined[symmetric])

(* first-order version !*)
lemma cp_OclForall1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->forAll(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, intro allI)
apply(erule_tac x=X in allE)
by(subst cp_OclForall, simp)

lemma (*cp_OclForall2 [simp,intro!]:*)
"cp (\<lambda>X St x. P (\<lambda>\<tau>. x) X St) \<Longrightarrow> cp S \<Longrightarrow> cp (\<lambda>X. (S X)->forAll(x|P x X)) "
apply(simp only: cp_def)
oops

lemma (*cp_OclForall:*)
"cp S \<Longrightarrow>
 (\<And> x. cp(P x)) \<Longrightarrow>
 cp(\<lambda>X. ((S X)->forAll(x | P x X)))"
oops

(*

lemma cp_OclForall2 [simp,intro!]:
"\<lbrakk> cp (\<lambda> X St.(\<lambda>x. P (\<lambda>\<tau>. x) X St));
   cp (S :: (('a,'c)VAL \<Rightarrow> ('a,('b::bot))Set)) \<rbrakk>
 \<Longrightarrow> cp(\<lambda>X. \<MathOclForAll> Y \<in> S X \<bullet> P (Y\<Colon>'a \<Rightarrow> 'b) X) "
apply(simp only: cp_def OclForAll_def)
apply(erule exE)+
apply(rule exI, rule allI, rule allI)
apply (simp only:)
apply(rule_tac t = "(\<lambda>x. P (\<lambda>\<tau>. x) X \<tau> )" and
               s = "f (X \<tau> ) \<tau> " in subst)
prefer 2
ML{* Unify.search_bound:=1000; *}
apply(rule refl)
ML{* Unify.search_bound:=20; *}
(* Miracle ! This works. Definitively a unification problem !!! *)
apply simp
done  (* temporary solution. *)
      (* TODO: improve !!! *)

*)

lemma cp_OclExists:
"(S->exists(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->exists(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclExists_def OclNot_def, subst cp_OclForall, simp)

(* first-order version !*)
lemma cp_OclExists1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->exists(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, intro allI)
apply(erule_tac x=X in allE)
by(subst cp_OclExists,simp)

lemma cp_OclIterate: "(X->iterate(a; x = A | P a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate(a; x = A | P a x)) \<tau>"
by(simp add: OclIterate_def cp_defined[symmetric])

lemma cp_OclSelect: "(X->select(a | P a)) \<tau> =
                ((\<lambda> _. X \<tau>)->select(a | P a)) \<tau>"
by(simp add: OclSelect_def cp_defined[symmetric])

lemma cp_OclReject: "(X->reject(a | P a)) \<tau> =
                ((\<lambda> _. X \<tau>)->reject(a | P a)) \<tau>"
by(simp add: OclReject_def, subst cp_OclSelect, simp)

lemmas cp_intro''[intro!,simp,code_unfold] =
       cp_intro'
       cp_OclIncluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncluding"]]
       cp_OclExcluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclExcluding"]]
       cp_OclIncludes  [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncludes"]]
       cp_OclExcludes  [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclExcludes"]]
       cp_OclSize      [THEN allI[THEN allI[THEN cpI1], of "OclSize"]]
       cp_OclIsEmpty   [THEN allI[THEN allI[THEN cpI1], of "OclIsEmpty"]]
       cp_OclNotEmpty  [THEN allI[THEN allI[THEN cpI1], of "OclNotEmpty"]]
       cp_OclANY      [THEN allI[THEN allI[THEN cpI1], of "OclANY"]]

subsection{* Const *}

lemma const_OclIncluding[simp,code_unfold] :
 assumes const_x : "const x"
     and const_S : "const S"
   shows  "const (S->including(x))"
   proof -
     have A:"\<And>\<tau> \<tau>'. \<not> (\<tau> \<Turnstile> \<upsilon> x) \<Longrightarrow> (S->including(x) \<tau>) = (S->including(x) \<tau>')"
            apply(simp add: foundation18)
            apply(erule const_subst[OF const_x const_invalid],simp_all)
            by(rule const_charn[OF const_invalid])
     have B: "\<And> \<tau> \<tau>'. \<not> (\<tau> \<Turnstile> \<delta> S) \<Longrightarrow> (S->including(x) \<tau>) = (S->including(x) \<tau>')"
            apply(simp add: foundation16', elim disjE)
            apply(erule const_subst[OF const_S const_invalid],simp_all)
            apply(rule const_charn[OF const_invalid])
            apply(erule const_subst[OF const_S const_null],simp_all)
            by(rule const_charn[OF const_invalid])
     show ?thesis
       apply(simp only: const_def,intro allI, rename_tac \<tau> \<tau>')
       apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> x)", simp add: A)
       apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> S)", simp_all add: B)
       apply(frule_tac \<tau>'1= \<tau>' in  const_OclValid2[OF const_x, THEN iffD1])
       apply(frule_tac \<tau>'1= \<tau>' in  const_OclValid1[OF const_S, THEN iffD1])
       apply(simp add: OclIncluding_def OclValid_def)
       apply(subst const_charn[OF const_x])
       apply(subst const_charn[OF const_S])
       by simp
qed

(*
lemma const_OclForall :
  assumes "const X"
  assumes "\<And>x \<tau>1 \<tau>2. x \<tau>1 = x \<tau>2 \<Longrightarrow> X' x \<tau>1 = X' x \<tau>2"
  shows "const (OclForall X X')"
 apply(simp only: const_def, intro allI)
 proof - fix \<tau>1 \<tau>2 show "OclForall X X' \<tau>1 = OclForall X X' \<tau>2"
  apply(subst (1 2) cp_OclForall, simp only: OclForall_def cp_defined[symmetric])
 by(simp only: const_defined[OF assms(1), simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_true[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_false[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_null[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_bot[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  assms(1)[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  assms(2)[of _ \<tau>1 \<tau>2])
qed

lemma const_OclIncludes :
  assumes "const X"
  assumes "const X'"
  shows "const (OclIncludes X X')"
 apply(rule const_imply3[OF _ assms], subst (1 2) cp_OclIncludes, simp only: OclIncludes_def cp_defined[symmetric] cp_valid[symmetric])
 apply(simp add:
  const_defined[OF assms(1), simplified const_def, THEN spec, THEN spec]
  const_valid[OF assms(2), simplified const_def, THEN spec, THEN spec]
  const_true[simplified const_def, THEN spec, THEN spec] assms[simplified const_def]
  bot_option_def)
by (metis (no_types) const_def const_defined const_true const_valid cp_defined cp_valid)

*)

section{* Fundamental Predicates on Set: Strict Equality *}

subsection{* Definition *}

text{* After the part of foundational operations on sets, we detail here equality on sets.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:*}

defs   StrictRefEq\<^sub>S\<^sub>e\<^sub>t :
      "(x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                         then (x \<triangleq> y)\<tau>
                                         else invalid \<tau>"

text{* One might object here that for the case of objects, this is an empty definition.
The answer is no, we will restrain later on states and objects such that any object
has its oid stored inside the object (so the ref, under which an object can be referenced
in the store will represented in the object itself). For such well-formed stores that satisfy
this invariant (the WFF-invariant), the referential equality and the
strong equality---and therefore the strict equality on sets in the sense above---coincides.*}

subsection{* Logic and Algebraic Layer on Set *}

subsubsection{* Reflexivity *}

text{* To become operational, we derive: *}

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_refl[simp,code_unfold]:
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclIf_def)

subsubsection{* Symmetry *}

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_sym:
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) = (y \<doteq> x)"
by(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t, subst StrongEq_sym, rule ext, simp)

subsubsection{* Execution with Invalid or Null as Argument *}

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict1[simp,code_unfold]: "((x::('\<AA>,'\<alpha>::null)Set) \<doteq> invalid)= invalid"
by(simp add:StrictRefEq\<^sub>S\<^sub>e\<^sub>t false_def true_def)

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict2[simp,code_unfold]: "(invalid \<doteq> (y::('\<AA>,'\<alpha>::null)Set))= invalid"
by(simp add:StrictRefEq\<^sub>S\<^sub>e\<^sub>t false_def true_def)



lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strictEq_valid_args_valid:
"(\<tau> \<Turnstile> \<delta> ((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
proof -
   have A: "\<tau> \<Turnstile> \<delta> (x \<doteq> y) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> \<tau> \<Turnstile> \<upsilon> y"
           apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t valid_def OclValid_def defined_def)
           apply(simp add: invalid_def bot_fun_def split: split_if_asm)
           done
   have B: "(\<tau> \<Turnstile> \<upsilon> x) \<and> (\<tau> \<Turnstile> \<upsilon> y) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (x \<doteq> y)"
           apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t, elim conjE)
           apply(drule foundation13[THEN iffD2],drule foundation13[THEN iffD2])
           apply(rule foundation23[THEN iffD2])
           apply(subst cp_defined, simp add: foundation22)
           apply(simp add: cp_defined[symmetric] foundation23[symmetric])
           done
   show ?thesis by(auto intro!: A B)
qed



subsubsection{* Behavior vs StrongEq *}

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_vs_StrongEq:
"\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(drule foundation13[THEN iffD2],drule foundation13[THEN iffD2])
by(simp add:StrictRefEq\<^sub>S\<^sub>e\<^sub>t foundation22)

subsubsection{* Context Passing *}


lemma cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t:"((X::('\<AA>,'\<alpha>::null)Set) \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
by(simp add:StrictRefEq\<^sub>S\<^sub>e\<^sub>t cp_StrongEq[symmetric] cp_valid[symmetric])


subsubsection{* Const *}

lemma const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t :
  assumes "const (X :: (_,_::null) Set)"
  assumes "const X'"
  shows "const (X \<doteq> X')"
 apply(simp only: const_def, intro allI)
 proof -
 fix \<tau>1 \<tau>2 show "(X \<doteq> X') \<tau>1 = (X \<doteq> X') \<tau>2"
  apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t)
 by(simp add: const_valid[OF assms(1), simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_valid[OF assms(2), simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_true[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_invalid[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_StrongEq[OF assms, simplified const_def, THEN spec, THEN spec])
qed


section{* Execution on Set's Operators (with mtSet and recursive case as arguments) *}

subsection{* OclIncluding *}

lemma OclIncluding_finite_rep_set :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert X_def x_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclIncluding_def Abs_Set_0_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma OclIncluding_rep_set:
 assumes S_def: "\<tau> \<Turnstile> \<delta> S"
   shows "\<lceil>\<lceil>Rep_Set_0 (S->including(\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) \<tau>)\<rceil>\<rceil> = insert \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 apply(simp add: OclIncluding_def S_def[simplified OclValid_def])
 apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF S_def], metis bot_option_def not_Some_eq)
 by(simp)

lemma OclIncluding_notempty_rep_set:
 assumes X_def: "\<tau> \<Turnstile> \<delta> X"
     and a_val: "\<tau> \<Turnstile> \<upsilon> a"
  shows "\<lceil>\<lceil>Rep_Set_0 (X->including(a) \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(simp add: OclIncluding_def X_def[simplified OclValid_def] a_val[simplified OclValid_def])
 apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF X_def], metis a_val foundation18')
 by(simp)

lemma OclIncluding_includes0:
 assumes "\<tau> \<Turnstile> X->includes(x)"
   shows "X->including(x) \<tau> = X \<tau>"
proof -
 have includes_def: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
 by (metis OCL_core.bot_fun_def OclIncludes_def OclValid_def defined3 foundation16)

 have includes_val: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
 by (metis (hide_lams, no_types) foundation6
       OclIncludes_valid_args_valid' OclIncluding_valid_args_valid OclIncluding_valid_args_valid'')

 show ?thesis
  apply(insert includes_def[OF assms] includes_val[OF assms] assms,
        simp add: OclIncluding_def OclIncludes_def OclValid_def true_def)
  apply(drule insert_absorb, simp, subst abs_rep_simp')
 by(simp_all add: OclValid_def true_def)
qed

lemma OclIncluding_includes:
 assumes "\<tau> \<Turnstile> X->includes(x)"
   shows "\<tau> \<Turnstile> X->including(x) \<triangleq> X"
by(simp add: StrongEq_def OclValid_def true_def OclIncluding_includes0[OF assms])

lemma OclIncluding_commute0 :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, 'a::null) Set)->including(i)->including(j) \<triangleq> (S->including(j)->including(i)))"
proof -
  have A : "\<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def i_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)
  have B : "\<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def j_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)

  have G1 : "Abs_Set_0 \<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
           by(insert A, simp add: Abs_Set_0_inject bot_option_def null_option_def)
  have G2 : "Abs_Set_0 \<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
           by(insert A, simp add: Abs_Set_0_inject bot_option_def null_option_def)
  have G3 : "Abs_Set_0 \<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
           by(insert B, simp add: Abs_Set_0_inject bot_option_def null_option_def)
  have G4 : "Abs_Set_0 \<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
           by(insert B, simp add: Abs_Set_0_inject bot_option_def null_option_def)

  have *   : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (i \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set_0_def  null_Set_0_def S_def i_val G1 G2)

  have **  : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (j \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set_0_def  null_Set_0_def S_def i_val G3 G4)

  have *** : "Abs_Set_0 \<lfloor>\<lfloor>insert(j \<tau>)\<lceil>\<lceil>Rep_Set_0(Abs_Set_0\<lfloor>\<lfloor>insert(i \<tau>)\<lceil>\<lceil>Rep_Set_0(S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)\<rceil>\<rceil>\<rfloor>\<rfloor> =
              Abs_Set_0 \<lfloor>\<lfloor>insert(i \<tau>)\<lceil>\<lceil>Rep_Set_0(Abs_Set_0\<lfloor>\<lfloor>insert(j \<tau>)\<lceil>\<lceil>Rep_Set_0(S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)\<rceil>\<rceil>\<rfloor>\<rfloor>"
              by(simp add: Abs_Set_0_inverse[OF A] Abs_Set_0_inverse[OF B] Set.insert_commute)
  show ?thesis
     apply(simp add: OclIncluding_def S_def[simplified OclValid_def]
                  i_val[simplified OclValid_def] j_val[simplified OclValid_def]
                  true_def OclValid_def StrongEq_def)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def ** ***)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * )
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * **)
     done
qed


lemma OclIncluding_commute[simp,code_unfold]:
"((S :: ('\<AA>, 'a::null) Set)->including(i)->including(j) = (S->including(j)->including(i)))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including(i)->including(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A': "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including(j)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B:"\<And> \<tau>.   \<tau> \<Turnstile> (j \<triangleq> invalid)   \<Longrightarrow> (S->including(i)->including(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B':"\<And> \<tau>.   \<tau> \<Turnstile> (j \<triangleq> invalid)   \<Longrightarrow> (S->including(j)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including(i)->including(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including(j)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including(i)->including(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including(j)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<upsilon> j)")
      apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
       apply(simp only: OclIncluding_commute0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
     apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
    apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 B[OF foundation22[THEN iffD2]] B'[OF foundation22[THEN iffD2]])
  apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
 done
qed


subsection{* OclExcluding *}

lemma OclExcluding_finite_rep_set :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert X_def x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclExcluding_def Abs_Set_0_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma OclExcluding_rep_set:
 assumes S_def: "\<tau> \<Turnstile> \<delta> S"
   shows "\<lceil>\<lceil>Rep_Set_0 (S->excluding(\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {\<lfloor>\<lfloor>x\<rfloor>\<rfloor>}"
 apply(simp add: OclExcluding_def S_def[simplified OclValid_def])
 apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
  apply(insert Set_inv_lemma[OF S_def], metis Diff_iff bot_option_def not_None_eq)
by(simp)

lemma OclExcluding_excludes0:
 assumes "\<tau> \<Turnstile> X->excludes(x)"
   shows "X->excluding(x) \<tau> = X \<tau>"
proof -
 have excludes_def: "\<tau> \<Turnstile> X->excludes(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
 by (metis (hide_lams, no_types) OclExcludes_defined_args_valid foundation6)

 have excludes_val: "\<tau> \<Turnstile> X->excludes(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
 by (metis (hide_lams, no_types) OclExcludes_def OclIncludes_defined_args_valid OclNot_defargs)

 show ?thesis
  apply(insert excludes_def[OF assms] excludes_val[OF assms] assms,
        simp add: OclExcluding_def OclExcludes_def OclIncludes_def OclNot_def OclValid_def true_def)
 by (metis (hide_lams, no_types) abs_rep_simp' assms excludes_def)
qed

lemma OclExcluding_excludes:
 assumes "\<tau> \<Turnstile> X->excludes(x)"
   shows "\<tau> \<Turnstile> X->excluding(x) \<triangleq> X"
by(simp add: StrongEq_def OclValid_def true_def OclExcluding_excludes0[OF assms])

lemma OclExcluding_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> ((Set{}->excluding(x))  \<triangleq>  Set{})"
proof -
  have A : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  by(simp add: null_option_def bot_option_def)
  have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)

  show ?thesis using val_x
    apply(auto simp: OclValid_def OclIncludes_def OclNot_def false_def true_def StrongEq_def
                     OclExcluding_def mtSet_def defined_def bot_fun_def null_fun_def null_Set_0_def)
     apply(auto simp: mtSet_def Set_0.Abs_Set_0_inverse
                      Set_0.Abs_Set_0_inject[OF B A])
  done
qed

lemma OclExcluding_commute0 :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, 'a::null) Set)->excluding(i)->excluding(j) \<triangleq> (S->excluding(j)->excluding(i)))"
proof -
  have A : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def i_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)
  have B : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(insert S_def j_val, frule Set_inv_lemma, simp add: foundation18 invalid_def)

  have G1 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
           by(insert A, simp add: Abs_Set_0_inject bot_option_def null_option_def)
  have G2 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
           by(insert A, simp add: Abs_Set_0_inject bot_option_def null_option_def)
  have G3 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
           by(insert B, simp add: Abs_Set_0_inject bot_option_def null_option_def)
  have G4 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
           by(insert B, simp add: Abs_Set_0_inject bot_option_def null_option_def)

  have *   : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {i \<tau>}\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set_0_def  null_Set_0_def S_def i_val G1 G2)

  have **  : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {j \<tau>}\<rfloor>\<rfloor>)) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
             by(auto simp: OclValid_def false_def  defined_def null_fun_def  true_def
                              bot_fun_def bot_Set_0_def  null_Set_0_def S_def i_val G3 G4)

  have *** : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0(Abs_Set_0\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0(S \<tau>)\<rceil>\<rceil>-{i \<tau>}\<rfloor>\<rfloor>)\<rceil>\<rceil>-{j \<tau>}\<rfloor>\<rfloor> =
              Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0(Abs_Set_0\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0(S \<tau>)\<rceil>\<rceil>-{j \<tau>}\<rfloor>\<rfloor>)\<rceil>\<rceil>-{i \<tau>}\<rfloor>\<rfloor>"
              apply(simp add: Abs_Set_0_inverse[OF A] Abs_Set_0_inverse[OF B])
             by (metis Diff_insert2 insert_commute)
  show ?thesis
     apply(simp add: OclExcluding_def S_def[simplified OclValid_def]
                  i_val[simplified OclValid_def] j_val[simplified OclValid_def]
                  true_def OclValid_def StrongEq_def)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def ** ***)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def *)
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * )
     apply(subst OCL_core.cp_defined,
           simp add: S_def[simplified OclValid_def]
                     i_val[simplified OclValid_def] j_val[simplified OclValid_def] true_def * **)
     done
qed


lemma OclExcluding_commute[simp,code_unfold]:
"((S :: ('\<AA>, 'a::null) Set)->excluding(i)->excluding(j) = (S->excluding(j)->excluding(i)))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> i \<triangleq> invalid   \<Longrightarrow> (S->excluding(i)->excluding(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A': "\<And> \<tau>.   \<tau> \<Turnstile> i \<triangleq> invalid   \<Longrightarrow> (S->excluding(j)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B:"\<And> \<tau>.   \<tau> \<Turnstile> j \<triangleq> invalid   \<Longrightarrow> (S->excluding(i)->excluding(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have B':"\<And> \<tau>.   \<tau> \<Turnstile> j \<triangleq> invalid   \<Longrightarrow> (S->excluding(j)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> S \<triangleq> invalid   \<Longrightarrow> (S->excluding(i)->excluding(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> S \<triangleq> invalid   \<Longrightarrow> (S->excluding(j)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> S \<triangleq> null   \<Longrightarrow> (S->excluding(i)->excluding(j)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> S \<triangleq> null   \<Longrightarrow> (S->excluding(j)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<upsilon> j)")
      apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
       apply(simp only: OclExcluding_commute0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
     apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
    apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 B[OF foundation22[THEN iffD2]] B'[OF foundation22[THEN iffD2]])
  apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
 done
qed


lemma OclExcluding_charn0_exec[simp,code_unfold]:
"(Set{}->excluding(x)) = (if (\<upsilon> x) then Set{} else invalid endif)"
proof -
  have A: "\<And> \<tau>. (Set{}->excluding(invalid)) \<tau> = (if (\<upsilon> invalid) then Set{} else invalid endif) \<tau>"
          by simp
  have B: "\<And> \<tau> x. \<tau> \<Turnstile> (\<upsilon> x) \<Longrightarrow>
                  (Set{}->excluding(x)) \<tau> = (if (\<upsilon> x) then Set{} else invalid endif) \<tau>"
          by(simp add: OclExcluding_charn0[THEN foundation22[THEN iffD1]])
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
     apply(simp add: B)
    apply(simp add: foundation18)
    apply(subst cp_OclExcluding, simp)
    apply(simp add: cp_OclIf[symmetric] cp_OclExcluding[symmetric] cp_valid[symmetric] A)
   done
qed

lemma OclExcluding_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> ((X->including(x))->excluding(y)) \<triangleq> ((X->excluding(y))->including(x))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have D : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have E : "x \<tau> \<noteq> y \<tau>"
          by(insert neq,
             auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def
                        false_def true_def defined_def valid_def bot_Set_0_def
                        null_fun_def null_Set_0_def StrongEq_def OclNot_def)

 have G1 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          by(insert C, simp add: Abs_Set_0_inject bot_option_def null_option_def)
 have G2 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          by(insert C, simp add: Abs_Set_0_inject bot_option_def null_option_def)
 have G : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          by(auto simp: OclValid_def false_def true_def defined_def
                        bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def G1 G2)

 have H1 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          by(insert D, simp add: Abs_Set_0_inject bot_option_def null_option_def)
 have H2 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          by(insert D, simp add: Abs_Set_0_inject bot_option_def null_option_def)
 have H : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          by(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def H1 H2)

 have Z : "insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>} = insert (x \<tau>) (\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>})"
          by(auto simp: E)
 show ?thesis
  apply(insert def_X[THEN  foundation13[THEN iffD2]] val_x[THEN  foundation13[THEN iffD2]]
               val_y[THEN  foundation13[THEN iffD2]])
  apply(simp add: foundation22 OclIncluding_def OclExcluding_def def_X[THEN foundation16[THEN iffD1,standard]])
  apply(subst cp_defined, simp)+
  apply(simp add: G H Abs_Set_0_inverse[OF C] Abs_Set_0_inverse[OF D] Z)
  done
qed



lemma OclExcluding_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (((X->including(x))->excluding(x)) \<triangleq> (X->excluding(x)))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 have G1 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          by(insert C, simp add: Abs_Set_0_inject bot_option_def null_option_def)
 have G2 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          by(insert C, simp add: Abs_Set_0_inject bot_option_def null_option_def)
 show ?thesis
   apply(insert def_X[THEN foundation16[THEN iffD1,standard]]
                val_x[THEN foundation18[THEN iffD1,standard]])
   apply(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def false_def true_def
                    invalid_def defined_def valid_def bot_Set_0_def null_fun_def null_Set_0_def
                    StrongEq_def)
   apply(subst cp_OclExcluding)
   apply(auto simp:OclExcluding_def)
            apply(simp add: Abs_Set_0_inverse[OF C])
           apply(simp_all add: false_def true_def defined_def valid_def
                               null_fun_def bot_fun_def null_Set_0_def bot_Set_0_def
                          split: bool.split_asm HOL.split_if_asm option.split)
   apply(auto simp: G1 G2)
  done
qed




theorem OclExcluding_charn3:  "((X->including(x))->excluding(x)) = (X->excluding(x))"
proof -
 have A1 : "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> (X->including(x)->excluding(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A1': "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> (X->excluding(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A2 : "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> (X->including(x)->excluding(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A2': "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> (X->excluding(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A3 : "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow> (X->including(x)->excluding(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
 have A3': "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow> (X->excluding(x)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 show ?thesis
 apply(rule ext, rename_tac "\<tau>")
 apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
  apply(case_tac "\<tau> \<Turnstile> (\<delta> X)")
   apply(simp only: OclExcluding_charn2[THEN foundation22[THEN iffD1]])
   apply(simp add: foundation16', elim disjE)
   apply(simp add: A1[OF foundation22[THEN iffD2]] A1'[OF foundation22[THEN iffD2]])
  apply(simp add: A2[OF foundation22[THEN iffD2]] A2'[OF foundation22[THEN iffD2]])
 apply(simp add:foundation18 A3[OF foundation22[THEN iffD2]] A3'[OF foundation22[THEN iffD2]])
 done
qed


text{* One would like a generic theorem of the form:
\begin{isar}[mathescape]
lemma OclExcluding_charn_exec:
       "(X->including(x::('$\mathfrak{A}$,'a::null)val)->excluding(y)) =
        (if \<delta> X then if x \<doteq> y
                     then X->excluding(y)
                     else X->excluding(y)->including(x)
                     endif
                else invalid endif)"
\end{isar}
Unfortunately, this does not hold in general, since referential equality is
an overloaded concept and has to be defined for each type individually.
Consequently, it is only valid for concrete  type instances for Boolean,
Integer, and Sets thereof...
*}


text{* The computational law \emph{OclExcluding-charn-exec} becomes generic since it
uses strict equality which in itself is generic. It is possible to prove
the following generic theorem and instantiate it later (using properties
that link the polymorphic logical strong equality with the concrete instance
of strict quality).*}
lemma OclExcluding_charn_exec:
 assumes strict1: "(x \<doteq> invalid) = invalid"
 and     strict2: "(invalid \<doteq> y) = invalid"
 and     StrictRefEq_valid_args_valid: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                     (\<tau> \<Turnstile> \<delta> (x \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
 and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
 and     StrictRefEq_vs_StrongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                      \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> (x \<triangleq> y)))"
 shows "(X->including(x::('\<AA>,'a::null)val)->excluding(y)) =
        (if \<delta> X then if x \<doteq> y
                     then X->excluding(y)
                     else X->excluding(y)->including(x)
                     endif
                else invalid endif)"
proof -
 (* Lifting theorems, largely analogous OclIncludes_execute_generic,
         with the same problems wrt. strict equality. *)
 have A1: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 have B1: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid  \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 have A2: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> X->including(x)->excluding(y) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 have B2: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> X->including(x)->excluding(y) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)

 note [simp] = cp_StrictRefEq [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]

 have C: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->excluding(y)) \<tau> =
           (if x \<doteq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by(simp add: strict2)

 have D: "\<And>\<tau>. \<tau> \<Turnstile> (y \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->excluding(y)) \<tau> =
           (if x \<doteq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by (simp add: strict1)

 have E: "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
              (if x \<doteq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau> =
              (if x \<triangleq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau>"
           apply(subst cp_OclIf)
           apply(subst StrictRefEq_vs_StrongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_OclIf[symmetric])

 have F: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
           (X->including(x)->excluding(y) \<tau>) = (X->excluding(y) \<tau>)"
           apply(drule StrongEq_L_sym)
           apply(rule foundation22[THEN iffD1])
           apply(erule StrongEq_L_subst2_rev,simp)
           by(simp add: OclExcluding_charn2)

 show ?thesis
    apply(rule ext, rename_tac "\<tau>")
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<delta> X))", simp add:defined_split,elim disjE A1 B1 A2 B2)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> x))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym)
     apply(simp add: foundation22 C)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> y))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym, simp add: foundation22 D, simp)
    apply(subst E,simp_all)
    apply(case_tac "\<tau> \<Turnstile> not (x \<triangleq> y)")
     apply(simp add: OclExcluding_charn1[simplified foundation22]
                     OclExcluding_charn2[simplified foundation22])
    apply(simp add: foundation9 F)
 done
qed


(* Hack to work around OF-Bug *)
schematic_lemma OclExcluding_charn_exec\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[simp,code_unfold]: "?X"
by(rule OclExcluding_charn_exec[OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict1 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2
                                StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid
                             cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_vs_StrongEq], simp_all)

schematic_lemma OclExcluding_charn_exec\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[simp,code_unfold]: "?X"
by(rule OclExcluding_charn_exec[OF StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict1 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict2
                                StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_defined_args_valid
                             cp_StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_vs_StrongEq], simp_all)

schematic_lemma OclExcluding_charn_exec\<^sub>S\<^sub>e\<^sub>t[simp,code_unfold]: "?X"
by(rule OclExcluding_charn_exec[OF StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict1 StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict2
                                StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strictEq_valid_args_valid
                             cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrictRefEq\<^sub>S\<^sub>e\<^sub>t_vs_StrongEq], simp_all)


subsection{* OclIncludes *}


lemma OclIncludes_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> not(Set{}->includes(x))"
using val_x
apply(auto simp: OclValid_def OclIncludes_def OclNot_def false_def true_def)
apply(auto simp: mtSet_def Set_0.Abs_Set_0_inverse)
done


lemma OclIncludes_charn0'[simp,code_unfold]:
"Set{}->includes(x) = (if \<upsilon> x then false else invalid endif)"
proof -
  have A: "\<And> \<tau>. (Set{}->includes(invalid)) \<tau> = (if (\<upsilon> invalid) then false else invalid endif) \<tau>"
          by simp
  have B: "\<And> \<tau> x. \<tau> \<Turnstile> (\<upsilon> x) \<Longrightarrow> (Set{}->includes(x)) \<tau> = (if \<upsilon> x then false else invalid endif) \<tau>"
          apply(frule OclIncludes_charn0, simp add: OclValid_def)
          apply(rule foundation21[THEN fun_cong, simplified StrongEq_def,simplified,
                     THEN iffD1, of _ _ "false"])
          by simp
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
     apply(simp_all add: B foundation18)
    apply(subst cp_OclIncludes, simp add: cp_OclIncludes[symmetric] A)
  done
qed

(*declare [[names_long,show_types,show_sorts]]*)
lemma OclIncludes_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (X->including(x)->includes(x))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 show ?thesis
  apply(subst OclIncludes_def, simp add: foundation10[simplified OclValid_def] OclValid_def
                                 def_X[simplified OclValid_def] val_x[simplified OclValid_def])
  apply(simp add: OclIncluding_def def_X[simplified OclValid_def] val_x[simplified OclValid_def]
                  Abs_Set_0_inverse[OF C] true_def)
 done
qed



lemma OclIncludes_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> (X->including(x)->includes(y)) \<triangleq> (X->includes(y))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(insert def_X val_x, frule Set_inv_lemma, simp add: foundation18 invalid_def)
 show ?thesis
  apply(subst OclIncludes_def,
        simp add: def_X[simplified OclValid_def] val_x[simplified OclValid_def]
                  val_y[simplified OclValid_def] foundation10[simplified OclValid_def]
                  OclValid_def StrongEq_def)
  apply(simp add: OclIncluding_def OclIncludes_def def_X[simplified OclValid_def]
                  val_x[simplified OclValid_def] val_y[simplified OclValid_def]
                  Abs_Set_0_inverse[OF C] true_def)
 by(metis foundation22 foundation6 foundation9 neq)
qed

text{* Here is again a generic theorem similar as above. *}

lemma OclIncludes_execute_generic:
assumes strict1: "(x \<doteq> invalid) = invalid"
and     strict2: "(invalid \<doteq> y) = invalid"
and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
and     StrictRefEq_vs_StrongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                      \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> (x \<triangleq> y)))"
shows
      "(X->including(x::('\<AA>,'a::null)val)->includes(y)) =
       (if \<delta> X then if x \<doteq> y then true else X->includes(y) endif else invalid endif)"
proof -
  have A: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev,simp,simp)
  have B: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid  \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev,simp,simp)

  note [simp] = cp_StrictRefEq [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]

  have C: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->includes(y)) \<tau> =
           (if x \<doteq> y then true else X->includes(y) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by (simp add: strict2)
  have D:"\<And>\<tau>. \<tau> \<Turnstile> (y \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->includes(y)) \<tau> =
           (if x \<doteq> y then true else X->includes(y) endif) \<tau>"
            apply(rule foundation22[THEN iffD1])
            apply(erule StrongEq_L_subst2_rev,simp,simp)
            by (simp add: strict1)
  have E: "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
              (if x \<doteq> y then true else X->includes(y) endif) \<tau> =
              (if x \<triangleq> y then true else X->includes(y) endif) \<tau>"
           apply(subst cp_OclIf)
           apply(subst StrictRefEq_vs_StrongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_OclIf[symmetric])
  have F: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
               (X->including(x)->includes(y)) \<tau> = (X->including(x)->includes(x)) \<tau>"
           apply(rule foundation22[THEN iffD1])
           by(erule StrongEq_L_subst2_rev,simp, simp)
  show ?thesis
    apply(rule ext, rename_tac "\<tau>")
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<delta> X))", simp add:defined_split,elim disjE A B)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> x))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym)
     apply(simp add: foundation22 C)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> y))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym, simp add: foundation22 D, simp)
    apply(subst E,simp_all)
    apply(case_tac "\<tau> \<Turnstile> not(x \<triangleq> y)")
     apply(simp add: OclIncludes_charn2[simplified foundation22])
    apply(simp add: foundation9 F
                    OclIncludes_charn1[THEN foundation13[THEN iffD2],
                                     THEN foundation22[THEN iffD1]])
  done
qed


(* Hack to work around OF-Bug *)
schematic_lemma OclIncludes_execute\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[simp,code_unfold]: "?X"
by(rule OclIncludes_execute_generic[OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict1 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2
                                 cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r
                                    StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_vs_StrongEq], simp_all)


schematic_lemma OclIncludes_execute\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[simp,code_unfold]: "?X"
by(rule OclIncludes_execute_generic[OF StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict1 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict2
                                 cp_StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n
                                    StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_vs_StrongEq], simp_all)


schematic_lemma OclIncludes_execute\<^sub>S\<^sub>e\<^sub>t[simp,code_unfold]: "?X"
by(rule OclIncludes_execute_generic[OF StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict1 StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict2
                                 cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t
                                    StrictRefEq\<^sub>S\<^sub>e\<^sub>t_vs_StrongEq], simp_all)

lemma OclIncludes_including_generic :
 assumes OclIncludes_execute_generic [simp] : "\<And>X x y.
           (X->including(x::('\<AA>,'a::null)val)->includes(y)) =
           (if \<delta> X then if x \<doteq> y then true else X->includes(y) endif else invalid endif)"
     and StrictRefEq_strict'' : "\<And>x y. \<delta> ((x::('\<AA>,'a::null)val) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
     and a_val : "\<tau> \<Turnstile> \<upsilon> a"
     and x_val : "\<tau> \<Turnstile> \<upsilon> x"
     and S_incl : "\<tau> \<Turnstile> (S)->includes((x::('\<AA>,'a::null)val))"
   shows "\<tau> \<Turnstile> S->including((a::('\<AA>,'a::null)val))->includes(x)"
proof -
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False"
 by (metis OCL_core.bot_fun_def foundation1 foundation18' valid3)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False"
 by (metis bot_fun_def discr_eq_bot1_true)
 have discr_neq_invalid_true : "\<And>\<tau>. (invalid \<tau> \<noteq> true \<tau>) = True"
 by (metis discr_eq_bot2_true invalid_def)
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False"
 by (metis bot_option_def invalid_def option.simps(2) true_def)
show ?thesis
  apply(simp)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S")
   prefer 2
   apply(insert S_incl[simplified OclIncludes_def], simp add:  OclValid_def)
   apply(metis discr_eq_bot2_true)
  apply(simp add: cp_OclIf[of "\<delta> S"] OclValid_def OclIf_def x_val[simplified OclValid_def]
                  discr_neq_invalid_true discr_eq_invalid_true)
 by (metis OclValid_def S_incl StrictRefEq_strict'' a_val foundation10 foundation6 x_val)
qed

lemmas OclIncludes_including\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r =
       OclIncludes_including_generic[OF OclIncludes_execute\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict'']

subsection{* OclExcludes *}

(*declare [[names_long,show_types,show_sorts]]*)
lemma OclExcludes_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (X->excluding(x)->excludes(x))"
proof -
 let ?OclSet = "\<lambda>S. \<lfloor>\<lfloor>S\<rfloor>\<rfloor> \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
 have diff_in_Set_0 : "?OclSet (\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>})"
  apply(simp, (rule disjI2)+)
 by (metis (hide_lams, no_types) Diff_iff Set_inv_lemma def_X)

 show ?thesis
  apply(subst OclExcludes_def, simp add: foundation10[simplified OclValid_def] OclValid_def
                                 def_X[simplified OclValid_def] val_x[simplified OclValid_def])
  apply(subst OclIncludes_def, simp add: OclNot_def)
  apply(simp add: OclExcluding_def def_X[simplified OclValid_def] val_x[simplified OclValid_def]
                  Abs_Set_0_inverse[OF diff_in_Set_0] true_def)
 by(simp add: OclAnd_def def_X[simplified OclValid_def] val_x[simplified OclValid_def] true_def)
qed

subsection{* OclSize *}

lemma [simp,code_unfold]: "Set{} ->size() = \<zero>"
 apply(rule ext)
 apply(simp add: defined_def mtSet_def OclSize_def
                 bot_Set_0_def bot_fun_def
                 null_Set_0_def null_fun_def)
 apply(subst Abs_Set_0_inject, simp_all add: bot_option_def null_option_def) +
by(simp add: Abs_Set_0_inverse bot_option_def null_option_def OclInt0_def)

lemma OclSize_including_exec[simp,code_unfold]:
 "((X ->including(x)) ->size()) = (if \<delta> X and \<upsilon> x then
                                     X ->size() +\<^sub>i\<^sub>n\<^sub>t if X ->includes(x) then \<zero> else \<one> endif
                                   else
                                     invalid
                                   endif)"
proof -

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  proof -
  fix \<tau>
  have includes_notin: "\<not> \<tau> \<Turnstile> X->includes(x) \<Longrightarrow> (\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                        x \<tau> \<notin> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  by(simp add: OclIncludes_def OclValid_def true_def)

  have includes_def: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
  by (metis OCL_core.bot_fun_def OclIncludes_def OclValid_def defined3 foundation16)

  have includes_val: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
  by (metis (hide_lams, no_types) foundation6
        OclIncludes_valid_args_valid' OclIncluding_valid_args_valid OclIncluding_valid_args_valid'')

  have ins_in_Set_0: "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
    \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"
   apply(simp add: bot_option_def null_option_def)
  by (metis (hide_lams, no_types) Set_inv_lemma foundation18' foundation5)

  have m : "\<And>\<tau>. (\<lambda>_. \<bottom>) = (\<lambda>_. invalid \<tau>)" by(rule ext, simp add:invalid_def)
  
  show "X->including(x)->size() \<tau> = (if \<delta> X and \<upsilon> x
                                     then X->size() +\<^sub>i\<^sub>n\<^sub>t if X->includes(x) then \<zero> else \<one> endif
                                     else invalid endif) \<tau>"
   apply(case_tac "\<tau> \<Turnstile> \<delta> X and \<upsilon> x", simp)
    apply(subst OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0)
    apply(case_tac "\<tau> \<Turnstile> X->includes(x)", simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0[symmetric])
     apply(case_tac "\<tau> \<Turnstile> ((\<upsilon> (X->size())) and not (\<delta> (X->size())))", simp)
      apply(drule foundation5[where P = "\<upsilon> X->size()"], erule conjE)
      apply(drule OclSize_infinite)
      apply(frule includes_def, drule includes_val, simp)
      apply(subst OclSize_def, subst OclIncluding_finite_rep_set, assumption+)
     apply (metis (hide_lams, no_types) invalid_def)

     apply(subst OclIf_false',
           metis (hide_lams, no_types) defined5 defined6 defined_and_I defined_not_I
                                       foundation1 foundation9)
    apply(subst cp_OclSize, simp add: OclIncluding_includes0 cp_OclSize[symmetric])
    (* *)
    apply(subst OclIf_false', subst foundation9,
          metis (hide_lams, no_types) OclIncludes_valid_args_valid', simp, simp add: OclSize_def)
    apply(drule foundation5)
    apply(subst (1 2) OclIncluding_finite_rep_set, fast+)
    apply(subst (1 2) cp_OclAnd, subst (1 2) OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp)
    apply(rule conjI)
     apply(simp add: OclIncluding_def)
     apply(subst Abs_Set_0_inverse[OF ins_in_Set_0], fast+)
     apply(subst (asm) (2 3) OclValid_def, simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclInt1_def)
     apply(rule impI)
     apply(drule Finite_Set.card.insert[where x = "x \<tau>"])
     apply(rule includes_notin, simp, simp)
     apply (metis Suc_eq_plus1 int_1 of_nat_add)

    apply(subst (1 2) m[of \<tau>], simp only:   OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0[symmetric],simp, simp add:invalid_def)
    apply(subst OclIncluding_finite_rep_set, fast+, simp add: OclValid_def)
   (* *)
   apply(subst OclIf_false', metis (hide_lams, no_types) defined6 foundation1 foundation9
                                                         OclExcluding_valid_args_valid'')
  by (metis cp_OclSize foundation18' OclIncluding_valid_args_valid'' invalid_def OclSize_invalid)
 qed
qed

subsection{* OclIsEmpty *}

lemma [simp,code_unfold]: "Set{}->isEmpty() = true"
by(simp add: OclIsEmpty_def)

lemma OclIsEmpty_including [simp]:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and X_finite: "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
shows "X->including(a)->isEmpty() \<tau> = false \<tau>"
proof -
 have A1 : "\<And>\<tau> X. X \<tau> = true \<tau> \<or> X \<tau> = false \<tau> \<Longrightarrow> (X and not X) \<tau> = false \<tau>"
 by (metis (no_types) OclAnd_false1 OclAnd_idem OclImplies_def OclNot3 OclNot_not OclOr_false1
                      cp_OclAnd cp_OclNot deMorgan1 deMorgan2)

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have B : "\<And>X \<tau>. \<tau> \<Turnstile> \<upsilon> X \<Longrightarrow> X \<tau> \<noteq> \<zero> \<tau> \<Longrightarrow> (X \<doteq> \<zero>) \<tau> = false \<tau>"
 by (metis OclAnd_true2 OclValid_def foundation16 foundation22 valid4
           StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict''
           bool_split invalid_def null_fun_def null_non_OclInt0)

 show ?thesis
  apply(simp add: OclIsEmpty_def del: OclSize_including_exec)
  apply(subst cp_OclOr, subst A1)
   apply(metis (hide_lams, no_types) defined_inject_true OclExcluding_valid_args_valid')
  apply(simp add: cp_OclOr[symmetric] del: OclSize_including_exec)
  apply(rule B,
        rule foundation20,
        metis (hide_lams, no_types) OclIncluding_defined_args_valid OclIncluding_finite_rep_set
                                    X_def X_finite a_val size_defined')
  apply(simp add: OclSize_def OclIncluding_finite_rep_set[OF X_def a_val] X_finite OclInt0_def)
 by (metis OclValid_def X_def a_val foundation10 foundation6
           OclIncluding_notempty_rep_set[OF X_def a_val])
qed

subsection{* OclNotEmpty *}

lemma [simp,code_unfold]: "Set{}->notEmpty() = false"
by(simp add: OclNotEmpty_def)

lemma OclNotEmpty_including [simp,code_unfold]:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and X_finite: "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
shows "X->including(a)->notEmpty() \<tau> = true \<tau>"
 apply(simp add: OclNotEmpty_def)
 apply(subst cp_OclNot, subst OclIsEmpty_including, simp_all add: assms)
by (metis OclNot4 cp_OclNot)

subsection{* OclANY *}

lemma [simp,code_unfold]: "Set{}->any() = null"
by(rule ext, simp add: OclANY_def, simp add: false_def true_def)

lemma OclANY_singleton_exec[simp,code_unfold]:
      "(Set{}->including(a))->any() = a"
 apply(rule ext, rename_tac \<tau>, simp add: mtSet_def OclANY_def)
 apply(case_tac "\<tau> \<Turnstile> \<upsilon> a")
  apply(simp add: OclValid_def mtSet_defined[simplified mtSet_def]
                  mtSet_valid[simplified mtSet_def] mtSet_rep_set[simplified mtSet_def])
  apply(subst (1 2) cp_OclAnd,
        subst (1 2) OclNotEmpty_including[where X = "Set{}", simplified mtSet_def])
     apply(simp add: mtSet_defined[simplified mtSet_def])
    apply(metis (hide_lams, no_types) finite.emptyI mtSet_def mtSet_rep_set)
   apply(simp add: OclValid_def)
  apply(simp add: OclIncluding_def)
  apply(rule conjI)
   apply(subst (1 2) Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
    apply(simp, metis OclValid_def foundation18')
   apply(simp)
 apply(simp add: mtSet_defined[simplified mtSet_def])
 (* *)
 apply(subgoal_tac "a \<tau> = \<bottom>")
  prefer 2
  apply(simp add: OclValid_def valid_def bot_fun_def split: split_if_asm)
 apply(simp)
 apply(subst (1 2 3 4) cp_OclAnd,
       simp add: mtSet_defined[simplified mtSet_def] valid_def bot_fun_def)
by(simp add: cp_OclAnd[symmetric], rule impI, simp add: false_def true_def)

subsection{* OclForall *}

lemma OclForall_mtSet_exec[simp,code_unfold] :"((Set{})->forAll(z| P(z))) = true"
apply(simp add: OclForall_def)
apply(subst mtSet_def)+
apply(subst Abs_Set_0_inverse, simp_all add: true_def)+
done


text{* The following rule is a main theorem of our approach: From a denotational definition
that assures consistency, but may be --- as in the case of the @{term "X->forAll(x | P x)"} ---
dauntingly complex, we derive operational rules that can serve as a gold-standard for operational
execution, since they may be evaluated in whatever situation and according to whatever strategy.
In the case of @{term "X->forAll(x | P x)"}, the operational rule gives immediately a way to
evaluation in any finite (in terms of conventional OCL: denotable) set, although the rule also
holds for the infinite case:

@{term "Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l ->forAll(x | (Integer\<^sub>n\<^sub>u\<^sub>l\<^sub>l ->forAll(y | x +\<^sub>i\<^sub>n\<^sub>t y \<triangleq> y +\<^sub>i\<^sub>n\<^sub>t x)))"}

or even:

@{term "Integer ->forAll(x | (Integer ->forAll(y | x +\<^sub>i\<^sub>n\<^sub>t y \<doteq> y +\<^sub>i\<^sub>n\<^sub>t x)))"}

are valid OCL statements in any context $\tau$.
*}

theorem OclForall_including_exec[simp,code_unfold] :
        assumes cp0 : "cp P"
        shows         "((S->including(x))->forAll(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                                then P x and (S->forAll(z | P(z)))
                                                                else invalid
                                                                endif)"
proof -
   have cp: "\<And>\<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" by(insert cp0, auto simp: cp_def)

   have cp_eq : "\<And>\<tau> v. (P x \<tau> = v) = (P (\<lambda>_. x \<tau>) \<tau> = v)" by(subst cp, simp)

   have cp_OclNot_eq : "\<And>\<tau> v. (P x \<tau> \<noteq> v) = (P (\<lambda>_. x \<tau>) \<tau> \<noteq> v)" by(subst cp, simp)

   have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
                               \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in>
                                 {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
           by(frule Set_inv_lemma, simp add: foundation18 invalid_def)

   have forall_including_invert : "\<And>\<tau> f. (f x \<tau> = f (\<lambda> _. x \<tau>) \<tau>) \<Longrightarrow>
                                          \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                                          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>) =
                                            (f x \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>))"
           apply(drule foundation5, simp add: OclIncluding_def)
           apply(subst Abs_Set_0_inverse)
           apply(rule insert_in_Set_0, fast+)
           by(simp add: OclValid_def)

   have exists_including_invert : "\<And>\<tau> f. (f x \<tau> = f (\<lambda> _. x \<tau>) \<tau>) \<Longrightarrow>
                                          \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                                          (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>) =
                                            (f x \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>))"
           apply(subst arg_cong[where f = "\<lambda>x. \<not>x",
                                OF forall_including_invert[where f = "\<lambda>x \<tau>. \<not> (f x \<tau>)"],
                                simplified])
           by simp_all

   have contradict_Rep_Set_0: "\<And>\<tau> S f. \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. f (\<lambda>_. x) \<tau> \<Longrightarrow>
                                       (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>)) = False"
           by(case_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>)) = True", simp_all)

   have bot_invalid : "\<bottom> = invalid"  by(rule ext, simp add: invalid_def bot_fun_def)

   have bot_invalid2 : "\<And>\<tau>. \<bottom> = invalid \<tau>"  by(simp add: invalid_def)

   have C1 : "\<And>\<tau>. P x \<tau> = false \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau>) \<Longrightarrow>
                  \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                  false \<tau> = (P x and OclForall S P) \<tau>"
           apply(simp add: cp_OclAnd[of "P x"])
           apply(elim disjE, simp)
            apply(simp only: cp_OclAnd[symmetric], simp)
           apply(subgoal_tac "OclForall S P \<tau> = false \<tau>")
            apply(simp only: cp_OclAnd[symmetric], simp)
           apply(simp add: OclForall_def)
           apply(fold OclValid_def, simp add:  OCL_core.foundation27)
           done

   have C2 : "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                  P x \<tau> = null \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau>) \<Longrightarrow>
                  P x \<tau> = invalid \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = invalid \<tau>) \<Longrightarrow>
                  \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau> \<Longrightarrow>
                  invalid \<tau> = (P x and OclForall S P) \<tau>"
           apply(subgoal_tac "(\<delta> S)\<tau> = true \<tau>")
            prefer 2 apply(simp add: OCL_core.foundation27, simp add: OclValid_def)
           apply(drule forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> false \<tau>", OF cp_OclNot_eq, THEN iffD1])
            apply(assumption)
           apply(simp add: cp_OclAnd[of "P x"],elim disjE, simp_all)
              apply(simp add: invalid_def null_fun_def null_option_def bot_fun_def bot_option_def)
             apply(subgoal_tac "OclForall S P \<tau> = invalid \<tau>")
              apply(simp only:cp_OclAnd[symmetric],simp,simp add:invalid_def bot_fun_def)
             apply(unfold OclForall_def, simp add: invalid_def false_def bot_fun_def,simp)
            apply(simp add:cp_OclAnd[symmetric],simp)
           apply(erule conjE)
           apply(subgoal_tac "(P x \<tau> = invalid \<tau>) \<or> (P x \<tau> = null \<tau>) \<or> (P x \<tau> = true \<tau>) \<or> (P x \<tau> = false \<tau>)")
            prefer 2 apply(rule OCL_core.bool_split_0)
           apply(elim disjE, simp_all)
            apply(simp only:cp_OclAnd[symmetric],simp)+
           done

   have A : "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                 OclForall (S->including(x)) P \<tau> = (P x and OclForall S P) \<tau>"
         proof - fix \<tau>
                 assume 0 : "\<tau> \<Turnstile> (\<delta> S and \<upsilon> x)"
                 let ?S = "\<lambda>ocl. P x \<tau> \<noteq> ocl \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> ocl \<tau>)"
                 let ?S' = "\<lambda>ocl. \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> ocl \<tau>"
                 let ?assms_1 = "?S' null"
                 let ?assms_2 = "?S' invalid"
                 let ?assms_3 = "?S' false"
                 have 4 : "?assms_3 \<Longrightarrow> ?S false"
                     apply(subst  forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> false \<tau>",symmetric])
                     by(simp_all add: cp_OclNot_eq 0)
                 have 5 : "?assms_2 \<Longrightarrow> ?S invalid"
                     apply(subst  forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> invalid \<tau>",symmetric])
                     by(simp_all add: cp_OclNot_eq 0)
                 have 6 : "?assms_1 \<Longrightarrow> ?S null"
                     apply(subst forall_including_invert[of "\<lambda> x \<tau>. P x \<tau> \<noteq> null \<tau>",symmetric])
                     by(simp_all add: cp_OclNot_eq 0)
                 have 7 : "(\<delta> S) \<tau> = true \<tau>"
                     by(insert 0, simp add: OCL_core.foundation27, simp add: OclValid_def)
         show "?thesis \<tau>"
           apply(subst OclForall_def)
           apply(simp add: cp_OclAnd[THEN sym] OclValid_def contradict_Rep_Set_0)
           apply(intro conjI impI,fold OclValid_def)
           apply(simp_all add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = null \<tau>", OF cp_eq])
           apply(simp_all add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = invalid \<tau>", OF cp_eq])
           apply(simp_all add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = false \<tau>", OF cp_eq])
           proof -
              assume 1 : "P x \<tau> = null \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau>)"
              and    2 : ?assms_2
              and    3 : ?assms_3
              show   "null \<tau> = (P x and OclForall S P) \<tau>"
              proof -
                 note 4 = 4[OF 3]
                 note 5 = 5[OF 2]
                 have 6 : "P x \<tau> = null \<tau> \<or> P x \<tau> = true \<tau>"
                     by(metis 4 5 OCL_core.bool_split_0)
                 show ?thesis
                 apply(insert 6, elim disjE)
                  apply(subst cp_OclAnd)
                  apply(simp add: OclForall_def 7 4[THEN conjunct2] 5[THEN conjunct2])
                  apply(simp_all add:cp_OclAnd[symmetric])
                 apply(subst cp_OclAnd, simp_all add:cp_OclAnd[symmetric] OclForall_def)
                 apply(simp add:4[THEN conjunct2] 5[THEN conjunct2] 0[simplified OclValid_def] 7)
                 apply(insert 1, elim disjE, auto)
                 done
              qed
           next
              assume 1 : ?assms_1
              and    2 : "P x \<tau> = invalid \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = invalid \<tau>)"
              and    3 : ?assms_3
              show   "invalid \<tau> = (P x and OclForall S P) \<tau>"
              proof -
                 note 4 = 4[OF 3]
                 note 6 = 6[OF 1]
                 have 5 : "P x \<tau> = invalid \<tau> \<or> P x \<tau> = true \<tau>"
                     by(metis 4 6 OCL_core.bool_split_0)
                 show ?thesis
                 apply(insert 5, elim disjE)
                  apply(subst cp_OclAnd)
                  apply(simp add: OclForall_def 4[THEN conjunct2] 6[THEN conjunct2] 7)
                  apply(simp_all add:cp_OclAnd[symmetric])
                 apply(subst cp_OclAnd, simp_all add:cp_OclAnd[symmetric] OclForall_def)
                 apply(insert 2, elim disjE, simp add: invalid_def true_def bot_option_def)
                 apply(simp add: 0[simplified OclValid_def] 4[THEN conjunct2] 6[THEN conjunct2] 7)
                 by(auto)
               qed
           next
              assume 1 : ?assms_1
              and    2 : ?assms_2
              and    3 : ?assms_3
              show   "true \<tau> = (P x and OclForall S P) \<tau>"
              proof -
                 note 4 = 4[OF 3]
                 note 5 = 5[OF 2]
                 note 6 = 6[OF 1]
                 have 8 : "P x \<tau> = true \<tau>"
                     by(metis 4 5 6 OCL_core.bool_split_0)
                 show ?thesis
                 apply(subst cp_OclAnd, simp add: 8 cp_OclAnd[symmetric])
                 by(simp add: OclForall_def 4 5 6 7)
              qed
           apply_end( simp add: 0
                    | rule C1, simp+
                    | rule C2, simp add: 0 )+
           qed
        qed

   have B : "\<And>\<tau>. \<not> (\<tau> \<Turnstile> (\<delta> S and \<upsilon> x)) \<Longrightarrow>
                 OclForall (S->including(x)) P \<tau> = invalid \<tau>"
           apply(rule foundation22[THEN iffD1])
           apply(simp only: foundation10' de_Morgan_conj foundation18'', elim disjE)
            apply(simp add:  OCL_core.defined_split, elim disjE)
             apply(erule StrongEq_L_subst2_rev, simp+)+
           done

   show ?thesis
           apply(rule ext, rename_tac \<tau>)
           apply(simp add: OclIf_def)
           apply(simp add: cp_defined[of "\<delta> S and \<upsilon> x"] cp_defined[THEN sym])
           apply(intro conjI impI)
           by(auto intro!: A B simp: OclValid_def)
qed




subsection{* OclExists *}

lemma OclExists_mtSet_exec[simp,code_unfold] :
"((Set{})->exists(z | P(z))) = false"
by(simp add: OclExists_def)

lemma OclExists_including_exec[simp,code_unfold] :
 assumes cp: "cp P"
 shows "((S->including(x))->exists(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                 then P x or (S->exists(z | P(z)))
                                                 else invalid
                                                 endif)"
 by(simp add: OclExists_def OclOr_def  cp OclNot_inject)


subsection{* OclIterate *}

lemma OclIterate_empty[simp,code_unfold]: "((Set{})->iterate(a; x = A | P a x)) = A"
proof -
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
 by (metis (no_types) defined_def mtSet_def mtSet_defined null_fun_def)
 show ?thesis
      apply(simp add: OclIterate_def mtSet_def Abs_Set_0_inverse valid_def C)
      apply(rule ext, rename_tac \<tau>)
      apply(case_tac "A \<tau> = \<bottom> \<tau>", simp_all, simp add:true_def false_def bot_fun_def)
      apply(simp add: Abs_Set_0_inverse)
 done
qed

text{* In particular, this does hold for A = null. *}

lemma OclIterate_including:
assumes S_finite:    "\<tau> \<Turnstile> \<delta>(S->size())"
and     F_valid_arg: "(\<upsilon> A) \<tau> = (\<upsilon> (F a A)) \<tau>"
and     F_commute:   "comp_fun_commute F"
and     F_cp:        "\<And> x y \<tau>. F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
shows   "((S->including(a))->iterate(a; x =     A | F a x)) \<tau> =
         ((S->excluding(a))->iterate(a; x = F a A | F a x)) \<tau>"
proof -
 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
    \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  by(frule Set_inv_lemma, simp add: foundation18 invalid_def)

 have insert_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_Set_0_def bot_fun_def null_Set_0_def null_fun_def)
  by(subst Abs_Set_0_inject,
     rule insert_in_Set_0, simp_all add: null_option_def bot_option_def)+

 have remove_finite : "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       finite ((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
   \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(frule Set_inv_lemma, simp add: foundation18 invalid_def)

 have remove_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_Set_0_def bot_fun_def null_Set_0_def null_fun_def)
  by(subst Abs_Set_0_inject,
     rule remove_in_Set_0, simp_all add: null_option_def bot_option_def)+

 have abs_rep: "\<And>x. \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow>
                    \<lceil>\<lceil>Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)\<rceil>\<rceil> = x"
 by(subst Abs_Set_0_inverse, simp_all)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 show ?thesis
  apply(subst (1 2) cp_OclIterate, subst OclIncluding_def, subst OclExcluding_def)
  apply(case_tac "\<not> ((\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> a) \<tau> = true \<tau>)", simp)

   apply(subgoal_tac "OclIterate (\<lambda>_. \<bottom>) A F \<tau> = OclIterate (\<lambda>_. \<bottom>) (F a A) F \<tau>", simp)
    apply(rule conjI, blast+)
  apply(simp add: OclIterate_def defined_def bot_option_def bot_fun_def false_def true_def)

  apply(simp add: OclIterate_def)
  apply((subst abs_rep[OF insert_in_Set_0[simplified OclValid_def], of \<tau>], simp_all)+,
        (subst abs_rep[OF remove_in_Set_0[simplified OclValid_def], of \<tau>], simp_all)+,
        (subst insert_defined, simp_all add: OclValid_def)+,
        (subst remove_defined, simp_all add: OclValid_def)+)

  apply(case_tac "\<not> ((\<upsilon> A) \<tau> = true \<tau>)", (simp add: F_valid_arg)+)
  apply(rule impI,
        subst Finite_Set.comp_fun_commute.fold_fun_left_comm[symmetric, OF F_commute],
        rule remove_finite, simp)

  apply(subst image_set_diff[OF inject], simp)
  apply(subgoal_tac "Finite_Set.fold F A (insert (\<lambda>\<tau>'. a \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)) \<tau> =
      F (\<lambda>\<tau>'. a \<tau>) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {\<lambda>\<tau>'. a \<tau>})) \<tau>")
   apply(subst F_cp, simp)

 by(subst Finite_Set.comp_fun_commute.fold_insert_remove[OF F_commute], simp+)
qed

subsection{* OclSelect *}

lemma OclSelect_mtSet_exec[simp,code_unfold]: "OclSelect mtSet P = mtSet"
 apply(rule ext, rename_tac \<tau>)
 apply(simp add: OclSelect_def mtSet_def defined_def false_def true_def
                 bot_Set_0_def bot_fun_def null_Set_0_def null_fun_def)
by(( subst (1 2 3 4 5) Abs_Set_0_inverse
   | subst Abs_Set_0_inject), (simp add: null_option_def bot_option_def)+)+

definition "OclSelect_body :: _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('\<AA>, 'a option option) Set
           \<equiv> (\<lambda>P x acc. if P x \<doteq> false then acc else acc->including(x) endif)"

theorem OclSelect_including_exec[simp,code_unfold]:
 assumes P_cp : "cp P"
 shows "OclSelect (X->including(y)) P = OclSelect_body P y (OclSelect (X->excluding(y)) P)"
 (is "_ = ?select")
proof -
 have P_cp: "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>" by(insert P_cp, auto simp: cp_def)

 have ex_including : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                                   (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X->including(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (f (P (\<lambda>_. y \<tau>)) \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>))"
      apply(simp add: OclIncluding_def OclValid_def)
       apply(subst Abs_Set_0_inverse, simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18',simp)

 have al_including : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                                   (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X->including(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (f (P (\<lambda>_. y \<tau>)) \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>))"
      apply(simp add: OclIncluding_def OclValid_def)
       apply(subst Abs_Set_0_inverse, simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18', simp)

 have ex_excluding1 : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<not> (f (P (\<lambda>_. y \<tau>)) \<tau>) \<Longrightarrow>
                                   (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X->excluding(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>)"
      apply(simp add: OclExcluding_def OclValid_def)
       apply(subst Abs_Set_0_inverse, simp, (rule disjI2)+)
      by (metis (no_types) Diff_iff OclValid_def Set_inv_lemma) auto

 have al_excluding1 : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> f (P (\<lambda>_. y \<tau>)) \<tau> \<Longrightarrow>
                                   (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>) =
                                   (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X->excluding(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x)) \<tau>)"
      apply(simp add: OclExcluding_def OclValid_def)
      apply(subst Abs_Set_0_inverse, simp, (rule disjI2)+)
      by (metis (no_types) Diff_iff OclValid_def Set_inv_lemma) auto

 have in_including : "\<And>f X y \<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                                  {x \<in> \<lceil>\<lceil>Rep_Set_0 (X->including(y) \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x) \<tau>)} =
                                   (let s = {x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. f (P (\<lambda>_. x) \<tau>)} in
                                    if f (P (\<lambda>_. y \<tau>) \<tau>) then insert (y \<tau>) s else s)"
      apply(simp add: OclIncluding_def OclValid_def)
      apply(subst Abs_Set_0_inverse, simp, (rule disjI2)+)
       apply (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18')
      by(simp add: Let_def, auto)

 let ?OclSet = "\<lambda>S. \<lfloor>\<lfloor>S\<rfloor>\<rfloor> \<in> {X. X = \<bottom> \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> \<bottom>)}"

 have diff_in_Set_0 : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow> ?OclSet (\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>})"
      apply(simp, (rule disjI2)+)
      by (metis (mono_tags) Diff_iff OclValid_def Set_inv_lemma)

 have ins_in_Set_0 : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow> (\<upsilon> y) \<tau> = true \<tau> \<Longrightarrow>
                           ?OclSet (insert (y \<tau>) {x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>})"
      apply(simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18')

 have ins_in_Set_0' : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow> (\<upsilon> y) \<tau> = true \<tau> \<Longrightarrow>
        ?OclSet (insert (y \<tau>) {x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> y \<tau> \<and> P (\<lambda>_. x) \<tau> \<noteq> false \<tau>})"
      apply(simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma foundation18')

 have ins_in_Set_0'' : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow>
        ?OclSet {x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}"
      apply(simp, (rule disjI2)+)
      by (metis (hide_lams, no_types) OclValid_def Set_inv_lemma)

 have ins_in_Set_0''' : "\<And>\<tau>. (\<delta> X) \<tau> = true \<tau> \<Longrightarrow>
        ?OclSet {x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> y \<tau> \<and> P (\<lambda>_. x) \<tau> \<noteq> false \<tau>}"
      apply(simp, (rule disjI2)+)
      by(metis (hide_lams, no_types) OclValid_def Set_inv_lemma)

 have if_same : "\<And>a b c d \<tau>. \<tau> \<Turnstile> \<delta> a \<Longrightarrow> b \<tau> = d \<tau> \<Longrightarrow> c \<tau> = d \<tau> \<Longrightarrow>
                             (if a then b else c endif) \<tau> = d \<tau>"
      by(simp add: OclIf_def OclValid_def)

 have invert_including : "\<And>P y \<tau>. P \<tau> = \<bottom> \<Longrightarrow> P->including(y) \<tau> = \<bottom>"
      by (metis (hide_lams, no_types) foundation16[THEN iffD1,standard]
                foundation18' OclIncluding_valid_args_valid)

 have exclude_defined : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow>
           (\<delta>(\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>{x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> y \<tau> \<and> P (\<lambda>_. x) \<tau>\<noteq>false \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
      apply(subst defined_def,
            simp add: false_def true_def bot_Set_0_def bot_fun_def null_Set_0_def null_fun_def)
      by(subst Abs_Set_0_inject[OF ins_in_Set_0'''[simplified false_def]],
         (simp add: OclValid_def bot_option_def null_option_def)+)+

 have if_eq : "\<And>x A B \<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((if x \<doteq> false then A else B endif) \<triangleq>
                                          (if x \<triangleq> false then A else B endif))"
      apply(simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def)
      apply(subst (2) StrongEq_def)
      by(subst cp_OclIf, simp add: cp_OclIf[symmetric] true_def)

 have OclSelect_body_bot: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> P y \<tau> \<noteq> \<bottom> \<Longrightarrow>
                               (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = \<bottom>) \<Longrightarrow> \<bottom> = ?select \<tau>"
      apply(drule ex_excluding1[where X = X and y = y and f = "\<lambda>x \<tau>. x \<tau> = \<bottom>"],
            (simp add: P_cp[symmetric])+)
      apply(subgoal_tac "\<tau> \<Turnstile> (\<bottom> \<triangleq> ?select)", simp add: OclValid_def StrongEq_def true_def bot_fun_def)
      apply(simp add: OclSelect_body_def)
      apply(subst StrongEq_L_subst3[OF _ if_eq], simp, metis foundation18')
      apply(simp add: OclValid_def, subst StrongEq_def, subst true_def, simp)
      apply(subgoal_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X->excluding(y) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = \<bottom> \<tau>")
       prefer 2 apply (metis OCL_core.bot_fun_def )
       apply(subst if_same[where d = "\<bottom>"])
        apply (metis defined7 transform1)
       apply(simp add: OclSelect_def bot_option_def bot_fun_def invalid_def)
      apply(subst invert_including)
      by(simp add: OclSelect_def bot_option_def bot_fun_def invalid_def)+


 have d_and_v_inject : "\<And>\<tau> X y. (\<delta> X and \<upsilon> y) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> X and \<upsilon> y) \<tau> = false \<tau>"
      apply(fold OclValid_def, subst OCL_core.foundation22[symmetric])
      apply(auto simp:foundation27  OCL_core.defined_split)
        apply(erule OCL_core.StrongEq_L_subst2_rev,simp,simp)
       apply(erule OCL_core.StrongEq_L_subst2_rev,simp,simp)
      by(erule OCL_core.foundation7'[THEN iffD2, THEN OCL_core.foundation15[THEN iffD2,
                                       THEN OCL_core.StrongEq_L_subst2_rev]],simp,simp)




 have OclSelect_body_bot': "\<And>\<tau>. (\<delta> X and \<upsilon> y) \<tau> \<noteq> true \<tau> \<Longrightarrow> \<bottom> = ?select \<tau>"
      apply(drule d_and_v_inject)
      apply(simp add: OclSelect_def OclSelect_body_def)
      apply(subst cp_OclIf, subst cp_OclIncluding, simp add: false_def true_def)
      apply(subst cp_OclIf[symmetric], subst cp_OclIncluding[symmetric])
      by (metis (lifting, no_types) OclIf_def foundation18 foundation18' invert_including)

 have conj_split2 : "\<And>a b c \<tau>. ((a \<triangleq> false) \<tau> = false \<tau> \<longrightarrow> b) \<and> ((a \<triangleq> false) \<tau> = true \<tau> \<longrightarrow> c) \<Longrightarrow>
                               (a \<tau> \<noteq> false \<tau> \<longrightarrow> b) \<and> (a \<tau> = false \<tau> \<longrightarrow> c)"
      by (metis OclValid_def defined7 foundation14 foundation22 foundation9)

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have cp_OclSelect_body : "\<And>\<tau>. ?select \<tau> = OclSelect_body P y (\<lambda>_.(OclSelect (X->excluding(y))P)\<tau>)\<tau>"
      apply(simp add: OclSelect_body_def)
      by(subst (1 2) cp_OclIf, subst (1 2) cp_OclIncluding, blast)

 have OclSelect_body_strict1 : "OclSelect_body P y invalid = invalid"
      by(rule ext, simp add: OclSelect_body_def OclIf_def)

 have bool_invalid: "\<And>(x::('\<AA>)Boolean) y \<tau>. \<not> (\<tau> \<Turnstile> \<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> invalid)"
      by(simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def StrongEq_def true_def)

 have conj_comm : "\<And>p q r. (p \<and> q \<and> r) = ((p \<and> q) \<and> r)" by blast

 have inv_bot : "\<And>\<tau>. invalid \<tau> = \<bottom> \<tau>" by (metis OCL_core.bot_fun_def invalid_def)
 have inv_bot' : "\<And>\<tau>. invalid \<tau> = \<bottom>" by (simp add: invalid_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(subst OclSelect_def)
  apply(case_tac "(\<delta> (X->including(y))) \<tau> = true \<tau>", simp)
   apply(( subst ex_including | subst in_including),
         metis OclValid_def foundation5,
         metis OclValid_def foundation5)+
   apply(simp add: Let_def inv_bot)
   apply(subst (2 4 7 9) bot_fun_def)

   apply(subst (4) false_def, subst (4) bot_fun_def, simp add: bot_option_def P_cp[symmetric])
   (* *)
   apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> P y))")
    apply(subgoal_tac "P y \<tau> \<noteq> false \<tau>")
     prefer 2
     apply (metis (hide_lams, no_types) foundation1 foundation18' valid4)
    apply(simp)
    (* *)
    apply(subst conj_comm, rule conjI)
     apply(drule_tac y = false in bool_invalid)
     apply(simp only: OclSelect_body_def,
           metis OclIf_def OclValid_def defined_def foundation2 foundation22
                 bot_fun_def invalid_def)
    (* *)
    apply(drule foundation5[simplified OclValid_def],
          subst al_including[simplified OclValid_def],
          simp,
          simp)
    apply(simp add: P_cp[symmetric])
    apply (metis OCL_core.bot_fun_def foundation18')

   apply(simp add: foundation18' bot_fun_def OclSelect_body_bot OclSelect_body_bot')
   (* *)
   apply(subst (1 2) al_including, metis OclValid_def foundation5, metis OclValid_def foundation5)
   apply(simp add: P_cp[symmetric], subst (4) false_def, subst (4) bot_option_def, simp)

   apply(simp add: OclSelect_def[simplified inv_bot'] OclSelect_body_def StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)
   apply(subst (1 2 3 4) cp_OclIf,
         subst (1 2 3 4) foundation18'[THEN iffD2, simplified OclValid_def],
         simp,
         simp only: cp_OclIf[symmetric] refl if_True)
   apply(subst (1 2) cp_OclIncluding, rule conj_split2, simp add: cp_OclIf[symmetric])
   apply(subst (1 2 3 4 5 6 7 8) cp_OclIf[symmetric], simp)
   apply(( subst ex_excluding1[symmetric]
         | subst al_excluding1[symmetric] ),
         metis OclValid_def foundation5,
         metis OclValid_def foundation5,
         simp add: P_cp[symmetric] bot_fun_def)+
   apply(simp add: bot_fun_def)
   apply(subst (1 2) invert_including, simp+)
   (* *)
   apply(rule conjI, blast)
   apply(intro impI conjI)
    apply(subst OclExcluding_def)
    apply(drule foundation5[simplified OclValid_def], simp)
    apply(subst Abs_Set_0_inverse[OF diff_in_Set_0], fast)
    apply(simp add: OclIncluding_def cp_valid[symmetric])
    apply((erule conjE)+, frule exclude_defined[simplified OclValid_def], simp)
    apply(subst Abs_Set_0_inverse[OF ins_in_Set_0'''], simp+)
    apply(subst Abs_Set_0_inject[OF ins_in_Set_0 ins_in_Set_0'], fast+)
   (* *)
   apply(simp add: OclExcluding_def)
   apply(simp add: foundation10[simplified OclValid_def])
   apply(subst Abs_Set_0_inverse[OF diff_in_Set_0], simp+)
   apply(subst Abs_Set_0_inject[OF ins_in_Set_0'' ins_in_Set_0'''], simp+)
   apply(subgoal_tac "P (\<lambda>_. y \<tau>) \<tau> = false \<tau>")
    prefer 2
    apply(subst P_cp[symmetric], metis OclValid_def foundation22)
   apply(rule equalityI)
    apply(rule subsetI, simp, metis)
   apply(rule subsetI, simp)
  (* *)
  apply(drule defined_inject_true)
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<delta> X) \<or> \<not> (\<tau> \<Turnstile> \<upsilon> y)")
   prefer 2
   apply (metis bot_fun_def OclValid_def foundation18' OclIncluding_defined_args_valid valid_def)
  apply(subst cp_OclSelect_body, subst cp_OclSelect, subst OclExcluding_def)
  apply(simp add: OclValid_def false_def true_def, rule conjI, blast)
  apply(simp add: OclSelect_invalid[simplified invalid_def]
                  OclSelect_body_strict1[simplified invalid_def]
                  inv_bot')
 done
qed

subsection{* OclReject *}

lemma OclReject_mtSet_exec[simp,code_unfold]: "OclReject mtSet P = mtSet"
by(simp add: OclReject_def)

lemma OclReject_including_exec[simp,code_unfold]:
 assumes P_cp : "cp P"
 shows "OclReject (X->including(y)) P = OclSelect_body (not o P) y (OclReject (X->excluding(y)) P)"
 apply(simp add: OclReject_def comp_def, rule OclSelect_including_exec)
by (metis assms cp_intro''(5))

section{* Execution on Set's Operators (higher composition) *}

subsection{* OclIncluding *}

(* logical level : *)
lemma OclIncluding_idem0 :
 assumes "\<tau> \<Turnstile> \<delta> S"
     and "\<tau> \<Turnstile> \<upsilon> i"
   shows "\<tau> \<Turnstile> (S->including(i)->including(i) \<triangleq> (S->including(i)))"
by(simp add: OclIncluding_includes OclIncludes_charn1 assms)

(* Pure algebraic level *)
theorem OclIncluding_idem[simp,code_unfold]: "((S :: ('\<AA>,'a::null)Set)->including(i)->including(i) = (S->including(i)))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including(i)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A':"\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including(i)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including(i)->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->including(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
      apply(simp only: OclIncluding_idem0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
      apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
     apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
  done
qed

subsection{* OclExcluding *}

(* logical level : *)
lemma OclExcluding_idem0 :
 assumes "\<tau> \<Turnstile> \<delta> S"
     and "\<tau> \<Turnstile> \<upsilon> i"
   shows "\<tau> \<Turnstile> (S->excluding(i)->excluding(i) \<triangleq> (S->excluding(i)))"
by(simp add: OclExcluding_excludes OclExcludes_charn1 assms)

(* Pure algebraic level *)
theorem OclExcluding_idem[simp,code_unfold]: "((S->excluding(i))->excluding(i)) = (S->excluding(i))"
proof -
  have A: "\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->excluding(i)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have A':"\<And> \<tau>.   \<tau> \<Turnstile> (i \<triangleq> invalid)   \<Longrightarrow> (S->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->excluding(i)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have C': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> invalid)   \<Longrightarrow> (S->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D: "\<And> \<tau>.   \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->excluding(i)->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  have D': "\<And> \<tau>.  \<tau> \<Turnstile> (S \<triangleq> null)   \<Longrightarrow> (S->excluding(i)) \<tau> = invalid \<tau>"
            apply(rule foundation22[THEN iffD1])
            by(erule StrongEq_L_subst2_rev, simp,simp)
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> i)")
     apply(case_tac "\<tau> \<Turnstile> (\<delta> S)")
      apply(simp only: OclExcluding_idem0[THEN foundation22[THEN iffD1]])
      apply(simp add: foundation16', elim disjE)
      apply(simp add: C[OF foundation22[THEN iffD2]] C'[OF foundation22[THEN iffD2]])
     apply(simp add: D[OF foundation22[THEN iffD2]] D'[OF foundation22[THEN iffD2]])
   apply(simp add:foundation18 A[OF foundation22[THEN iffD2]] A'[OF foundation22[THEN iffD2]])
  done
qed

subsection{* OclIncludes *}


lemma OclIncludes_any[simp,code_unfold]:
      "X->includes(X->any()) = (if \<delta> X then
                                  if \<delta> (X->size()) then not(X->isEmpty())
                                  else X->includes(null) endif
                                else invalid endif)"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)



 have notempty': "\<And>\<tau> X. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> not (X->isEmpty()) \<tau> \<noteq> true \<tau> \<Longrightarrow>
                        X \<tau> = Set{} \<tau>"
  apply(case_tac "X \<tau>", rename_tac X', simp add: mtSet_def Abs_Set_0_inject)
  apply(erule disjE, metis (hide_lams, no_types) bot_Set_0_def bot_option_def foundation16[THEN iffD1,standard])
  apply(erule disjE, metis (hide_lams, no_types) bot_option_def
                                                 null_Set_0_def null_option_def foundation16[THEN iffD1,standard])
  apply(case_tac X', simp, metis (hide_lams, no_types) bot_Set_0_def foundation16[THEN iffD1,standard])
  apply(rename_tac X'', case_tac X'', simp)
   apply (metis (hide_lams, no_types) foundation16[THEN iffD1,standard] null_Set_0_def)
  apply(simp add: OclIsEmpty_def OclSize_def)
  apply(subst (asm) cp_OclNot, subst (asm) cp_OclOr, subst (asm) cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r,
        subst (asm) cp_OclAnd, subst (asm) cp_OclNot)
  apply(simp only: OclValid_def foundation20[simplified OclValid_def]
                   cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
  apply(simp add: Abs_Set_0_inverse split: split_if_asm)
 by(simp add: true_def OclInt0_def OclNot_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def)

 have B: "\<And>X \<tau>. \<not> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> (\<delta> (X->size())) \<tau> = false \<tau>"
  apply(subst cp_defined)
  apply(simp add: OclSize_def)
 by (metis OCL_core.bot_fun_def defined_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>, simp only: OclIncludes_def OclANY_def)
  apply(subst cp_OclIf, subst (2) cp_valid)
  apply(case_tac "(\<delta> X) \<tau> = true \<tau>",
        simp only: foundation20[simplified OclValid_def] cp_OclIf[symmetric], simp,
        subst (1 2) cp_OclAnd, simp add: cp_OclAnd[symmetric])
   apply(case_tac "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>")
    apply(frule size_defined'[THEN iffD2, simplified OclValid_def], assumption)
    apply(subst (1 2 3 4) cp_OclIf, simp)
    apply(subst (1 2 3 4) cp_OclIf[symmetric], simp)
    apply(case_tac "(X->notEmpty()) \<tau> = true \<tau>", simp)
     apply(frule OclNotEmpty_has_elt[simplified OclValid_def], simp)
     apply(simp add: OclNotEmpty_def cp_OclIf[symmetric])
     apply(subgoal_tac "(SOME y. y \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>) \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>", simp add: true_def)
      apply(metis OclValid_def Set_inv_lemma foundation18' null_option_def true_def)
     apply(rule someI_ex, simp)
    apply(simp add: OclNotEmpty_def cp_valid[symmetric])
    apply(subgoal_tac "\<not> (null \<tau> \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)", simp)
     apply(subst OclIsEmpty_def, simp add: OclSize_def)
     apply(subst cp_OclNot, subst cp_OclOr, subst cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r, subst cp_OclAnd,
           subst cp_OclNot, simp add: OclValid_def foundation20[simplified OclValid_def]
                                      cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
     apply(frule notempty'[simplified OclValid_def],
           (simp add: mtSet_def Abs_Set_0_inverse OclInt0_def false_def)+)
    apply(drule notempty'[simplified OclValid_def], simp, simp)
    apply (metis (hide_lams, no_types) empty_iff mtSet_rep_set)
   (* *)
   apply(frule B)
   apply(subst (1 2 3 4) cp_OclIf, simp)
   apply(subst (1 2 3 4) cp_OclIf[symmetric], simp)
   apply(case_tac "(X->notEmpty()) \<tau> = true \<tau>", simp)
    apply(frule OclNotEmpty_has_elt[simplified OclValid_def], simp)
    apply(simp add: OclNotEmpty_def OclIsEmpty_def)
    apply(subgoal_tac "X->size() \<tau> = \<bottom>")
     prefer 2
     apply (metis (hide_lams, no_types) OclSize_def)
    apply(subst (asm) cp_OclNot, subst (asm) cp_OclOr, subst (asm) cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r,
          subst (asm) cp_OclAnd, subst (asm) cp_OclNot)
    apply(simp add: OclValid_def foundation20[simplified OclValid_def]
                    cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
    apply(simp add: OclNot_def StrongEq_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def false_def true_def
                    bot_option_def bot_fun_def invalid_def)

   apply (metis OCL_core.bot_fun_def null_fun_def null_is_valid valid_def)
 by(drule defined_inject_true,
    simp add: false_def true_def OclIf_false[simplified false_def] invalid_def)
qed

subsection{* OclSize *}

lemma [simp,code_unfold]: "\<delta> (Set{} ->size()) = true"
by simp


lemma [simp,code_unfold]: "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have OclIncluding_finite_rep_set : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule OclIncluding_finite_rep_set)
 by(metis OclValid_def foundation5)+

 have card_including_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> =
                                 (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
 by(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->including(x)->size())) \<tau> = true \<tau>", simp del: OclSize_including_exec)
   apply(subst cp_OclAnd, subst cp_defined, simp only: cp_defined[of "X->including(x)->size()"],
         simp add: OclSize_def)
   apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil>)", simp)
    apply(erule conjE,
          simp add: OclIncluding_finite_rep_set[simplified OclValid_def] card_including_exec
                    cp_OclAnd[of "\<delta> X" "\<upsilon> x"]
                    cp_OclAnd[of "true", THEN sym])
    apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
    apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def],
          simp only: cp_OclAnd[THEN sym])
   apply(simp, simp add: defined_def true_def false_def bot_fun_def bot_option_def)

  apply(drule defined_inject_true[of "X->including(x)->size()"],
        simp del: OclSize_including_exec,
        simp only: cp_OclAnd[of "\<delta> (X->size())" "\<upsilon> x"],
        simp add: cp_defined[of "X->including(x)->size()" ] cp_defined[of "X->size()" ]
             del: OclSize_including_exec,
        simp add: OclSize_def card_including_exec
             del: OclSize_including_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: OclIncluding_finite_rep_set[simplified OclValid_def] card_including_exec,
        simp only: cp_OclAnd[THEN sym],
        simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
   apply(simp add: OclIncluding_finite_rep_set[simplified OclValid_def] card_including_exec)+
  apply(simp only: cp_OclAnd[THEN sym], simp, rule impI, erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_OclAnd[of "\<delta> X" "\<upsilon> x"])
 by(drule valid_inject_true[of "x"], simp add: cp_OclAnd[of _ "\<upsilon> x"])
qed

lemma [simp,code_unfold]: "\<delta> ((X ->excluding(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have OclExcluding_finite_rep_set : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                                     finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil> =
                                     finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule OclExcluding_finite_rep_set)
 by(metis OclValid_def foundation5)+

 have card_excluding_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> =
                                   (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
 by(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->excluding(x)->size())) \<tau> = true \<tau>", simp)
   apply(subst cp_OclAnd, subst cp_defined, simp only: cp_defined[of "X->excluding(x)->size()"],
         simp add: OclSize_def)
   apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil>)", simp)
    apply(erule conjE,
          simp add: OclExcluding_finite_rep_set[simplified OclValid_def] card_excluding_exec
                    cp_OclAnd[of "\<delta> X" "\<upsilon> x"]
                    cp_OclAnd[of "true", THEN sym])
    apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
    apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def],
          simp only: cp_OclAnd[THEN sym])
   apply(simp, simp add: defined_def true_def false_def bot_fun_def bot_option_def)

  apply(drule defined_inject_true[of "X->excluding(x)->size()"],
        simp,
        simp only: cp_OclAnd[of "\<delta> (X->size())" "\<upsilon> x"],
        simp add: cp_defined[of "X->excluding(x)->size()" ] cp_defined[of "X->size()" ],
        simp add: OclSize_def card_excluding_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: OclExcluding_finite_rep_set[simplified OclValid_def] card_excluding_exec,
        simp only: cp_OclAnd[THEN sym],
        simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
   apply(simp add: OclExcluding_finite_rep_set[simplified OclValid_def] card_excluding_exec)+
  apply(simp only: cp_OclAnd[THEN sym], simp, rule impI, erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_OclAnd[of "\<delta> X" "\<upsilon> x"])
 by(drule valid_inject_true[of "x"], simp add: cp_OclAnd[of _ "\<upsilon> x"])
qed

lemma [simp]:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X) and \<upsilon>(x))"
by(simp add: size_defined[OF X_finite] del: OclSize_including_exec)


subsection{* OclForall *}

lemma OclForall_rep_set_false:
 assumes "\<tau> \<Turnstile> \<delta> X"
 shows "(OclForall X P \<tau> = false \<tau>) = (\<exists>x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>\<tau>. x) \<tau> = false \<tau>)"
by(insert assms, simp add: OclForall_def OclValid_def false_def true_def invalid_def
                           bot_fun_def bot_option_def null_fun_def null_option_def)

lemma OclForall_rep_set_true:
 assumes "\<tau> \<Turnstile> \<delta> X"
 shows "(\<tau> \<Turnstile> OclForall X P) = (\<forall>x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> P (\<lambda>\<tau>. x))"
proof -
 have destruct_ocl : "\<And>x \<tau>. x = true \<tau> \<or> x = false \<tau> \<or> x = null \<tau> \<or> x = \<bottom> \<tau>"
  apply(case_tac x) apply (metis bot_Boolean_def)
  apply(rename_tac x', case_tac x') apply (metis null_Boolean_def)
  apply(rename_tac x'', case_tac x'') apply (metis (full_types) true_def)
 by (metis (full_types) false_def)

 have disjE4 : "\<And> P1 P2 P3 P4 R.
   (P1 \<or> P2 \<or> P3 \<or> P4) \<Longrightarrow> (P1 \<Longrightarrow> R) \<Longrightarrow> (P2 \<Longrightarrow> R) \<Longrightarrow> (P3 \<Longrightarrow> R) \<Longrightarrow> (P4 \<Longrightarrow> R) \<Longrightarrow> R"
 by metis
 show ?thesis
  apply(simp add: OclForall_def OclValid_def true_def false_def invalid_def
                  bot_fun_def bot_option_def null_fun_def null_option_def split: split_if_asm)
  apply(rule conjI, rule impI) apply (metis OCL_core.drop.simps option.distinct(1) invalid_def)
  apply(rule impI, rule conjI, rule impI) apply (metis option.distinct(1))
  apply(rule impI, rule conjI, rule impI) apply (metis OCL_core.drop.simps)
  apply(intro conjI impI ballI)
   proof - fix x show "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>None\<rfloor> \<Longrightarrow>
                       \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. \<exists>y. P (\<lambda>_. x) \<tau> = \<lfloor>y\<rfloor> \<Longrightarrow>
                       \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<lfloor>\<lfloor>False\<rfloor>\<rfloor> \<Longrightarrow>
                       x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> P (\<lambda>\<tau>. x) \<tau> = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>"
   apply(erule_tac x = x in ballE)+
   by(rule disjE4[OF destruct_ocl[of "P (\<lambda>\<tau>. x) \<tau>"]],
      (simp add: true_def false_def null_fun_def null_option_def bot_fun_def bot_option_def)+)
  apply_end(simp add: assms[simplified OclValid_def true_def])+
 qed
qed

lemma OclForall_includes :
 assumes x_def : "\<tau> \<Turnstile> \<delta> x"
     and y_def : "\<tau> \<Turnstile> \<delta> y"
   shows "(\<tau> \<Turnstile> OclForall x (OclIncludes y)) = (\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>)"
 apply(simp add: OclForall_rep_set_true[OF x_def],
       simp add: OclIncludes_def OclValid_def y_def[simplified OclValid_def])
 apply(insert Set_inv_lemma[OF x_def], simp add: valid_def false_def true_def bot_fun_def)
by(rule iffI, simp add: subsetI, simp add: subsetD)

lemma OclForall_not_includes :
 assumes x_def : "\<tau> \<Turnstile> \<delta> x"
     and y_def : "\<tau> \<Turnstile> \<delta> y"
   shows "(OclForall x (OclIncludes y) \<tau> = false \<tau>) = (\<not> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>)"
 apply(simp add: OclForall_rep_set_false[OF x_def],
       simp add: OclIncludes_def OclValid_def y_def[simplified OclValid_def])
 apply(insert Set_inv_lemma[OF x_def], simp add: valid_def false_def true_def bot_fun_def)
by(rule iffI, metis set_rev_mp, metis subsetI)

lemma OclForall_iterate:
 assumes S_finite: "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
   shows "S->forAll(x | P x) \<tau> = (S->iterate(x; acc = true | acc and P x)) \<tau>"
proof -
 have and_comm : "comp_fun_commute (\<lambda>x acc. acc and P x)"
  apply(simp add: comp_fun_commute_def comp_def)
 by (metis OclAnd_assoc OclAnd_commute)

 have ex_insert : "\<And>x F P. (\<exists>x\<in>insert x F. P x) = (P x \<or> (\<exists>x\<in>F. P x))"
 by (metis insert_iff)

 have destruct_ocl : "\<And>x \<tau>. x = true \<tau> \<or> x = false \<tau> \<or> x = null \<tau> \<or> x = \<bottom> \<tau>"
  apply(case_tac x) apply (metis bot_Boolean_def)
  apply(rename_tac x', case_tac x') apply (metis null_Boolean_def)
  apply(rename_tac x'', case_tac x'') apply (metis (full_types) true_def)
 by (metis (full_types) false_def)

 have disjE4 : "\<And> P1 P2 P3 P4 R.
   (P1 \<or> P2 \<or> P3 \<or> P4) \<Longrightarrow> (P1 \<Longrightarrow> R) \<Longrightarrow> (P2 \<Longrightarrow> R) \<Longrightarrow> (P3 \<Longrightarrow> R) \<Longrightarrow> (P4 \<Longrightarrow> R) \<Longrightarrow> R"
 by metis

 let ?P_eq = "\<lambda>x b \<tau>. P (\<lambda>_. x) \<tau> = b \<tau>"
 let ?P = "\<lambda>set b \<tau>. \<exists>x\<in>set. ?P_eq x b \<tau>"
 let ?if = "\<lambda>f b c. if f b \<tau> then b \<tau> else c"
 let ?forall = "\<lambda>P. ?if P false (?if P invalid (?if P null (true \<tau>)))"
 show ?thesis
  apply(simp only: OclForall_def OclIterate_def)
  apply(case_tac "\<tau> \<Turnstile> \<delta> S", simp only: OclValid_def)
   apply(subgoal_tac "let set = \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> in
                      ?forall (?P set) =
                      Finite_Set.fold (\<lambda>x acc. acc and P x) true ((\<lambda>a \<tau>. a) ` set) \<tau>",
         simp only: Let_def, simp add: S_finite, simp only: Let_def)
   apply(case_tac "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = {}", simp)
   apply(rule finite_ne_induct[OF S_finite], simp)
    (* *)
    apply(simp only: image_insert)
    apply(subst comp_fun_commute.fold_insert[OF and_comm], simp)
     apply (metis empty_iff image_empty)
    apply(simp add: invalid_def)
    apply (metis OCL_core.bot_fun_def destruct_ocl null_fun_def)
   (* *)
   apply(simp only: image_insert)
   apply(subst comp_fun_commute.fold_insert[OF and_comm], simp)
    apply (metis (mono_tags) imageE)

   (* *)
   apply(subst cp_OclAnd) apply(drule sym, drule sym, simp only:, drule sym, simp only:)
   apply(simp only: ex_insert)
   apply(subgoal_tac "\<exists>x. x\<in>F") prefer 2
    apply(metis all_not_in_conv)
   proof - fix x F show "(\<delta> S) \<tau> = true \<tau> \<Longrightarrow> \<exists>x. x \<in> F \<Longrightarrow>
            ?forall (\<lambda>b \<tau>. ?P_eq x b \<tau> \<or> ?P F b \<tau>) =
            ((\<lambda>_. ?forall (?P F)) and (\<lambda>_. P (\<lambda>\<tau>. x) \<tau>)) \<tau>"
    apply(rule disjE4[OF destruct_ocl[where x = "P (\<lambda>\<tau>. x) \<tau>"]])
       apply(simp_all add: true_def false_def invalid_def OclAnd_def
                           null_fun_def null_option_def bot_fun_def bot_option_def)
   by (metis (lifting) option.distinct(1))+
   apply_end(simp add: OclValid_def)+
 qed
qed

lemma OclForall_cong:
 assumes "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<tau> \<Turnstile> P (\<lambda>\<tau>. x) \<Longrightarrow> \<tau> \<Turnstile> Q (\<lambda>\<tau>. x)"
 assumes P: "\<tau> \<Turnstile> OclForall X P"
 shows "\<tau> \<Turnstile> OclForall X Q"
proof -
 have def_X: "\<tau> \<Turnstile> \<delta> X"
 by(insert P, simp add: OclForall_def OclValid_def bot_option_def true_def split: split_if_asm)
 show ?thesis
  apply(insert P)
  apply(subst (asm) OclForall_rep_set_true[OF def_X], subst OclForall_rep_set_true[OF def_X])
 by (simp add: assms)
qed

lemma OclForall_cong':
 assumes "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<tau> \<Turnstile> P (\<lambda>\<tau>. x) \<Longrightarrow> \<tau> \<Turnstile> Q (\<lambda>\<tau>. x) \<Longrightarrow> \<tau> \<Turnstile> R (\<lambda>\<tau>. x)"
 assumes P: "\<tau> \<Turnstile> OclForall X P"
 assumes Q: "\<tau> \<Turnstile> OclForall X Q"
 shows "\<tau> \<Turnstile> OclForall X R"
proof -
 have def_X: "\<tau> \<Turnstile> \<delta> X"
 by(insert P, simp add: OclForall_def OclValid_def bot_option_def true_def split: split_if_asm)
 show ?thesis
  apply(insert P Q)
  apply(subst (asm) (1 2) OclForall_rep_set_true[OF def_X], subst OclForall_rep_set_true[OF def_X])
 by (simp add: assms)
qed

subsection{* Strict Equality *}

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_defined :
 assumes x_def: "\<tau> \<Turnstile> \<delta> x"
 assumes y_def: "\<tau> \<Turnstile> \<delta> y"
 shows "((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) \<tau> =
                (x->forAll(z| y->includes(z)) and (y->forAll(z| x->includes(z)))) \<tau>"
proof -
 have rep_set_inj : "\<And>\<tau>. (\<delta> x) \<tau> = true \<tau> \<Longrightarrow>
                         (\<delta> y) \<tau> = true \<tau> \<Longrightarrow>
                          x \<tau> \<noteq> y \<tau> \<Longrightarrow>
                          \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil> \<noteq> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>"
  apply(simp add: defined_def)
  apply(split split_if_asm, simp add: false_def true_def)+
  apply(simp add: null_fun_def null_Set_0_def bot_fun_def bot_Set_0_def)

  apply(case_tac "x \<tau>", rename_tac x')
  apply(case_tac x', simp_all, rename_tac x'')
  apply(case_tac x'', simp_all)

  apply(case_tac "y \<tau>", rename_tac y')
  apply(case_tac y', simp_all, rename_tac y'')
  apply(case_tac y'', simp_all)

  apply(simp add: Abs_Set_0_inverse)
 by(blast)

 show ?thesis
  apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def
    foundation20[OF x_def, simplified OclValid_def]
    foundation20[OF y_def, simplified OclValid_def])
  apply(subgoal_tac "\<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = true \<tau> \<or> \<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = false \<tau>")
   prefer 2
   apply(simp add: false_def true_def)
  (* *)
  apply(erule disjE)
   apply(simp add: true_def)

   apply(subgoal_tac "(\<tau> \<Turnstile> OclForall x (OclIncludes y)) \<and> (\<tau> \<Turnstile> OclForall y (OclIncludes x))")
    apply(subst cp_OclAnd, simp add: true_def OclValid_def)
   apply(simp add: OclForall_includes[OF x_def y_def]
                   OclForall_includes[OF y_def x_def])

  (* *)
  apply(simp)

  apply(subgoal_tac "OclForall x (OclIncludes y) \<tau> = false \<tau> \<or>
                     OclForall y (OclIncludes x) \<tau> = false \<tau>")
   apply(subst cp_OclAnd, metis OclAnd_false1 OclAnd_false2 cp_OclAnd)
  apply(simp only: OclForall_not_includes[OF x_def y_def, simplified OclValid_def]
                   OclForall_not_includes[OF y_def x_def, simplified OclValid_def],
        simp add: false_def)
 by (metis OclValid_def rep_set_inj subset_antisym x_def y_def)
qed

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec[simp,code_unfold] :
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) =
  (if \<delta> x then (if \<delta> y
                then ((x->forAll(z| y->includes(z)) and (y->forAll(z| x->includes(z)))))
                else if \<upsilon> y
                      then false (* x'->includes = null *)
                      else invalid
                      endif
                endif)
         else if \<upsilon> x (* null = ??? *)
              then if \<upsilon> y then not(\<delta> y) else invalid endif
              else invalid
              endif
         endif)"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<not> (\<tau> \<Turnstile> \<delta> P)) = ((\<delta> P) \<tau> = false \<tau>)"
 by (metis bot_fun_def OclValid_def defined_def foundation16 null_fun_def)

 have valid_inject_true : "\<And>\<tau> P. (\<not> (\<tau> \<Turnstile> \<upsilon> P)) = ((\<upsilon> P) \<tau> = false \<tau>)"
 by (metis bot_fun_def OclIf_true' OclIncludes_charn0 OclIncludes_charn0' OclValid_def valid_def
           foundation6 foundation9)
 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  (* *)
  apply(simp add: OclIf_def
                  defined_inject_true[simplified OclValid_def]
                  valid_inject_true[simplified OclValid_def],
        subst false_def, subst true_def, simp)
  apply(subst (1 2) cp_OclNot, simp, simp add: cp_OclNot[symmetric])
  apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_defined[simplified OclValid_def])
 by(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def false_def true_def valid_def defined_def)
qed

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow>
    \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def)
 apply(split split_if_asm)
  apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma OclIncluding_cong' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
    \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including(x) \<doteq> (t->including(x)))"
proof -
 have cp: "cp (\<lambda>s. (s->including(x)))"
  apply(simp add: cp_def, subst cp_OclIncluding)
 by (rule_tac x = "(\<lambda>xab ab. ((\<lambda>_. xab)->including(\<lambda>_. x ab)) ab)" in exI, simp)

 show "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> ?thesis"
  apply(rule_tac P = "\<lambda>s. (s->including(x))" in StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1)
       apply(rule cp)
      apply(simp add: foundation20) apply(simp add: foundation20)
    apply (simp add: foundation10 foundation6)+
 done
qed

lemma OclIncluding_cong : "\<And>(s::('\<AA>,'a::null)Set) t x y \<tau>. \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                             \<tau> \<Turnstile> s \<doteq> t \<Longrightarrow> x = y \<Longrightarrow> \<tau> \<Turnstile> s->including(x) \<doteq> (t->including(y))"
 apply(simp only:)
 apply(rule OclIncluding_cong', simp_all only:)
by(auto simp: OclValid_def OclIf_def invalid_def bot_option_def OclNot_def split : split_if_asm)

lemma const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_empty : "const X \<Longrightarrow>
                                       const (X \<doteq> Set{})"
 apply(rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t, assumption)
by(simp)

lemma const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including : "const a \<Longrightarrow> const S \<Longrightarrow> const X \<Longrightarrow>
                                       const (X \<doteq> S->including(a))"
 apply(rule const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t, assumption)
by(rule const_OclIncluding)

section{* Test Statements *}

Assert   "(\<tau> \<Turnstile> (Set{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>} \<doteq> Set{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>}))"
Assert   "(\<tau> \<Turnstile> (Set{\<lambda>_. \<lfloor>x\<rfloor>} \<doteq> Set{\<lambda>_. \<lfloor>x\<rfloor>}))"

end
