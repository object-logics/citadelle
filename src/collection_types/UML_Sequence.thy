(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Sequence.thy --- Library definitions.
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

theory  UML_Sequence
imports "../basic_types/UML_Boolean"
        "../basic_types/UML_Integer"
begin

section{* Collection Type Sequence: Operations *}

subsection{* Constants: mtSequence *}
definition mtSequence ::"('\<AA>,'\<alpha>::null) Sequence"  ("Sequence{}")
where     "Sequence{} \<equiv> (\<lambda> \<tau>.  Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>[]::'\<alpha> list\<rfloor>\<rfloor> )"

declare mtSequence_def[code_unfold]

lemma mtSequence_defined[simp,code_unfold]:"\<delta>(Sequence{}) = true"
apply(rule ext, auto simp: mtSequence_def defined_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                           bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtSequence_valid[simp,code_unfold]:"\<upsilon>(Sequence{}) = true"
apply(rule ext,auto simp: mtSequence_def valid_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                          bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtSequence_rep_set: "\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Sequence{} \<tau>)\<rceil>\<rceil> = []"
 apply(simp add: mtSequence_def, subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
by(simp add: bot_option_def)+

lemma [simp,code_unfold]: "const Sequence{}"
by(simp add: const_def mtSequence_def)


text{* Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid. *}


lemmas cp_intro''\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e[intro!,simp,code_unfold] = cp_intro'

subsubsection{* Properties of Sequence Type:  *}

text{* Every element in a defined sequence is valid. *}

lemma Sequence_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<forall>x\<in>set \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot"
apply(insert Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e [of "X \<tau>"], simp)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def
           split:split_if_asm)
 apply(erule contrapos_pp [of "Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = bot"])
 apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
 apply(simp add: Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>) = null"])
apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], rule Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e, simp)
apply(simp add: Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse  null_option_def)
by (simp add: bot_option_def)

subsection{* Strict Equality *}

subsubsection{* Definition *}

text{* After the part of foundational operations on sets, we detail here equality on sets.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:*}

defs   StrictRefEq\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e [code_unfold]:
      "((x::('\<AA>,'\<alpha>::null)Sequence) \<doteq> y) \<equiv> (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                                  then (x \<triangleq> y)\<tau>
                                                  else invalid \<tau>)"


text{* Property proof in terms of @{term "profile_bin3"}*}
interpretation  StrictRefEq\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e : profile_bin3 "\<lambda> x y. (x::('\<AA>,'\<alpha>::null)Sequence) \<doteq> y" 
                by unfold_locales (auto simp:  StrictRefEq\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e)
 

subsection{* Standard Operations *}

subsubsection{* Definition: including *}

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>  @ [y \<tau>] \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclIncluding   ("_->including\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclIncluding : 
               profile_bin2 OclIncluding "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor>"
proof -  
 have A : "\<And>x y. x \<noteq> bot \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> bot  \<Longrightarrow>
           \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                         defined_def false_def true_def null_fun_def bot_fun_def])  
                                       
         show "profile_bin2 OclIncluding (\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclIncluding_def bot_option_def null_option_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" in contrapos_pp)
          apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject [OF A])
             apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" in contrapos_pp)
         apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF A])
            apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def null_option_def)
         done
qed

syntax
  "_OclFinsequence" :: "args => ('\<AA>,'a::null) Sequence"    ("Sequence{(_)}")
translations
  "Sequence{x, xs}" == "CONST OclIncluding (Sequence{xs}) x"
  "Sequence{x}"     == "CONST OclIncluding (Sequence{}) x "

  typ int
  typ num

subsubsection{* Definition: excluding *}
subsubsection{* Definition: union *}
subsubsection{* Definition: append *}
text{* identical to including *}
subsubsection{* Definition: prepend *}
subsubsection{* Definition: subSequence *}
subsubsection{* Definition: at *}
subsubsection{* Definition: first *}
subsubsection{* Definition: last *}
subsubsection{* Definition: asSet *}
  
  
(* open problem: An executable code-generator setup for the Sequence type. Some bits and pieces
so far : 
instantiation int :: equal
begin

definition
  "HOL.equal k l \<longleftrightarrow> k = (l::int)"

instance by default (rule equal_int_def)

end

lemma equal_int_code [code]:
  "HOL.equal 0 (0::int) \<longleftrightarrow> True"
  "HOL.equal 0 (Pos l) \<longleftrightarrow> False"
  "HOL.equal 0 (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Pos k) 0 \<longleftrightarrow> False"
  "HOL.equal (Pos k) (Pos l) \<longleftrightarrow> HOL.equal k l"
  "HOL.equal (Pos k) (Neg l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) 0 \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Pos l) \<longleftrightarrow> False"
  "HOL.equal (Neg k) (Neg l) \<longleftrightarrow> HOL.equal k l"
  by (auto simp add: equal)
*)  
  

instantiation Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e  :: (equal)equal
begin
  definition "HOL.equal k l \<longleftrightarrow>  (k::('a::equal)Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) =  l"
  instance   by default (rule equal_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
end

lemma equal_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_code [code]:
  "HOL.equal k (l::('a::{equal,null})Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<longleftrightarrow> Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e k = Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e l"
  by (auto simp add: equal Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
  
subsection{* Test Statements *}

Assert   "(\<tau> \<Turnstile> (Sequence{} \<doteq> Sequence{}))" 
Assert   " \<tau> \<Turnstile> (Sequence{\<one>,invalid,\<two>} \<triangleq> invalid)"


(* TODO Frederic ?:
Assert   "\<not> (\<tau> \<Turnstile> (Sequence{\<one>,\<one>,\<two>} \<doteq> Sequence{\<one>,\<two>}))"
Assert   "\<not> (\<tau> \<Turnstile> (Sequence{\<one>,\<two>} \<doteq> Sequence{\<two>,\<one>}))"
*)

end
