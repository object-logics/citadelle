(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
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
        (* UML_Set *)
begin

section{* Collection Type Sequence: Operations *}

subsubsection{* Properties of the Sequence Type  *}
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

text_raw{* \isatagafp *}

lemma [simp,code_unfold]: "const Sequence{}"
by(simp add: const_def mtSequence_def)

text{* Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid. *}

lemmas cp_intro''\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e[intro!,simp,code_unfold] = cp_intro'
text_raw{* \endisatagafp *}


subsection{* Definition: Strict Equality \label{sec:seq-strict-equality}*}

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

subsection{* Definition: prepend *}
definition OclPrepend   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclPrepend x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> (y \<tau>)#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclPrepend   ("_->prepend\<^sub>S\<^sub>e\<^sub>q'(_')")

interpretation OclPrepend:profile_bin2 OclPrepend "\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>"
proof -  
 have A : "\<And>x y. x \<noteq> bot \<Longrightarrow> x \<noteq> null \<Longrightarrow>  y \<noteq> bot  \<Longrightarrow>
           \<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by(auto intro!:Sequence_inv_lemma[simplified OclValid_def 
                         defined_def false_def true_def null_fun_def bot_fun_def])  
                                       
         show "profile_bin2 OclPrepend (\<lambda>x y. Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor>)"
         apply unfold_locales  
          apply(auto simp:OclPrepend_def bot_option_def null_option_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def 
               bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" 
                in contrapos_pp)
          apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject [OF A])
             apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>y#\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" 
               in contrapos_pp)
         apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF A])
            apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def 
                                 bot_option_def null_option_def)
         done
qed
                
syntax
  "_OclFinsequence" :: "args => ('\<AA>,'a::null) Sequence"    ("Sequence{(_)}")
translations
  "Sequence{x, xs}" == "CONST OclPrepend (Sequence{xs}) x"
  "Sequence{x}"     == "CONST OclPrepend (Sequence{}) x "

subsection{* Definition: including *}

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
          apply(auto simp:OclIncluding_def bot_option_def null_option_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def 
               bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
          apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e None" 
                in contrapos_pp)
          apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject [OF A])
             apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def)
         apply(erule_tac Q="Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil> @ [y]\<rfloor>\<rfloor> = Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>" 
               in contrapos_pp)
         apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[OF A])
            apply(simp_all add:  null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_option_def null_option_def)
         done
qed

lemma [simp] : "(Sequence{}->including\<^sub>S\<^sub>e\<^sub>q(a)) = (Sequence{}->prepend\<^sub>S\<^sub>e\<^sub>q(a))"
sorry

lemma [simp] : "((S->prepend\<^sub>S\<^sub>e\<^sub>q(a))->including\<^sub>S\<^sub>e\<^sub>q(b)) = ((S->including\<^sub>S\<^sub>e\<^sub>q(b))->prepend\<^sub>S\<^sub>e\<^sub>q(a))"
sorry

subsection{* Definition: excluding *}
definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclExcluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> filter (\<lambda>x. x = y \<tau>)
                                                                   \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclExcluding   ("_->excluding\<^sub>S\<^sub>e\<^sub>q'(_')")

subsection{* Definition: append *}
text{* identical to including *}
definition OclAppend   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclAppend = OclIncluding"

(* TODO: Locale Setup by hand. *)

subsection{* Definition: union *}
definition OclUnion   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<alpha>) Sequence] \<Rightarrow> ('\<AA>,'\<alpha>) Sequence"
where     "OclUnion x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                                then Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> @
                                                        \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (y \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>
                                    else invalid \<tau> )"
notation   OclUnion   ("_->union\<^sub>S\<^sub>e\<^sub>q'(_')")
(* TODO: Locale Setup. *)


subsection{* Definition: subSequence *}
(*TODO.*)  

subsection{* Definition: at *}
definition OclAt   :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>) Integer] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclAt x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                             then if  1 \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil> \<and>  \<lceil>\<lceil>y \<tau>\<rceil>\<rceil> \<le> length\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> 
                                  then \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> ! (nat \<lceil>\<lceil>y \<tau>\<rceil>\<rceil> + 1) 
                                  else invalid \<tau>
                             else invalid \<tau> )"
notation   OclAt ("_->at\<^sub>S\<^sub>e\<^sub>q'(_')")


subsection{* Definition: first *}
definition OclFirst   :: "[('\<AA>,'\<alpha>::null) Sequence] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclFirst x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau>
                                    then hd \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> 
                                    else invalid \<tau> )"
notation   OclFirst   ("_->first\<^sub>S\<^sub>e\<^sub>q'(_')")


subsection{* Definition: last *}
definition OclLast   :: "[('\<AA>,'\<alpha>::null) Sequence] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "OclLast x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau>
                                    then last \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x \<tau>)\<rceil>\<rceil> 
                                    else invalid \<tau> )"
notation   OclLast   ("_->last\<^sub>S\<^sub>e\<^sub>q'(_')")

subsection{* Definition: iterate *}

value "foldr (% x S. [x+1]@S) [1::int,2,3] []"
definition OclIterate :: "[('\<AA>,'\<alpha>::null) Sequence,('\<AA>,'\<beta>::null)val,
                           ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where "OclIterate S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> 
                                  then (foldr (F) (map (\<lambda>a \<tau>. a) \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>))(A)\<tau>
                                  else \<bottom>)"
syntax
  "_OclIterate"  :: "[('\<AA>,'\<alpha>::null) Set, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate\<^sub>S\<^sub>e\<^sub>q'(_;_=_ | _')" (*[71,100,70]50*))
translations
  "X->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P)" == "CONST OclIterate X A (%a. (% x. P))"

lemma iterate_strict1[simp]:"invalid->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P) = invalid"  
by(simp add: OclIterate_def false_def true_def, simp add: invalid_def)

lemma iterate_strict2[simp]:"null->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P) = invalid"  
by(simp add: OclIterate_def false_def true_def, simp add: invalid_def)

lemma iterate_mt[simp]:"Sequence{}->iterate\<^sub>S\<^sub>e\<^sub>q(a; x = A | P) = A"  
apply(simp add: OclIterate_def foundation22[symmetric] foundation13, 
      rule ext, rename_tac "\<tau>")
apply(case_tac "\<tau> \<Turnstile> \<upsilon> A", simp_all add: foundation18')
apply(simp add: mtSequence_def)
apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse) by auto

lemma iterate_prepend[simp]:
assumes strict1 : "\<And>X. P invalid X = invalid"
and     strict2 : "\<And>X. P X invalid = invalid"
shows  "(S->prepend\<^sub>S\<^sub>e\<^sub>q(a))->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = A | P b x) = S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = P a A| P b x)"
sorry

subsection{* Definition: forall *}
definition OclForall     :: "[('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall S P = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = true | x and (P b)))"

syntax
  "_OclForallSeq" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forAll\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->forAll\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST UML_Sequence.OclForall X (%x. P)"

subsection{* Definition: exists *}
definition OclExists     :: "[('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclExists S P = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = false | x or (P b)))"

syntax
  "_OclExistSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->exists\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->exists\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST OclExists X (%x. P)"


subsection{* Definition: collect *}
definition OclCollect     :: "[('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val]\<Rightarrow>('\<AA>,'\<beta>::null)Sequence"
where     "OclCollect S P = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = Sequence{} | x->prepend\<^sub>S\<^sub>e\<^sub>q(P b)))"

syntax
  "_OclCollectSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->collect\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->collect\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST OclCollect X (%x. P)"


subsection{* Definition: select *}
definition OclSelect     :: "[('\<AA>,'\<alpha>::null)Sequence,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean]\<Rightarrow>('\<AA>,'\<alpha>::null)Sequence"
where     "OclSelect S P = 
           (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = Sequence{} | if P b then x->prepend\<^sub>S\<^sub>e\<^sub>q(b) else x endif))"

syntax
  "_OclSelectSeq" :: "[('\<AA>,'\<alpha>::null) Sequence,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"  ("(_)->select\<^sub>S\<^sub>e\<^sub>q'(_|_')")
translations
  "X->select\<^sub>S\<^sub>e\<^sub>q(x | P)" == "CONST UML_Sequence.OclSelect X (%x. P)"


subsection{* Definition: size *}
definition OclSize     :: "[('\<AA>,'\<alpha>::null)Sequence]\<Rightarrow>('\<AA>)Integer" ("(_)->size\<^sub>S\<^sub>e\<^sub>q'(')")
where     "OclSize S = (S->iterate\<^sub>S\<^sub>e\<^sub>q(b; x = \<zero> | x +\<^sub>i\<^sub>n\<^sub>t \<one> ))"

subsection{* Definition: isEmpty *}
definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Sequence \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((\<upsilon> x and not (\<delta> x)) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty\<^sub>S\<^sub>e\<^sub>q'(')" (*[66]*))

subsection{* Definition: NotEmpty *}

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Sequence \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty\<^sub>S\<^sub>e\<^sub>q'(')" (*[66]*))

(*TODO.*)  
  
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

Assert   "\<tau> \<Turnstile> (Sequence{} \<doteq> Sequence{})" 
Assert   "\<tau> \<Turnstile> (Sequence{\<one>,\<two>} \<triangleq> Sequence{}->prepend\<^sub>S\<^sub>e\<^sub>q(\<two>)->prepend\<^sub>S\<^sub>e\<^sub>q(\<one>))" 
Assert   "\<tau> \<Turnstile> (Sequence{\<one>,invalid,\<two>} \<triangleq> invalid)"


(* TODO Frederic ?:
Assert   "\<not> (\<tau> \<Turnstile> (Sequence{\<one>,\<one>,\<two>} \<doteq> Sequence{\<one>,\<two>}))"
Assert   "\<not> (\<tau> \<Turnstile> (Sequence{\<one>,\<two>} \<doteq> Sequence{\<two>,\<one>}))"
*)

end
