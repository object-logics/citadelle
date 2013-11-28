(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib_ground.thy --- Example using the OCL library.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013      Universite Paris-Sud, France
 *               2013      IRT SystemX, France
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

header{* Gogolla's challenge on Sets *}

theory
  OCL_lib_ground
imports
  "../src/OCL_lib"
begin

(*
Sequence{6,8}->iterate(i;r1:Sequence(Integer)=Sequence{9}|
  r1->iterate(j;r2:Sequence(Integer)=r1|
    r2->including(0)->including(i)->including(j)))
*)
text{* In order to analyze the performance of the library,
we propose in this section to execute and normalize a not trivial OCL expression.
Consider for instance this ground term:
@{term "Set{\<six>,\<eight>}->iterate(i;r1=Set{\<nine>}|
  r1->iterate(j;r2=r1|
    r2->including(\<zero>)->including(i)->including(j)))"}.
Starting from a set of numbers, this complex expression finally involves only two combinators:
1) @{term OclIterate\<^sub>S\<^sub>e\<^sub>t}, and
2) @{term OclIncluding}.

As there is no removing, we conjecture that the final result should be equal to the set
containing all ground numbers appearing in the expression: that is @{term \<six>}, @{term \<eight>}, @{term \<nine>}, @{term \<zero>}. *}
(* text{*(modulo ordering and duplication for sequences)*} *)

text{* The following part sets up the necessary requirement towards an automatic execution.
The goal is to normalize a general term composed of a set of numbers applied to an arbitrary nesting of
@{term OclIterate\<^sub>S\<^sub>e\<^sub>t} and @{term OclIncluding}.
One solution is to rawly compute the initial term by following a call by value strategy or by need.
However for efficiency reasons, we present in the next subsections some algebraic properties on sets
that would shortcut the number of reduction steps, by reaching optimaly a normal form. *}

section{* Introduction *}

text{* Besides the @{term invalid} exception element, the other important concept that
characterizes OCL sets in our formalization is the finiteness property.
Since the iteration could only be performed on finite sets, the definition of @{term OclIterate\<^sub>S\<^sub>e\<^sub>t}
contains as prerequisite a check that the given argument is finite. If it is the case,
@{term Finite_Set.fold} is then called internally to execute the iteration. *}

text{* Recall that our goal is to provide a generic solution to the Gogolla's challenge,
in the sense that we focus on an arbitrary list of nested @{term OclIterate\<^sub>S\<^sub>e\<^sub>t} combinators.
A naive approach for simplifying such huge expression would be to repeatedly rewrite with
@{term OclIterate\<^sub>S\<^sub>e\<^sub>t_including}.
However, @{term OclIterate\<^sub>S\<^sub>e\<^sub>t_including} contains @{term "comp_fun_commute F"} as hypothesis
and this one is generally difficult to prove. Indeed, the easiest case would be when simplifying
the outermost @{term OclIterate\<^sub>S\<^sub>e\<^sub>t} since the overall expression is ground. But for the others inner nested
@{term OclIterate\<^sub>S\<^sub>e\<^sub>t}, the @{term "F"} function could have as free variable a set
where its validity, definedness and finiteness are unknown --
and the finiteness is precisely required for all sets occuring
in a chain of @{term OclIterate\<^sub>S\<^sub>e\<^sub>t} nested term. *}

text{* Thus we propose to write an Isabelle locale similar as the locale @{term "comp_fun_commute"}
but containing the additional properties that sets should fulfill
while traveling through the nested @{term OclIterate\<^sub>S\<^sub>e\<^sub>t}.
For reusability, these properties will be abstractly regrouped in @{term "is_int"} (representing ground value in a set, like integer)
and @{term "all_defined"} (representing ground sets). *}

definition "is_int x \<equiv> \<forall> \<tau>. \<tau> \<Turnstile> \<upsilon> x \<and> (\<forall>\<tau>0. x \<tau> = x \<tau>0)"

lemma int_is_valid : "\<And>x. is_int x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
by (metis foundation18' is_int_def)

definition "all_int_set S \<equiv> finite S \<and> (\<forall>x\<in>S. is_int x)"
definition "all_int \<tau> S \<equiv> (\<tau> \<Turnstile> \<delta> S) \<and> all_int_set \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
definition "all_defined_set \<tau> S \<equiv> finite S \<and> (\<forall>x\<in>S. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x)))"
definition "all_defined_set' \<tau> S \<equiv> finite S"
definition "all_defined \<tau> S \<equiv> (\<tau> \<Turnstile> \<delta> S) \<and> all_defined_set' \<tau> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"

lemma all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> S \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 apply(simp add: all_defined_def, erule conjE, frule Set_inv_lemma)
 apply(simp add: all_defined_def all_defined_set'_def all_int_set_def is_int_def defined_def OclValid_def)
by (metis (no_types) OclValid_def foundation18' true_def Set_inv_lemma')

term "all_defined \<tau> (f \<zero> Set{\<zero>}) = (all_defined \<tau> Set{\<zero>})"
 (* we check here that all_defined could at least be applied to some useful value
    (i.e. we examine the type of all_defined) *)

lemma int_trivial : "is_int (\<lambda>_. \<lfloor>a\<rfloor>)" by(simp add: is_int_def OclValid_def valid_def bot_fun_def bot_option_def)

lemma EQ_sym : "(x::(_, _) Set) = y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<doteq> y)"
  apply(simp add: OclValid_def)
done

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma abs_rep_simp :
 assumes S_all_def : "all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
   shows "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
by(rule abs_rep_simp', simp add: assms[simplified all_defined_def])

lemma cp_all_def : "all_defined \<tau> f = all_defined \<tau>' (\<lambda>_. f \<tau>)"
  apply(simp add: all_defined_def all_defined_set'_def OclValid_def)
  apply(subst cp_defined)
by (metis (no_types) OclValid_def foundation16)

lemma cp_all_def' : "(\<forall>\<tau>. all_defined \<tau> f) = (\<forall>\<tau> \<tau>'. all_defined \<tau>' (\<lambda>_. f \<tau>))"
 apply(rule iffI)
 apply(rule allI) apply(erule_tac x = \<tau> in allE) apply(rule allI)
 apply(simp add: cp_all_def[THEN iffD1])
 apply(subst cp_all_def, blast)
done

lemma S_lift :
 assumes S_all_def : "all_defined (\<tau> :: '\<AA> st) S"
   shows "\<exists>S'. (\<lambda>a (_::'\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = (\<lambda>a (_::'\<AA> st). \<lfloor>a\<rfloor>) ` S'"
by(rule S_lift', simp add: assms[simplified all_defined_def])

lemma destruct_int : "is_int i \<Longrightarrow> \<exists>! j. i = (\<lambda>_. j)"
 proof - fix \<tau> show "is_int i \<Longrightarrow> ?thesis"
  apply(rule_tac a = "i \<tau>" in ex1I)
  apply(rule ext, simp add: is_int_def)
  apply (metis surj_pair)
  apply(simp)
 done
 apply_end(simp)
qed

section{* Properties: mtSet *}

lemma mtSet_all_def : "all_defined \<tau> Set{}"
proof -
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 show ?thesis
  apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set_0_inverse B)
 by (metis (no_types) foundation16 mtSet_def mtSet_defined transform1)
qed

lemma cp_mtSet : "\<And>x. Set{} = (\<lambda>_. Set{} x)"
by (metis (hide_lams, no_types) mtSet_def)

section{* Properties: OclIncluding *}

subsection{* Identity *}

lemma including_id' : "all_defined \<tau> (S:: ('\<AA>, 'a option option) Set) \<Longrightarrow>
                       x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       S->including(\<lambda>\<tau>. x) \<tau> = S \<tau>"
proof -
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "               all_defined \<tau> S \<Longrightarrow>
                      x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      ?thesis"
  apply(simp add: OclIncluding_def all_defined1[simplified OclValid_def] OclValid_def insert_absorb abs_rep_simp del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
 by (metis OCL_core.bot_fun_def all_defined_def foundation18' valid_def Set_inv_lemma')
qed

lemma including_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
   shows "            \<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->including(\<lambda>\<tau>. x) = S"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have x_val : "\<And>\<tau>. (\<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
               \<tau> \<Turnstile> \<upsilon> (\<lambda>\<tau>. x)"
  apply(insert S_all_def)
  apply(simp add: all_defined_def all_defined_set_def)
 by (metis (no_types) foundation18' Set_inv_lemma')

 show "               (\<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
                      ?thesis"
  apply(rule ext, rename_tac \<tau>', simp add: OclIncluding_def)
  apply(subst insert_absorb) apply (metis (full_types) surj_pair)
  apply(subst abs_rep_simp, simp add: S_all_def, simp)
  proof - fix \<tau>' show "\<forall>a b. x \<in> \<lceil>\<lceil>Rep_Set_0 (S (a, b))\<rceil>\<rceil> \<Longrightarrow> ((\<delta> S) \<tau>' = true \<tau>' \<longrightarrow> (\<upsilon> (\<lambda>\<tau>. x)) \<tau>' \<noteq> true \<tau>') \<longrightarrow> \<bottom> = S \<tau>'"
  apply(frule x_val[simplified, where \<tau> = \<tau>'])
  apply(insert S_all_def[where \<tau> = \<tau>'])
  apply(subst all_defined1[simplified OclValid_def], simp)
  by (metis OclValid_def)
 qed
 apply_end(simp)
qed

subsection{* Commutativity *}

lemma including_swap__generic :
 assumes includes_execute_generic [simp] : "\<And>X x y. (X->including(x::('\<AA>,'a::null)val)->includes(y)) =
       (if \<delta> X then if x \<doteq> y then true else X->includes(y) endif else invalid endif)"
 assumes StrictRefEq_refl [simp] : "\<And>(x::('\<AA>,'a::null)val). (x \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
 assumes StrictRefEq_defined_args_valid : "\<And>(x::('\<AA>,'a::null)val) y \<tau>. (\<tau> \<Turnstile> \<delta> (x \<doteq> y)) = (\<tau> \<Turnstile> \<upsilon> x \<and> \<tau> \<Turnstile> \<upsilon> y)"
 assumes including_includes: "\<And>(S :: ('\<AA>, 'a::null) Set) a x \<tau>. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> S->includes(x) \<Longrightarrow> \<tau> \<Turnstile> S->including(a)->includes(x)"
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, 'a) Set)->including(i)->including(j) \<doteq> (S->including(j)->including(i)))"
proof -

 have OclAnd_true : "\<And>a b. \<tau> \<Turnstile> a \<Longrightarrow> \<tau> \<Turnstile> b \<Longrightarrow> \<tau> \<Turnstile> a and b"
 by (simp add: foundation10 foundation6)

 have OclIf_true'' : "\<And>P B\<^sub>1 B\<^sub>2. \<tau> \<Turnstile> P \<Longrightarrow> \<tau> \<Turnstile> B\<^sub>1 \<Longrightarrow> \<tau> \<Turnstile> if P then B\<^sub>1 else B\<^sub>2 endif"
 by (metis OclIf_true' OclValid_def)

 have OclIf_false'' : "\<And>P B\<^sub>1 B\<^sub>2. \<tau> \<Turnstile> \<delta> P \<Longrightarrow> \<not> (\<tau> \<Turnstile> P) \<Longrightarrow> \<tau> \<Turnstile> B\<^sub>2 \<Longrightarrow> \<tau> \<Turnstile> if P then B\<^sub>1 else B\<^sub>2 endif"
 by (metis OclIf_def OclValid_def)

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_null_true : "\<And>\<tau>. (null \<tau> = true \<tau>) = False" by (metis OclValid_def foundation4)
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis defined3 defined_def discr_eq_false_true)
 have discr_neq_true_false : "\<And>\<tau>. (true \<tau> \<noteq> false \<tau>) = True" by (metis discr_eq_false_true)
 have discr_neq_true_bot : "\<And>\<tau>. (true \<tau> \<noteq> bot \<tau>) = True" by (metis discr_eq_bot1_true)
 have discr_neq_true_null : "\<And>\<tau>. (true \<tau> \<noteq> null \<tau>) = True" by (metis discr_eq_null_true)

 have forall_includes2 : "\<And>a b. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> b \<Longrightarrow> \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> (OclForall S (OclIncludes (S->including(a)->including(b))))"
 proof -
  have consist : "\<And>x. (\<delta> S) \<tau> = true \<tau> \<Longrightarrow> x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>"
  by(simp add: Set_inv_lemma'[simplified OclValid_def])
  show "\<And>a b. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> b \<Longrightarrow> \<tau> \<Turnstile> \<delta> S \<Longrightarrow> ?thesis a b"
   apply(simp add: OclForall_def OclValid_def discr_eq_false_true discr_eq_bot1_true discr_eq_null_true)
   apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (S->including(a)->including(b)->includes((\<lambda>_. x))) \<tau> = true \<tau>")
   apply(simp add: discr_neq_true_null discr_neq_true_bot discr_neq_true_false)
   apply(rule ballI)
   apply(rule including_includes[simplified OclValid_def], simp, rule consist, simp, simp)+
   apply(frule Set_inv_lemma'[simplified OclValid_def]) apply assumption
   apply(simp add: OclIncludes_def true_def)
  done
 qed

 show "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ?thesis"
  apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
  (* *)
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)+
  apply(subst (1 2) forall_set_including_exec, simp add: cp_OclIncludes1, simp add: cp_OclIncludes1)+
  apply(subst OclAnd_true)
  (* *)
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)+
  apply(subst OclAnd_true)
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)
  apply(case_tac "\<tau> \<Turnstile> (i \<doteq> j)")
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)
  apply(subst OclIf_false'', simp_all add: StrictRefEq_defined_args_valid)
  apply( subst OclAnd_true
       | subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)+
  apply(simp add: forall_includes2)
  (* *)
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)+
  apply(subst OclAnd_true)
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)
  apply(case_tac "\<tau> \<Turnstile> (j \<doteq> i)")
  apply(subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)
  apply(subst OclIf_false'', simp_all add: StrictRefEq_defined_args_valid)
  apply( subst OclAnd_true
       | subst OclIf_true'', simp_all add: foundation10 foundation6 del: forall_set_including_exec)+
  apply(simp add: forall_includes2)
 done
 apply_end(simp_all add: assms)
qed

lemma including_swap_0_generic :
 assumes includes_execute_generic : "\<And>X x y. (X->including(x::('\<AA>,'a::null)val)->includes(y)) =
       (if \<delta> X then if x \<doteq> y then true else X->includes(y) endif else invalid endif)"
 assumes StrictRefEq_refl : "\<And>(x::('\<AA>,'a::null)val). (x \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
 assumes StrictRefEq_defined_args_valid : "\<And>(x::('\<AA>,'a::null)val) y \<tau>. (\<tau> \<Turnstile> \<delta> (x \<doteq> y)) = (\<tau> \<Turnstile> \<upsilon> x \<and> \<tau> \<Turnstile> \<upsilon> y)"
 assumes including_includes: "\<And>(S :: ('\<AA>, 'a::null) Set) a x \<tau>. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> S->includes(x) \<Longrightarrow> \<tau> \<Turnstile> S->including(a)->includes(x)"
 shows "(S :: ('\<AA>, 'a) Set)->including(i)->including(j) = (S->including(j)->including(i))"
proof -
 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)
 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> S)", simp add: OclIncluding_def OclValid_def)
  apply(drule defined_inject_true)
  apply(subst (2 4 6 8 10) cp_defined)
  apply(simp add: false_def true_def)
  apply(rule conjI, rule impI)+
  apply (metis foundation16 foundation18' foundation23 null_option_def)
  apply (metis (lifting) OCL_core.bot_fun_def defined_def true_def valid_def)
  apply (metis (lifting) OCL_core.bot_fun_def defined_def true_def valid_def)
  (* *)
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> i)", simp add: OclIncluding_def OclValid_def)
  apply(drule valid_inject_true)
  apply(subst (2) cp_defined)
  apply(simp add: false_def true_def)
  apply (metis (lifting) OCL_core.bot_fun_def OclValid_def defined_def foundation2 true_def)
  (* *)
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> j)", simp add: OclIncluding_def OclValid_def)
  apply(drule valid_inject_true)
  apply(subst (2) cp_defined)
  apply(simp add: false_def true_def)
  apply (metis (lifting) OCL_core.bot_fun_def OclValid_def defined_def foundation2 true_def)
  (* *)
  proof - fix \<tau> show "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> S->including(i)->including(j) \<tau> = S->including(j)->including(i) \<tau>"
   apply(insert including_swap__generic[OF includes_execute_generic StrictRefEq_refl StrictRefEq_defined_args_valid including_includes, of \<tau> S i j],
         simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def)
   apply(simp add: OclValid_def split: split_if_asm)
   apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) \<tau> = true \<tau> \<and> (\<delta> S and \<upsilon> j and \<upsilon> i) \<tau> = true \<tau>")
    prefer 2
    apply (metis OclValid_def foundation3)
  by(simp add: true_def)
  apply_end(simp+)
 qed
qed

lemma including_swap'_generic :
 assumes including_swap_0 : "\<And>(S:: ('\<AA>, 'a::null) Set) i j. S->including(i)->including(j) = S->including(j)->including(i)"
 shows "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, 'a::null) Set)->including(i)->including(j) \<tau> = (S->including(j)->including(i)) \<tau>)"
by(simp add: including_swap_0)

lemma including_swap_generic :
 assumes including_swap_0 : "\<And>(S:: ('\<AA>, 'a::null) Set) i j. S->including(i)->including(j) = S->including(j)->including(i)"
 shows "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, 'a::null) Set)->including(i)->including(j) = (S->including(j)->including(i)))"
by(simp add: including_swap_0)

subsection{* Congruence *}

lemma including_subst_set : "(s::('\<AA>,'a::null)Set) = t \<Longrightarrow> s->including(x) = (t->including(x))"
by(simp)

lemma including_subst_set' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including(x) \<doteq> (t->including(x)))"
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

lemma including_subst_set'' : "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> (s::('\<AA>,'a::null)Set) \<tau> = t \<tau> \<Longrightarrow> s->including(x) \<tau> = (t->including(x)) \<tau>"
 apply(frule including_subst_set'[where s = s and t = t and x = x], simp_all del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
 apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def del: StrictRefEq\<^sub>S\<^sub>e\<^sub>t_exec)
 apply (metis (hide_lams, no_types) OclValid_def foundation20 foundation22)
by (metis cp_OclIncluding)


subsection{* all defined (construction) *}

lemma cons_all_def :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
  assumes x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "all_defined \<tau> S->including(x)"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]
                       x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
  qed

 have G1 : "\<And>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert C, simp)
          apply(simp add:  S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>] x_val[of \<tau>] A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
  done
 qed

 have G2 : "\<And>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert C, simp)
          apply(simp add:  S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>] x_val[of \<tau>] A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
  done
 qed

 have G : "\<And>\<tau>. (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def G1 G2)
  done
 qed

 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

  show ?thesis
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def OclIncluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux]
                S_all_def[simplified all_defined_def, of \<tau>]
                x_val[of \<tau>], simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>"])
   apply(simp add: all_defined_set'_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

lemma cons_all_def' :
  assumes S_all_def : "all_defined \<tau> S"
  assumes x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "all_defined \<tau> (S->including(x))"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1]
                       x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

 have G1 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          apply(insert C, simp)
          apply(simp add:  S_all_def[simplified all_defined_def, THEN conjunct1] x_val A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
  done

 have G2 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          apply(insert C, simp)
          apply(simp add:  S_all_def[simplified all_defined_def, THEN conjunct1] x_val A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
  done

 have G : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def G1 G2)
  done

 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
  show ?thesis
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def OclIncluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux]
                S_all_def[simplified all_defined_def]
                x_val, simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau> then Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<union> {x \<tau>}\<rfloor>\<rfloor> else \<bottom>"])
   apply(simp add: all_defined_set'_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

subsection{* all defined (inversion) *}

lemma invert_all_defined : "all_defined \<tau> (S->including(x)) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> S"
 proof -
 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

 have finite_including_rep_set : "\<And>\<tau> X x. \<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_including_rep_set)
  apply(metis OclValid_def foundation5)+
 done

  show "all_defined \<tau> (S->including(x)) \<Longrightarrow> ?thesis"
   apply(simp add: all_defined_def all_defined_set'_def)
   apply(erule conjE, frule finite_including_rep_set[of \<tau> S x], simp)
  by (metis foundation5)
qed

lemma invert_all_defined' : "(\<forall>\<tau>. all_defined \<tau> (S->including(\<lambda>(_:: '\<AA> st). x))) \<Longrightarrow> is_int (\<lambda> (_:: '\<AA> st). x) \<and> (\<forall>\<tau>. all_defined \<tau> S)"
   apply(rule conjI)
   apply(simp only: is_int_def, rule allI)
   apply(erule_tac x = \<tau> in allE, simp)
   apply(drule invert_all_defined, simp)
   apply(rule allI)
   apply(erule_tac x = \<tau> in allE)
   apply(drule invert_all_defined, simp)
done

subsection{* Preservation of cp *}

lemma including_cp_gen : "cp f \<Longrightarrow> cp (\<lambda>r2. ((f r2)->including(x)))"
 apply(unfold cp_def)
 apply(subst cp_OclIncluding[of _ x])
 apply(drule exE) prefer 2 apply assumption
 apply(rule_tac x = "\<lambda> X_\<tau> \<tau>. ((\<lambda>_. fa X_\<tau> \<tau>)->including(\<lambda>_. x \<tau>)) \<tau>" in exI, simp)
done

lemma including_cp : "cp (\<lambda>r2. (r2->including(x)))"
 apply(unfold cp_def)
 apply(subst cp_OclIncluding[of _ x])
 apply(rule_tac x = "\<lambda> X_\<tau> \<tau>. ((\<lambda>_. X_\<tau>)->including(\<lambda>_. x \<tau>)) \<tau>" in exI, simp)
done

lemma including_cp' : "cp (OclIncluding S)"
 apply(unfold cp_def)
 apply(subst cp_OclIncluding)
 apply(rule_tac x = "\<lambda> X_\<tau> \<tau>. ((\<lambda>_. S \<tau>)->including(\<lambda>_. X_\<tau>)) \<tau>" in exI, simp)
done

lemma including_cp''' : "cp (OclIncluding S->including(i)->including(j))"
 apply(unfold cp_def)
 apply(subst cp_OclIncluding)
 apply(rule_tac x = "\<lambda> X_\<tau> \<tau>. ((\<lambda>_. S->including(i)->including(j) \<tau>)->including(\<lambda>_. X_\<tau>)) \<tau>" in exI, simp)
done

lemma including_cp2 : "cp (\<lambda>r2. (r2->including(x))->including(y))"
by(rule including_cp_gen, simp add: including_cp)

lemma including_cp3 : "cp (\<lambda>r2. ((r2->including(x))->including(y))->including(z))"
by(rule including_cp_gen, simp add: including_cp2)

subsection{* Preservation of global judgment *}

lemma including_cp_all :
 assumes x_int : "is_int x"
     and S_def : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> S"
     and S_incl : "S \<tau>1 = S \<tau>2"
   shows  "S->including(x) \<tau>1 = S->including(x) \<tau>2"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(unfold OclIncluding_def)
  apply(simp add:  S_def[simplified OclValid_def] int_is_valid[OF x_int, simplified OclValid_def] S_incl)
  apply(subgoal_tac "x \<tau>1 = x \<tau>2", simp)
  apply(insert x_int[simplified is_int_def, THEN spec, of \<tau>1, THEN conjunct2, THEN spec], simp)
 done
qed

subsection{* Preservation of non-emptiness *}

lemma including_notempty :
  assumes S_def : "\<tau> \<Turnstile> \<delta> S"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
      and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
    shows "\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show ?thesis
  apply(unfold OclIncluding_def)
  apply(simp add: S_def[simplified OclValid_def] x_val[simplified OclValid_def] Abs_Set_0_inverse[OF insert_in_Set_0[OF S_def x_val]])
 done
qed

lemma including_notempty' :
  assumes x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "\<lceil>\<lceil>Rep_Set_0 (Set{x} \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have insert_in_Set_0 : "\<And>S \<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show ?thesis
  apply(unfold OclIncluding_def)
  apply(simp add: x_val[simplified OclValid_def])
  apply(subst Abs_Set_0_inverse)
  apply(rule insert_in_Set_0)
  apply(simp add: mtSet_all_def)
  apply(simp_all add: x_val)
 done
qed

end