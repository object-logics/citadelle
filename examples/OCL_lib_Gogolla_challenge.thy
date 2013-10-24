(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib_Gogolla_challenge.thy --- Example using the OCL library.
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

header{* Gogolla's challenge *}

theory
  OCL_lib_Gogolla_challenge
imports
  "../src/OCL_lib"
begin

section{* Gogolla's Challenge on Sets *}
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
1) @{term OclIterate\<^isub>S\<^isub>e\<^isub>t}, and
2) @{term OclIncluding}.

As there is no removing, we conjecture that the final result should be equal to the set
containing all ground numbers appearing in the expression: that is @{term \<six>}, @{term \<eight>}, @{term \<nine>}, @{term \<zero>}. *} 
(* text{*(modulo ordering and duplication for sequences)*} *)

text{* The following part sets up the necessary requirement towards an automatic execution.
The goal is to normalize a general term composed of a set of numbers applied to an arbitrary nesting of 
@{term OclIterate\<^isub>S\<^isub>e\<^isub>t} and @{term OclIncluding}. 
One solution is to rawly compute the initial term by following a call by value strategy or by need. 
However for efficiency reasons, we present in the next subsections some algebraic properties on sets
that would shortcut the number of reduction steps, by reaching optimaly a normal form. *}

subsection{* Introduction *}

text{* Besides the @{term invalid} exception element, the other important concept that
characterizes OCL sets in our formalization is the finiteness property.
Since the iteration could only be performed on finite sets, the definition of @{term OclIterate\<^isub>S\<^isub>e\<^isub>t}
contains as prerequisite a check that the given argument is finite. If it is the case, 
@{term Finite_Set.fold} is then called internally to execute the iteration. *}

text{* Recall that our goal is to provide a generic solution to the Gogolla's challenge, 
in the sense that we focus on an arbitrary list of nested @{term OclIterate\<^isub>S\<^isub>e\<^isub>t} combinators. 
A naive approach for simplifying such huge expression would be to repeatedly rewrite with
@{term OclIterate\<^isub>S\<^isub>e\<^isub>t_including}. 
However, @{term OclIterate\<^isub>S\<^isub>e\<^isub>t_including} contains @{term "comp_fun_commute F"} as hypothesis 
and this one is generally difficult to prove. Indeed, the easiest case would be when simplifying 
the outermost @{term OclIterate\<^isub>S\<^isub>e\<^isub>t} since the overall expression is ground. But for the others inner nested 
@{term OclIterate\<^isub>S\<^isub>e\<^isub>t}, the @{term "F"} function could have as free variable a set
where its validity, definedness and finiteness are unknown --
and the finiteness is precisely required for all sets occuring
in a chain of @{term OclIterate\<^isub>S\<^isub>e\<^isub>t} nested term. *}

text{* Thus we propose to write an Isabelle locale similar as the locale @{term "comp_fun_commute"}
but containing the additional properties that sets should fulfill
while traveling through the nested @{term OclIterate\<^isub>S\<^isub>e\<^isub>t}.
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

lemma StrictRefEq\<^isub>S\<^isub>e\<^isub>t_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq\<^isub>S\<^isub>e\<^isub>t OclValid_def)
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

subsection{* mtSet *}

lemma mtSet_all_def : "all_defined \<tau> Set{}"
proof -
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 show ?thesis
  apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set_0_inverse B)
 by (metis (no_types) foundation16 mtSet_def mtSet_defined transform1)
qed

lemma cp_mtSet : "\<And>x. Set{} = (\<lambda>_. Set{} x)"
by (metis (hide_lams, no_types) mtSet_def)

subsection{* OclIncluding *}

subsubsection{* Identity *}

lemma including_id' : "all_defined \<tau> (S:: ('\<AA>, 'a option option) Set) \<Longrightarrow>
                       x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                       S->including(\<lambda>\<tau>. x) \<tau> = S \<tau>"
proof -
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "               all_defined \<tau> S \<Longrightarrow>
                      x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      ?thesis"
  apply(simp add: OclIncluding_def all_defined1[simplified OclValid_def] OclValid_def insert_absorb abs_rep_simp del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
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

subsubsection{* Commutativity *}

lemma including_swap_ :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, int option option) Set)->including(i)->including(j) \<doteq> (S->including(j)->including(i)))"
proof -

 have OclAnd_true : "\<And>a b. \<tau> \<Turnstile> a \<Longrightarrow> \<tau> \<Turnstile> b \<Longrightarrow> \<tau> \<Turnstile> a and b"
 by (simp add: foundation10 foundation6)

 have discr_eq_false_true :  "(false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_false_bot : "\<And>\<tau>. (false \<tau> = bot \<tau>) = False" by (metis OCL_core.bot_fun_def bot_option_def false_def option.simps(2))
 have discr_eq_false_null : "\<And>\<tau>. (false \<tau> = null \<tau>) = False" by (metis defined4 foundation1 foundation17 null_fun_def)
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)
 have discr_eq_null_false : "\<And>\<tau>. (null \<tau> = false \<tau>) = False" by (metis defined4 foundation1 foundation16 null_fun_def)
 have discr_eq_null_true : "\<And>\<tau>. (null \<tau> = true \<tau>) = False" by (metis OclValid_def foundation4)
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis defined3 defined_def discr_eq_false_true)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False" by (metis bot_fun_def discr_eq_bot1_true)
 have discr_eq_bot1_false : "\<And>\<tau>. (\<bottom> \<tau> = false \<tau>) = False" by (metis OCL_core.bot_fun_def defined4 foundation1 foundation16)
 have discr_eq_bot2_false : "\<And>\<tau>. (\<bottom> = false \<tau>) = False" by (metis foundation1 foundation18' valid4)
 have discr_neq_false_true : "\<And>\<tau>. (false \<tau> \<noteq> true \<tau>) = True" by (metis discr_eq_false_true)
 have discr_neq_true_false : "\<And>\<tau>. (true \<tau> \<noteq> false \<tau>) = True" by (metis discr_eq_false_true)
 have discr_neq_true_bot : "\<And>\<tau>. (true \<tau> \<noteq> bot \<tau>) = True" by (metis OCL_core.bot_fun_def discr_eq_bot2_true)
 have discr_neq_true_null : "\<And>\<tau>. (true \<tau> \<noteq> null \<tau>) = True" by (metis discr_eq_null_true)
 have discr_neq_invalid_true : "\<And>\<tau>. (invalid \<tau> \<noteq> true \<tau>) = True" by (metis discr_eq_bot2_true invalid_def)
 have discr_neq_invalid_bot : "\<And>\<tau>. (invalid \<tau> \<noteq> \<bottom> \<tau>) = False" by (metis bot_fun_def invalid_def)

 have bot_in_set_0 : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have forall_includes_id : "\<And>a b. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> (OclForall S (OclIncludes S))"
 by(simp add: forall_includes)

 have forall_includes2 : "\<And>a b. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> b \<Longrightarrow> \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> (OclForall S (OclIncludes (S->including(a)->including(b))))"
 proof -
  have consist : "\<And>x. (\<delta> S) \<tau> = true \<tau> \<Longrightarrow> x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>"
  by(simp add: Set_inv_lemma'[simplified OclValid_def])
  show "\<And>a b. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> b \<Longrightarrow> \<tau> \<Turnstile> \<delta> S \<Longrightarrow> ?thesis a b"
   apply(simp add: OclForall_def OclValid_def discr_eq_false_true discr_eq_bot1_true discr_eq_null_true)
   apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (S->including(a)->including(b)->includes((\<lambda>_. x))) \<tau> = true \<tau>")
   apply(simp add: discr_neq_true_null discr_neq_true_bot discr_neq_true_false)
   apply(rule ballI)
   apply(rule including_includes[simplified OclValid_def], simp, rule consist, simp_all)+
   apply(frule Set_inv_lemma'[simplified OclValid_def]) apply assumption
   apply(simp add: OclIncludes_def true_def)
  done
 qed

 show "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ?thesis"
  apply(simp add:
   cp_OclIf[of "\<delta> S and \<upsilon> i and \<upsilon> j"]
   cp_OclIf[of "\<delta> S and \<upsilon> j and \<upsilon> i"]
   cp_OclNot[of "\<delta> S and \<upsilon> j and \<upsilon> i"])
  apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) = (\<delta> S and \<upsilon> j and \<upsilon> i)")
   prefer 2
   apply (metis OclAnd_assoc OclAnd_commute)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S and \<upsilon> i and \<upsilon> j")
   prefer 2
   apply (metis foundation10 foundation6)
  apply(simp add: OclValid_def)
  apply(rule OclAnd_true[simplified OclValid_def])
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = j])
  apply(simp)
  apply(simp add:
   cp_OclIf[of "\<delta> S and \<upsilon> i and \<upsilon> j"]
   cp_OclIf[of "\<delta> S and \<upsilon> j and \<upsilon> i"]
   cp_OclNot[of "\<delta> S and \<upsilon> j and \<upsilon> i"])
  apply(simp add: cp_OclIf[symmetric])
  apply(rule OclAnd_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_OclIf[of "\<delta> S and \<upsilon> j"] cp_OclIf[of "i \<doteq> j"] cp_OclIf[of "\<delta> S"] cp_OclIf[of "if \<upsilon> j then true else invalid endif"] cp_OclIf[of "\<upsilon> j"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> j)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_OclIf[symmetric])
  apply(simp add: OclIf_def discr_eq_invalid_true)
  apply (metis OclValid_def StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_defined_args_valid)
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = i])
  apply(simp add:
   cp_OclIf[of "\<delta> S and \<upsilon> i"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> i)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_OclIf[symmetric])
  apply(rule OclAnd_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_OclIf[of "\<delta> S and \<upsilon> j"] cp_OclIf[of "i \<doteq> j"] cp_OclIf[of "\<delta> S"] cp_OclIf[of "if \<upsilon> i then true else invalid endif"] cp_OclIf[of "\<upsilon> i"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> j)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_OclIf[symmetric])
  (* *)
  apply(rule forall_includes2[simplified OclValid_def]) apply(simp) apply(simp) apply(simp)
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = i])
  apply(simp)
  apply(simp add:
   cp_OclIf[of "\<delta> S and \<upsilon> i and \<upsilon> j"]
   cp_OclIf[of "\<delta> S and \<upsilon> j and \<upsilon> i"])
  apply(simp add: cp_OclIf[symmetric])
  apply(rule OclAnd_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_OclIf[of "\<delta> S and \<upsilon> i"] cp_OclIf[of "j \<doteq> i"] cp_OclIf[of "\<delta> S"] cp_OclIf[of "if \<upsilon> i then true else invalid endif"] cp_OclIf[of "\<upsilon> i"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> i)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_OclIf[symmetric])
  apply(simp add: OclIf_def discr_eq_invalid_true)
  apply (metis OclValid_def StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_defined_args_valid)
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = j])
  apply(simp add:
   cp_OclIf[of "\<delta> S and \<upsilon> j"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> j)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_OclIf[symmetric])
  apply(rule OclAnd_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_OclIf[of "\<delta> S and \<upsilon> i"] cp_OclIf[of "j \<doteq> i"] cp_OclIf[of "\<delta> S"] cp_OclIf[of "if \<upsilon> j then true else invalid endif"] cp_OclIf[of "\<upsilon> j"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> i)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_OclIf[symmetric])
  (* *)
  apply(rule forall_includes2[simplified OclValid_def]) apply(simp) apply(simp) apply(simp)
 done
 apply_end(simp_all add: assms)
qed

lemma including_swap' : "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, int option option) Set)->including(i)->including(j) \<tau> = (S->including(j)->including(i)) \<tau>)"
 apply(frule including_swap_[where i = i and j = j], simp_all del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 apply(simp add: StrictRefEq\<^isub>S\<^isub>e\<^isub>t OclValid_def del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) \<tau> = true \<tau> \<and> (\<delta> S and \<upsilon> j and \<upsilon> i) \<tau> = true \<tau>")
  prefer 2
  apply(metis OclValid_def foundation3)
 apply(simp add: StrongEq_def true_def)
done

lemma including_swap : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, int option option) Set)->including(i)->including(j) = (S->including(j)->including(i)))"
 apply(rule ext, rename_tac \<tau>)
 apply(erule_tac x = \<tau> in allE)+
 apply(frule including_swap_[where i = i and j = j], simp_all del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 apply(simp add: StrictRefEq\<^isub>S\<^isub>e\<^isub>t OclValid_def del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) \<tau> = true \<tau> \<and> (\<delta> S and \<upsilon> j and \<upsilon> i) \<tau> = true \<tau>")
  prefer 2
  apply(metis OclValid_def foundation3)
 apply(simp add: StrongEq_def true_def)
done

subsubsection{* Congruence *}

lemma including_subst_set : "(s::('\<AA>,'a::null)Set) = t \<Longrightarrow> s->including(x) = (t->including(x))"
by(simp)

lemma including_subst_set' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including(x) \<doteq> (t->including(x)))"
proof -
 have cp: "cp (\<lambda>s. (s->including(x)))"
  apply(simp add: cp_def, subst cp_OclIncluding)
 by (rule_tac x = "(\<lambda>xab ab. ((\<lambda>_. xab)->including(\<lambda>_. x ab)) ab)" in exI, simp)

 show "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> ?thesis"
  apply(rule_tac P = "\<lambda>s. (s->including(x))" in StrictRefEq\<^isub>S\<^isub>e\<^isub>t_L_subst1)
  apply(rule cp)
  apply(simp add: foundation20) apply(simp add: foundation20)
  apply (simp add: foundation10 foundation6)+
 done
qed

lemma including_subst_set'' : "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> (s::('\<AA>,'a::null)Set) \<tau> = t \<tau> \<Longrightarrow> s->including(x) \<tau> = (t->including(x)) \<tau>"
 apply(frule including_subst_set'[where s = s and t = t and x = x], simp_all del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 apply(simp add: StrictRefEq\<^isub>S\<^isub>e\<^isub>t OclValid_def del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 apply (metis (hide_lams, no_types) OclValid_def foundation20 foundation22)
by (metis cp_OclIncluding)


subsubsection{* all defined (construction) *}

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

subsubsection{* all defined (inversion) *}

lemma invert_all_defined : "all_defined \<tau> (S->including(x)) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> S"
 proof -
 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

 have finite_including_exec : "\<And>\<tau> X x. \<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_including_exec)
  apply(metis OclValid_def foundation5)+
 done

  show "all_defined \<tau> (S->including(x)) \<Longrightarrow> ?thesis"
   apply(simp add: all_defined_def all_defined_set'_def)
   apply(erule conjE, frule finite_including_exec[of \<tau> S x], simp)
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

subsubsection{* Preservation of cp *}

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

subsubsection{* Preservation of global judgment *}

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

subsubsection{* Preservation of non-emptiness *}

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

subsection{* Constant set *}

lemma cp_singleton :
assumes x_int : "is_int (\<lambda>(_:: '\<AA> st). x)"
 shows "(\<lambda>_. Set{\<lambda>(_:: '\<AA> st). x} \<tau>) = Set{\<lambda>(_:: '\<AA> st). x}"
apply(rule ext, rename_tac \<tau>')
apply(rule including_cp_all, simp add: x_int, simp)
apply(subst (1 2) cp_mtSet, simp)
done

lemma cp_doubleton :
 assumes x_int : "is_int (\<lambda>(_:: '\<AA> st). x)"
     and a_int : "is_int a"
   shows "(\<lambda>_. Set{\<lambda>(_:: '\<AA> st). x, a} \<tau>) = Set{\<lambda>(_:: '\<AA> st). x, a}"
 apply(rule ext, rename_tac \<tau>')
 apply(rule including_cp_all, simp add: x_int, simp add: a_int int_is_valid)
 apply(rule including_cp_all, simp add: a_int, simp)
 apply(subst (1 2) cp_mtSet, simp)
done

lemma flatten_int' :
  assumes a_all_def : "\<And>\<tau>. all_defined \<tau> Set{\<lambda>(\<tau>:: '\<AA> st). (a :: 'a option option)}"
      and a_int : "is_int (\<lambda>(\<tau>:: '\<AA> st). a)"
    shows "let a = \<lambda>(\<tau>:: '\<AA> st). (a :: _) in Set{a,a} = Set{a}"
proof -
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 have B' : "\<lfloor>\<lfloor>{a}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(simp) apply(rule disjI2)+ apply(insert int_is_valid[OF a_int]) by (metis foundation18')
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
 by (metis B Abs_Set_0_cases Abs_Set_0_inverse cp_defined defined_def false_def mtSet_def mtSet_defined null_fun_def null_option_def null_set_OclNot_defined true_def)

 show ?thesis
  apply(simp add: Let_def)
  apply(rule including_id, simp add: a_all_def)
  apply(rule allI, simp add: OclIncluding_def int_is_valid[OF a_int, simplified OclValid_def] mtSet_def Abs_Set_0_inverse[OF B] C Abs_Set_0_inverse[OF B'])
 done
qed

lemma flatten_int :
  assumes a_int : "is_int (a :: ('\<AA>, 'a option option) val)"
  shows "Set{a,a} = Set{a}"
proof -
 have all_def : "\<And>\<tau>. all_defined \<tau> Set{a}"
  apply(rule cons_all_def)
  apply(simp add: mtSet_all_def int_is_valid[OF a_int])+
 done

 show ?thesis
  apply(insert a_int, drule destruct_int)
  apply(drule ex1E) prefer 2 apply assumption
  apply(simp)
  apply(rule flatten_int'[simplified Let_def])
  apply(insert all_def, simp)
  apply(insert a_int, simp)
 done
qed

subsection{* OclExcluding *}
subsubsection{* Identity *}

lemma excluding_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and x_int : "is_int (\<lambda>(\<tau>:: '\<AA> st). x)"
   shows "            \<forall>\<tau>. x \<notin> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->excluding(\<lambda>\<tau>. x) = S"
proof -

 have S_incl : "\<forall>(x :: ('\<AA>, 'a option option) Set). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
  apply(rule allI) apply(rule impI)+
  apply(rule ext, rename_tac \<tau>)
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(simp add: mtSet_def)
 by (metis abs_rep_simp)

 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "               (\<forall>\<tau>. x \<notin> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
                      ?thesis"
  apply(rule ext, rename_tac \<tau>', simp add: OclExcluding_def S_all_def[simplified all_defined_def OclValid_def] int_is_valid[OF x_int, simplified OclValid_def])

  proof - fix \<tau>' show "\<forall>a b. x \<notin> \<lceil>\<lceil>Rep_Set_0 (S (a, b))\<rceil>\<rceil> \<Longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>')\<rceil>\<rceil> - {x}\<rfloor>\<rfloor> = S \<tau>'"

  apply(subst finite_induct[where P = "\<lambda>set. x \<notin> set \<longrightarrow> (\<forall>set'. all_defined \<tau>' set' \<longrightarrow> set = \<lceil>\<lceil>Rep_Set_0 (set' \<tau>')\<rceil>\<rceil> \<longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>set - {x}\<rfloor>\<rfloor> = set' \<tau>')", THEN mp, THEN spec, THEN mp])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])
  apply(simp)
  apply(rule allI, rename_tac S') apply(rule impI)+
  apply(drule_tac f = "\<lambda>x. Abs_Set_0 \<lfloor>\<lfloor>x\<rfloor>\<rfloor>" in arg_cong)
  apply(simp)

  apply(subst abs_rep_simp, simp)
  apply(simp)
  apply(rename_tac x' F)
  apply(rule impI, rule allI, rename_tac S') apply(rule impI)+
  proof - fix x' F S' show "\<forall>a b. x \<notin> \<lceil>\<lceil>Rep_Set_0 (S (a, b))\<rceil>\<rceil> \<Longrightarrow>
                finite F \<Longrightarrow>
                x' \<notin> F \<Longrightarrow>
                x \<notin> F \<longrightarrow> (\<forall>xa. all_defined \<tau>' xa \<longrightarrow> F = \<lceil>\<lceil>Rep_Set_0 (xa \<tau>')\<rceil>\<rceil> \<longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>F - {x}\<rfloor>\<rfloor> = xa \<tau>') \<Longrightarrow>
                x \<notin> insert x' F \<Longrightarrow> all_defined \<tau>' S' \<Longrightarrow> insert x' F = \<lceil>\<lceil>Rep_Set_0 (S' \<tau>')\<rceil>\<rceil> \<Longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>insert x' F - {x}\<rfloor>\<rfloor> = S' \<tau>'"
   apply(subgoal_tac "x \<notin> F", simp)
   apply(rule abs_rep_simp, simp)
  by (metis insertCI)
  apply_end(simp)+
  apply_end(metis surj_pair)
  prefer 3
  apply_end(rule refl)
  apply_end(simp add: S_all_def, simp)
  qed
 qed
qed

subsubsection{* all defined (construction) *}

lemma cons_all_def_e :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
  assumes x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "all_defined \<tau> S->excluding(x)"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]
                       x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
  qed

 have G1 : "\<And>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert C[of \<tau>], simp)
          apply(simp add: Abs_Set_0_inject bot_option_def)
  done
 qed

 have G2 : "\<And>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert C[of \<tau>], simp)
          apply(simp add: Abs_Set_0_inject bot_option_def null_option_def)
  done
 qed

 have G : "\<And>\<tau>. (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def G1 G2)
  done
 qed

 have invert_all_defined_aux : "(\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done

  show ?thesis
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def OclExcluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux]
                S_all_def[simplified all_defined_def, of \<tau>]
                x_val[of \<tau>], simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor>"])
   apply(simp add: all_defined_set'_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

subsubsection{* Execution *}

lemma excluding_unfold :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
      and x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "\<lceil>\<lceil>Rep_Set_0 (S->excluding(x) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]
                       x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
  qed
 show ?thesis
  apply(simp add: OclExcluding_def all_defined1[OF S_all_def, simplified OclValid_def] x_val[simplified OclValid_def] Abs_Set_0_inverse[OF C])
 done
qed

subsection{* OclIncluding and OclExcluding *}
subsubsection{* Identity *}

lemma Ocl_insert_Diff :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, 'a option option) Set)"
     and x_mem : "\<And>\<tau>. x \<in> (\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
     and x_int : "is_int x"
   shows "S->excluding(x)->including(x) = S"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: foundation18 invalid_def)
 done
 have remove_in_Set_0 : "\<And>\<tau>. ?this \<tau>"
  apply(rule remove_in_Set_0)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF x_int])+
 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 show ?thesis

  apply(rule ext, rename_tac \<tau>)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> (S->excluding(x))")
   prefer 2
   apply(simp add: foundation10 all_defined1[OF S_all_def] int_is_valid[OF x_int])
  apply(simp add: OclExcluding_def OclIncluding_def all_defined1[OF S_all_def, simplified OclValid_def] Abs_Set_0_inverse[OF remove_in_Set_0] int_is_valid[OF x_int, simplified OclValid_def] OclValid_def)
  proof - fix \<tau> show " Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
  apply(rule ex1E[OF destruct_int[OF x_int]], rename_tac x', simp)
  apply(subgoal_tac "x' \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>")
  apply(drule insert_Diff[symmetric], simp)
  apply(simp add: abs_rep_simp[OF S_all_def[where \<tau> = \<tau>]])
  apply(insert x_mem[of \<tau>], simp)
  apply(rule inj_image_mem_iff[THEN iffD1]) prefer 2 apply assumption
  apply(simp add: inject)
  done
 qed
qed

subsection{* OclIterate *}

subsubsection{* all defined (inversion) *}

lemma i_invert_all_defined_not :
 assumes A_all_def : "\<exists>\<tau>. \<not> all_defined \<tau> S"
   shows "\<exists>\<tau>. \<not> all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 show ?thesis
  apply(insert A_all_def)
  apply(drule exE) prefer 2 apply assumption
  apply(rule_tac x = \<tau> in exI)
  proof - fix \<tau> show "\<not> all_defined \<tau> S \<Longrightarrow> \<not> all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
   apply(case_tac "\<tau> \<Turnstile> (\<delta> S) \<and> \<tau> \<Turnstile> (\<upsilon> S) \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp add: OclValid_def all_defined_def)
   apply(simp add: all_defined_set'_def)
   apply(simp add: all_defined_def all_defined_set'_def defined_def OclValid_def false_def true_def bot_fun_def)
  done
 qed
qed

lemma i_invert_all_defined :
 assumes A_all_def : "\<And>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   shows "all_defined \<tau> S"
by (metis A_all_def i_invert_all_defined_not)

lemma i_invert_all_defined' :
 assumes A_all_def : "\<forall>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   shows "\<forall>\<tau>. all_defined \<tau> S"
by (metis A_all_def i_invert_all_defined)

subsection{* comp fun commute *}
subsubsection{* Main *}

text{* TODO add some comment on comparison with inductively constructed OCL term *}
(*
inductive EQ1_fold_graph :: "(('\<AA>, _) val
   \<Rightarrow> ('\<AA>, _) Set
     \<Rightarrow> ('\<AA>, _) Set) \<Rightarrow> ('\<AA>, _) Set \<Rightarrow> ('\<AA>, _) Set \<Rightarrow> ('\<AA>, _) Set \<Rightarrow> bool"
 for f and z where
  EQ1_emptyI [intro]: "EQ1_fold_graph f z Set{} z" |
  EQ1_insertI [intro]: "\<not> (\<tau> \<Turnstile> A->includes(x)) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow> all_defined \<tau> A \<Longrightarrow> EQ1_fold_graph f z A y
      \<Longrightarrow> EQ1_fold_graph f z (A->including(x)) (f x y)"

inductive_cases EQ1_empty_fold_graphE [elim!]: "EQ1_fold_graph f z Set{} x"
*)

(*
inductive EQ_fold_graph :: "(('\<AA>, _) val
                              \<Rightarrow> ('\<AA>, _) Set
                              \<Rightarrow> ('\<AA>, _) Set)
                            \<Rightarrow> ('\<AA>, _) Set
                            \<Rightarrow> ('\<AA>, _) val set
                            \<Rightarrow> ('\<AA>, _) Set
                            \<Rightarrow> bool"
 for f and z  where
  EQ_emptyI [intro]: "EQ_fold_graph f z {} z" |
  EQ_insertI [intro]: "(\<lambda>_. x) \<notin> A \<Longrightarrow> \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow> EQ_fold_graph f z A y
      \<Longrightarrow> EQ_fold_graph f z (insert (\<lambda>_. x) A) (f (\<lambda>_. x) y)"

thm EQ_fold_graph_def
thm EQ_insertI
*)
(*
inductive_cases EQ_empty_fold_graphE [elim!]: "EQ_fold_graph f z {} x"
*)

locale EQ_comp_fun_commute0_gen0_bis'' =
  fixes f000 :: "'b \<Rightarrow> 'c"
  fixes is_i :: "'\<AA> st \<Rightarrow> 'c \<Rightarrow> bool"
  fixes is_i' :: "'\<AA> st \<Rightarrow> 'c \<Rightarrow> bool"
  fixes all_i_set :: "'c set \<Rightarrow> bool"

  fixes f :: "'c
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes i_set : "\<And>x A. all_i_set (insert x A) \<Longrightarrow> ((\<forall>\<tau>. is_i \<tau> x) \<and> all_i_set A)"
  assumes i_set' : "\<And>x A. ((\<forall>\<tau>. is_i \<tau> (f000 x)) \<and> all_i_set A) \<Longrightarrow> all_i_set (insert (f000 x) A)"
  assumes i_set'' : "\<And>x A. ((\<forall>\<tau>. is_i \<tau> (f000 x)) \<and> all_i_set A) \<Longrightarrow> all_i_set (A - {f000 x})"
  assumes i_set_finite : "all_i_set A \<Longrightarrow> finite A"
  assumes i_val : "\<And>x \<tau>. is_i \<tau> x \<Longrightarrow> is_i' \<tau> x"
  assumes f000_inj : "\<And>x y. x \<noteq> y \<Longrightarrow> f000 x \<noteq> f000 y"

  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (f000 x) S \<tau> = f (f000 x) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f (f000 x) y)) = ((\<forall>\<tau>. is_i' \<tau> (f000 x)) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             (\<And>\<tau>. is_i' \<tau> (f000 x)) \<Longrightarrow>
                             (\<And>\<tau>. is_i' \<tau> (f000 y)) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (f000 y) (f (f000 x) S) = f (f000 x) (f (f000 y) S)"

 inductive EQG_fold_graph :: "('b \<Rightarrow> 'c)
                            \<Rightarrow> ('c
                              \<Rightarrow> ('\<AA>, 'a) Set
                              \<Rightarrow> ('\<AA>, 'a) Set)
                            \<Rightarrow> ('\<AA>, 'a) Set
                            \<Rightarrow> 'c set
                            \<Rightarrow> ('\<AA>, 'a) Set
                            \<Rightarrow> bool"
  for is_i and F and z where
  EQG_emptyI [intro]: "EQG_fold_graph is_i F z {} z" |
  EQG_insertI [intro]: "is_i x \<notin> A \<Longrightarrow>
                       EQG_fold_graph is_i F z A y \<Longrightarrow>
                       EQG_fold_graph is_i F z (insert (is_i x) A) (F (is_i x) y)"

 inductive_cases EQG_empty_fold_graphE [elim!]: "EQG_fold_graph is_i f z {} x"
 definition "foldG is_i f z A = (THE y. EQG_fold_graph is_i f z A y)"

lemma eqg_fold_of_fold :
 assumes fold_g : "fold_graph F z (f000 ` A) y"
   shows "EQG_fold_graph f000 F z (f000 ` A) y"
  apply(insert fold_g)
  apply(subgoal_tac "\<And>A'. fold_graph F z A' y \<Longrightarrow> A' \<subseteq> f000 ` A \<Longrightarrow> EQG_fold_graph f000 F z A' y")
  apply(simp)
  proof - fix A' show "fold_graph F z A' y \<Longrightarrow> A' \<subseteq> f000 ` A \<Longrightarrow> EQG_fold_graph f000 F z A' y"
  apply(induction set: fold_graph)
  apply(rule EQG_emptyI)
  apply(simp, erule conjE)
  apply(drule imageE) prefer 2 apply assumption
  apply(simp)
  apply(rule EQG_insertI, simp, simp)
 done
qed

lemma fold_of_eqg_fold :
 assumes fold_g : "EQG_fold_graph f000 F z A y"
   shows "fold_graph F z A y"
 apply(insert fold_g)
 apply(induction set: EQG_fold_graph)
 apply(rule emptyI)
 apply(simp add: insertI)
done

context EQ_comp_fun_commute0_gen0_bis''
begin

 lemma fold_graph_insertE_aux:
   assumes y_defined : "\<And>\<tau>. all_defined \<tau> y"
   assumes a_valid : "\<forall>\<tau>. is_i' \<tau> (f000 a)"
   shows
   "EQG_fold_graph f000 f z A y \<Longrightarrow> (f000 a) \<in> A \<Longrightarrow> \<exists>y'. y = f (f000 a) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQG_fold_graph f000 f z (A - {(f000 a)}) y'"
 apply(insert y_defined)
 proof (induct set: EQG_fold_graph)
   case (EQG_insertI x A y)
   assume "\<And>\<tau>. all_defined \<tau> (f (f000 x) y)"
   then show "\<forall>\<tau>. is_i' \<tau> (f000 x) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case"
   proof (cases "x = a") assume "x = a" with EQG_insertI show "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" by (metis Diff_insert_absorb all_def)
   next apply_end(simp)

     assume "f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y)"
     then obtain y' where y: "y = f (f000 a) y'" and "(\<forall>\<tau>. all_defined \<tau> y')" and y': "EQG_fold_graph f000 f z (A - {(f000 a)}) y'"
      using EQG_insertI by (metis OCL_core.drop.simps insert_iff)
     have "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y')"
       apply(subgoal_tac "\<forall>\<tau>. is_i' \<tau> (f000 a) \<and> (\<forall>\<tau>. all_defined \<tau> y')") apply(simp only:)
       apply(subst (asm) cp_all_def) unfolding y apply(subst (asm) cp_all_def[symmetric])
       apply(insert all_def[where x = "a" and y = y', THEN iffD1], blast)
     done
     moreover have "\<forall>\<tau>. is_i' \<tau> (f000 x) \<Longrightarrow> \<forall>\<tau>. is_i' \<tau> (f000 a) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y') \<Longrightarrow> f (f000 x) y = f (f000 a) (f (f000 x) y')"
       unfolding y
     by(rule commute, blast+)
     moreover have "EQG_fold_graph f000 f z (insert (f000 x) A - {f000 a}) (f (f000 x) y')"
       using y' and `f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y)` and `f000 x \<notin> A`
       apply (simp add: insert_Diff_if OCL_lib_Gogolla_challenge.EQG_insertI)
     done
     apply_end(subgoal_tac "f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> \<exists>y'. f (f000 x) y = f (f000 a) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQG_fold_graph f000 f z (insert (f000 x) A - {(f000 a)}) y'")
     ultimately show "(\<forall>\<tau>. is_i' \<tau> (f000 x)) \<and> f000 x \<noteq> f000 a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" apply(auto simp: a_valid)
     by (metis (mono_tags) `\<And>\<tau>. all_defined \<tau> (f (f000 x) y)` all_def)
    apply_end(drule f000_inj, blast)+
   qed
  apply_end simp

  fix x y
  show "(\<And>\<tau>. all_defined \<tau> (f (f000 x) y)) \<Longrightarrow> \<forall>\<tau>. is_i' \<tau> (f000 x)"
   apply(rule all_def[where x = x and y = y, THEN iffD1, THEN conjunct1], simp) done
  apply_end blast
  fix x y \<tau>
  show "(\<And>\<tau>. all_defined \<tau> (f (f000 x) y)) \<Longrightarrow> all_defined \<tau> y"
   apply(rule all_def[where x = x, THEN iffD1, THEN conjunct2, THEN spec], simp) done
  apply_end blast
 qed

 lemma fold_graph_insertE:
   assumes v_defined : "\<And>\<tau>. all_defined \<tau> v"
       and x_valid : "\<forall>\<tau>. is_i' \<tau> (f000 x)"
       and "EQG_fold_graph f000 f z (insert (f000 x) A) v" and "(f000 x) \<notin> A"
   obtains y where "v = f (f000 x) y" and "is_i' \<tau> (f000 x)" and "\<And>\<tau>. all_defined \<tau> y" and "EQG_fold_graph f000 f z A y"
  apply(insert fold_graph_insertE_aux[OF v_defined x_valid `EQG_fold_graph f000 f z (insert (f000 x) A) v` insertI1] x_valid `(f000 x) \<notin> A`)
  apply(drule exE) prefer 2 apply assumption
  apply(drule Diff_insert_absorb, simp only:)
 done

 lemma fold_graph_determ:
  assumes x_defined : "\<And>\<tau>. all_defined \<tau> x"
      and y_defined : "\<And>\<tau>. all_defined \<tau> y"
    shows "EQG_fold_graph f000 f z A x \<Longrightarrow> EQG_fold_graph f000 f z A y \<Longrightarrow> y = x"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: EQG_fold_graph)
   case (EQG_insertI x A y v)
   from `\<And>\<tau>. all_defined \<tau> (f (f000 x) y)`
   have "\<forall>\<tau>. is_i' \<tau> (f000 x)" by(metis all_def)
   from `\<And>\<tau>. all_defined \<tau> v` and `\<forall>\<tau>. is_i' \<tau> (f000 x)` and `EQG_fold_graph f000 f z (insert (f000 x) A) v` and `(f000 x) \<notin> A`
   obtain y' where "v = f (f000 x) y'" and "\<And>\<tau>. all_defined \<tau> y'" and "EQG_fold_graph f000 f z A y'"
     by (rule fold_graph_insertE, simp)
   from EQG_insertI have "\<And>\<tau>. all_defined \<tau> y" by (metis all_def)
   from `\<And>\<tau>. all_defined \<tau> y` and `\<And>\<tau>. all_defined \<tau> y'` and `EQG_fold_graph f000 f z A y'` have "y' = y" by (metis EQG_insertI.hyps(3))
   with `v = f (f000 x) y'` show "v = f (f000 x) y" by (simp)
   apply_end(rule_tac f = f in EQG_empty_fold_graphE, auto)
 qed

 lemma det_init2 :
   assumes z_defined : "\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> z"
       and A_int : "all_i_set A"
     shows "EQG_fold_graph f000 f z A x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: EQG_fold_graph)
   apply_end(simp)
   apply_end(subst all_def, drule i_set, auto, rule i_val, blast)
 qed

 lemma fold_graph_determ3 : (* WARNING \<forall> \<tau> is implicit *)
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_i_set A"
     shows "EQG_fold_graph f000 f z A x \<Longrightarrow> EQG_fold_graph f000 f z A y \<Longrightarrow> y = x"
  apply(insert z_defined A_int)
  apply(rule fold_graph_determ)
  apply(rule det_init2[THEN spec]) apply(blast)+
  apply(rule det_init2[THEN spec]) apply(blast)+
 done

 lemma fold_graph_fold:
  assumes z_int : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
  shows "EQG_fold_graph f000 f z (f000 ` A) (foldG f000 f z (f000 ` A))"
 proof -
  from A_int have "finite (f000 ` A)" by (simp add: i_set_finite)
  then have "\<exists>x. fold_graph f z (f000 ` A) x" by (rule finite_imp_fold_graph)
  then have "\<exists>x. EQG_fold_graph f000 f z (f000 ` A) x" by (metis eqg_fold_of_fold)
  moreover note fold_graph_determ3[OF z_int A_int]
  ultimately have "\<exists>!x. EQG_fold_graph f000 f z (f000 ` A) x" by(rule ex_ex1I)
  then have "EQG_fold_graph f000 f z (f000 ` A) (The (EQG_fold_graph f000 f z (f000 ` A)))" by (rule theI')
  then show ?thesis by(unfold foldG_def)
 qed

 lemma fold_equality:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
     shows "EQG_fold_graph f000 f z (f000 ` A) y \<Longrightarrow> foldG f000 f z (f000 ` A) = y"
  apply(rule fold_graph_determ3[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done

 lemma fold_insert:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_i_set (f000 ` A)"
       and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
       and x_nA : "f000 x \<notin> f000 ` A"
   shows "foldG f000 f z (f000 ` (insert x A)) = f (f000 x) (foldG f000 f z (f000 ` A))"
 proof (rule fold_equality)
   have "EQG_fold_graph f000 f z (f000 `A) (foldG f000 f z (f000 `A))" by (rule fold_graph_fold[OF z_defined A_int])
   with x_nA show "EQG_fold_graph f000 f z (f000 `(insert x A)) (f (f000 x) (foldG f000 f z (f000 `A)))" apply(simp add: image_insert) by(rule EQG_insertI, simp, simp)
   apply_end (simp add: z_defined)
   apply_end (simp only: image_insert)
   apply_end(rule i_set', simp add: x_int A_int)
 qed

 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
      and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z (f000 ` insert x A) = f (f000 x) (Finite_Set.fold f z (f000 ` A))"
  proof -
   have eq_f : "\<And>A. Finite_Set.fold f z (f000 ` A) = foldG f000 f z (f000 ` A)"
    apply(simp add: Finite_Set.fold_def foldG_def)
   by (metis eqg_fold_of_fold fold_of_eqg_fold)

  have x_nA : "f000 x \<notin> f000 ` A"
   apply(simp add: image_iff)
  by (metis x_nA f000_inj)

  have "foldG f000 f z (f000 ` insert x A) = f (f000 x) (foldG f000 f z (f000 ` A))"
   apply(rule fold_insert) apply(simp add: assms x_nA)+
  done

  thus ?thesis by (subst (1 2) eq_f, simp)
 qed

 lemma all_int_induct :
   assumes i_fin : "all_i_set (f000 ` F)"
   assumes "P {}"
       and insert: "\<And>x F. all_i_set (f000 ` F) \<Longrightarrow> \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> x \<notin> F \<Longrightarrow> P (f000 ` F) \<Longrightarrow> P (f000 ` (insert x F))"
   shows "P (f000 ` F)"
 proof -
  from i_fin have "finite (f000 ` F)" by (simp add: i_set_finite)
  then have "finite F" apply(rule finite_imageD) apply(simp add: inj_on_def, insert f000_inj, blast) done
  show "?thesis"
  using `finite F` and i_fin
  proof induct
    apply_end(simp)
    show "P {}" by fact
    apply_end(simp add: i_set)
    apply_end(rule insert[simplified], simp add: i_set, simp add: i_set)
    apply_end(simp, simp)
  qed
 qed

 lemma all_defined_fold_rec :
  assumes A_defined : "\<And>\<tau>. all_defined \<tau> A"
      and x_notin : "x \<notin> Fa"
    shows "
        all_i_set (f000 ` insert x Fa) \<Longrightarrow>
        (\<And>\<tau>. all_defined \<tau> (Finite_Set.fold f A (f000 ` Fa))) \<Longrightarrow>
        all_defined \<tau> (Finite_Set.fold f A (f000 ` insert x Fa))"
  apply(subst (asm) image_insert)
  apply(frule i_set[THEN conjunct1])
  apply(subst fold_insert'[OF A_defined])
   apply(rule i_set[THEN conjunct2], simp)
   apply(simp)
   apply(simp add: x_notin)
  apply(rule all_def[THEN iffD2, THEN spec])
  apply(simp add: i_val)
 done

 lemma (in -) fold_empty [simp]: "foldG f000 f z {} = z"
 by (unfold foldG_def) blast

 lemma fold_def :
   assumes z_def : "\<And>\<tau>. all_defined \<tau> z"
   assumes F_int : "all_i_set (f000 ` F)"
   shows "all_defined \<tau> (Finite_Set.fold f z (f000 ` F))"
 apply(subgoal_tac "\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold f z (f000 ` F))", blast)
 proof (induct rule: all_int_induct[OF F_int])
  apply_end(simp add:z_def)
  apply_end(rule allI)
  apply_end(rule all_defined_fold_rec[OF z_def], simp, simp add: i_set', blast)
 qed

 lemma fold_fun_comm:
   assumes z_def : "\<And>\<tau>. all_defined \<tau> z"
   assumes A_int : "all_i_set (f000 ` A)"
       and x_val : "\<And>\<tau>. is_i' \<tau> (f000 x)"
     shows "f (f000 x) (Finite_Set.fold f z (f000 ` A)) = Finite_Set.fold f (f (f000 x) z) (f000 ` A)"
 proof -
  have fxz_def: "\<And>\<tau>. all_defined \<tau> (f (f000 x) z)"
  by(rule all_def[THEN iffD2, THEN spec], simp add: z_def x_val)

  show ?thesis
  proof (induct rule: all_int_induct[OF A_int])
   apply_end(simp)
   apply_end(rename_tac x' F)
   apply_end(subst fold_insert'[OF z_def], simp, simp, simp)
   apply_end(subst fold_insert'[OF fxz_def], simp, simp, simp)
   apply_end(subst commute[symmetric])
   apply_end(simp add: x_val)
   apply_end(rule i_val, blast)
   apply_end(subst fold_def[OF z_def], simp_all)
  qed
 qed

 lemma fold_rec:
    assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
        and A_int : "all_i_set (f000 ` A)"
        and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
        and "x \<in> A"
   shows "Finite_Set.fold f z (f000 ` A) = f (f000 x) (Finite_Set.fold f z (f000 ` (A - {x})))"
 proof -
   have f_inj : "inj f000" by (simp add: inj_on_def, insert f000_inj, blast)
   from A_int have A_int: "all_i_set (f000 ` (A - {x}))" apply(subst image_set_diff[OF f_inj]) apply(simp, rule i_set'', simp add: x_int) done
   have A: "f000 ` A = insert (f000 x) (f000 ` (A - {x}))" using `x \<in> A` by blast
   then have "Finite_Set.fold f z (f000 ` A) = Finite_Set.fold f z (insert (f000 x) (f000 ` (A - {x})))" by simp
   also have "\<dots> = f (f000 x) (Finite_Set.fold f z (f000 ` (A - {x})))" by(simp only: image_insert[symmetric], rule fold_insert'[OF z_defined A_int x_int], simp)
   finally show ?thesis .
 qed

 lemma fold_insert_remove:
    assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
        and A_int : "all_i_set (f000 ` A)"
        and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
   shows "Finite_Set.fold f z (f000 ` insert x A) = f (f000 x) (Finite_Set.fold f z (f000 ` (A - {x})))"
 proof -
   from A_int have "finite (f000 ` A)" by (simp add: i_set_finite)
   then have "finite (f000 ` insert x A)" by auto
   moreover have "x \<in> insert x A" by auto
   moreover from A_int have A_int: "all_i_set (f000 ` insert x A)" by (simp, subst i_set', simp_all add: x_int)
   ultimately have "Finite_Set.fold f z (f000 ` insert x A) = f (f000 x) (Finite_Set.fold f z (f000 ` (insert x A - {x})))"
   by (subst fold_rec[OF z_defined A_int x_int], simp_all)
   then show ?thesis by simp
 qed

 lemma finite_fold_insert :
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_i_set (f000 ` A)"
      and x_int : "\<forall>\<tau>. is_i \<tau> (f000 x)"
      and "x \<notin> A"
   shows "finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold f z (f000 ` insert x A) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (f (f000 x) (Finite_Set.fold f z (f000 ` A)) \<tau>)\<rceil>\<rceil>"
   apply(subst fold_insert', simp_all add: assms)
 done
end

locale EQ_comp_fun_commute0_gen0_bis' = EQ_comp_fun_commute0_gen0_bis'' +
  assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f (f000 x) S \<tau>1 = f (f000 x) S \<tau>2"
  assumes notempty : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f (f000 x) S \<tau>)\<rceil>\<rceil> \<noteq> {}"

context EQ_comp_fun_commute0_gen0_bis'
begin
 lemma downgrade_up : "EQ_comp_fun_commute0_gen0_bis'' f000 is_i is_i' all_i_set f" by default
 lemma downgrade : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f" by default
end

 lemma fold_cong''' :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and t_def : "\<And>\<tau>. all_defined \<tau> t"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<tau> \<Longrightarrow> f (f000 x) s \<tau> = g (f000 x) s \<tau>)"
      and ab : "A = B"
      and st : "s \<tau> = t \<tau>'"
      and P0 : "P s \<tau>"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<tau> \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F)) \<tau>"
    shows "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` B) \<tau>'"
 proof -
  interpret EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f by (rule f_comm)
  note g_comm_down = g_comm[THEN EQ_comp_fun_commute0_gen0_bis'.downgrade_up]
  note g_fold_insert' = EQ_comp_fun_commute0_gen0_bis''.fold_insert'[OF g_comm_down]
  note g_cp_set = EQ_comp_fun_commute0_gen0_bis''.cp_set[OF g_comm_down]
  note g_fold_def = EQ_comp_fun_commute0_gen0_bis''.fold_def[OF g_comm_down]
  note g_cp_gen = EQ_comp_fun_commute0_gen0_bis'.cp_gen[OF g_comm]
  have "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` A) \<tau>'"
   apply(rule all_int_induct[OF a_def], simp add: st)
   apply(subst fold_insert', simp add: s_def, simp, simp, simp)
   apply(subst g_fold_insert', simp add: t_def, simp, simp, simp)
   apply(subst g_cp_set, rule allI, rule g_fold_def, simp add: t_def, simp)
   apply(drule sym, simp)
   apply(subst g_cp_gen[of _ _ _ \<tau>], simp, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp, simp)
   apply(subst g_cp_set[symmetric], rule allI, rule fold_def, simp add: s_def, simp)
   apply(rule cong, simp)
   (* *)
   apply(rule all_int_induct, simp, simp add: P0, simp add: st[symmetric] P0)
   apply(rule Prec[simplified], simp_all)
  done
  thus ?thesis by (simp add: st[symmetric] ab[symmetric])
 qed

 lemma fold_cong'' :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<tau> \<Longrightarrow> f (f000 x) s \<tau> = g (f000 x) s \<tau>)"
      and ab : "A = B"
      and st : "s = t"
      and stau : "s \<tau> = s \<tau>'"
      and P0 : "P s \<tau>"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<tau> \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F)) \<tau>"
    shows "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` B) \<tau>'"
 proof -
  interpret EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f by (rule f_comm)
  note g_comm_down = g_comm[THEN EQ_comp_fun_commute0_gen0_bis'.downgrade_up]
  note g_fold_insert' = EQ_comp_fun_commute0_gen0_bis''.fold_insert'[OF g_comm_down]
  note g_cp_set = EQ_comp_fun_commute0_gen0_bis''.cp_set[OF g_comm_down]
  note g_fold_def = EQ_comp_fun_commute0_gen0_bis''.fold_def[OF g_comm_down]
  note g_cp_gen = EQ_comp_fun_commute0_gen0_bis'.cp_gen[OF g_comm]
  have "Finite_Set.fold g s (f000 ` A) \<tau>' = Finite_Set.fold f s (f000 ` A) \<tau>"
   apply(rule all_int_induct[OF a_def], simp add: stau)
   apply(subst fold_insert', simp add: s_def, simp, simp, simp)
   apply(subst g_fold_insert', simp add: s_def, simp, simp, simp)
   apply(subst g_cp_set, rule allI, rule g_fold_def, simp add: s_def, simp)
   apply(simp, subst g_cp_set[symmetric], rule allI, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp)
   apply(subst g_cp_gen[of _ _ _ \<tau>], simp, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp, simp)
   apply(subst g_cp_set[symmetric], rule allI, subst cp_all_def[where \<tau>' = \<tau>], subst cp_all_def[symmetric], rule fold_def, simp add: s_def, simp)
   apply(rule cong[symmetric], simp)
   (* *)
   apply(rule all_int_induct, simp, simp add: P0, simp add: st[symmetric] P0)
   apply(rule Prec[simplified], simp_all)
  done
  thus ?thesis by (simp add: st[symmetric] ab[symmetric])
 qed

 lemma fold_cong' :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<tau> \<Longrightarrow> f (f000 x) s \<tau> = g (f000 x) s \<tau>)"
      and ab : "A = B"
      and st : "s = t"
      and P0 : "P s \<tau>"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<tau> \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F)) \<tau>"
    shows "Finite_Set.fold f s (f000 ` A) \<tau> = Finite_Set.fold g t (f000 ` B) \<tau>"
 by(rule fold_cong''[OF f_comm g_comm a_def s_def cong ab st], simp, simp, simp, rule P0, rule Prec, blast+)

 lemma fold_cong :
  assumes f_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set f"
      and g_comm : "EQ_comp_fun_commute0_gen0_bis' f000 is_i is_i' all_i_set g"
      and a_def : "all_i_set (f000 ` A)"
      and s_def : "\<And>\<tau>. all_defined \<tau> s"
      and cong : "(\<And>x s. \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow> P s \<Longrightarrow> f (f000 x) s = g (f000 x) s)"
      and ab : "A = B"
      and st : "s = t"
      and P0 : "P s"
      and Prec : "\<And>x F.
        all_i_set (f000 ` F) \<Longrightarrow>
        \<forall>\<tau>. is_i \<tau> (f000 x) \<Longrightarrow>
        x \<notin> F \<Longrightarrow>
        P (Finite_Set.fold f s (f000 ` F)) \<Longrightarrow> P (Finite_Set.fold f s (f000 ` insert x F))"
    shows "Finite_Set.fold f s (f000 ` A) = Finite_Set.fold g t (f000 ` B)"
  apply(rule ext, rule fold_cong'[OF f_comm g_comm a_def s_def])
  apply(subst cong, simp, simp, simp, rule ab, rule st, rule P0)
  apply(rule Prec, simp_all)
 done


subsubsection{* Sublocale *}

locale EQ_comp_fun_commute =
  fixes f :: "('\<AA>, 'a option option) val
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_x : "\<And>x S \<tau>. f x S \<tau> = f (\<lambda>_. x \<tau>) S \<tau>"
  assumes cp_set : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. is_int x \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty : "\<And>x S \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y \<tau>. all_defined \<tau> (f x y) = (\<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> y)"
  assumes commute: "\<And>x y S \<tau>.
                             \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                             all_defined \<tau> S \<Longrightarrow>
                             f y (f x S) \<tau> = f x (f y S) \<tau>"

sublocale EQ_comp_fun_commute < EQ_comp_fun_commute0_gen0_bis' "\<lambda>x. x" "\<lambda>_. is_int" "\<lambda>\<tau> x. \<tau> \<Turnstile> \<upsilon> x" all_int_set
 apply(default)
 apply(simp add: all_int_set_def) apply(simp add: all_int_set_def) apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def)
 apply(simp add: int_is_valid, simp)
 apply(rule cp_set)
 apply(rule iffI)
 apply(rule conjI) apply(rule allI) apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption apply(rule all_def[THEN iffD1, THEN conjunct1], blast)
 apply(rule allI) apply(drule allE) prefer 2 apply assumption apply(rule all_def[THEN iffD1, THEN conjunct2], blast)
 apply(erule conjE) apply(rule allI)  apply(rule all_def[THEN iffD2], blast)
 apply(rule ext, rename_tac \<tau>)
 apply(rule commute) apply(blast)+
 apply(rule cp_gen, simp, blast, simp)
 apply(rule notempty, blast, simp add: int_is_valid, simp)
done

locale EQ_comp_fun_commute0_gen0 =
  fixes f000 :: "'b \<Rightarrow> ('\<AA>, 'a option option) val"
  fixes all_def_set :: "'\<AA> st \<Rightarrow> 'b set \<Rightarrow> bool"
  fixes f :: "'b
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes def_set : "\<And>x A. (\<forall>\<tau>. all_def_set \<tau> (insert x A)) = (is_int (f000 x) \<and> (\<forall>\<tau>. all_def_set \<tau> A))"
  assumes def_set' : "\<And>x A. (is_int (f000 x) \<and> (\<forall>\<tau>. all_def_set \<tau> A)) \<Longrightarrow> \<forall>\<tau>. all_def_set \<tau> (A - {x})"
  assumes def_set_finite : "\<forall>\<tau>. all_def_set \<tau> A \<Longrightarrow> finite A"
  assumes all_i_set_to_def : "all_int_set (f000 ` F) \<Longrightarrow> \<forall>\<tau>. all_def_set \<tau> F"

  assumes f000_inj : "\<And>x y. x \<noteq> y \<Longrightarrow> f000 x \<noteq> f000 y"

  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (f000 x) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"

  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (f000 x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (f000 x) \<Longrightarrow>
                             is_int (f000 y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"

sublocale EQ_comp_fun_commute0_gen0 < EQ_comp_fun_commute0_gen0_bis' "\<lambda>x. x" "\<lambda>_ x. is_int (f000 x)" "\<lambda>_ x. is_int (f000 x)" "\<lambda>x. \<forall>\<tau>. all_def_set \<tau> x"
 apply default
 apply(drule def_set[THEN iffD1], blast)
 apply(simp add: def_set[THEN iffD2])
 apply(simp add: def_set')
 apply(simp add: def_set_finite)
 apply(simp)
 apply(simp)
 apply(rule cp_set, simp)
 apply(insert all_def, blast)
 apply(rule commute, blast+)
 apply(rule cp_gen', blast+)
 apply(rule notempty', blast+)
done

locale EQ_comp_fun_commute0 =
  fixes f :: "'a option option
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (\<lambda>(_::'\<AA> st). x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'\<AA> st). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"

sublocale EQ_comp_fun_commute0 < EQ_comp_fun_commute0_gen0 "\<lambda>x (_::'\<AA> st). x" all_defined_set
 apply default
 apply(rule iffI)
  apply(simp add: all_defined_set_def is_int_def)
  apply(simp add: all_defined_set_def is_int_def)
  apply(simp add: all_defined_set_def is_int_def)
  apply(simp add: all_defined_set_def)
 apply(simp add: all_int_set_def all_defined_set_def int_is_valid)
 apply(rule finite_imageD, blast, metis inj_onI)
 apply metis
 apply(rule cp_gen', simp, simp, simp)
 apply(rule notempty', simp, simp, simp)
 apply(rule cp_set, simp)
 apply(rule all_def)
 apply(rule commute, simp, simp, blast)
done

locale EQ_comp_fun_commute000 =
  fixes f :: "('\<AA>, 'a option option) val
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (\<lambda>(_::'\<AA> st). x) S \<tau> = f (\<lambda>(_::'\<AA> st). x) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f (\<lambda>(_::'\<AA> st). x) y)) = (is_int (\<lambda>(_ :: '\<AA> st). x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'\<AA> st). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (\<lambda>(_::'\<AA> st). y) (f (\<lambda>(_::'\<AA> st). x) S) = f (\<lambda>(_::'\<AA> st). x) (f (\<lambda>(_::'\<AA> st). y) S)"

sublocale EQ_comp_fun_commute000 < EQ_comp_fun_commute0_gen0_bis'' "\<lambda>x (_::'\<AA> st). x" "\<lambda>_. is_int" "\<lambda>_. is_int" all_int_set
 apply default
  apply(simp add: all_int_set_def is_int_def)
  apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def)
 apply(simp add: all_int_set_def)
 apply(simp)
 apply(metis)
 apply(rule cp_set, simp)
 apply(insert all_def, blast)
 apply(rule commute, simp, simp, blast)
done

lemma c0_of_c :
 assumes f_comm : "EQ_comp_fun_commute f"
   shows "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
proof - interpret EQ_comp_fun_commute f by (rule f_comm) show ?thesis
 apply default
 apply(rule cp_set)
 apply(subst cp_gen, simp, blast, simp, simp)
 apply(rule notempty, blast, simp add: int_is_valid, simp)
 apply (metis (mono_tags) all_def is_int_def)

 apply(rule ext, rename_tac \<tau>)
 apply(subst commute)
 apply (metis is_int_def)+
 done
qed

lemma c000_of_c0 :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
   shows "EQ_comp_fun_commute000 f"
proof - interpret EQ_comp_fun_commute0 "\<lambda>x. f (\<lambda>_. x)" by (rule f_comm) show ?thesis
 apply default
 apply(rule cp_set, simp)
 apply(rule all_def)
 apply(rule commute)
 apply(blast)+
 done
qed

locale EQ_comp_fun_commute0' =
  fixes f :: "'a option
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y S.
                             is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow>
                             is_int (\<lambda>(_::'\<AA> st). \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"

sublocale EQ_comp_fun_commute0' < EQ_comp_fun_commute0_gen0 "\<lambda>x (_::'\<AA> st). \<lfloor>x\<rfloor>" all_defined_set'
 apply default
 apply(rule iffI)
  apply(simp add: all_defined_set'_def is_int_def, metis bot_option_def foundation18' option.distinct(1))
  apply(simp add: all_defined_set'_def is_int_def)
 apply(simp add: all_defined_set'_def is_int_def)
  apply(simp add: all_defined_set'_def)
 apply(simp add: all_int_set_def all_defined_set'_def int_is_valid)
 apply(rule finite_imageD, blast, metis (full_types) UNIV_I inj_Some inj_fun subsetI subset_inj_on)
 apply (metis option.inject)
 apply(rule cp_gen', simp, simp, simp)
 apply(rule notempty', simp, simp, simp)
 apply(rule cp_set, simp)
 apply(rule all_def)
 apply(rule commute, simp, simp, blast)
done

locale EQ_comp_fun_commute000' =
  fixes f :: "('\<AA>, 'a option option) val
              \<Rightarrow> ('\<AA>, 'a option option) Set
              \<Rightarrow> ('\<AA>, 'a option option) Set"
  assumes cp_set : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> f (\<lambda>_. \<lfloor>x\<rfloor>) S \<tau> = f (\<lambda>_. \<lfloor>x\<rfloor>) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y (\<tau> :: '\<AA> st). (\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> (f (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>) y)) = (\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>) \<and> (\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> y))"
  assumes commute: "\<And>x y S (\<tau> :: '\<AA> st).
                             \<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>x\<rfloor>) \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (\<lambda>_. \<lfloor>y\<rfloor>) (f (\<lambda>_. \<lfloor>x\<rfloor>) S) = f (\<lambda>_. \<lfloor>x\<rfloor>) (f (\<lambda>_. \<lfloor>y\<rfloor>) S)"

sublocale EQ_comp_fun_commute000' < EQ_comp_fun_commute0_gen0_bis'' "\<lambda>x (_::'\<AA> st). \<lfloor>x\<rfloor>" "\<lambda>\<tau> x. \<tau> \<Turnstile> \<upsilon> x" "\<lambda>\<tau> x. \<tau> \<Turnstile> \<upsilon> x" all_int_set
 apply default
 apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def is_int_def)
 apply(simp add: all_int_set_def)
 apply(simp add: all_int_set_def)
 apply(simp)
 apply (metis option.inject)
 apply(rule cp_set, simp)
 apply(rule iffI)
 apply(rule conjI, rule allI)
 apply(rule all_def[THEN iffD1, THEN conjunct1], blast)
 apply(rule all_def[THEN iffD1, THEN conjunct2], blast)
 apply(rule all_def[THEN iffD2], blast)
 apply(rule commute, blast+)
done

lemma c0'_of_c0 :
 assumes "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
   shows "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. f (\<lambda>_. x)" by (rule assms) show ?thesis
 apply default
 apply(rule cp_set, simp)
 apply(rule cp_gen', simp, simp, simp)
 apply(rule notempty', simp, simp, simp)
 apply(rule all_def)
 apply(rule commute) apply(blast)+
 done
qed

lemma c000'_of_c0' :
 assumes f_comm : "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "EQ_comp_fun_commute000' f"
proof - interpret EQ_comp_fun_commute0' "\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm) show ?thesis
 apply default
 apply(rule cp_set, simp)
 apply(subst all_def, simp only: is_int_def valid_def OclValid_def bot_fun_def false_def true_def, blast)
 apply(rule commute)
 apply(simp add: int_trivial)+
 done
qed

context EQ_comp_fun_commute
begin
 lemmas F_cp = cp_x
 lemmas F_cp_set = cp_set
 lemmas fold_fun_comm = fold_fun_comm[simplified]
 lemmas fold_insert_remove = fold_insert_remove[simplified]
 lemmas fold_insert = fold_insert'[simplified]
 lemmas all_int_induct = all_int_induct[simplified]
 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified image_ident]
 lemmas downgrade = downgrade
end

context EQ_comp_fun_commute000
begin
 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set ((\<lambda>a (\<tau> :: '\<AA> st). a) ` A)"
      and x_int : "is_int (\<lambda>(_ :: '\<AA> st). x)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). a) ` (insert x A)) = f (\<lambda>(_ :: '\<AA> st). x) (Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). a) ` A))"
  apply(rule fold_insert', simp_all add: assms)
 done

 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified]
 lemmas fold_def = fold_def
end

context EQ_comp_fun_commute000'
begin
 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set ((\<lambda>a (\<tau> :: '\<AA> st). \<lfloor>a\<rfloor>) ` A)"
      and x_int : "is_int (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). \<lfloor>a\<rfloor>) ` (insert x A)) = f (\<lambda>(_ :: '\<AA> st). \<lfloor>x\<rfloor>) (Finite_Set.fold f z ((\<lambda>a (\<tau> :: '\<AA> st). \<lfloor>a\<rfloor>) ` A))"
  apply(rule fold_insert', simp_all only: assms)
  apply(insert x_int[simplified is_int_def], auto)
 done

 lemmas fold_def = fold_def
end

context EQ_comp_fun_commute0_gen0
begin
 lemma fold_insert:
   assumes z_defined : "\<forall>(\<tau> :: '\<AA> st). all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: '\<AA> st). all_def_set \<tau> A"
       and x_int : "is_int (f000 x)"
       and "x \<notin> A"
   shows "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z A)"
 by(rule fold_insert'[simplified], simp_all add: assms)

 lemmas downgrade = downgrade
end

context EQ_comp_fun_commute0
begin
 lemmas fold_insert = fold_insert
 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified image_ident]
end

context EQ_comp_fun_commute0'
begin
 lemmas fold_insert = fold_insert
 lemmas all_defined_fold_rec = all_defined_fold_rec[simplified image_ident]
end

subsubsection{* Misc *}

lemma img_fold :
 assumes g_comm : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. G (f000 x))"
     and a_def : "\<forall>\<tau>. all_defined \<tau> A"
     and fini : "all_int_set (f000 ` Fa)"
     and g_fold_insert : "\<And>x F. x \<notin> F \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` F) \<Longrightarrow> Finite_Set.fold G A (insert (f000 x) (f000 ` F)) = G (f000 x) (Finite_Set.fold G A (f000 ` F))"
   shows  "Finite_Set.fold (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) A (f000 ` Fa) =
           Finite_Set.fold (\<lambda>x. G (f000 x)) A Fa"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. G (f000 x)" by (rule g_comm)
 show ?thesis
  apply(rule finite_induct[where P = "\<lambda>set. let set' = f000 ` set in
                                               all_int_set set' \<longrightarrow>
                                               Finite_Set.fold G A set' = Finite_Set.fold (\<lambda>x. G (f000 x)) A set"
                  and F = Fa, simplified Let_def, THEN mp])
  apply(insert fini[simplified all_int_set_def, THEN conjunct1], rule finite_imageD, assumption)
  apply (metis f000_inj inj_onI)
  apply(simp)
  apply(rule impI)+

  apply(subgoal_tac "all_int_set (f000 ` F)", simp)

  apply(subst EQ_comp_fun_commute0_gen0.fold_insert[OF g_comm])
   apply(simp add: a_def)
   apply(simp add: all_i_set_to_def)
   apply(simp add: invert_int)
   apply(simp)
   apply(drule sym, simp only:)
   apply(subst g_fold_insert, simp, simp add: invert_int, simp)
  apply(simp)

  apply(rule invert_all_int_set, simp)
  apply(simp add: fini)
 done
qed

context EQ_comp_fun_commute0_gen0 begin lemma downgrade' : "EQ_comp_fun_commute0_gen0 f000 all_def_set f" by default end
context EQ_comp_fun_commute0 begin lemmas downgrade' = downgrade' end
context EQ_comp_fun_commute0' begin lemmas downgrade' = downgrade' end

subsection{* comp fun commute OclIncluding *}
subsubsection{* Preservation of comp fun commute (main) *}

lemma including_commute_gen_var :
  assumes f_comm : "EQ_comp_fun_commute F"
      and f_out : "\<And>x y S \<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> F x (S->including(y)) \<tau> = (F x S)->including(y) \<tau>"
      and a_int : "is_int a"
    shows "EQ_comp_fun_commute (\<lambda>j r2. ((F j r2)->including(a)))"
proof -
 interpret EQ_comp_fun_commute F by (rule f_comm)

 have f_cp : "\<And>x y \<tau>. F x y \<tau> = F (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>) \<tau>"
 by (metis F_cp F_cp_set)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def)
  apply(rule conjI)+
  apply(rule allI)+

  proof - fix x S \<tau> show "(F x S)->including(a) \<tau> = (F (\<lambda>_. x \<tau>) S)->including(a) \<tau>"
  by(subst (1 2) cp_OclIncluding, subst F_cp, simp)

  apply_end(rule conjI)+ apply_end(rule allI)+

  fix x S \<tau> show "(F x S)->including(a) \<tau> = (F x (\<lambda>_. S \<tau>))->including(a) \<tau>"
  by(subst (1 2) cp_OclIncluding, subst F_cp_set, simp)

  apply_end(rule allI)+ apply_end(rule impI)+

  fix x fix S fix \<tau>1 \<tau>2
  show "is_int x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> ((F x S)->including(a)) \<tau>1 = ((F x S)->including(a)) \<tau>2"
   apply(subgoal_tac "x \<tau>1 = x \<tau>2") prefer 2 apply (simp add: is_int_def) apply(metis surj_pair)
   apply(subgoal_tac "\<And>\<tau>. all_defined \<tau> (F x S)") prefer 2 apply(rule all_def[THEN iffD2], simp only: int_is_valid, blast)
   apply(subst including_cp_all[of _ _ \<tau>1 \<tau>2]) apply(simp add: a_int) apply(rule all_defined1, blast)
   apply(rule cp_gen, simp, blast, simp)
   apply(simp)
  done
  apply_end(simp) apply_end(simp) apply_end(simp) apply_end(rule conjI)
  apply_end(rule allI)+ apply_end(rule impI)+

  apply_end(rule including_notempty)
  apply_end(rule all_defined1)
  apply_end(simp add: all_def, metis surj_pair, simp)
  apply_end(simp add: int_is_valid[OF a_int])
  apply_end(rule notempty, blast, simp, simp)

  apply_end(rule conjI) apply_end(rule allI)+
  apply_end(rule iffI)
  apply_end(drule invert_all_defined, simp add: all_def)
  apply_end(rule cons_all_def', simp add: all_def)
  apply_end(simp add: int_is_valid[OF a_int])

  apply_end(rule allI)+ apply_end(rule impI)+

  fix x y S \<tau> show "\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> all_defined \<tau> S \<Longrightarrow>
  (F y ((F x S)->including(a)))->including(a) \<tau> =
  (F x ((F y S)->including(a)))->including(a) \<tau>"
   apply(rule including_subst_set'')
   apply(rule all_defined1)
   apply(simp add: all_def, rule cons_all_def', simp add: all_def)
   apply(simp add: int_is_valid[OF a_int])
   apply(rule all_defined1)
   apply(simp add: all_def, rule cons_all_def', simp add: all_def)
   apply(simp add: int_is_valid[OF a_int])+
   apply(subst f_out)
   apply(rule all_defined1, simp add: all_def, simp)
   apply(simp add: int_is_valid[OF a_int])
   apply(subst cp_OclIncluding)
   apply(subst commute, simp_all add: cp_OclIncluding[symmetric] f_out[symmetric])
   apply(subst f_out[symmetric])
   apply(rule all_defined1, simp add: all_def, simp)
   apply(simp add: int_is_valid[OF a_int])
   apply(simp)
  done
  apply_end(simp)+
 qed
qed

subsubsection{* Preservation of comp fun commute (instance) *}

lemma including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, int option option) Set). (r2->including(j)))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def including_cp including_cp')
  apply(rule conjI, rule conjI) apply(subst (1 2) cp_OclIncluding, simp) apply(rule conjI) apply(subst (1 2) cp_OclIncluding, simp) apply(rule allI)+
  apply(rule impI)+
  apply(rule including_cp_all) apply(simp) apply(rule all_defined1, blast) apply(simp)
  apply(rule conjI) apply(rule allI)+
  apply(rule impI)+ apply(rule including_notempty) apply(rule all_defined1, blast) apply(simp) apply(simp)
  apply(rule conjI) apply(rule allI)+
  apply(rule iff[THEN mp, THEN mp], rule impI)
  apply(rule invert_all_defined, simp)
  apply(rule impI, rule cons_all_def') apply(simp) apply(simp)
  apply(rule allI)+ apply(rule impI)+
  apply(rule including_swap', simp_all add: all_defined_def)
 done
qed

lemma including_commute2 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). ((acc->including(x))->including(i)))"
 apply(rule including_commute_gen_var)
 apply(rule including_commute)
 apply(rule including_swap', simp_all add: i_int)
done

lemma including_commute3 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(i)->including(x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def including_cp2 including_cp')
  apply(rule conjI, rule conjI) apply(subst (1 2) cp_OclIncluding, simp) apply(rule conjI) apply(subst (1 2) cp_OclIncluding, subst (1 3) cp_OclIncluding, simp) apply(rule allI)+
  apply(rule impI)+
  apply(rule including_cp_all) apply(simp) apply (metis (hide_lams, no_types) all_defined1 foundation10 foundation6 i_val including_defined_args_valid')
  apply(rule including_cp_all) apply(simp add: i_int) apply(rule all_defined1, blast) apply(simp)
  apply(rule conjI) apply(rule allI)+

  apply(rule impI)+
  apply(rule including_notempty) apply (metis (hide_lams, no_types) all_defined1 foundation10 foundation6 i_val including_defined_args_valid') apply(simp)
  apply(rule including_notempty) apply(rule all_defined1, blast) apply(simp add: i_val) apply(simp)
  apply(rule conjI) apply(rule allI)+

  apply(rule iff[THEN mp, THEN mp], rule impI)
  apply(drule invert_all_defined, drule conjE) prefer 2 apply assumption
  apply(drule invert_all_defined, drule conjE) prefer 2 apply assumption
  apply(simp)

  apply(rule impI, rule cons_all_def', rule cons_all_def') apply(simp) apply(simp add: i_val) apply(simp)
  apply(rule allI)+ apply(rule impI)+
  apply(subst including_swap')
   apply(metis (hide_lams, no_types) all_defined1 cons_all_def' i_val)
   apply(simp add: i_val)
   apply(simp)
  apply(rule sym)
  apply(subst including_swap')
   apply(metis (hide_lams, no_types) all_defined1 cons_all_def' i_val)
   apply(simp add: i_val)
   apply(simp)

  apply(rule including_subst_set'')
   apply(rule all_defined1)
   apply(rule cons_all_def')+ apply(simp_all add: i_val)
   apply(insert i_val) apply (metis (hide_lams, no_types) all_defined1 foundation10 foundation6)
  apply(subst including_swap')
  apply(metis (hide_lams, no_types) all_defined1 cons_all_def')
  apply(simp)+
 done
qed

lemma including_commute4 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(i)->including(x)->including(j))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 have j_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> j" by (simp add: int_is_valid[OF j_int])
 show ?thesis
  apply(rule including_commute_gen_var)
  apply(rule including_commute3)
  apply(simp_all add: i_int j_int)
  apply(subgoal_tac " S->including(y)->including(i)->including(x) \<tau> = S->including(i)->including(y)->including(x) \<tau>")
  prefer 2
  apply(rule including_subst_set'')
  apply (metis (hide_lams, no_types) foundation10 foundation6 i_val including_defined_args_valid')+
  apply(rule including_swap', simp_all add: i_val)
  apply(rule including_swap')
  apply (metis (hide_lams, no_types) foundation10 foundation6 i_val including_defined_args_valid')+
 done
qed

lemma including_commute5 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(x)->including(j)->including(i))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 have j_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> j" by (simp add: int_is_valid[OF j_int])
 show ?thesis
  apply(rule including_commute_gen_var)+
  apply(simp add: including_commute)
  apply(rule including_swap', simp_all add: i_int j_int)
  apply(subgoal_tac " S->including(y)->including(x)->including(j) \<tau> = S->including(x)->including(y)->including(j) \<tau>")
  prefer 2
  apply(rule including_subst_set'')
  apply (metis (hide_lams, no_types) foundation10 foundation6 j_val including_defined_args_valid')+
  apply(rule including_swap', simp_all)
  apply(rule including_swap')
  apply (metis (hide_lams, no_types) foundation10 foundation6 j_val including_defined_args_valid')+
 done
qed

lemma including_commute6 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(i)->including(j)->including(x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" by (simp add: int_is_valid[OF i_int])
 have j_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> j" by (simp add: int_is_valid[OF j_int])
 show ?thesis
  apply(simp only: EQ_comp_fun_commute_def including_cp3 including_cp''')
  apply(rule conjI, rule conjI) apply(subst (1 2) cp_OclIncluding, simp)
  apply(rule conjI) apply(subst (1 2) cp_OclIncluding, subst (1 3) cp_OclIncluding, subst (1 4) cp_OclIncluding, simp) apply(rule allI)+
  apply(rule impI)+
  apply(rule including_cp_all) apply(simp) apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val j_val)
  apply(rule including_cp_all) apply(simp) apply(simp add: j_int)  apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val)
  apply(rule including_cp_all) apply(simp) apply(simp add: i_int) apply(rule all_defined1, blast) apply(simp)
  apply(rule conjI) apply(rule allI)+

  apply(rule impI)+
  apply(rule including_notempty)  apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val j_val) apply(simp)
  apply(rule including_notempty)  apply (metis (hide_lams, no_types) all_defined1 cons_all_def i_val)  apply(simp add: j_val)
  apply(rule including_notempty) apply(rule all_defined1, blast) apply(simp add: i_val) apply(simp)
  apply(rule conjI) apply(rule allI)+

  apply(rule iff[THEN mp, THEN mp], rule impI)
  apply(drule invert_all_defined, drule conjE) prefer 2 apply assumption
  apply(drule invert_all_defined, drule conjE) prefer 2 apply assumption
  apply(drule invert_all_defined, drule conjE) prefer 2 apply assumption
  apply(simp)

  apply(rule impI, rule cons_all_def', rule cons_all_def', rule cons_all_def') apply(simp) apply(simp add: i_val) apply(simp add: j_val) apply(simp)
  apply(rule allI)+ apply(rule impI)+

  apply(subst including_swap')
   apply(metis (hide_lams, no_types) all_defined1 cons_all_def' i_val j_val)
   apply(simp add: j_val)
   apply(simp)
  apply(rule sym)
  apply(subst including_swap')
   apply(metis (hide_lams, no_types) all_defined1 cons_all_def' i_val j_val)
   apply(simp add: j_val)
   apply(simp)

  apply(rule including_subst_set'')
   apply(rule all_defined1)
   apply(rule cons_all_def')+ apply(simp_all add: i_val j_val)
   apply(insert i_val j_val) apply (metis (hide_lams, no_types) all_defined1 foundation10 foundation6)

  apply(subst including_swap')
   apply(metis (hide_lams, no_types) all_defined1 cons_all_def' i_val)
   apply(simp add: i_val)
   apply(simp)
  apply(rule sym)
  apply(subst including_swap')
   apply(metis (hide_lams, no_types) all_defined1 cons_all_def' i_val)
   apply(simp add: i_val)
   apply(simp)

  apply(rule including_subst_set'')
   apply(rule all_defined1)
   apply(rule cons_all_def')+ apply(simp_all add: i_val j_val)
   apply(insert i_val j_val) apply (metis (hide_lams, no_types) all_defined1 foundation10 foundation6)

  apply(subst including_swap')
  apply(metis (hide_lams, no_types) all_defined1 cons_all_def')
  apply(simp)+
 done
qed

subsection{* comp fun commute OclIterate *}
subsubsection{* Congruence *}

lemma iterate_subst_set_rec :
 assumes A_defined : "\<forall>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
   shows "let Fa' = (\<lambda>a \<tau>. a) ` Fa
                    ; x' = \<lambda>\<tau>. x in
           x \<notin> Fa \<longrightarrow>
           all_int_set (insert x' Fa') \<longrightarrow>
           (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A Fa')) \<longrightarrow>
           (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A (insert x' Fa')))"
 apply(simp only: Let_def) apply(rule impI)+ apply(rule allI)+
 apply(rule EQ_comp_fun_commute000.all_defined_fold_rec[OF F_commute[THEN c0_of_c, THEN c000_of_c0]], simp add: A_defined, simp, simp, blast)
done

lemma iterate_subst_set_rec0 :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F:: ('\<AA>, _) val
   \<Rightarrow> ('\<AA>, _) Set
     \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
   shows "
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A (insert x Fa))"
 apply(rule allI, rule EQ_comp_fun_commute0.all_defined_fold_rec[OF F_commute])
 apply(simp, simp, simp add: all_int_set_def all_defined_set_def is_int_def, blast)
done

lemma iterate_subst_set_rec0' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. (F:: ('\<AA>, _) val
   \<Rightarrow> ('\<AA>, _) Set
     \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). \<lfloor>a\<rfloor>) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)) A Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)) A (insert x Fa))"
 apply(rule allI, rule EQ_comp_fun_commute0'.all_defined_fold_rec[OF F_commute])
 apply(simp, simp, simp add: all_int_set_def all_defined_set'_def is_int_def, blast)
done

lemma iterate_subst_set_gen :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> P acc \<Longrightarrow> F x acc = G x acc"
     and P0 : "P A"
     and Prec : "\<And>x Fa. all_int_set Fa \<Longrightarrow>
             is_int x \<Longrightarrow> x \<notin> Fa \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A Fa) \<Longrightarrow> P (Finite_Set.fold F A Fa) \<Longrightarrow> P (F x (Finite_Set.fold F A Fa))"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -

 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 interpret EQ_comp_fun_commute F by (rule F_commute)
 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def, rule ext)
  proof -
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)", simp)

  apply(rule fold_cong[where P = "\<lambda>s. \<forall>\<tau>. all_defined \<tau> s \<and> P s", OF downgrade EQ_comp_fun_commute.downgrade[OF G_commute], simplified image_ident])
   apply(simp only: S_all_int)
   apply(simp only: A_all_def)
   apply(rule fold_eq, simp add: int_is_valid, simp, simp)
  apply(simp, simp, simp add: A_all_def)
  apply(simp add: P0)
  apply(rule allI)
  apply(subst EQ_comp_fun_commute.all_defined_fold_rec[OF F_commute], simp add: A_all_def, simp, simp add: all_int_set_def, blast)
  apply(subst fold_insert, simp add: A_all_def, simp, simp, simp)
  apply(simp add: Prec)
  done
 qed
qed

lemma iterate_subst_set :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
by(rule iterate_subst_set_gen[OF S_all_def A_all_def F_commute G_commute fold_eq], (simp add: int_is_valid)+)

lemma iterate_subst_set' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -
 interpret EQ_comp_fun_commute F by (rule F_commute)
 show ?thesis
  apply(rule iterate_subst_set_gen[where P = "\<lambda>acc. \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>'", OF S_all_def A_all_def F_commute G_commute fold_eq], blast+)
  apply(simp add: A_include)
  apply(rule allI)+
  apply(rule cp_gen, simp, blast, blast)
 done
qed

lemma iterate_subst_set'' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {}"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> (\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {}) \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -
 interpret EQ_comp_fun_commute F by (rule F_commute)
 show ?thesis
  apply(rule iterate_subst_set_gen[where P = "\<lambda>acc. (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {})", OF S_all_def A_all_def F_commute G_commute fold_eq], blast, blast, blast)
  apply(simp add: A_notempty)
  apply(rule allI)+
  apply(rule notempty, blast, simp add: int_is_valid, blast)
 done
qed

lemma iterate_subst_set_gen0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. F (f000 x))"
     and G_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (f000 x))"
     and fold_eq : "\<And>x acc. is_int (f000 x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> P acc \<tau> \<Longrightarrow> F (f000 x) acc \<tau> = G (f000 x) acc \<tau>"
     and P0 : "P A \<tau>"
     and Prec : "\<And>x Fa. \<forall>(\<tau>::'\<AA> st). all_def_set \<tau> Fa \<Longrightarrow>
           is_int (f000 x) \<Longrightarrow>
           x \<notin> Fa \<Longrightarrow>
           \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (f000 x)) A Fa) \<Longrightarrow>
           P (Finite_Set.fold (\<lambda>x. F (f000 x)) A Fa) \<tau> \<Longrightarrow>
           P (F (f000 x) (Finite_Set.fold (\<lambda>x. F (f000 x)) A Fa)) \<tau>"
     and f_fold_insert : "\<And>x S. x \<notin> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold F A (insert (f000 x) (f000 ` S)) = F (f000 x) (Finite_Set.fold F A (f000 ` S))"
     and g_fold_insert : "\<And>x S. x \<notin> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold G A (insert (f000 x) (f000 ` S)) = G (f000 x) (Finite_Set.fold G A (f000 ` S))"
     and S_lift : "all_defined \<tau> S \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = f000 ` S'"
   shows "(S->iterate(x;acc=A|F x acc)) \<tau> = (S->iterate(x;acc=A|G x acc)) \<tau>"
proof -
 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_all_def' : "\<And>\<tau> \<tau>'. all_defined_set' \<tau>' \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
  apply(insert S_all_def)
  apply(subst (asm) cp_all_def, simp add: all_defined_def all_defined_set'_def, blast)
 done

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. F (f000 x)" by (rule F_commute)
 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  proof -
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
  apply(rule S_lift[OF S_all_def, THEN exE], simp)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, drule sym, simp add: S_all_int, rule f_fold_insert, simp_all) apply(subst img_fold[OF G_commute], simp add: A_all_def, drule sym, simp add: S_all_int, rule g_fold_insert, simp_all)
  apply(rule fold_cong'[where P = "\<lambda>s \<tau>. (\<forall>\<tau>. all_defined \<tau> s) \<and> P s \<tau>", OF downgrade EQ_comp_fun_commute0_gen0.downgrade[OF G_commute], simplified image_ident])
  apply(rule all_i_set_to_def)
  apply(drule sym, simp add: S_all_int, simp add: A_all_def)
   apply(rule fold_eq, simp add: int_is_valid, blast, simp)
  apply(simp, simp, simp add: A_all_def, rule P0)
  apply(rule conjI)+
  apply(subst all_defined_fold_rec[simplified], simp add: A_all_def, simp) apply(subst def_set[THEN iffD2, THEN spec], simp) apply(simp, blast, simp)
  apply(subst fold_insert, simp add: A_all_def, simp, simp, simp)
  apply(rule Prec, simp+)
  done
 qed
qed

lemma iterate_subst_set0_gen :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> P acc \<tau> \<Longrightarrow> F (\<lambda>_. x) acc \<tau> = G (\<lambda>_. x) acc \<tau>"
     and P0 : "P A \<tau>"
     and Prec : "\<And>x Fa. \<forall>(\<tau>::'\<AA> st). all_defined_set \<tau> Fa \<Longrightarrow>
           is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow>
           x \<notin> Fa \<Longrightarrow>
           \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<Longrightarrow>
           P (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<tau> \<Longrightarrow>
           P (F (\<lambda>_. x) (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa)) \<tau>"
   shows "(S->iterate(x;acc=A|F x acc)) \<tau> = (S->iterate(x;acc=A|G x acc)) \<tau>"
 apply(rule iterate_subst_set_gen0[OF S_all_def A_all_def F_commute[THEN EQ_comp_fun_commute0.downgrade'] G_commute[THEN EQ_comp_fun_commute0.downgrade']])
 apply(rule fold_eq, simp, simp, simp)
 apply(rule P0, rule Prec, blast+)
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], simp add: A_all_def, blast+)
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF G_commute[THEN c000_of_c0[where f = G]], simplified], simp add: A_all_def, blast+)
done

lemma iterate_subst_set0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>(_:: '\<AA> st). x))) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> F (\<lambda>_. x) acc = G (\<lambda>_. x) acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
 apply(rule ext, rule iterate_subst_set0_gen, simp_all add: assms)
 apply(subst fold_eq, simp_all add: int_is_valid)
done

lemma iterate_subst_set'0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc \<tau>. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> F (\<lambda>_. x) acc = G (\<lambda>_. x) acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)
 show ?thesis
  apply(rule ext, rule iterate_subst_set0_gen[where P = "\<lambda>acc _. \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>'", OF S_all_def A_all_def F_commute G_commute])
  apply(subst fold_eq, simp+, simp add: A_include)
  apply(rule allI)+
  apply(rule cp_gen', simp, blast, blast)
 done
qed

lemma iterate_subst_set''0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'\<AA> st). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> F (\<lambda>_. x) acc \<tau> = G (\<lambda>_. x) acc \<tau>"
   shows "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A|F x acc)) \<tau> = (S->iterate(x;acc=A|G x acc)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)
 show "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(rule iterate_subst_set0_gen[where P = "\<lambda>acc \<tau>. \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {}", OF S_all_def A_all_def F_commute G_commute])
  apply(subst fold_eq, simp+)
  apply(rule notempty', simp+)
 done
qed

lemma iterate_subst_set___ :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and G_commute : "EQ_comp_fun_commute0' (\<lambda>x. (G :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. \<lfloor>x\<rfloor>))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> F (\<lambda>_. \<lfloor>x\<rfloor>) acc \<tau> = G (\<lambda>_. \<lfloor>x\<rfloor>) acc \<tau>"
   shows "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A|F x acc)) \<tau> = (S->iterate(x;acc=A|G x acc)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0' "\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule F_commute)
 show "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(rule iterate_subst_set_gen0[where P = "\<lambda>acc \<tau>. (\<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>') \<and> \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {}", OF S_all_def A_all_def F_commute[THEN EQ_comp_fun_commute0'.downgrade'] G_commute[THEN EQ_comp_fun_commute0'.downgrade']])
  apply(rule fold_eq, blast+, simp add: A_include)
  apply(rule conjI)+
  apply(rule allI)+
  apply(rule cp_gen', blast+)
  apply(rule notempty', blast+)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], simp add: A_all_def, blast+)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF G_commute[THEN c000'_of_c0'[where f = G]], simplified], simp add: A_all_def, blast+)
  apply(rule S_lift, simp)
 done
qed

subsubsection{* Context passing *}

lemma cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1_gen:
 assumes f_comm : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. f (f000 x))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and f_fold_insert : "\<And>x S A. (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> x \<notin> S \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold f A (insert (f000 x) (f000 ` S)) = f (f000 x) (Finite_Set.fold f A (f000 ` S))"
     and S_lift : "all_defined \<tau> X \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> = f000 ` S'"
   shows "(X->iterate(a; x = A | f a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate(a; x = (\<lambda>_. A \<tau>) | f a x)) \<tau>"
proof -
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have A_all_def' : "\<And>\<tau> \<tau>'. all_defined \<tau> (\<lambda>a. A \<tau>')" by(subst cp_all_def[symmetric], simp add: A_all_def)

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. f (f000 x)" by (rule f_comm)
 show ?thesis
 apply(subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t[symmetric])
 apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def cp_valid[symmetric])
 apply(case_tac "\<not>((\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)", blast)
 apply(simp)
 apply(erule conjE)+
 apply(frule Set_inv_lemma[simplified OclValid_def])
 proof -
 assume "(\<delta> X) \<tau> = true \<tau>"
    "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
    "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> \<bottom>"
 then have X_def : "all_defined \<tau> X" by (metis (lifting, no_types) OclValid_def all_defined_def all_defined_set'_def foundation18')
 show "Finite_Set.fold f A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>) \<tau> = Finite_Set.fold f (\<lambda>_. A \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>) \<tau>"
  apply(rule S_lift[OF X_def, THEN exE], simp)
  apply(subst (1 2) img_fold[OF f_comm], simp add: A_all_def', drule sym, simp add: all_def_to_all_int[OF X_def])
  apply(rule f_fold_insert, simp_all add: A_all_def' A_all_def)+
  apply(rule fold_cong'''[where P = "\<lambda>_ _. True", OF downgrade downgrade, simplified image_ident])
  apply(rule all_i_set_to_def)
  apply(drule sym, simp add: all_def_to_all_int[OF X_def], simp add: A_all_def) apply(subst cp_all_def[symmetric], simp add: A_all_def)
  apply(blast+)
 done
 qed
qed

lemma cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1:
 assumes f_comm : "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "(X->iterate(a; x = A | f a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate(a; x = (\<lambda>_. A \<tau>) | f a x)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0' "\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm)
 show ?thesis
  apply(rule cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1_gen[OF downgrade' A_all_def])
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF f_comm[THEN c000'_of_c0'[where f = f]], simplified], simp_all)
  apply(rule S_lift, simp)
 done
qed

subsubsection{* all defined (construction) *}

lemma i_cons_all_def :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F :: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> S"
   shows "all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[simplified all_defined_def OclValid_def]
                  A_all_def[simplified all_defined_def all_defined_set'_def]
                  A_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(subgoal_tac "\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold F S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))", metis (lifting, no_types) foundation16 all_defined_def)
  apply(rule allI, rule EQ_comp_fun_commute000.fold_def[OF F_commute[THEN c000_of_c0]], simp add: A_all_def, simp add: A_all_def')
 done
qed

lemma i_cons_all_def'' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S A F)"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: S_all_def)
 done

 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def OclValid_def]
                  S_all_def[simplified all_defined_def all_defined_set'_def]
                  A_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(subgoal_tac "\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))", metis (lifting, no_types) foundation16 all_defined_def)
  apply(rule S_lift[THEN exE, OF S_all_def[of \<tau>]], simp only:)
  apply(rule allI, rule EQ_comp_fun_commute000'.fold_def[OF F_commute[THEN c000'_of_c0']], simp add: A_all_def, drule sym, simp add: A_all_def')
 done
qed

lemma i_cons_all_def''cp :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "all_defined \<tau> (\<lambda>\<tau>. OclIterate\<^isub>S\<^isub>e\<^isub>t (\<lambda>_. S \<tau>) (\<lambda>_. A \<tau>) F \<tau>)"
 apply(subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[symmetric, OF F_commute A_all_def])
 apply(rule i_cons_all_def''[OF F_commute S_all_def A_all_def])
done

lemma i_cons_all_def' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> S"
   shows "all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
by(rule i_cons_all_def'', simp_all add: assms)

subsubsection{* Preservation of global jugdment *}

lemma iterate_cp_all_gen :
 assumes F_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. F (f000 x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: '\<AA> st) = S \<tau>2"
     and f_fold_insert : "\<And>x A S. x \<notin> S \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold F A (insert (f000 x) (f000 ` S)) = F (f000 x) (Finite_Set.fold F A (f000 ` S))"
     and S_lift : "all_defined \<tau>2 S \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>2)\<rceil>\<rceil> = f000 ` S'"
   shows "OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>1 = OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>2"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. F (f000 x)" by (rule F_commute)
 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set'_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  S_cp)
  apply(rule S_lift[OF A_all_def[THEN spec], THEN exE], simp)
  apply(subst (1 2) img_fold[OF F_commute], simp add: A_all_def, drule sym, simp add: A_all_def', rule f_fold_insert, simp_all add: A_all_def)
  apply(subst (1 2) image_ident[symmetric])
  apply(rule fold_cong''[where P = "\<lambda>_ _. True", OF F_commute[THEN EQ_comp_fun_commute0_gen0.downgrade] F_commute[THEN EQ_comp_fun_commute0_gen0.downgrade]])
    apply(rule all_i_set_to_def)
  apply(drule sym, simp add: A_all_def', simp add: A_all_def)
  apply(simp_all add: S_cp)
 done
qed

lemma iterate_cp_all :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: '\<AA> st) = S \<tau>2"
   shows "OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>1 = OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>2"
 apply(rule iterate_cp_all_gen[OF F_commute[THEN EQ_comp_fun_commute0.downgrade'] A_all_def S_cp])
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], blast+)
done

lemma iterate_cp_all' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: '\<AA> st) = S \<tau>2"
   shows "OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>1 = OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>2"
 apply(rule iterate_cp_all_gen[OF F_commute[THEN EQ_comp_fun_commute0'.downgrade'] A_all_def S_cp])
 apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], blast+)
 apply(rule S_lift, simp)
done

subsubsection{* Preservation of non-emptiness *}

lemma iterate_notempty_gen :
 assumes F_commute : "EQ_comp_fun_commute0_gen0 f000 all_def_set (\<lambda>x. (F:: ('\<AA>, 'a option option) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (f000 x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
     and f_fold_insert : "\<And>x A S. x \<notin> S \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow> is_int (f000 x) \<Longrightarrow> all_int_set (f000 ` S) \<Longrightarrow> Finite_Set.fold F A (insert (f000 x) (f000 ` S)) = F (f000 x) (Finite_Set.fold F A (f000 ` S))"
     and S_lift : "all_defined \<tau> S \<Longrightarrow> \<exists>S'. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = f000 ` S'"
   shows "\<lceil>\<lceil>Rep_Set_0 (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 interpret EQ_comp_fun_commute0_gen0 f000 all_def_set "\<lambda>x. F (f000 x)" by (rule F_commute)
 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set'_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(insert S_notempty)
  apply(rule S_lift[OF A_all_def[THEN spec], THEN exE], simp)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, drule sym, simp add: A_all_def', rule f_fold_insert, simp_all add: A_all_def)
  apply(subst (2) image_ident[symmetric])
   apply(rule all_int_induct)
    apply(rule all_i_set_to_def)
    apply(drule sym, simp add: A_all_def')
    apply(simp)
  apply(simp)
  apply(subst fold_insert[OF A_all_def], metis surj_pair, simp, simp)
  apply(rule notempty, rule allI, rule fold_def[simplified], simp add: A_all_def, blast+)
 done
qed

lemma iterate_notempty :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F:: ('\<AA>, _) val
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
   shows "\<lceil>\<lceil>Rep_Set_0 (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(rule iterate_notempty_gen[OF F_commute[THEN EQ_comp_fun_commute0.downgrade'] A_all_def S_notempty])
 apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], blast+)
done

lemma iterate_notempty' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
   shows "\<lceil>\<lceil>Rep_Set_0 (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(rule iterate_notempty_gen[OF F_commute[THEN EQ_comp_fun_commute0'.downgrade'] A_all_def S_notempty])
 apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], blast+)
 apply(rule S_lift, simp)
done

subsubsection{* Preservation of comp fun commute (main) *}

lemma iterate_commute' :
 assumes f_comm : "\<And>a. EQ_comp_fun_commute0' (\<lambda>x. F a (\<lambda>_. \<lfloor>x\<rfloor>))"

 assumes f_notempty : "\<And>S x y \<tau>. is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow>
            is_int (\<lambda>(_::'\<AA> st). \<lfloor>y\<rfloor>) \<Longrightarrow>
            (\<forall>(\<tau>::'\<AA> st). all_defined \<tau> S) \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            OclIterate\<^isub>S\<^isub>e\<^isub>t (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x)) (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x)) (F y) \<tau> =
            OclIterate\<^isub>S\<^isub>e\<^isub>t (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F y)) (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F y)) (F x) \<tau>"

 shows "EQ_comp_fun_commute0' (\<lambda>x S. S ->iterate(j;S=S | F x j S))"
 proof - interpret EQ_comp_fun_commute0' "\<lambda>x. F a (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm)
 apply_end(simp only: EQ_comp_fun_commute0'_def)
 apply_end(rule conjI)+ apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm], blast, simp)
 apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(subst iterate_cp_all', simp add: f_comm, simp, simp, simp)

 apply_end(rule conjI)+ apply_end(rule allI)+ apply_end(rule impI)+

 show "\<And>x S \<tau>.
        \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow>
        is_int (\<lambda>_. \<lfloor>x\<rfloor>) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x) \<tau>)\<rceil>\<rceil> \<noteq> {}"
 by(rule iterate_notempty'[OF f_comm], simp_all)

 apply_end(simp) apply_end(simp) apply_end(simp)
 apply_end(rule conjI)+ apply_end(rule allI)+
 fix x y \<tau>
 show "(\<forall>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t y y (F x))) = (is_int (\<lambda>(_:: '\<AA> st). \<lfloor>x\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  apply(rule iffI, rule conjI) apply(simp add: is_int_def OclValid_def valid_def bot_fun_def bot_option_def)
  apply(rule i_invert_all_defined'[where F = "F x"], simp)
  apply(rule allI, rule i_cons_all_def'[where F = "F x", OF f_comm], blast)
 done

 apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(rule ext, rename_tac \<tau>)
 fix S and x and y and \<tau>
 show " is_int (\<lambda>(_::'\<AA> st). \<lfloor>x\<rfloor>) \<Longrightarrow>
             is_int (\<lambda>(_::'\<AA> st). \<lfloor>y\<rfloor>) \<Longrightarrow>
             (\<forall>(\<tau>::'\<AA> st). all_defined \<tau> S) \<Longrightarrow>
             OclIterate\<^isub>S\<^isub>e\<^isub>t (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x)) (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x)) (F y) \<tau> =
             OclIterate\<^isub>S\<^isub>e\<^isub>t (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F y)) (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F y)) (F x) \<tau> "
  apply(case_tac "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = {}")
  apply(subgoal_tac "S \<tau> = Set{} \<tau>")
  prefer 2
  apply(drule_tac f = "\<lambda>s. Abs_Set_0 \<lfloor>\<lfloor>s\<rfloor>\<rfloor>" in arg_cong)
  apply(subgoal_tac "S \<tau> = Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>")
  prefer 2
  apply(metis abs_rep_simp)
  apply(simp add: mtSet_def)

  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm]) apply(rule i_cons_all_def'[OF f_comm], blast)+
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm])
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm], blast) apply(blast)
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm], blast)
  apply(simp)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm, symmetric])
   apply(subst (1 2) cp_mtSet[symmetric])
    apply(rule i_cons_all_def'[OF f_comm]) apply(simp add: mtSet_all_def)+
   apply(subst (1 2) cp_mtSet[symmetric])
    apply(rule i_cons_all_def'[OF f_comm]) apply(simp add: mtSet_all_def)+

  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm])
   apply(rule i_cons_all_def'[OF f_comm], metis surj_pair)
   apply(rule i_cons_all_def'[OF f_comm], metis surj_pair)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm])
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm]) apply(metis surj_pair)+
   apply(subst cp_all_def[symmetric])  apply(rule i_cons_all_def'[OF f_comm]) apply(metis surj_pair)+
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm, symmetric])
   apply(rule i_cons_all_def''cp[OF f_comm]) apply(metis surj_pair) apply(metis surj_pair) apply(metis surj_pair)
   apply(rule i_cons_all_def''cp[OF f_comm]) apply(metis surj_pair) apply(metis surj_pair)

  apply(rule f_notempty, simp_all)

 done
qed

subsection{* comp fun commute OclIterate and OclIncluding *}
subsubsection{* Identity *}

lemma i_including_id' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
   shows "(Finite_Set.fold (\<lambda>j r2. r2->including(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)) \<tau> = S \<tau>"
proof -
 have invert_set_0 : "\<And>x F. \<lfloor>\<lfloor>insert x F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow> \<lfloor>\<lfloor>F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(auto simp: bot_option_def null_option_def)

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done
 show "Finite_Set.fold (\<lambda>j r2. r2->including(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> = S \<tau>"
  apply(subst finite_induct[where P = "\<lambda>set. all_defined_set \<tau> set \<and> \<lfloor>\<lfloor>set\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<longrightarrow>
                                             (\<forall>(s :: ('\<AA>, _) Set). (\<forall>\<tau>. all_defined \<tau> s) \<longrightarrow>
                                                  (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set)))) \<and>
                                             (\<forall>s. (\<forall>\<tau>. all_defined \<tau> s) \<and> (set \<subseteq> \<lceil>\<lceil>Rep_Set_0 (s \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                                                  (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set)) \<tau> = s \<tau>)"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])
  apply(simp)
  defer
  apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>], frule Set_inv_lemma)
  apply(simp add: foundation18 all_defined_set_def invalid_def S_all_def[simplified all_defined_def all_defined_set'_def])
  apply (metis assms order_refl)
  apply(simp)

  (* *)
  apply(rule impI) apply(erule conjE)+
  apply(drule invert_set_0, simp del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
  apply(frule invert_all_def_set, simp del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
  apply(erule conjE)+

  (* *)
  apply(rule conjI)
  apply(rule allI, rename_tac SSS, rule impI, rule allI, rule allI)
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF _ including_commute], simp)
  apply(simp)
  apply(simp add: all_int_set_def all_defined_set_def is_int_def) apply (metis (mono_tags) foundation18')
  apply(simp)
  (* *)
  apply(rule allI, rename_tac SS, rule impI)
  apply(drule all_def_to_all_int_)+
  apply(subst EQ_comp_fun_commute.fold_insert[where f = "(\<lambda>j r2. (r2->including(j)))", OF including_commute])
  apply(metis PairE)
  apply(simp)+
  apply(rule invert_int, simp)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(simp)
  apply(subst including_id')
  apply(metis prod.exhaust)
  apply(auto)
 done
qed

lemma iterate_including_id :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     shows "(S ->iterate(j;r2=S | r2->including(j))) = S"
  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def OclValid_def del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec, rule ext)
  apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
   prefer 2
   proof -
   fix \<tau>
   show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
   apply(simp add: S_all_def[of \<tau>, simplified all_defined_def OclValid_def all_defined_set'_def]
                   foundation20[simplified OclValid_def])
   done
  apply_end(subst i_including_id', simp_all add: S_all_def)
qed

lemma i_including_id00 :
 assumes S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 ((S :: ('\<AA>, int option option) Set) \<tau>)\<rceil>\<rceil>)"
   shows "\<And>\<tau>. \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a) ; set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x) in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set') = S')"
proof -
 have S_incl : "\<forall>(x :: ('\<AA>, 'a option option) Set). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
  apply(rule allI) apply(rule impI)+
  apply(rule ext, rename_tac \<tau>)
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(simp add: mtSet_def)
 by (metis abs_rep_simp)

 have invert_set_0 : "\<And>x F. \<lfloor>\<lfloor>insert x F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow> \<lfloor>\<lfloor>F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(auto simp: bot_option_def null_option_def)

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have rec : "\<And>x (F :: '\<AA> Integer set). all_int_set F \<Longrightarrow>
            is_int x \<Longrightarrow>
            x \<notin> F \<Longrightarrow>
            \<forall>x. (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow>
                (let img = op ` (\<lambda>a \<tau>. a); set' = F; f = \<lambda>x. x
                 in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = x) \<Longrightarrow>
            \<forall>xa. (\<forall>\<tau>. all_defined \<tau> xa) \<longrightarrow>
                 (let img = op ` (\<lambda>a \<tau>. a); set' = insert x F; f = \<lambda>x. x
                  in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (xa \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = xa)"
  apply(simp only: Let_def image_ident)

  proof - fix \<tau> fix x fix F :: "'\<AA> Integer set"
   show "all_int_set F \<Longrightarrow>
            is_int x \<Longrightarrow>
            x \<notin> F \<Longrightarrow>
            \<forall>x. (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. F = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(j)) Set{} F = x \<Longrightarrow>
            \<forall>xa. (\<forall>\<tau>. all_defined \<tau> xa) \<longrightarrow> (\<forall>\<tau>. insert x F = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (xa \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(j)) Set{} (insert x F) = xa"
  apply(rule allI, rename_tac S) apply(rule impI)+
  apply(subst sym[of "insert x F"], blast)
  apply(drule_tac x = "S->excluding(x)" in allE) prefer 2 apply assumption
  apply(subgoal_tac "\<And>\<tau>. (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S->excluding(x) \<tau>)\<rceil>\<rceil> = ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) - {x}", simp only:)
  apply(subgoal_tac "(\<forall>\<tau>. all_defined \<tau> S->excluding(x))")
   prefer 2
   apply(rule allI)
   apply(rule cons_all_def_e, metis)
   apply(rule int_is_valid, simp)
  apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute]) prefer 5
  apply(drule arg_cong[where f = "\<lambda>S. (S->including(x))"], simp)
  apply(rule Ocl_insert_Diff)
   apply(metis surj_pair)
   apply(subst sym[of "insert x F"], metis surj_pair)
   apply(simp)+
   apply(subst mtSet_all_def)
   apply(simp)+
  apply(subst excluding_unfold)
  apply(metis surj_pair)
  apply(rule int_is_valid, simp)
  apply(subst image_set_diff, simp add: inject)
  apply(simp)
  apply(drule destruct_int)
    apply(frule_tac P = "\<lambda>j. x = (\<lambda>_. j)" in ex1E) prefer 2 apply assumption
  apply(blast)
  done
 qed

 fix \<tau>
 show "\<forall>S'.  (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a); set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x)  in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set') = S')"
  apply(rule allI)
  proof - fix S' :: "('\<AA>, _) Set" show "(\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = op ` (\<lambda>a \<tau>. a); set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>; f = \<lambda>x. x
           in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = S')"
   apply(simp add: Let_def, rule impI)
   apply(subgoal_tac "(let img = op ` (\<lambda>a \<tau>. a); set' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>; f = \<lambda>x. x
    in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = S')") prefer 2

   apply(subst EQ_comp_fun_commute.all_int_induct[where P = "\<lambda>set.
   \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a)
     ; set' = set ; f = (\<lambda>x. x) in
                 (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                 (Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set') = S')"
                                 and F = "(\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", OF including_commute, THEN spec, of S'])
   apply(simp add: S_all_int)
   apply(simp add: S_incl)
   apply(rule rec)
   apply(simp) apply(simp) apply(simp) apply(simp)
   apply (metis pair_collapse)
   apply(blast)

   apply(simp add: Let_def)

  done
 qed
qed

lemma iterate_including_id00 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
       and S_incl : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
     shows "(S->iterate(j;r2=Set{} | r2->including(j))) = S"
 apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def OclValid_def del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec, rule ext)
 apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq\<^isub>S\<^isub>e\<^isub>t_exec)
 prefer 2
  proof -
   have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
   by(rule all_def_to_all_int, simp add: assms)

   fix \<tau>
   show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
     apply(simp add: S_all_def[of \<tau>, simplified all_defined_def OclValid_def all_defined_set'_def]
                     foundation20[simplified OclValid_def])
  done
 fix \<tau> show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(j)) Set{} ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> = S \<tau>"
  apply(subst i_including_id00[simplified Let_def image_ident, where S = S and \<tau> = \<tau>])
   prefer 4
   apply(rule refl)
   apply(simp add: S_all_int S_all_def)+
 by (metis S_incl)
qed

subsubsection{* all defined (construction) *}

lemma preserved_defined :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "let S' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> in
          \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A S')"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 show ?thesis
  apply(subst Let_def)
  apply(rule finite_induct[where P = "\<lambda>set.
                                                let set' = (\<lambda>a \<tau>. a) ` set in
                                                all_int_set set' \<longrightarrow>
                                                (\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A set'))"
                               and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp])
  apply(simp add: S_all_def[where \<tau> = \<tau>, simplified all_defined_def all_defined_set'_def])
  apply(simp add: A_all_def)
  apply(rule impI, simp only: image_insert, rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp])
  apply(simp add: A_all_def)
  apply(simp add: including_commute)
  apply(simp)
  apply(simp)
  apply(drule invert_all_int_set, simp)

  apply(rule all_def_to_all_int[OF S_all_def])
 done
qed

subsubsection{* Preservation of comp fun commute (main) *}

lemma iterate_including_commute :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: '\<AA> st). x} Set{\<lambda>(_:: '\<AA> st). x} F->including(\<lambda>(_:: '\<AA> st). y) =
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: '\<AA> st). y} Set{\<lambda>(_:: '\<AA> st). y} F->including(\<lambda>(_:: '\<AA> st). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
            \<forall>(\<tau> :: '\<AA> st). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (OclIterate\<^isub>S\<^isub>e\<^isub>t ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: '\<AA> st). x)) ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: '\<AA> st). x)) F)->including(\<lambda>(_:: '\<AA> st). y) \<tau> =
                (OclIterate\<^isub>S\<^isub>e\<^isub>t ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: '\<AA> st). y)) ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: '\<AA> st). y)) F)->including(\<lambda>(_:: '\<AA> st). x) \<tau> "
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | F j r2)->including(\<lambda>(_:: '\<AA> st). x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)


 show ?thesis
  apply(simp only: EQ_comp_fun_commute0_def)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(subst (1 2) cp_OclIncluding, subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0]], blast, simp)
  apply(rule allI)+ apply(rule impI)+
  apply(rule including_cp_all, simp, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast)
  apply(rule iterate_cp_all, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(rule including_notempty, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: int_is_valid)
  apply(rule iterate_notempty, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+
  apply(rule iffI)
  apply(drule invert_all_defined', erule conjE, rule conjI, simp)
  apply(rule i_invert_all_defined'[where F = F], simp)
  apply(rule allI, rule cons_all_def, rule i_cons_all_def[OF f_comm], blast, simp add: int_is_valid)
  apply(rule allI)+ apply(rule impI)+

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = {}")
  apply(subgoal_tac "S \<tau> = Set{} \<tau>")
  prefer 2
  apply(drule_tac f = "\<lambda>s. Abs_Set_0 \<lfloor>\<lfloor>s\<rfloor>\<rfloor>" in arg_cong)
  apply(subgoal_tac "S \<tau> = Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>")
  prefer 2
  apply(metis abs_rep_simp)
  apply(simp add: mtSet_def)

  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0]])
   apply(rule cons_all_def') apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], blast)+ apply(simp add: int_is_valid)
   apply(rule cons_all_def') apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], blast)+ apply(simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)
  apply(subst (1 2 4 5) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0]], blast)
  apply(simp)
  apply(subst (1 2 4 5) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0], symmetric], simp add: mtSet_all_def)
  apply(simp)
  apply(subst (1 2 4 5) cp_OclIncluding[symmetric])
  apply(subst (1 2 3 4) cp_singleton, simp, simp)
  apply(subst (1 2) cp_OclIncluding[symmetric])
  apply(subst f_empty, simp_all)

  apply(rule com, simp_all)
 done
qed

lemma iterate_including_commute_var :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. (F :: '\<AA> Integer
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: '\<AA> st). x, a} Set{\<lambda>(_:: '\<AA> st). x, a} F->including(\<lambda>(_:: '\<AA> st). y) =
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: '\<AA> st). y, a} Set{\<lambda>(_:: '\<AA> st). y, a} F->including(\<lambda>(_:: '\<AA> st). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
            \<forall>(\<tau> :: '\<AA> st). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (OclIterate\<^isub>S\<^isub>e\<^isub>t (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). x)) (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). x)) F)->including(\<lambda>(_:: '\<AA> st). y) \<tau> =
                (OclIterate\<^isub>S\<^isub>e\<^isub>t (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). y)) (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). y)) F)->including(\<lambda>(_:: '\<AA> st). x) \<tau> "
     and a_int : "is_int a"
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. (((r1 ->iterate(j;r2=r1 | F j r2))->including(a))->including(\<lambda>(_:: '\<AA> st). x)))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(simp only: EQ_comp_fun_commute0_def)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(subst (1 2) cp_OclIncluding, subst (1 2 3 4) cp_OclIncluding, subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0]], blast, simp)
  apply(rule allI)+ apply(rule impI)+
  apply(rule including_cp_all, simp, rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid)
  apply(rule including_cp_all, simp add: a_int, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid)
  apply(rule iterate_cp_all, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(rule including_notempty, rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: a_int int_is_valid)
  apply(rule iterate_notempty, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+
  apply(rule iffI)
  apply(drule invert_all_defined', erule conjE, rule conjI, simp)
  apply(rule destruct_int[OF a_int, THEN ex1_implies_ex, THEN exE], rename_tac a', simp only:)
  apply(drule invert_all_defined', erule conjE)
  apply(rule i_invert_all_defined'[where F = F], simp)
  apply(rule allI, rule cons_all_def, rule cons_all_def, rule i_cons_all_def[OF f_comm], blast) apply(simp add: int_is_valid a_int)+
  apply((rule allI)+, (rule impI)+)+

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = {}")
  apply(subgoal_tac "S \<tau> = Set{} \<tau>")
  prefer 2
  apply(drule_tac f = "\<lambda>s. Abs_Set_0 \<lfloor>\<lfloor>s\<rfloor>\<rfloor>" in arg_cong)
  apply(subgoal_tac "S \<tau> = Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>")
  prefer 2
  apply (metis abs_rep_simp prod.exhaust)
  apply(simp add: mtSet_def)


  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2 3 4) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0]])
   apply(rule cons_all_def')+ apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], metis surj_pair) apply(simp add: a_int int_is_valid)+
   apply(rule cons_all_def')+ apply(rule i_cons_all_def'[where F = F, OF f_comm[THEN c0'_of_c0]], metis surj_pair) apply(simp add: a_int int_is_valid)+
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8 9 10 11 12) cp_OclIncluding)

  apply(subst (1 2 4 5) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0]], metis surj_pair)
  apply(simp)
  apply(subst (1 2 4 5) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF f_comm[THEN c0'_of_c0], symmetric], simp add: mtSet_all_def)
  apply(simp)
  apply(subst (1 2 3 4 7 8 9 10) cp_OclIncluding[symmetric])
  apply(subst (1 2 3 4) cp_doubleton, simp, simp add: a_int, simp)
  apply(subst (1 2 3 4) cp_OclIncluding[symmetric])

  apply(subst (3 6) including_swap)
  apply(rule allI, rule all_defined1, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule mtSet_all_def) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int)
  apply(rule allI, rule all_defined1, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule mtSet_all_def) apply(simp add: int_is_valid a_int)+
  apply(rule including_subst_set'')
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule mtSet_all_def) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int)
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule mtSet_all_def) apply(simp add: int_is_valid a_int)+

  apply(subst f_empty, simp_all)

  apply(subst (3 6) including_swap)
  apply(rule allI, rule all_defined1, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule i_cons_all_def, simp add: f_comm, metis surj_pair) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int)
  apply(rule allI, rule all_defined1, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule i_cons_all_def, simp add: f_comm, metis surj_pair) apply(simp add: int_is_valid a_int)+
  apply(rule including_subst_set'')
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule i_cons_all_def, simp add: f_comm, metis surj_pair) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int) apply(simp add: int_is_valid a_int)
  apply(rule all_defined1, rule cons_all_def, rule i_cons_all_def, simp add: f_comm) apply(rule cons_all_def)+ apply(rule i_cons_all_def, simp add: f_comm, metis surj_pair) apply(simp add: int_is_valid a_int)+

  apply(rule com, simp_all)
 done
qed

subsubsection{* Execution (OclIterate, OclIncluding to OclExcluding) *}

lemma EQ_OclIterate\<^isub>S\<^isub>e\<^isub>t_including:
 assumes S_all_int: "\<And>(\<tau>::'\<AA> st). all_int_set ((\<lambda> a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 assumes S_all_def:    "\<And>\<tau>. all_defined \<tau> S"
 and     A_all_def:    "\<And>\<tau>. all_defined \<tau> A"
 and     F_commute:   "EQ_comp_fun_commute F"
 and     a_int : "is_int a"
 shows   "((S->including(a))->iterate(a; x =     A | F a x)) =
          ((S->excluding(a))->iterate(a; x = F a A | F a x))"
proof -

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have F_cp : "\<And> x y \<tau>. F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
  proof - interpret EQ_comp_fun_commute F by (rule F_commute) fix x y \<tau> show "F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
   by(rule F_cp)
 qed

 have F_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> (F a A)"
  proof - interpret EQ_comp_fun_commute F by (rule F_commute) fix \<tau> show "\<tau> \<Turnstile> \<upsilon> (F a A)"
  apply(insert
    all_def
    int_is_valid[OF a_int]
    A_all_def, simp add: all_defined1 foundation20)
  done
 qed

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 have insert_in_Set_0 : "\<And>\<tau>. ?this \<tau>"
  apply(rule insert_in_Set_0)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 have insert_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set_0_def null_Set_0_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set_0_inject)
  apply(rule insert_in_Set_0, simp_all add: bot_option_def)

  apply(subst Abs_Set_0_inject)
  apply(rule insert_in_Set_0, simp_all add: null_option_def bot_option_def)
 done
 have insert_defined : "\<And>\<tau>. ?this \<tau>"
  apply(rule insert_defined)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 have remove_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have remove_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
  proof - fix \<tau> show "?thesis \<tau>"
   apply(insert S_all_int[of \<tau>], simp add: all_int_set_def, rule remove_finite)
   apply(erule conjE, drule finite_imageD)
   apply (metis inj_onI, simp)
  done
 qed

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: foundation18 invalid_def)
 done
 have remove_in_Set_0 : "\<And>\<tau>. ?this \<tau>"
  apply(rule remove_in_Set_0)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 have remove_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set_0_def null_Set_0_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set_0_inject)
  apply(rule remove_in_Set_0, simp_all add: bot_option_def)

  apply(subst Abs_Set_0_inject)
  apply(rule remove_in_Set_0, simp_all add: null_option_def bot_option_def)
 done
 have remove_defined : "\<And>\<tau>. ?this \<tau>"
  apply(rule remove_defined)
 by(simp add: S_all_def[simplified all_defined_def] int_is_valid[OF a_int])+

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  proof - fix \<tau> show "OclIterate\<^isub>S\<^isub>e\<^isub>t S->including(a) A F \<tau> = OclIterate\<^isub>S\<^isub>e\<^isub>t S->excluding(a) (F a A) F \<tau>"
   apply(simp only: cp_OclIterate\<^isub>S\<^isub>e\<^isub>t[of "S->including(a)"] cp_OclIterate\<^isub>S\<^isub>e\<^isub>t[of "S->excluding(a)"])
   apply(subst OclIncluding_def, subst OclExcluding_def)

   apply(simp add: S_all_def[simplified all_defined_def OclValid_def] int_is_valid[OF a_int, simplified OclValid_def])

   apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
   apply(simp add: Abs_Set_0_inverse[OF insert_in_Set_0] Abs_Set_0_inverse[OF remove_in_Set_0]
                   foundation20[OF all_defined1[OF A_all_def], simplified OclValid_def]
                   S_all_def[simplified all_defined_def all_defined_set_def]
                   insert_defined
                   remove_defined
                   F_val[of \<tau>, simplified OclValid_def])

   apply(subst EQ_comp_fun_commute.fold_fun_comm[where f = F and z = A and x = a and A = "((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))", symmetric, OF F_commute A_all_def _ int_is_valid[OF a_int]])
   apply(simp add: remove_all_int)

   apply(subst image_set_diff[OF inject], simp)
   apply(subgoal_tac "Finite_Set.fold F A (insert (\<lambda>\<tau>'. a \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)) \<tau> =
       F (\<lambda>\<tau>'. a \<tau>) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {\<lambda>\<tau>'. a \<tau>})) \<tau>")
   apply(subst F_cp)
   apply(simp)

   apply(subst EQ_comp_fun_commute.fold_insert_remove[OF F_commute A_all_def S_all_int])
   apply (metis (mono_tags) a_int foundation18' is_int_def)
   apply(simp)
  done
 qed
qed

subsubsection{* Execution OclIncluding out of OclIterate (theorem) *}

lemma including_out1 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: ('\<AA>, _) Set)->iterate(x;acc=A | acc->including(x)->including(i))) \<tau> = (S->iterate(x;acc=A | acc->including(x))->including(i)) \<tau>"
proof -

 have i_valid : "\<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i"
 by (metis i_int int_is_valid)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)


 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done


 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)


 have invert_all_defined_fold : "\<And> F x a b. let F' = (\<lambda>a \<tau>. a) ` F in x \<notin> F \<longrightarrow> all_int_set (insert (\<lambda>\<tau>. x) F') \<longrightarrow> all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A (insert (\<lambda>\<tau>. x) F')) \<longrightarrow>
               all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A F')"
 proof - fix F x a b show "?thesis F x a b"
  apply(simp add: Let_def) apply(rule impI)+
  apply(insert arg_cong[where f = "\<lambda>x. all_defined (a, b) x", OF EQ_comp_fun_commute.fold_insert[OF including_commute, where x= "(\<lambda>\<tau>. x)" and A = "(\<lambda>a \<tau>. a) ` F" and z = A]]
               allI[where P = "\<lambda>x. all_defined x A", OF A_all_def])
  apply(simp)
  apply(subgoal_tac "all_int_set ((\<lambda>a \<tau>. a) ` F)")
  prefer 2
  apply(simp add: all_int_set_def, auto)
  apply(drule invert_int, simp)
  apply(subgoal_tac "(\<lambda>(\<tau>:: '\<AA> st). x) \<notin> (\<lambda>a (\<tau>:: '\<AA> st). a) ` F")
  prefer 2
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)

  apply(simp)
  apply(rule invert_all_defined[THEN conjunct2, of _ _ "\<lambda>\<tau>. x"], simp)
  done
 qed

 have i_out : "\<And>i' x F. i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
          (((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A
            ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))->including(i) =
           (((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))"
 proof - fix i' x F show "i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow> ?thesis i' x F"
  apply(simp)
  apply(subst including_id[where S = "((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(\<lambda>_. i')"])
  apply(rule cons_all_def)+
  apply(case_tac \<tau>'', simp)
  apply (metis (no_types) foundation18' is_int_def)
  apply(insert i_int, simp add: is_int_def)
  apply (metis (no_types) foundation18')
  apply(rule allI)
  proof - fix \<tau> show "is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
                      i' \<in> \<lceil>\<lceil>Rep_Set_0 ((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x)->including(\<lambda>_. i') \<tau>)\<rceil>\<rceil>"
   apply(insert including_charn1[where X = "(Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x)" and x = "\<lambda>_. i'" and \<tau> = \<tau>])
   apply(subgoal_tac "\<tau> \<Turnstile> \<delta> Finite_Set.fold (\<lambda>j r2. r2->including(j)) A ((\<lambda>a \<tau>. a) ` F)->including(\<lambda>\<tau>. x)")
    prefer 2
    apply(rule all_defined1, rule cons_all_def, metis surj_pair)
    apply(simp add: int_is_valid)
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. i')")
    prefer 2
    apply(drule int_is_valid[where \<tau> = \<tau>], simp add: foundation20)
   apply(simp)

   apply(simp add: OclIncludes_def OclValid_def)
   apply(subgoal_tac "(\<delta> Finite_Set.fold (\<lambda>j r2. r2->including(j)) A ((\<lambda>a \<tau>. a) ` F) and \<upsilon> (\<lambda>\<tau>. x) and \<upsilon> (\<lambda>_. i')) \<tau> = true \<tau>")
   apply (metis option.inject true_def)
   by (metis OclValid_def foundation10 foundation6)
  qed simp_all
 qed

 have i_out1 : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
        Finite_Set.fold (\<lambda>x acc. (acc->including(x))->including(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) =
        (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))->including(i)"
 proof - fix \<tau> show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
         Finite_Set.fold (\<lambda>x acc. (acc->including(x))->including(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) =
         (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))->including(i)"
  apply(subst finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. a) ` set
                                               ; fold_set = Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A set' in
                                               (\<forall>\<tau>. all_defined \<tau> fold_set) \<and>
                                               set' \<noteq> {} \<longrightarrow>
                                               all_int_set set' \<longrightarrow>
                                               (Finite_Set.fold (\<lambda>x acc. (acc->including(x))->including(i)) A set') =
                                               (fold_set->including(i))"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def])
  apply(simp add: S_finite)
  apply(simp)
  defer

  apply(subst preserved_defined[where \<tau> = \<tau>, simplified Let_def])
  apply(simp add: S_all_def)
  apply(simp add: A_all_def)
  apply(simp)

  apply(rule all_def_to_all_int, simp add: S_all_def)
  apply(simp add: cp_OclIncluding[of _ i])

  (* *)
  apply(rule impI)+ apply(erule conjE)+
  apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute])
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute2])
  apply(simp add: i_int)
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subgoal_tac "(\<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)))")
  prefer 2
  apply(rule allI) apply(erule_tac x = a in allE)
  apply(rule allI) apply(erule_tac x = b in allE)
  apply(simp add: invert_all_defined_fold[simplified Let_def, THEN mp, THEN mp, THEN mp])

  apply(simp)

  (* *)
  apply(case_tac "F = {}", simp)
  apply(simp add: all_int_set_def)
  apply(subst including_swap)
  apply(rule allI, rule all_defined1) apply (metis PairE)
  apply(rule allI)
  apply(simp add: i_valid foundation20)
  apply(simp add: is_int_def)
  apply(insert destruct_int[OF i_int])
  apply(frule ex1E) prefer 2 apply assumption
  apply(rename_tac i')

  proof -
   fix x F i'
    show "i = (\<lambda>_. i') \<Longrightarrow>
          is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow>
          \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
     (((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))->including(i) =
                ((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i)"
    apply(rule i_out[where i' = i' and x = x and F = F], simp_all)
    done
   apply_end assumption
   apply_end(blast)+
  qed
 qed simp

 show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def] all_defined1[OF S_all_def, simplified OclValid_def] all_defined1[OF A_all_def, THEN foundation20, simplified OclValid_def])
  apply(drule i_out1)
  apply(simp add: cp_OclIncluding[of _ i])
 done
qed

lemma including_out2 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     and x0_int : "is_int x0"
     shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A | acc->including(x0)->including(x)->including(i))) \<tau> = (S->iterate(x;acc=A | acc->including(x0)->including(x))->including(i)) \<tau>"
proof -
 have x0_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x0" apply(insert x0_int[simplified is_int_def]) by (metis foundation18')
 have i_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> i" apply(insert i_int[simplified is_int_def]) by (metis foundation18')

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have init_out1 : "(S->iterate(x;acc=A | acc->including(x0)->including(x)->including(i))) = (S->iterate(x;acc=A | acc->including(x)->including(x0)->including(i)))"
  apply(rule iterate_subst_set[OF S_all_def A_all_def including_commute4 including_commute5])
  apply(simp add: x0_int i_int)+
  apply(rule including_subst_set)
  apply(rule including_swap)
  apply(simp add: all_defined_def x0_val)+
 done

 have init_out2 : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A | acc->including(x0)->including(x))->including(i)) \<tau> = (S->iterate(x;acc=A | acc->including(x))->including(x0)->including(i)) \<tau>"
  apply(rule including_subst_set'') prefer 4
  apply(simp add: including_out1[OF S_all_def A_all_def x0_int, symmetric])
  apply(subst iterate_subst_set[OF S_all_def A_all_def including_commute3 including_commute2])
  apply(simp add: x0_int)+ apply(rule x0_int)
  apply(rule including_swap)
  apply(simp add: all_defined_def x0_val)+
  (* *)
  apply(rule all_defined1)
  apply(rule i_cons_all_def'') apply(rule including_commute3[THEN c0_of_c, THEN c0'_of_c0], simp add: x0_int, simp add: S_all_def, simp add: A_all_def)
  apply(rule all_defined1)
  apply(rule cons_all_def)
  apply(rule i_cons_all_def'') apply(rule including_commute[THEN c0_of_c, THEN c0'_of_c0], simp add: x0_int, simp add: S_all_def, simp add: A_all_def, simp add: int_is_valid[OF x0_int])
  apply(simp add: int_is_valid[OF i_int])
 done

 have i_valid : "\<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i"
 by (metis i_int int_is_valid)


 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set'_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have invert_all_def_set : "\<And>x F \<tau>. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)


 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done


 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)


 have invert_all_defined_fold : "\<And> F x a b. let F' = (\<lambda>a \<tau>. a) ` F in x \<notin> F \<longrightarrow> all_int_set (insert (\<lambda>\<tau>. x) F') \<longrightarrow> all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A (insert (\<lambda>\<tau>. x) F')) \<longrightarrow>
               all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A F')"
 proof - fix F x a b show "?thesis F x a b"
  apply(simp add: Let_def) apply(rule impI)+
  apply(insert arg_cong[where f = "\<lambda>x. all_defined (a, b) x", OF EQ_comp_fun_commute.fold_insert[OF including_commute, where x= "(\<lambda>\<tau>. x)" and A = "(\<lambda>a \<tau>. a) ` F" and z = A]]
               allI[where P = "\<lambda>x. all_defined x A", OF A_all_def])
  apply(simp)
  apply(subgoal_tac "all_int_set ((\<lambda>a \<tau>. a) ` F)")
  prefer 2
  apply(simp add: all_int_set_def, auto)
  apply(drule invert_int, simp)
  apply(subgoal_tac "(\<lambda>(\<tau>:: '\<AA> st). x) \<notin> (\<lambda>a (\<tau>:: '\<AA> st). a) ` F")
  prefer 2
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)

  apply(simp)
  apply(rule invert_all_defined[THEN conjunct2, of _ _ "\<lambda>\<tau>. x"], simp)
  done
 qed

 have i_out : "\<And>i i' x F. is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
          (((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A
            ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))->including(i) =
           (((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))"
 proof - fix i i' x F show "is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow> ?thesis i i' x F"
  apply(simp)
  apply(subst including_id[where S = "((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(\<lambda>_. i')"])
  apply(rule cons_all_def)+
  apply(case_tac \<tau>'', simp)
  apply (metis (no_types) foundation18' is_int_def)
  apply(simp add: is_int_def)
  apply (metis (no_types) foundation18')
  apply(rule allI)
  proof - fix \<tau> show "is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
                      i' \<in> \<lceil>\<lceil>Rep_Set_0 ((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x)->including(\<lambda>_. i') \<tau>)\<rceil>\<rceil>"
   apply(insert including_charn1[where X = "(Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x)" and x = "\<lambda>_. i'" and \<tau> = \<tau>])
   apply(subgoal_tac "\<tau> \<Turnstile> \<delta> Finite_Set.fold (\<lambda>j r2. r2->including(j)) A ((\<lambda>a \<tau>. a) ` F)->including(\<lambda>\<tau>. x)")
    prefer 2
    apply(rule all_defined1, rule cons_all_def, metis surj_pair)
    apply(simp add: int_is_valid)
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. i')")
    prefer 2
    apply(drule int_is_valid[where \<tau> = \<tau>], simp add: foundation20)
   apply(simp)

   apply(simp add: OclIncludes_def OclValid_def)
   apply(subgoal_tac "(\<delta> Finite_Set.fold (\<lambda>j r2. r2->including(j)) A ((\<lambda>a \<tau>. a) ` F) and \<upsilon> (\<lambda>\<tau>. x) and \<upsilon> (\<lambda>_. i')) \<tau> = true \<tau>")
   apply (metis option.inject true_def)
   by (metis OclValid_def foundation10 foundation6)
  qed simp_all
 qed

 have destruct3 : "\<And>A B C \<tau>. (\<tau> \<Turnstile> A) \<and> (\<tau> \<Turnstile> B) \<and> (\<tau> \<Turnstile> C) \<Longrightarrow> (\<tau> \<Turnstile> (A and B and C))"
 by (metis foundation10 foundation6)

 have i_out1 : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
        Finite_Set.fold (\<lambda>x acc. (acc->including(x))->including(x0)->including(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) =
        (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))->including(x0)->including(i)"
 proof - fix \<tau> show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
         Finite_Set.fold (\<lambda>x acc. (acc->including(x))->including(x0)->including(i)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) =
         (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))->including(x0)->including(i)"
  apply(subst finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. a) ` set
                                               ; fold_set = Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A set' in
                                               (\<forall>\<tau>. all_defined \<tau> fold_set) \<and>
                                               set' \<noteq> {} \<longrightarrow>
                                               all_int_set set' \<longrightarrow>
                                               (Finite_Set.fold (\<lambda>x acc. (acc->including(x))->including(x0)->including(i)) A set') =
                                               (fold_set->including(x0)->including(i))"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def])
  apply(simp add: S_finite)
  apply(simp)
  defer

  apply(subst preserved_defined[where \<tau> = \<tau>, simplified Let_def])
  apply(simp add: S_all_def)
  apply(simp add: A_all_def)
  apply(simp)

  apply(rule all_def_to_all_int, simp add: S_all_def)
  apply(simp add: cp_OclIncluding[of _ i])

  (* *)
  apply(rule impI)+ apply(erule conjE)+
  apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute])
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst EQ_comp_fun_commute.fold_insert[OF including_commute5])
  apply(simp add: i_int)
  apply(simp add: x0_int)
  apply(simp add: A_all_def)
  apply(simp add: all_int_set_def)
  apply(simp add: invert_int)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subgoal_tac "(\<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)))")
  prefer 2
  apply(rule allI) apply(erule_tac x = a in allE)
  apply(rule allI) apply(erule_tac x = b in allE)
  apply(simp add: invert_all_defined_fold[simplified Let_def, THEN mp, THEN mp, THEN mp])

  apply(simp)

  (* *)
  apply(case_tac "F = {}", simp)
  apply(simp add: all_int_set_def)

  apply(subgoal_tac "((((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A ((\<lambda>a \<tau>. a) ` F)->including(x0))->including(i))->including(\<lambda>\<tau>. x))->including(x0))->including(i) =
                     (((((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A ((\<lambda>a \<tau>. a) ` F)->including(\<lambda>\<tau>. x))->including(x0))->including(x0))->including(i))->including(i))")
   prefer 2
   apply(rule including_subst_set)
   apply(rule sym)
   apply(subst including_swap[where i = x0 and j = "i"]) prefer 4
   apply(rule including_subst_set)
    apply(subst including_swap[where j = "x0"]) prefer 4
    apply(rule including_swap) prefer 4

    apply(rule allI, rule all_defined1) apply (metis PairE)
    apply(rule allI, rule all_defined1) apply(rule cons_all_def) apply (metis PairE)
   apply(simp_all add: i_valid x0_val int_is_valid)
   apply(rule allI, rule allI, rule destruct3)
   apply(rule conjI, rule all_defined1) apply(simp)
   apply(simp add: int_is_valid x0_val)
  (* *)

  apply(insert destruct_int[OF i_int])
  apply(frule_tac P = "\<lambda>j. i = (\<lambda>_. j)" in ex1E) prefer 2 apply assumption
  apply(rename_tac i')

  apply(insert destruct_int[OF x0_int])
  apply(frule_tac P = "\<lambda>j. x0 = (\<lambda>_. j)" in ex1E) prefer 2 apply assumption
  apply(rename_tac x0')

  proof -
   fix x F i' x0'
    show "i = (\<lambda>_. i') \<Longrightarrow>
          x0 = (\<lambda>_. x0') \<Longrightarrow>
          is_int (\<lambda>(\<tau>:: '\<AA> st). x) \<Longrightarrow>
          \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
     (((((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(x0))->including(x0))->including(i))->including(i) =
                (((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(x0))->including(i)"
    apply(subst i_out[where i' = x0' and x = x and F = F, OF x0_int])
    apply(simp) apply(simp) apply(simp)
    apply(subst including_swap[where i = x0 and j = i]) prefer 4
    apply(subst including_swap[where i = x0 and j = i]) prefer 4
    apply(subst including_swap[where i = x0 and j = i]) prefer 4
    apply(rule including_subst_set)
    apply(rule i_out[where i' = i' and x = x and F = F, OF i_int], simp)
    apply(simp) apply(simp)

  apply(rule allI, rule all_defined1) apply(rule cons_all_def) apply (metis PairE)
  apply (simp add: int_is_valid)
  apply(simp add: i_valid x0_val)+
  apply(insert x0_val, simp)
  apply(insert i_valid, simp)

  apply(rule allI, rule all_defined1) apply(rule cons_all_def)+ apply (metis PairE)
  apply (simp add: int_is_valid)
  apply(simp add: i_valid x0_val)+
  by (metis prod.exhaust)
   apply_end assumption
   apply_end assumption
   apply_end(blast)
   apply_end(blast)
  qed
 qed simp

 show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(simp only: init_out1, subst init_out2, simp)
  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set'_def] all_defined1[OF S_all_def, simplified OclValid_def] all_defined1[OF A_all_def, THEN foundation20, simplified OclValid_def])
  apply(simp add: i_out1)
  apply(simp add: cp_OclIncluding[of _ i] cp_OclIncluding[of _ x0])
 done
qed


lemma including_out0 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
       and S_include : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
       and S_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
       and a_int : "is_int a"
     shows "(S->iterate(x;acc=Set{a} | acc->including(x))) = (S->including(a))"

 apply(rule ex1E[OF destruct_int[OF a_int]], rename_tac a', simp)
 apply(case_tac "\<forall>\<tau>. a' \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>")
proof -
 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have a_all_def : "\<And>\<tau>. all_defined \<tau> Set{a}"
 by(rule cons_all_def, rule mtSet_all_def, simp add: int_is_valid[OF a_int])

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have Sa_include : "\<And>a' \<tau> \<tau>'. (\<lambda>_. a') = a \<Longrightarrow> S->including(a) \<tau> = S->including(a) \<tau>'"
 apply(simp add: cp_OclIncluding[of _ a])
 apply(drule sym[of _ a], simp add: cp_OclIncluding[symmetric])
  proof - fix a' \<tau> \<tau>' show "a = (\<lambda>_. a') \<Longrightarrow> \<lambda>_. S \<tau>->including(\<lambda>_. a') \<tau> = \<lambda>_. S \<tau>'->including(\<lambda>_. a') \<tau>'"
   apply(simp add: OclIncluding_def)
   apply(drule sym[of a])
   apply(simp add: cp_defined[symmetric])
   apply(simp add: all_defined1[OF S_all_def, simplified OclValid_def] int_is_valid[OF a_int, simplified OclValid_def])
   apply(subst S_include[of \<tau> \<tau>'], simp)
  done
 qed

 have gen_all : "\<And>a. \<exists> \<tau>. a \<notin> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<forall> \<tau>. a \<notin> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
  apply(rule allI)
  apply(drule exE) prefer 2 apply assumption
 by(subst S_include, simp)

 fix a' show "a = (\<lambda>_. a') \<Longrightarrow> \<forall>\<tau>. a' \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> (S ->iterate(x;acc=Set{\<lambda>_. a'} | acc->including(x))) = S->including(\<lambda>_. a')"
  apply(subst including_id[OF S_all_def, symmetric], simp)
  apply(drule sym[of a], simp)
  apply(subst EQ_OclIterate\<^isub>S\<^isub>e\<^isub>t_including[where a = a and A = "Set{a}" and F = "\<lambda>a A. (A->including(a))", simplified flatten_int[OF a_int], OF S_all_int S_all_def a_all_def including_commute a_int])
  apply(subst EQ_OclIterate\<^isub>S\<^isub>e\<^isub>t_including[where a = a and A = "Set{}" and F = "\<lambda>a A. (A->including(a))", symmetric, OF S_all_int S_all_def mtSet_all_def including_commute a_int])
  apply(rule iterate_including_id00)
  apply(rule cons_all_def, simp_all add: S_all_def int_is_valid[OF a_int])
  apply(simp add: Sa_include)
 done
 apply_end simp_all

 fix a'
 show "a = (\<lambda>_. a') \<Longrightarrow>
         \<forall>y. (\<lambda>_. a') = (\<lambda>_. y) \<longrightarrow> y = a' \<Longrightarrow> \<exists>a b. a' \<notin> \<lceil>\<lceil>Rep_Set_0 (S (a, b))\<rceil>\<rceil> \<Longrightarrow> (S ->iterate(x;acc=Set{\<lambda>_. a'} | acc->including(x))) = S->including(\<lambda>_. a')"
  apply(drule gen_all[simplified])
  apply(subst excluding_id[OF S_all_def, symmetric])
  prefer 2 apply (simp)
  apply(drule sym[of a], simp add: a_int)
  apply(drule sym[of a], simp)
  apply(subst EQ_OclIterate\<^isub>S\<^isub>e\<^isub>t_including[where a = a and A = "Set{}" and F = "\<lambda>a A. (A->including(a))", symmetric, OF S_all_int S_all_def mtSet_all_def including_commute a_int])
  apply(rule iterate_including_id00)
  apply(rule cons_all_def, simp_all add: S_all_def int_is_valid[OF a_int])
  apply(simp add: Sa_include)
 done
 apply_end simp_all
qed

subsubsection{* Execution OclIncluding out of OclIterate (corollary) *}

lemma iterate_including_id_out :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(a)->including(j))) \<tau> = S->including(a) \<tau>"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
 apply(subst iterate_subst_set0[where G = "\<lambda>j r2. r2->including(j)->including(a)"])
  apply(simp add: S_def)
  apply(rule including_commute3[THEN c0_of_c], simp add: a_int)
  apply(rule including_commute2[THEN c0_of_c], simp add: a_int)
  apply(rule including_swap)
  apply (metis (hide_lams, no_types) all_defined1)
  apply(simp add: a_int int_is_valid)+
  apply(subst including_out1) apply(simp add: S_def a_int)+
  apply(subst iterate_including_id, simp add: S_def, simp)
done
qed

lemma iterate_including_id_out' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(j)->including(a))) \<tau> = S->including(a) \<tau>"
  apply(subst including_out1) apply(simp add: S_def a_int)+
  apply(subst iterate_including_id, simp add: S_def, simp)
done

lemma iterate_including_id_out'''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(a)->including(j)->including(b))) \<tau> = S->including(a)->including(b) \<tau>"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(subst including_out2) apply(simp add: S_def a_int b_int)+
  apply(rule including_subst_set'')
  apply(rule all_defined1, rule i_cons_all_def, rule including_commute3[THEN c0_of_c], simp add: a_int, simp add: S_def)
  apply(rule all_defined1, rule cons_all_def, simp add: S_def, simp add: int_is_valid[OF a_int], simp add: int_is_valid[OF b_int])

  apply(rule iterate_including_id_out) apply(simp add: S_def a_int)+
 done
qed

lemma iterate_including_id_out''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(a)->including(b)->including(j))) \<tau> = S->including(a)->including(b) \<tau>"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
show "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
 apply(subst iterate_subst_set0[where G = "\<lambda>j r2. r2->including(a)->including(j)->including(b)"])
  apply(simp add: S_def)
  apply(rule including_commute6[THEN c0_of_c], simp add: a_int, simp add: b_int)
  apply(rule including_commute4[THEN c0_of_c], simp add: a_int, simp add: b_int)
  apply(rule including_swap)
  apply(rule allI, rule all_defined1, rule cons_all_def', blast, simp add: int_is_valid[OF a_int], simp add: int_is_valid[OF b_int], simp)
 apply(rule iterate_including_id_out'''') apply(simp add: S_def a_int b_int)+
done
qed

subsection{* Conclusion *}

lemma GogollasChallenge_on_sets:
      "\<tau> \<Turnstile> (Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j)))) \<doteq> Set{\<zero>, \<six>, \<eight>, \<nine>}"
proof -
 have all_defined_68 : "\<And>\<tau>. all_defined \<tau> Set{\<six>, \<eight>}"
   apply(rule cons_all_def)+
   apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set_0_inverse mtSet_defined[simplified mtSet_def])
   apply(simp)+
 done
 have all_defined_9 : "\<And>\<tau>. all_defined \<tau> Set{\<nine>}"
   apply(rule cons_all_def)+
   apply(simp add: all_defined_def all_defined_set'_def mtSet_def Abs_Set_0_inverse mtSet_defined[simplified mtSet_def])
   apply(simp)+
 done

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have OclInt0_int : "is_int \<zero>" by (metis StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' foundation1 is_int_def null_non_OclInt0 OclInt0_def valid4)
 have OclInt6_int : "is_int \<six>" by (metis StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' foundation1 is_int_def null_non_OclInt6 OclInt6_def valid4)
 have OclInt8_int : "is_int \<eight>" by (metis StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' foundation1 is_int_def null_non_OclInt8 OclInt8_def valid4)
 have OclInt9_int : "is_int \<nine>" by (metis StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' foundation1 is_int_def null_non_OclInt9 OclInt9_def valid4)

 have commute8: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(x))" apply(rule including_commute3) by (simp add: OclInt0_int)
 have commute7: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(x)->including(\<zero>))" apply(rule including_commute2) by (simp add: OclInt0_int)
 have commute4: "\<And>x acc. is_int x \<Longrightarrow> EQ_comp_fun_commute (\<lambda>xa acc. acc->including(\<zero>)->including(xa)->including(x))" apply(rule including_commute4) by(simp add: OclInt0_int, blast)
 have commute3: "\<And>x acc. is_int x \<Longrightarrow> EQ_comp_fun_commute (\<lambda>xa acc. acc->including(\<zero>)->including(x)->including(xa))" apply(rule including_commute6) by(simp add: OclInt0_int, blast)

 have swap1 : "\<And>(S:: ('\<AA>, _) Set) y x.
              is_int x \<Longrightarrow>
              is_int y \<Longrightarrow>
              \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow>
                   ((((S->including(\<zero>))->including(x))->including(\<zero>))->including(y)) =
                   ((((S->including(\<zero>))->including(y))->including(\<zero>))->including(x))"
  apply(subst (2 5) including_swap)
  apply(rule allI, rule all_defined1, rule cons_all_def, blast)
  apply(simp, simp add: int_is_valid)+
  apply(rule including_swap)
  apply(rule allI, rule all_defined1)
  apply(rule cons_all_def)+ apply(blast)
  apply(simp, simp add: int_is_valid)+
 done

 have commute5: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(\<lambda>(_:: '\<AA> st). x))"
  apply(rule iterate_including_commute, rule commute8[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst iterate_including_id_out)
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  apply(rule sym, subst cp_OclIncluding)
  apply(subst iterate_including_id_out)
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  (* *)
   apply(subst including_swap)
    apply (metis (hide_lams, no_types) foundation1 mtSet_defined)
    apply(simp add: int_is_valid)
    apply(simp)
   apply(rule sym)
   apply(subst including_swap)
    apply (metis (hide_lams, no_types) foundation1 mtSet_defined)
    apply(simp add: int_is_valid)
    apply(simp)
   apply(subst (1 2) cp_OclIncluding[symmetric])
   apply(rule including_swap')
   apply(simp add: int_is_valid) apply(simp add: int_is_valid) apply(simp add: int_is_valid)

  (* *)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF including_commute3[THEN c0_of_c, THEN c0'_of_c0]], simp add: OclInt0_int)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute3[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute3[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)

  apply(subst (1 2 3 4 5) iterate_including_id_out)

  apply(metis surj_pair, simp add: OclInt0_int, simp)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule i_cons_all_def, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)

  apply(rule including_notempty)
  apply(rule all_defined1, rule cp_all_def[THEN iffD1], rule i_cons_all_def, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(rule iterate_notempty, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1) apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)

  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute6: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(\<lambda>(_:: '\<AA> st). x))"
  apply(rule iterate_including_commute, rule commute7[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst iterate_including_id_out')
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  apply(rule sym, subst cp_OclIncluding)
  apply(subst iterate_including_id_out')
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: OclInt0_int)
   apply (metis including_notempty' is_int_def)
  (* *)
   apply(subst including_swap)
    apply (metis (hide_lams, no_types) foundation1 mtSet_defined)
    apply(simp add: int_is_valid)
    apply(simp)
   apply(rule sym)
   apply(subst including_swap)
    apply (metis (hide_lams, no_types) foundation1 mtSet_defined)
    apply(simp add: int_is_valid)
    apply(simp)
   apply(subst (1 2) cp_OclIncluding[symmetric])
   apply(rule including_swap')
   apply(simp add: int_is_valid) apply(simp add: int_is_valid) apply(simp add: int_is_valid)
  (* *)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1[OF including_commute2[THEN c0_of_c, THEN c0'_of_c0]], simp add: OclInt0_int)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
   apply(rule cons_all_def') apply(rule i_cons_all_def) apply(rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast, simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)

  apply(subst (1 2 3 4 5) iterate_including_id_out')

  apply(metis surj_pair, simp add: OclInt0_int, simp)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule i_cons_all_def, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)

  apply(rule including_notempty)
  apply(rule all_defined1, rule cp_all_def[THEN iffD1], rule i_cons_all_def, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(rule iterate_notempty, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: OclInt0_int)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1) apply(metis surj_pair, simp add: OclInt0_int, simp add: int_is_valid)

  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute9: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(\<lambda>_. x))"
  apply(rule iterate_including_commute_var, rule including_commute[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) iterate_including_id)
   apply (metis StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' cons_all_def' foundation1 is_int_def mtSet_all_def null_non_OclInt0 valid4)
   apply (metis StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' cons_all_def' foundation1 is_int_def mtSet_all_def null_non_OclInt0 valid4)

    apply(subst (1 2) cp_OclIncluding[symmetric])
    apply(rule including_swap')
    apply (metis (hide_lams, no_types) all_defined1 including_defined_args_valid int_is_valid mtSet_all_def OclInt0_int)
     apply(simp add: int_is_valid) apply(simp add: int_is_valid)
  (* *)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1, rule including_commute[THEN c0_of_c, THEN c0'_of_c0])
   apply(rule cons_all_def')+ apply(rule i_cons_all_def) apply(rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
   apply(rule cons_all_def')+ apply(rule i_cons_all_def) apply(rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)


  apply(subst (1 2 3 4 5 6) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8 9 10) cp_OclIncluding)
  apply(subst (1 2 3 4 5) iterate_including_id)

  apply(metis surj_pair)
  apply(subst (1 2) cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule cons_all_def', rule i_cons_all_def, rule including_commute[THEN c0_of_c], metis surj_pair) apply(simp add: int_is_valid)+
  apply(subst (1 2) cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule cons_all_def', metis surj_pair) apply(simp add: int_is_valid)+ apply(metis surj_pair)

  apply(subst (1 2 3 4 5 6) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding[symmetric])
  apply(rule including_swap') apply(rule all_defined1, rule cons_all_def, metis surj_pair) apply(simp add: int_is_valid OclInt0_int)+
 done

 have commute1: "EQ_comp_fun_commute0' (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(\<lambda>(_:: '\<AA> st). \<lfloor>x\<rfloor>)->including(j)))"
  apply(rule iterate_commute')
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp add: int_trivial)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1)
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute6[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute6[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
  apply(subst (1 2 3 4 5) iterate_including_id_out''')
  apply(simp_all add: OclInt0_int)
  apply(metis surj_pair)
  apply(subst cp_all_def[symmetric])
  apply(rule i_cons_all_def)
   apply(rule including_commute6[THEN c0_of_c], simp add: OclInt0_int, simp)
   apply(metis surj_pair)
  apply(rule iterate_notempty)
   apply(rule including_commute6[THEN c0_of_c], simp add: OclInt0_int, simp)
   apply(metis surj_pair)
   apply(simp)
  apply(subst cp_all_def[symmetric])
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(subst (1 2 3 4) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute2: "EQ_comp_fun_commute0' (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(\<lambda>(_:: '\<AA> st). \<lfloor>x\<rfloor>)))"
  apply(rule iterate_commute')
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp add: int_trivial)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1)
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute4[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: OclInt0_int, simp) apply(rule i_cons_all_def) apply(rule including_commute4[THEN c0_of_c], simp add: OclInt0_int, simp, blast)
  apply(subst (1 2 3 4 5) iterate_including_id_out'''')
  apply(simp_all add: OclInt0_int)
  apply(metis surj_pair)
  apply(subst cp_all_def[symmetric])
  apply(rule i_cons_all_def)
   apply(rule including_commute4[THEN c0_of_c], simp add: OclInt0_int, simp)
   apply(metis surj_pair)
  apply(rule iterate_notempty)
   apply(rule including_commute4[THEN c0_of_c], simp add: OclInt0_int, simp)
   apply(metis surj_pair)
   apply(simp)
  apply(subst cp_all_def[symmetric])
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
  apply(rule cons_all_def')+
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(rule including_notempty)
   apply(rule all_defined1)
   apply(metis surj_pair)
   apply(simp add: int_is_valid)+
  apply(subst (1 2 3 4) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding[symmetric])
  apply(subst swap1, simp_all)
 done

 have set68_notempty : "\<And>(\<tau>:: '\<AA> st). \<lceil>\<lceil>Rep_Set_0 (Set{\<six>, \<eight>} \<tau>)\<rceil>\<rceil> \<noteq> {}"
  apply(rule including_notempty)
  apply(simp add: mtSet_all_def)
  apply(simp add: int_is_valid)
  apply(rule including_notempty')
 by(simp add: int_is_valid)
 have set9_notempty : "\<And>(\<tau>:: '\<AA> st). \<lceil>\<lceil>Rep_Set_0 (Set{\<nine>} \<tau>)\<rceil>\<rceil> \<noteq> {}"
  apply(rule including_notempty')
 by(simp add: int_is_valid)
 have set68_cp : "\<And>(\<tau>:: '\<AA> st) (\<tau>':: '\<AA> st). Set{\<six>, \<eight>} \<tau> = Set{\<six>, \<eight>} \<tau>'"
  apply(rule including_cp_all) apply(simp add: OclInt6_int) apply(simp add: mtSet_all_def)
  apply(rule including_cp_all) apply(simp add: OclInt8_int) apply(simp add: mtSet_all_def)
 by (simp add: mtSet_def)
 have set9_cp : "\<And>(\<tau>1:: '\<AA> st) (\<tau>2:: '\<AA> st). Set{\<nine>} \<tau>1 = Set{\<nine>} \<tau>2"
  apply(rule including_cp_all) apply(simp add: OclInt9_int) apply(simp add: mtSet_all_def)
 by (simp add: mtSet_def)

 note iterate_subst_set___ = iterate_subst_set___[OF all_defined_68 all_defined_9 set9_cp _ _ _ set9_notempty]
 note iterate_subst_set''0 = iterate_subst_set''0[OF all_defined_68 all_defined_9 _ _ _ set9_notempty]
 note iterate_subst_set'0 = iterate_subst_set'0[OF all_defined_68 all_defined_9 set9_cp]

 have GogollasChallenge_on_sets:
      "(Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j)))) \<tau> = Set{\<zero>, \<six>, \<eight>, \<nine>} \<tau>"
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(i))"])
   apply(simp add: commute1, simp add: commute2)
  apply(subst iterate_subst_set[where G = "\<lambda>j r2. r2->including(\<zero>)->including(j)->including(\<lambda>_. \<lfloor>x\<rfloor>)"]) apply(blast)+
   apply(simp add: commute3, simp add: commute4)
  apply(rule including_swap)
   apply (metis (hide_lams, mono_tags) StrictRefEq\<^isub>I\<^isub>n\<^isub>t\<^isub>e\<^isub>g\<^isub>e\<^isub>r_strict' all_defined_def including_defined_args_valid' null_non_OclInt0 OclAnd_true1 transform1_rev valid4)
   apply(simp add: int_is_valid)+
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(i)"])
   apply(simp add: commute2, simp add: commute5[THEN c0'_of_c0])
  apply(rule including_out2)
   apply(blast) apply(blast) apply(blast) apply(simp add: OclInt0_int) apply(simp)
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(i)"])
   apply(simp add: commute5[THEN c0'_of_c0], simp add: commute6[THEN c0'_of_c0])
  apply(rule including_subst_set'')
   apply(rule all_defined1, rule i_cons_all_def, rule including_commute3[THEN c0_of_c], simp add: OclInt0_int, blast)
   apply(rule all_defined1, rule i_cons_all_def, rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast)
   apply(simp add: int_is_valid)
  apply(subst iterate_subst_set[where G = "\<lambda>j r2. r2->including(j)->including(\<zero>)"]) apply(blast)+
   apply(simp add: commute8, simp add: commute7)
  apply(rule including_swap)
   apply(simp add: all_defined1) apply(simp) apply(simp only: foundation20, simp) apply(simp)
  (* *)
  apply(subst iterate_subst_set''0[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(i)"])
   apply(simp add: commute6, simp add: commute9)
  apply(rule including_subst_set'')
   apply(rule all_defined1) apply(rule i_cons_all_def, rule including_commute2[THEN c0_of_c], simp add: OclInt0_int, blast)
   apply(rule all_defined1) apply(rule cons_all_def, rule i_cons_all_def, rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
  apply(rule including_out1)
   apply(blast) apply(blast) apply(simp add: OclInt0_int) apply(simp)
  (* *)
  apply(subst iterate_subst_set'0[where G = "\<lambda>i r1. r1->including(\<zero>)->including(i)"])
   apply(simp add: commute9, simp add: commute8[THEN c0_of_c])
  apply(rule including_subst_set)+
  apply(rule iterate_including_id) apply(blast)+
  (* *)
  apply(subst iterate_subst_set[where G = "\<lambda>i r1. r1->including(i)->including(\<zero>)"])
   apply(simp add: all_defined_68, simp add: all_defined_9, simp add: commute8, simp add: commute7)
  apply(rule including_swap)
   apply(simp add: all_defined1) apply(simp) apply(simp only: foundation20, simp)
  (* *)
  apply(subst including_out1[OF all_defined_68 all_defined_9 OclInt0_int set68_notempty])
  (* *)
  apply(rule including_subst_set'')
   apply(rule all_defined1, rule i_cons_all_def'', rule including_commute[THEN c0_of_c, THEN c0'_of_c0], simp add: all_defined_68, simp add: all_defined_9)
   apply (metis (hide_lams, no_types) all_defined1 all_defined_68 all_defined_9 including_defined_args_valid)
   apply(simp)
  (* *)
  apply(subst including_out0[OF all_defined_68 set68_cp set68_notempty OclInt9_int])
  (* *)
  apply(subst including_swap[where i = \<six>])
   apply(simp)+
  (* *)
  apply(subst including_swap)
   apply(simp)+
 done

 have valid_1 : "\<tau> \<Turnstile> \<upsilon> (Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j))))"
 by(rule foundation20, rule all_defined1, rule i_cons_all_def'', rule commute1, rule all_defined_68, rule all_defined_9)

 have valid_2 : "\<tau> \<Turnstile> \<upsilon> Set{\<zero>, \<six>, \<eight>, \<nine>}"
  apply(rule foundation20, rule all_defined1) apply(rule cons_all_def)+
  apply(simp_all add: mtSet_all_def)
 done

 show ?thesis
  apply(simp only: StrictRefEq\<^isub>S\<^isub>e\<^isub>t OclValid_def StrongEq_def valid_1[simplified OclValid_def] valid_2[simplified OclValid_def])
  apply(simp add: GogollasChallenge_on_sets true_def)
 done
qed

end
