(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_basic_type_String.thy --- Library definitions.
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

theory  OCL_basic_type_String
imports OCL_Types OCL_basic_type_Boolean
begin

section{* Basic Type String: Operations *}

subsection{* Basic String Constants *}

text{* Although the remaining part of this library reasons about
integers abstractly, we provide here as example some convenient shortcuts. *}

definition OclStringa ::"('\<AA>)String" ("\<a>")
where      "\<a> = (\<lambda> _ . \<lfloor>\<lfloor>''a''\<rfloor>\<rfloor>)"

definition OclStringb ::"('\<AA>)String" ("\<b>")
where      "\<b> = (\<lambda> _ . \<lfloor>\<lfloor>''b''\<rfloor>\<rfloor>)"

definition OclStringc ::"('\<AA>)String" ("\<c>")
where      "\<c> = (\<lambda> _ . \<lfloor>\<lfloor>''c''\<rfloor>\<rfloor>)"

subsection{* Validity and Definedness Properties *}

lemma  "\<delta>(null::('\<AA>)String) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)String) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:valid_def true_def
               bot_fun_def bot_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<delta> \<a> = true" by(simp add:OclStringa_def)
lemma [simp,code_unfold]: "\<upsilon> \<a> = true" by(simp add:OclStringa_def)


subsection{* String Operations *}

subsubsection{* Definition *}
text{* Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot). *}
text{* Note that we can not follow the lexis of the OCL Standard for Isabelle
technical reasons; these operators are heavily overloaded in the HOL library
that a further overloading would lead to heavy technical buzz in this
document.
*}
definition OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g ::"('\<AA>)String \<Rightarrow> ('\<AA>)String \<Rightarrow> ('\<AA>)String" (infix "+\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" 40)
where "x +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>concat [\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>, \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>]\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g : binop_infra1 "op +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" "\<lambda> x y. \<lfloor>\<lfloor>concat [\<lceil>\<lceil>x\<rceil>\<rceil>, \<lceil>\<lceil>y\<rceil>\<rceil>]\<rfloor>\<rfloor>"
         by unfold_locales (auto simp:OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def bot_option_def null_option_def)

(*
definition OclLess\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g ::"('\<AA>)String \<Rightarrow> ('\<AA>)String \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" 35)
where "x <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclLess\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g : binop_infra1 "op <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> < \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclLess\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def bot_option_def null_option_def)

definition OclLe\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g ::"('\<AA>)String \<Rightarrow> ('\<AA>)String \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" 35)
where "x \<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "
interpretation OclLe\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g : binop_infra1 "op \<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g" "\<lambda> x y. \<lfloor>\<lfloor>\<lceil>\<lceil>x\<rceil>\<rceil> \<le> \<lceil>\<lceil>y\<rceil>\<rceil>\<rfloor>\<rfloor>"
         by   unfold_locales  (auto simp:OclLe\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def bot_option_def null_option_def)
*)
subsubsection{* Basic Properties *}

lemma OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_not_commute: "\<exists>X Y. (X +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g Y) \<noteq> (Y +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g X)"
  apply(rule_tac x = "\<lambda>_. \<lfloor>\<lfloor>''b''\<rfloor>\<rfloor>" in exI)
  apply(rule_tac x = "\<lambda>_. \<lfloor>\<lfloor>''a''\<rfloor>\<rfloor>" in exI)
  apply(simp_all add:OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def)
  by(auto, drule fun_cong, auto)

subsubsection{* Execution with Invalid or Null or Zero as Argument *}
(*
lemma OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_zero1[simp,code_unfold] :
"(x +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<zero>) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
 proof (rule ext, rename_tac \<tau>, case_tac "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau>")
  fix \<tau> show "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau> \<Longrightarrow>
              (x +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_true', simp add: OclValid_def)
  by (metis OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def OclNot_defargs OclValid_def foundation5 foundation9)
  apply_end assumption
 next fix \<tau>
  have A: "\<And>\<tau>. (\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x))) = (x \<tau> = invalid \<tau> \<or> \<tau> \<Turnstile> \<delta> x)"
  by (metis OclNot_not OclOr_def defined5 defined6 defined_not_I foundation11 foundation18'
            foundation6 foundation7 foundation9 invalid_def)
  have B: "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor> = x \<tau>"
   apply(cases "x \<tau>", metis bot_option_def foundation16)
   apply(rename_tac x', case_tac x', metis bot_option_def foundation16 null_option_def)
  by(simp)
  show "\<tau> \<Turnstile> not (\<upsilon> x and not (\<delta> x)) \<Longrightarrow>
              (x +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_false', simp, simp add: A, auto simp: OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_def OclString0_def)
     (* *)
     apply(simp add: foundation16'[simplified OclValid_def])
    apply(simp add: B)
  by(simp add: OclValid_def)
  apply_end(metis OclValid_def defined5 defined6 defined_and_I defined_not_I foundation9)
qed

lemma OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_zero2[simp,code_unfold] :
"(\<zero> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g x) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
by(subst OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_commute, simp)
*)



subsubsection{* Test Statements *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}
(*
Assert "  \<tau> \<Turnstile> ( \<nine> \<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>\<zero> )"
Assert "  \<tau> \<Turnstile> (( \<four> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<four> ) \<le>\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>\<zero> )"
Assert "\<not>(\<tau> \<Turnstile> (( \<four> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g ( \<four> +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<four> )) <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>\<zero> ))"
Assert "  \<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g \<one>)) "
*)

subsection{* Fundamental Predicates on Strings: Strict Equality *}

subsubsection{* Definition *}

text{* The last basic operation belonging to the fundamental infrastructure
of a value-type in OCL is the weak equality, which is defined similar
to the @{typ "('\<AA>)Boolean"}-case as strict extension of the strong equality:*}
defs   StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g[code_unfold] :
      "(x::('\<AA>)String) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y) \<tau>
                                    else invalid \<tau>"


subsubsection{* Validity and Definedness Properties (I) *}

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)String) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)

subsubsection{* Validity and Definedness Properties (II) *}

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)String) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> (\<upsilon> y))"
by(simp add: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g OclValid_def true_def invalid_def valid_def bot_option_def
           split: bool.split_asm HOL.split_if_asm)

subsubsection{* Validity and Definedness Properties (III) Miscellaneous *}

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_strict'' : "\<delta> ((x::('\<AA>)String) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_defined_args_valid)

(* Probably not very useful *)
lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_strict :
  assumes A: "\<upsilon> (x::('\<AA>)String) = true"
  and     B: "\<upsilon> y = true"
  shows   "\<upsilon> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g true_def valid_def defined_def
                            bot_fun_def bot_option_def)
  done


(* Probably not very useful *)
lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_strict' :
  assumes A: "\<upsilon> (((x::('\<AA>)String)) \<doteq> y) = true"
  shows      "\<upsilon> x = true \<and> \<upsilon> y = true"
  apply(insert A, rule conjI)
   apply(rule ext, rename_tac \<tau>, drule_tac x=\<tau> in fun_cong)
   prefer 2
   apply(rule ext, rename_tac \<tau>, drule_tac x=\<tau> in fun_cong)
   apply(simp_all add: StrongEq_def StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g
                       false_def true_def valid_def defined_def)
   apply(case_tac "y \<tau>", auto)
    apply(simp_all add: true_def invalid_def bot_fun_def)
  done

subsubsection{* Reflexivity *}

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_refl[simp,code_unfold] :
"((x::('\<AA>)String) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g OclIf_def)

subsubsection{* Execution with Invalid or Null as Argument *}

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_strict1[simp,code_unfold] : "((x::('\<AA>)String) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g true_def false_def)

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_strict2[simp,code_unfold] : "(invalid \<doteq> (x::('\<AA>)String)) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g true_def false_def)

lemma integer_non_null [simp]: "((\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) \<doteq> (null::('\<AA>)String)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma null_non_integer [simp]: "((null::('\<AA>)String) \<doteq> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma OclString0_non_null [simp,code_unfold]: "(\<a> \<doteq> null) = false" by(simp add: OclStringa_def)
lemma null_non_OclString0 [simp,code_unfold]: "(null \<doteq> \<a>) = false" by(simp add: OclStringa_def)


(* plus all the others ...*)

subsubsection{* Const *}

lemma [simp,code_unfold]: "const(\<a>)" by(simp add: const_ss OclStringa_def)


subsubsection{* Behavior vs StrongEq *}

lemma StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g_vs_StrongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)String) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g OclValid_def)
apply(subst cp_StrongEq[of _ "(x \<triangleq> y)"])
by simp


subsubsection{* Context Passing *}

lemma cp_StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g:
"((X::('\<AA>)String) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g StrongEq_def valid_def  cp_defined[symmetric])


lemmas cp_intro'\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g =
       cp_StrictRefEq\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g[THEN allI[THEN allI[THEN allI[THEN cpI2]],  of "StrictRefEq"]]
       OclAdd\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g.cp
       (*OclLess\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g.cp      OclLe\<^sub>S\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g.cp*)


subsection{* Test Statements on Basic String *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}


text{* Elementary computations on String *}

Assert "\<tau> \<Turnstile> \<a> <> \<b>"
Assert "\<tau> \<Turnstile> \<b> <> \<a>"
Assert "\<tau> \<Turnstile> \<b> \<doteq> \<b>"

Assert "  \<tau> \<Turnstile> \<upsilon> \<a>"
Assert "  \<tau> \<Turnstile> \<delta> \<a>"
Assert "  \<tau> \<Turnstile> \<upsilon> (null::('\<AA>)String)"
Assert "  \<tau> \<Turnstile> (invalid \<triangleq> invalid)"
Assert "  \<tau> \<Turnstile> (null \<triangleq> null)"
Assert "  \<tau> \<Turnstile> (\<a> \<triangleq> \<a>)"
Assert "\<not>(\<tau> \<Turnstile> (\<a> \<triangleq> \<b>))"
Assert "\<not>(\<tau> \<Turnstile> (invalid \<triangleq> \<b>))"
Assert "\<not>(\<tau> \<Turnstile> (null \<triangleq> \<b>))"
Assert "\<not>(\<tau> \<Turnstile> (invalid \<doteq> (invalid::('\<AA>)String)))" (* Without typeconstraint not executable.*)
Assert "\<not>(\<tau> \<Turnstile> \<upsilon> (invalid \<doteq> (invalid::('\<AA>)String)))" (* Without typeconstraint not executable.*)
Assert "\<not>(\<tau> \<Turnstile> (invalid <> (invalid::('\<AA>)String)))" (* Without typeconstraint not executable.*)
Assert "\<not>(\<tau> \<Turnstile> \<upsilon> (invalid <> (invalid::('\<AA>)String)))" (* Without typeconstraint not executable.*)
Assert "  \<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)String) )" (* Without typeconstraint not executable.*)
Assert "  \<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)String) )" (* Without typeconstraint not executable.*)
Assert "  \<tau> \<Turnstile> (\<b> \<doteq> \<b>)"
Assert "\<not>(\<tau> \<Turnstile> (\<b> <> \<b>))"
Assert "\<not>(\<tau> \<Turnstile> (\<b> \<doteq> \<c>))"
Assert "  \<tau> \<Turnstile> (\<b> <> \<c>)"
(*Assert "\<not>(\<tau> \<Turnstile> (\<zero> <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g null))"
Assert "\<not>(\<tau> \<Turnstile> (\<delta> (\<zero> <\<^sub>s\<^sub>t\<^sub>r\<^sub>i\<^sub>n\<^sub>g null)))"
*)

end
