(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib.thy --- Library definitions.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2013 Université Paris-Sud, France
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

header{* Part II: Library Definitions *}

theory OCL_lib
imports OCL_core
begin

section{* Basic Types: Void and Integer *}
subsection{* Void *}
(* subsection{* Basic Constants *} *)
type_synonym ('\<AA>)Void = "('\<AA>,unit option) val"
text {* Note that this \emph{minimal} OCL type contains only two elements:
undefined and null. For technical reasons, he does not contain to the null-class yet.*}

subsection{* Integer *}
text{* Since Integer is again a basic type, we define its semantic domain
as the valuations over @{typ "int option option"}*}
type_synonym ('\<AA>)Integer = "('\<AA>,int option option) val"

definition ocl_zero ::"('\<AA>)Integer" ("\<zero>")
where      "\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>0::int\<rfloor>\<rfloor>)"

definition ocl_one ::"('\<AA>)Integer" ("\<one> ")
where      "\<one>  = (\<lambda> _ . \<lfloor>\<lfloor>1::int\<rfloor>\<rfloor>)"

definition ocl_two ::"('\<AA>)Integer" ("\<two>")
where      "\<two> = (\<lambda> _ . \<lfloor>\<lfloor>2::int\<rfloor>\<rfloor>)"

definition ocl_three ::"('\<AA>)Integer" ("\<three>")
where      "\<three> = (\<lambda> _ . \<lfloor>\<lfloor>3::int\<rfloor>\<rfloor>)"

definition ocl_four ::"('\<AA>)Integer" ("\<four>")
where      "\<four> = (\<lambda> _ . \<lfloor>\<lfloor>4::int\<rfloor>\<rfloor>)"

definition ocl_five ::"('\<AA>)Integer" ("\<five>")
where      "\<five> = (\<lambda> _ . \<lfloor>\<lfloor>5::int\<rfloor>\<rfloor>)"

definition ocl_six ::"('\<AA>)Integer" ("\<six>")
where      "\<six> = (\<lambda> _ . \<lfloor>\<lfloor>6::int\<rfloor>\<rfloor>)"

definition ocl_seven ::"('\<AA>)Integer" ("\<seven>")
where      "\<seven> = (\<lambda> _ . \<lfloor>\<lfloor>7::int\<rfloor>\<rfloor>)"

definition ocl_eight ::"('\<AA>)Integer" ("\<eight>")
where      "\<eight> = (\<lambda> _ . \<lfloor>\<lfloor>8::int\<rfloor>\<rfloor>)"

definition ocl_nine ::"('\<AA>)Integer" ("\<nine>")
where      "\<nine> = (\<lambda> _ . \<lfloor>\<lfloor>9::int\<rfloor>\<rfloor>)"

definition ocl_ten ::"('\<AA>)Integer" ("\<one>\<zero>")
where      "\<one>\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>10::int\<rfloor>\<rfloor>)"

text{* Here is a way to cast in standard operators
via the type class system of Isabelle. *}

subsection{* Validity and Definedness *}

lemma [simp,code_unfold]:"\<upsilon> \<zero> = true"
by(simp add:ocl_zero_def valid_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]:"\<delta> \<one> = true"
by(simp add:ocl_one_def defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]:"\<upsilon> \<one> = true"
by(simp add:ocl_one_def valid_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]:"\<delta> \<two> = true"
by(simp add:ocl_two_def defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]:"\<upsilon> \<two> = true"
by(simp add:ocl_two_def valid_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<upsilon> \<six> = true"
by(simp add:ocl_six_def valid_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> \<eight> = true"
by(simp add:ocl_eight_def valid_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> \<nine> = true"
by(simp add:ocl_nine_def valid_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

subsection{* Arithmetical Operations on Integer *}

text{* Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot). *}
text{* Note that we can not follow the lexis of standard OCL for Isabelle-
technical reasons; these operators are heavily overloaded in the library
that a further overloading would lead to heavy technical buzz in this
document... *}
definition ocl_add_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "\<oplus>" 40)
where "x \<oplus> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> + \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "


definition ocl_less_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<prec>" 40)
where "x \<prec> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "

definition ocl_le_int ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<preceq>" 40)
where "x \<preceq> y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "

text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to "True".*}

value "\<tau>\<^isub>0 \<Turnstile> (\<nine> \<preceq> \<one>\<zero> )"
value "\<tau>\<^isub>0 \<Turnstile> (( \<four> \<oplus> \<four> ) \<preceq> \<one>\<zero> )"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> ((\<four> \<oplus>( \<four> \<oplus> \<four> )) \<prec> \<one>\<zero> ))"


section{* Fundamental Predicates on Boolean and Integer : Strict Equality *}

subsection{* Definition *}

text{* Note that the strict equality on basic types (actually on all types)
must be exceptionally defined on null --- otherwise the entire concept of
null in the language does not make much sense. This is an important exception
from the general rule that null arguments --- especially if passed as "self"-argument ---
lead to invalid results. *}

consts StrictRefEq :: "[('\<AA>,'a)val,('\<AA>,'a)val] \<Rightarrow> ('\<AA>)Boolean" (infixl "\<doteq>" 30)

syntax
  "notequal"        :: "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean"   (infix "<>" 40)
translations
  "a <> b" == "CONST not( a \<doteq> b)"

defs   StrictRefEq_bool[code_unfold] :
      "(x::('\<AA>)Boolean) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y)\<tau>
                                    else invalid \<tau>"

defs   StrictRefEq_int[code_unfold] :
      "(x::('\<AA>)Integer) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y) \<tau>
                                    else invalid \<tau>"

subsection{* Logic and Algebraic Layer on Basic Types *}

subsubsection{* Validity and Definedness (I) *}

lemma StrictRefEq_bool_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)Boolean) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq_bool OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)

lemma StrictRefEq_int_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)Integer) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq_int OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)

subsubsection{* Validity and Definedness (II) *}

lemma StrictRefEq_bool_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Boolean) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq_bool OclValid_def true_def invalid_def
             bot_option_def
        split: bool.split_asm HOL.split_if_asm)

lemma StrictRefEq_int_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Integer) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> (\<upsilon> y))"
by(simp add: StrictRefEq_int OclValid_def true_def invalid_def valid_def bot_option_def
           split: bool.split_asm HOL.split_if_asm)

subsubsection{* Reflexivity *}

lemma StrictRefEq_bool_refl[simp,code_unfold] :
"((x::('\<AA>)Boolean) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq_bool if_ocl_def)

lemma StrictRefEq_int_refl[simp,code_unfold] :
"((x::('\<AA>)Integer) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq_int if_ocl_def)

subsubsection{* Execution with invalid as argument *}

lemma StrictRefEq_bool_strict1[simp] : "((x::('\<AA>)Boolean) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strict2[simp] : "(invalid \<doteq> (x::('\<AA>)Boolean)) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_int_strict1[simp] : "((x::('\<AA>)Integer) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strict2[simp] : "(invalid \<doteq> (x::('\<AA>)Integer)) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

subsubsection{* Behavior vs StrongEq *}

lemma StrictRefEq_bool_vs_strongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)Boolean) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq_bool OclValid_def)
apply(subst cp_StrongEq)back
by simp


lemma StrictRefEq_int_vs_strongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)Integer) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq_int OclValid_def)
apply(subst cp_StrongEq)back
by simp

subsubsection{* Miscellaneous *}

lemma StrictRefEq_bool_strict'' : "\<delta> ((x::('\<AA>)Boolean) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 StrictRefEq_bool_defined_args_valid)

lemma StrictRefEq_int_strict'' : "\<delta> ((x::('\<AA>)Integer) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 StrictRefEq_int_defined_args_valid)

(* Probably not very useful *)
lemma StrictRefEq_int_strict :
  assumes A: "\<upsilon> (x::('\<AA>)Integer) = true"
  and     B: "\<upsilon> y = true"
  shows   "\<upsilon> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq_int true_def valid_def defined_def
                            bot_fun_def bot_option_def)
  done


(* Probably not very useful *)
lemma StrictRefEq_int_strict' :
  assumes A: "\<upsilon> (((x::('\<AA>)Integer)) \<doteq> y) = true"
  shows      "\<upsilon> x = true \<and> \<upsilon> y = true"
  apply(insert A, rule conjI)
  apply(rule ext, drule_tac x=xa in fun_cong)
  prefer 2
  apply(rule ext, drule_tac x=xa in fun_cong)
  apply(simp_all add: StrongEq_def StrictRefEq_int
                            false_def true_def valid_def defined_def)
  apply(case_tac "y xa", auto)
  apply(simp_all add: true_def invalid_def bot_fun_def)
  done

subsubsection{* Context Passing *}

lemma cp_StrictRefEq_bool:
"((X::('\<AA>)Boolean) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_bool StrongEq_def defined_def valid_def  cp_defined[symmetric])

lemma cp_StrictRefEq_int:
"((X::('\<AA>)Integer) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_int StrongEq_def valid_def  cp_defined[symmetric])


lemmas cp_intro'[simp,intro!] =
       cp_intro'
       cp_StrictRefEq_bool[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]
       cp_StrictRefEq_int[THEN allI[THEN allI[THEN allI[THEN cpI2]],  of "StrictRefEq"]]



subsection{* Test Statements on Basic Types. *}

text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to "True".*}

text{* Elementary computations on Booleans *}
value "\<tau>\<^isub>0 \<Turnstile> \<upsilon>(true)"
value "\<tau>\<^isub>0 \<Turnstile> \<delta>(false)"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> \<delta>(null))"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> \<delta>(invalid))"
value "\<tau>\<^isub>0 \<Turnstile> \<upsilon>((null::('\<AA>)Boolean))"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> \<upsilon>(invalid))"
value "\<tau>\<^isub>0 \<Turnstile> (true and true)"
value "\<tau>\<^isub>0 \<Turnstile> (true and true \<triangleq> true)"
value "\<tau>\<^isub>0 \<Turnstile> ((null or null) \<triangleq> null)"
value "\<tau>\<^isub>0 \<Turnstile> ((null or null) \<doteq> null)"
value "\<tau>\<^isub>0 \<Turnstile> ((true \<triangleq> false) \<triangleq> false)"
value "\<tau>\<^isub>0 \<Turnstile> ((invalid \<triangleq> false) \<triangleq> false)"
value "\<tau>\<^isub>0 \<Turnstile> ((invalid \<doteq> false) \<triangleq> invalid)"


text{* Elementary computations on Integer *}
value "\<tau>\<^isub>0 \<Turnstile> \<upsilon>(\<four>)"
value "\<tau>\<^isub>0 \<Turnstile> \<delta>(\<four>)"
value "\<tau>\<^isub>0 \<Turnstile> \<upsilon>((null::('\<AA>)Integer))"
value "\<tau>\<^isub>0 \<Turnstile> (invalid \<triangleq> invalid )"
value "\<tau>\<^isub>0 \<Turnstile> (null \<triangleq> null )"
value "\<tau>\<^isub>0 \<Turnstile> (\<four> \<triangleq> \<four>)"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> (\<nine> \<triangleq> \<one>\<zero> ))"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> (invalid \<triangleq> \<one>\<zero> ))"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> (null \<triangleq> \<one>\<zero> ))"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> (invalid \<doteq> (invalid::('\<AA>)Integer)))" (* Without typeconstraint not executable.*)
value "\<tau>\<^isub>0 \<Turnstile> (null \<doteq> (null::('\<AA>)Integer) )" (* Without typeconstraint not executable.*)
value "\<tau>\<^isub>0 \<Turnstile> (null \<doteq> (null::('\<AA>)Integer) )" (* Without typeconstraint not executable.*)
value "\<tau>\<^isub>0 \<Turnstile> (\<four> \<doteq> \<four>)"
value "\<not>(\<tau>\<^isub>0 \<Turnstile> (\<four> \<doteq> \<one>\<zero> ))"


lemma  "\<delta>(null::('\<AA>)Integer) = false" by simp (* recall *)
lemma  "\<upsilon>(null::('\<AA>)Integer) = true"  by simp (* recall *)

subsection{* More algebraic and logical layer on basic types*}

subsubsection{* Execution with Integer as argument *}

lemma zero_non_null [simp]: "(\<zero> \<doteq> null) = false"
by(rule ext,auto simp:ocl_zero_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
lemma null_non_zero [simp]: "(null \<doteq> \<zero>) = false"
by(rule ext,auto simp:ocl_zero_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma one_non_null [simp]: "(\<one> \<doteq> null) = false"
by(rule ext,auto simp:ocl_one_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
lemma null_non_one [simp]: "(null \<doteq> \<one>) = false"
by(rule ext,auto simp:ocl_one_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma two_non_null [simp]: "(\<two> \<doteq> null) = false"
by(rule ext,auto simp:ocl_two_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
lemma null_non_two [simp]: "(null \<doteq> \<two>) = false"
by(rule ext,auto simp:ocl_two_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma six_non_null [simp]: "(\<six> \<doteq> null) = false"
by(rule ext,auto simp:ocl_six_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
lemma null_non_six [simp]: "(null \<doteq> \<six>) = false"
by(rule ext,auto simp:ocl_six_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma eight_non_null [simp]: "(\<eight> \<doteq> null) = false"
by(rule ext,auto simp:ocl_eight_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
lemma null_non_eight [simp]: "(null \<doteq> \<eight>) = false"
by(rule ext,auto simp:ocl_eight_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma nine_non_null [simp]: "(\<nine> \<doteq> null) = false"
by(rule ext,auto simp:ocl_nine_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
lemma null_non_nine [simp]: "(null \<doteq> \<nine>) = false"
by(rule ext,auto simp:ocl_nine_def  null_def StrictRefEq_int valid_def invalid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

(* plus all the others ...*)



section {* Complex Types: The Set-Collection Type *}

no_notation None ("\<bottom>")
notation bot ("\<bottom>")

subsection {* The construction of the Set-Collection Type *}

text{* For the semantic construction of the collection types, we have two goals:
\begin{enumerate}
\item we want the types to be \emph{fully abstract}, i.e. the type should not
      contain junk-elements that are not representable by OCL expressions, and
\item we want a possibility to nest collection types (so, we want the
      potential to talking about @{text "Set(Set(Sequences(Pairs(X,Y))))"}).
\end{enumerate}
The former principe rules out the option to define @{text "'\<alpha> Set"} just by
 @{text "('\<AA>, ('\<alpha> option option) set) val"}. This would allow sets to contain
junk elements such as @{text "{\<bottom>}"} which we need to identify with undefinedness
itself. Abandoning fully abstractness of rules would later on produce all sorts
of problems when quantifying over the elements of a type.
However, if we build an own type, then it must conform to our abstract interface
in order to have nested types: arguments of type-constructors must conform to our
abstract interface, and the result type too.
*}

text{* The core of an own type construction is done via a type definition which
provides the raw-type @{text "'\<alpha> Set_0"}. it is shown that this type "fits" indeed
into the abstract type interface discussed in the previous section. *}

typedef '\<alpha> Set_0 ="{X::('\<alpha>\<Colon>null) set option option.
                      X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
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

lemma Set_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> (X \<tau> = Abs_Set_0 \<lfloor>bot\<rfloor>)
                                     \<or> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot)"
apply(insert OCL_lib.Set_0.Rep_Set_0 [of "X \<tau>"], simp)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Set_0_def null_Set_0_def null_fun_def
           split:split_if_asm)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = bot"])
apply(subst Abs_Set_0_inject[symmetric], rule Rep_Set_0, simp)
apply(simp add: Rep_Set_0_inverse bot_Set_0_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = null"])
apply(subst Abs_Set_0_inject[symmetric], rule Rep_Set_0, simp)
apply(simp add: Rep_Set_0_inverse  null_option_def)
done
(*
lemma Set_inv_lemma2 : " (\<tau> \<Turnstile> \<delta> X) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (\<lambda>_. e) \<Longrightarrow>  e \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
sorry
*)
lemma invalid_set_not_defined [simp,code_unfold]:"\<delta>(invalid::('\<AA>,'\<alpha>::null) Set) = false" by simp
lemma null_set_not_defined [simp,code_unfold]:"\<delta>(null::('\<AA>,'\<alpha>::null) Set) = false"
by(simp add: defined_def null_fun_def)
lemma invalid_set_valid [simp,code_unfold]:"\<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set) = false"
by simp
lemma null_set_valid [simp,code_unfold]:"\<upsilon>(null::('\<AA>,'\<alpha>::null) Set) = true"
apply(simp add: valid_def null_fun_def bot_fun_def bot_Set_0_def null_Set_0_def)
apply(subst Abs_Set_0_inject,simp_all add: null_option_def bot_option_def)
done

text{* ... which means that we can have a type @{text "('\<AA>,('\<AA>,('\<AA>) Integer) Set) Set"}
corresponding exactly to Set(Set(Integer)) in OCL notation. Note that the parameter
@{text "\<AA>"} still refers to the object universe; making the OCL semantics entirely parametric
in the object universe makes it possible to study (and prove) its properties
independently from a concrete class diagram. *}

subsection{* Constants on Sets *}
definition mtSet::"('\<AA>,'\<alpha>::null) Set"  ("Set{}")
where "Set{} \<equiv> (\<lambda> \<tau>.  Abs_Set_0 \<lfloor>\<lfloor>{}::'\<alpha> set\<rfloor>\<rfloor> )"


lemma mtSet_defined[simp,code_unfold]:"\<delta>(Set{}) = true"
apply(rule ext, auto simp: mtSet_def defined_def null_Set_0_def
                           bot_Set_0_def bot_fun_def null_fun_def)
apply(simp_all add: Abs_Set_0_inject bot_option_def null_Set_0_def null_option_def)
done

lemma mtSet_valid[simp,code_unfold]:"\<upsilon>(Set{}) = true"
apply(rule ext,auto simp: mtSet_def valid_def null_Set_0_def
                          bot_Set_0_def bot_fun_def null_fun_def)
apply(simp_all add: Abs_Set_0_inject bot_option_def null_Set_0_def null_option_def)
done

text{* Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid. *}

subsection{* Library Operations on Sets *}

subsubsection{* Future Operator to be defined *}

consts (* abstract set collection operations *)
 (* OclSize        :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"      *)
 (* OclIncludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    *)
 (* OclExcludes    :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> '\<AA> Boolean"    *)
 (* OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"   *)
 (* OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val'] \<Rightarrow> ('\<AA>,'\<alpha>) Set"   *)
 (* OclIsEmpty     :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean" *)
 (* OclNotEmpty    :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"*)
    OclUnion       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclIntersection:: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclIncludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclExcludesAll :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Boolean"
    OclComplement  :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> ('\<AA>,'\<alpha>) Set"
    OclSum         :: " ('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Integer"
    OclCount       :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) Set] \<Rightarrow> '\<AA> Integer"

notation
    OclCount       ("_->count'(_')" [66,65]65)
notation
    OclSum         ("_->sum'(')" [66])
notation
    OclIncludesAll ("_->includesAll'(_')" [66,65]65)
notation
    OclExcludesAll ("_->excludesAll'(_')" [66,65]65)
notation
    OclComplement  ("_->complement'(')")
notation
    OclUnion       ("_->union'(_')"          [66,65]65)
notation
    OclIntersection("_->intersection'(_')"   [71,70]70)


subsubsection{* Some definitions *}

definition OclSize     :: "('\<AA>,'\<alpha>::null)Set \<Rightarrow> '\<AA> Integer"
where     "OclSize x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> finite(\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>)
                             then \<lfloor>\<lfloor> int(card \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<rfloor>\<rfloor>
                             else \<bottom> )"
notation  (* standard ascii syntax *)
           OclSize        ("_->size'(')" [66])

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>  \<union> {y \<tau>} \<rfloor>\<rfloor>
                                    else \<bottom> )"
notation   OclIncluding   ("_->including'(_')")

definition OclIncludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclIncludes x y = (\<lambda> \<tau>.   if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then \<lfloor>\<lfloor>(y \<tau>) \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<rfloor>\<rfloor>
                                     else \<bottom>  )"
notation   OclIncludes    ("_->includes'(_')" [66,65]65)

definition OclExcluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclExcluding x y = (\<lambda> \<tau>.  if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                     then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> - {y \<tau>} \<rfloor>\<rfloor>
                                     else \<bottom> )"
notation   OclExcluding   ("_->excluding'(_')")

definition OclExcludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludes x y = (not(OclIncludes x y))"
notation   OclExcludes    ("_->excludes'(_')" [66,65]65)

text{* The following definition follows the requirement of the
standard to treat null as neutral element of sets. It is
a well-documented exception from the general strictness
rule and the rule that the distinguished argument self should
be non-null. *}
definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((x \<doteq> null) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty'(')" [66])

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty'(')" [66])

definition OclIterate\<^isub>S\<^isub>e\<^isub>t :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<beta>::null)val,
                             ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where "OclIterate\<^isub>S\<^isub>e\<^isub>t S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>
                                  then (Finite_Set.fold (F) (A) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))\<tau>
                                  else \<bottom>)"
syntax
  "_OclIterate"  :: "[('\<AA>,'\<alpha>::null) Set, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate'(_;_=_ | _')" [71,100,70]50)
translations
  "X->iterate(a; x = A | P)" == "CONST OclIterate\<^isub>S\<^isub>e\<^isub>t X A (%a. (% x. P))"


definition OclForall     :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall S P = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau>
                                 then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = false \<tau>)
                                      then false \<tau>
                                      else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = \<bottom> \<tau>)
                                           then \<bottom> \<tau>
                                           else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = null \<tau>)
                                                then null \<tau>
                                                else true \<tau>
                                 else \<bottom>)"
syntax
  "_OclForall" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forall'(_|_')")
translations
  "X->forall(x | P)" == "CONST OclForall X (%x. P)"


definition OclExists     :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclExists S P = not(OclForall S (\<lambda> X. not (P X)))"

syntax
  "_OclExist" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->exists'(_|_')")
translations
  "X->exists(x | P)" == "CONST OclExists X (%x. P)"

subsubsection{* Context Passing *}

lemma cp_OclIncluding:
"(X->including(x)) \<tau> = ((\<lambda> _. X \<tau>)->including(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclIncluding_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclExcluding:
"(X->excluding(x)) \<tau> = ((\<lambda> _. X \<tau>)->excluding(\<lambda> _. x \<tau>)) \<tau>"
by(auto simp: OclExcluding_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclIncludes:
"(X->includes(x)) \<tau> = (OclIncludes (\<lambda> _. X \<tau>) (\<lambda> _. x \<tau>) \<tau>)"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclIncludes1:
"(X->includes(x)) \<tau> = (OclIncludes X (\<lambda> _. x \<tau>) \<tau>)"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclForall:
"(X->forall(x | P x)) \<tau> = ((\<lambda> _. X \<tau>)->forall(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclForall_def cp_defined[symmetric])

(* Why does this not work syntactically ???
   lemma cp_OclIncludes: "(X->includes(x)) \<tau> = (((\<lambda> _. X \<tau>)->includes( \<lambda> _. x \<tau>)) \<tau>)" *)

lemmas cp_intro''[simp,intro!] =
       cp_intro'
       cp_OclIncludes  [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncludes"]]
       cp_OclIncluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncluding"]]
       cp_OclExcluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclExcluding"]]


section{* Fundamental Predicates on Set *}
subsection{* Validity and Definedness *}

subsubsection{* OclIncluding *}

lemma including_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->including(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<delta>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_neq_bot_bot : "\<And>\<tau>. (\<bottom> \<noteq> \<bottom> \<tau>) = False" by (metis OCL_core.bot_fun_def)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->including(x)))"
          apply(frule C, simp)
          apply(subst OclIncluding_def, subst OclValid_def, subst defined_def, simp add: discr_neq_bot_bot discr_eq_false_true)
          apply(simp add: OclValid_def)
          apply(subgoal_tac "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None \<and> Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>")
          apply(simp add: OCL_core.bot_fun_def bot_Set_0_def null_Set_0_def null_fun_def)
          apply(subgoal_tac "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> None \<and> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> \<lfloor>None\<rfloor>")
          apply(simp add: A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
          by (metis (hide_lams, no_types) option.distinct(1) option.inject)
show ?thesis by(auto dest:D intro:E)
qed



lemma including_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->including(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have D: "(\<tau> \<Turnstile> \<upsilon>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->including(x)))"
          by(simp add: foundation20 including_defined_args_valid)
show ?thesis by(auto dest:D intro:E)
qed

lemma including_defined_args_valid'[simp,code_unfold]:
"\<delta>(X->including(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:including_defined_args_valid foundation10 defined_and_I)

lemma including_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->including(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:including_valid_args_valid foundation10 defined_and_I)


subsubsection{* OclExcluding *}

lemma excluding_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->excluding(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<delta>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_neq_bot_bot : "\<And>\<tau>. (\<bottom> \<noteq> \<bottom> \<tau>) = False" by (metis OCL_core.bot_fun_def)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->excluding(x)))"
          apply(frule C, simp)
          apply(subst OclExcluding_def, subst OclValid_def, subst defined_def, simp add: discr_neq_bot_bot discr_eq_false_true)
          apply(simp add: OclValid_def)
          apply(subgoal_tac "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None \<and> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>")
          apply(simp add: OCL_core.bot_fun_def bot_Set_0_def null_Set_0_def null_fun_def)
          apply(subgoal_tac "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> None \<and> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<noteq> \<lfloor>None\<rfloor>")
          apply(simp add: A Abs_Set_0_inject Abs_Set_0_inverse B C OclExcluding_def OclValid_def Option.set.simps(2) Rep_Set_0_inverse bot_Set_0_def bot_option_def null_Set_0_def null_option_def option.distinct(1))
          by (metis (hide_lams, no_types) option.distinct(1) option.inject)
show ?thesis by(auto dest:D intro:E)
qed


lemma excluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excluding(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have D: "(\<tau> \<Turnstile> \<upsilon>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->excluding(x)))"
          by(simp add: foundation20 excluding_defined_args_valid)
show ?thesis by(auto dest:D intro:E)
qed


lemma excluding_valid_args_valid'[simp,code_unfold]:
"\<delta>(X->excluding(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:excluding_defined_args_valid foundation10 defined_and_I)


lemma excluding_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->excluding(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:excluding_valid_args_valid foundation10 defined_and_I)

subsubsection{* OclIncludes *}

lemma includes_defined_args_valid:
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

lemma includes_valid_args_valid:
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

lemma includes_valid_args_valid'[simp,code_unfold]:
"\<delta>(X->includes(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:includes_defined_args_valid foundation10 defined_and_I)

lemma includes_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->includes(x)) = ((\<delta> X) and (\<upsilon> x))"
by(auto intro!: transform2_rev simp:includes_valid_args_valid foundation10 defined_and_I)


(* and many more, forall exists. *)





subsection{* Execution (I) *}

subsubsection{* OclIterate *}

lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_strict1[simp]:"invalid->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^isub>S\<^isub>e\<^isub>t_def defined_def valid_def false_def true_def)

lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_null1[simp]:"null->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^isub>S\<^isub>e\<^isub>t_def defined_def valid_def false_def true_def)


lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_strict2[simp]:"S->iterate(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^isub>S\<^isub>e\<^isub>t_def defined_def valid_def false_def true_def)

text{* An open question is this ... *}
lemma (*OclIterate\<^isub>S\<^isub>e\<^isub>t_null2[simp]:*) "S->iterate(a; x = null | P a x) = invalid"
oops
text{* In the definition above, this does not hold in general.
       And I believe, this is how it should be ... *}

subsubsection{* OclIncluding *}

lemma including_strict1[simp,code_unfold]:"(invalid->including(x)) = invalid"
by(simp add: bot_fun_def OclIncluding_def invalid_def defined_def valid_def false_def true_def)

lemma including_strict2[simp,code_unfold]:"(X->including(invalid)) = invalid"
by(simp add: OclIncluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma including_strict3[simp,code_unfold]:"(null->including(x)) = invalid"
by(simp add: OclIncluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

subsubsection{* OclExcluding *}

lemma excluding_strict1[simp,code_unfold]:"(invalid->excluding(x)) = invalid"
by(simp add: bot_fun_def OclExcluding_def invalid_def defined_def valid_def false_def true_def)

lemma excluding_strict2[simp,code_unfold]:"(X->excluding(invalid)) = invalid"
by(simp add: OclExcluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma excluding_strict3[simp,code_unfold]:"(null->excluding(x)) = invalid"
by(simp add: OclExcluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

subsubsection{* OclIncludes *}

lemma includes_strict1[simp,code_unfold]:"(invalid->includes(x)) = invalid"
by(simp add: bot_fun_def OclIncludes_def invalid_def defined_def valid_def false_def true_def)

lemma includes_strict2[simp,code_unfold]:"(X->includes(invalid)) = invalid"
by(simp add: OclIncludes_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma includes_strict3[simp,code_unfold]:"(null->includes(x)) = invalid"
by(simp add: OclIncludes_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

(*  forall ? exists ?*)

subsection{* Execution (II) Some computational laws *}

subsubsection{* OclIncluding and OclIncludes *}

lemma including_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> not(Set{}->includes(x))"
using val_x
apply(auto simp: OclValid_def OclIncludes_def not_def false_def true_def)
apply(auto simp: mtSet_def OCL_lib.Set_0.Abs_Set_0_inverse)
done


lemma including_charn0'[simp,code_unfold]:
"Set{}->includes(x) = (if \<upsilon> x then false else invalid endif)"
proof -
  have A: "\<And> \<tau>. (Set{}->includes(invalid)) \<tau> = (if (\<upsilon> invalid) then false else invalid endif) \<tau>"
          by simp
  have B: "\<And> \<tau> x. \<tau> \<Turnstile> (\<upsilon> x) \<Longrightarrow> (Set{}->includes(x)) \<tau> = (if \<upsilon> x then false else invalid endif) \<tau>"
          apply(frule including_charn0, simp add: OclValid_def)
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
lemma including_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (X->including(x)->includes(x))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 show ?thesis
  apply(subst OclIncludes_def, simp add: def_X[simplified OclValid_def] val_x[simplified OclValid_def] foundation10[simplified OclValid_def] OclValid_def)
  apply(simp add: OclIncluding_def def_X[simplified OclValid_def] val_x[simplified OclValid_def] Abs_Set_0_inverse[OF C] true_def)
 done
qed



lemma including_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> (X->including(x)->includes(y)) \<triangleq> (X->includes(y))"
proof -
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 show ?thesis
  apply(subst OclIncludes_def, simp add: def_X[simplified OclValid_def] val_x[simplified OclValid_def] val_y[simplified OclValid_def] foundation10[simplified OclValid_def] OclValid_def StrongEq_def)
  apply(simp add: OclIncluding_def OclIncludes_def def_X[simplified OclValid_def] val_x[simplified OclValid_def] val_y[simplified OclValid_def] Abs_Set_0_inverse[OF C] true_def)
 by(metis foundation22 foundation6 foundation9 neq)
qed

text{* One would like a generic theorem of the form:
\begin{verbatim}
lemma includes_execute[code_unfold]:
"(X->including(x)->includes(y)) = (if \<delta> X then if x \<doteq> y
                                               then true
                                               else X->includes(y)
                                               endif
                                          else invalid endif)"

\end{verbatim}
Unfortunately, this does not hold in general, since referential equality is
an overloaded concept and has to be defined for each type individually.
Consequently, it is only valid for concrete  type instances for Boolean,
Integer, and Sets thereof...
*}


text{* The computational law \verb+includes_execute+ becomes generic since it
uses strict equality which in itself is generic. It is possible to prove
the following generic theorem and instantiate it if a number of properties
that link the polymorphic logical, Strong Equality with the concrete instance
of strict quality.*}
lemma includes_execute_generic:
assumes strict1: "(x \<doteq> invalid) = invalid"
and     strict2: "(invalid \<doteq> y) = invalid"
and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
and     StrictRefEq_vs_strongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                      \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> (x \<triangleq> y)))"
shows
      "(X->including(x::('\<AA>,'a::null)val)->includes(y)) =
       (if \<delta> X then if x \<doteq> y then true else X->includes(y) endif else invalid endif)"
proof -
  have A: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid \<tau>"
            apply(subst cp_OclIncludes, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_OclIncluding[symmetric] cp_OclIncludes[symmetric])
            by simp
  have B: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid  \<tau>"
            apply(subst cp_OclIncludes, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_OclIncluding[symmetric] cp_OclIncludes[symmetric])
            by simp
  have C: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->includes(y)) \<tau> =
           (if x \<doteq> y then true else X->includes(y) endif) \<tau>"
            apply(subst cp_if_ocl,subst cp_StrictRefEq)
            apply(subst cp_OclIncludes, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_if_ocl[symmetric] cp_OclIncluding[symmetric]
                             cp_StrictRefEq[symmetric] cp_OclIncludes[symmetric] )
            by (simp add: strict2)
  have D:"\<And>\<tau>. \<tau> \<Turnstile> (y \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->includes(y)) \<tau> =
           (if x \<doteq> y then true else X->includes(y) endif) \<tau>"
            apply(subst cp_if_ocl, subst cp_StrictRefEq)
            apply(subst cp_OclIncludes, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_if_ocl[symmetric] cp_OclIncluding[symmetric]
                             cp_StrictRefEq[symmetric] cp_OclIncludes[symmetric])
            by (simp add: strict1)
  have E: "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
              (if x \<doteq> y then true else X->includes(y) endif) \<tau> =
              (if x \<triangleq> y then true else X->includes(y) endif) \<tau>"
           apply(subst cp_if_ocl)
           apply(subst StrictRefEq_vs_strongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_if_ocl[symmetric])
  have F: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
               (X->including(x)->includes(y)) \<tau> = (X->including(x)->includes(x)) \<tau>"
           apply(subst cp_OclIncludes)
           apply(drule foundation22[THEN iffD1], drule sym, simp)
           by(simp add:cp_OclIncludes[symmetric])
  show ?thesis
    apply(rule ext, rename_tac "\<tau>")
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<delta> X))", simp add:def_split_local,elim disjE A B)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> x))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym)
    apply(simp add: foundation22 C)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> y))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym, simp add: foundation22 D, simp)
    apply(subst E,simp_all)
    apply(case_tac "\<tau> \<Turnstile> not(x \<triangleq> y)")
    apply(simp add: including_charn2[simplified foundation22])
    apply(simp add: foundation9 F
                    including_charn1[THEN foundation13[THEN iffD2],
                                     THEN foundation22[THEN iffD1]])
  done
qed

subsection{* Strict Equality *}

text{* This section of foundational operations on sets is closed with a paragraph
on equality. Strong Equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:*}

defs   StrictRefEq_set :
      "(x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                         then (x \<triangleq> y)\<tau>
                                         else invalid \<tau>"

lemma RefEq_set_refl[simp,code_unfold]:
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq_set if_ocl_def)


lemma StrictRefEq_set_strict1: "((x::('\<AA>,'\<alpha>::null)Set) \<doteq> invalid)= invalid"
by(simp add:StrictRefEq_set false_def true_def)

lemma StrictRefEq_set_strict2: "(invalid \<doteq> (y::('\<AA>,'\<alpha>::null)Set))= invalid"
by(simp add:StrictRefEq_set false_def true_def)

lemma StrictRefEq_set_strictEq_valid_args_valid:
"(\<tau> \<Turnstile> \<delta> ((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
proof -
   have A: "\<tau> \<Turnstile> \<delta> (x \<doteq> y) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> \<tau> \<Turnstile> \<upsilon> y"
           apply(simp add: StrictRefEq_set valid_def OclValid_def defined_def)
           apply(simp add: invalid_def bot_fun_def split: split_if_asm)
           done
   have B: "(\<tau> \<Turnstile> \<upsilon> x) \<and> (\<tau> \<Turnstile> \<upsilon> y) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (x \<doteq> y)"
           apply(simp add: StrictRefEq_set, elim conjE)
           apply(drule foundation13[THEN iffD2],drule foundation13[THEN iffD2])
           apply(rule cp_validity[THEN iffD2])
           apply(subst cp_defined, simp add: foundation22)
           apply(simp add: cp_defined[symmetric] cp_validity[symmetric])
           done
   show ?thesis by(auto intro!: A B)
qed

lemma cp_StrictRefEq_set:"((X::('\<AA>,'\<alpha>::null)Set) \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
by(simp add:StrictRefEq_set cp_StrongEq[symmetric] cp_valid[symmetric])


lemma strictRefEq_set_vs_strongEq:
"\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(drule foundation13[THEN iffD2],drule foundation13[THEN iffD2])
by(simp add:StrictRefEq_set foundation22)

subsection{* Algebraic Properties on Strict Equality *}

text{* One might object here that for the case of objects, this is an empty definition.
The answer is no, we will restrain later on states and objects such that any object
has its id stored inside the object (so the ref, under which an object can be referenced
in the store will represented in the object itself). For such well-formed stores that satisfy
this invariant (the WFF - invariant), the referential equality and the strong equality ---
and therefore the strict equality on sets in the sense above) coincides.*}

text{* To become operational, we derive: *}

lemma StrictRefEq_set_refl (* [simp,code_unfold] *) :
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq_set if_ocl_def)

text{* The key for an operational definition if OclForall given below. *}

text{* The case of the size definition is somewhat special, we admit
explicitly in Essential OCL the possibility of infinite sets. For
the size definition, this requires an extra condition that assures
that the cardinality of the set is actually a defined integer. *}

(* Hack to work around OF-Bug *)
schematic_lemma includes_execute_int[code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq_int_strict1 StrictRefEq_int_strict2
                                 cp_StrictRefEq_int
                                    StrictRefEq_int_vs_strongEq], simp_all)


schematic_lemma includes_execute_bool[code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq_bool_strict1 StrictRefEq_bool_strict2
                                 cp_StrictRefEq_bool
                                    StrictRefEq_bool_vs_strongEq], simp_all)


schematic_lemma includes_execute_set[code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq_set_strict1 StrictRefEq_set_strict2
                                 cp_StrictRefEq_set
                                    strictRefEq_set_vs_strongEq], simp_all)



lemma excluding_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> ((Set{}->excluding(x))  \<triangleq>  Set{})"
proof -
  have A : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
  have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)

  show ?thesis using val_x
    apply(auto simp: OclValid_def OclIncludes_def not_def false_def true_def StrongEq_def
                     OclExcluding_def mtSet_def defined_def bot_fun_def null_fun_def null_Set_0_def)
    apply(auto simp: mtSet_def OCL_lib.Set_0.Abs_Set_0_inverse
                     OCL_lib.Set_0.Abs_Set_0_inject[OF B A])
  done
qed


lemma excluding_charn0_exec[code_unfold]:
"(Set{}->excluding(x)) = (if (\<upsilon> x) then Set{} else invalid endif)"
proof -
  have A: "\<And> \<tau>. (Set{}->excluding(invalid)) \<tau> = (if (\<upsilon> invalid) then Set{} else invalid endif) \<tau>"
          by simp
  have B: "\<And> \<tau> x. \<tau> \<Turnstile> (\<upsilon> x) \<Longrightarrow> (Set{}->excluding(x)) \<tau> = (if (\<upsilon> x) then Set{} else invalid endif) \<tau>"
          by(simp add: excluding_charn0[THEN foundation22[THEN iffD1]])
  show ?thesis
    apply(rule ext, rename_tac \<tau>)
    apply(case_tac "\<tau> \<Turnstile> (\<upsilon> x)")
      apply(simp add: B)
      apply(simp add: foundation18)
      apply(subst cp_OclExcluding, simp)
      apply(simp add: cp_if_ocl[symmetric] cp_OclExcluding[symmetric] cp_valid[symmetric] A)
   done
qed

lemma excluding_charn1:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> ((X->including(x))->excluding(y)) \<triangleq> ((X->excluding(y))->including(x))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 have D : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 have E : "x \<tau> \<noteq> y \<tau>"
          apply(insert neq)
          by(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def
                        false_def true_def defined_def valid_def bot_Set_0_def
                        null_fun_def null_Set_0_def StrongEq_def not_def)

 have G1 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          apply(insert C, simp)
          apply(simp add:  def_X val_x A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
 done
 have G2 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          apply(insert C, simp)
          apply(simp add:  def_X val_x A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
 done

 have G : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def G1 G2)
 done
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have H1 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          apply(insert D, simp)
          apply(simp add: A Abs_Set_0_inject Abs_Set_0_inverse B C OclExcluding_def OclValid_def Option.set.simps(2) Rep_Set_0_inverse bot_Set_0_def bot_option_def null_Set_0_def null_option_def option.distinct(1))
 done
 have H2 : "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          apply(insert D, simp)
          apply(simp add: A Abs_Set_0_inject Abs_Set_0_inverse B C OclExcluding_def OclValid_def Option.set.simps(2) Rep_Set_0_inverse bot_Set_0_def bot_option_def null_Set_0_def null_option_def option.distinct(1))
 done
 have H : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def H1 H2)
 done

 have Z:"insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>} = insert (x \<tau>) (\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>})"
         by(auto simp: E)
 show ?thesis
  apply(insert def_X[THEN  foundation13[THEN iffD2]] val_x[THEN  foundation13[THEN iffD2]]
               val_y[THEN  foundation13[THEN iffD2]])
  apply(simp add: foundation22 OclIncluding_def OclExcluding_def def_X[THEN foundation17])
  apply(subst cp_defined, simp)  apply(subst cp_defined, simp)
  apply(subst cp_defined, simp)  apply(subst cp_defined, simp)
  apply(subst cp_defined, simp)
  apply(simp add: G H Abs_Set_0_inverse[OF C] Abs_Set_0_inverse[OF D] Z)
  done
qed

lemma excluding_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> (((X->including(x))->excluding(x)) \<triangleq> (X->excluding(x)))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 have G1 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 None"
          apply(insert C, simp)
          apply(simp add:  def_X val_x A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
 done
 have G2 : "Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<noteq> Abs_Set_0 \<lfloor>None\<rfloor>"
          apply(insert C, simp)
          apply(simp add:  def_X val_x A Abs_Set_0_inject B C OclValid_def Rep_Set_0_cases Rep_Set_0_inverse bot_Set_0_def bot_option_def insert_compr insert_def not_Some_eq null_Set_0_def null_option_def)
 done
 show ?thesis
   apply(insert def_X[THEN foundation17] val_x[THEN foundation19])
   apply(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def false_def true_def
                    invalid_def defined_def valid_def bot_Set_0_def null_fun_def null_Set_0_def
                    StrongEq_def)
   apply(subst cp_OclExcluding) back
   apply(auto simp:OclExcluding_def)
   apply(simp add: Abs_Set_0_inverse[OF C])
   apply(simp_all add: false_def true_def defined_def valid_def
                       null_fun_def bot_fun_def null_Set_0_def bot_Set_0_def
                  split: bool.split_asm HOL.split_if_asm option.split)
   apply(auto simp: G1 G2)
  done
qed

lemma excluding_charn_exec[code_unfold]:
 assumes strict1: "(x \<doteq> invalid) = invalid"
 and     strict2: "(invalid \<doteq> y) = invalid"
 and     StrictRefEq_valid_args_valid: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                     (\<tau> \<Turnstile> \<delta> (x \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
 and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
 and     StrictRefEq_vs_strongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                      \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> (\<tau> \<Turnstile> ((x \<doteq> y) \<triangleq> (x \<triangleq> y)))"
 shows "(X->including(x::('\<AA>,'a::null)val)->excluding(y)) =
        (if \<delta> X then if x \<doteq> y
                     then X->excluding(y)
                     else X->excluding(y)->including(x)
                     endif
                else invalid endif)"
proof -
 (* Lifting theorems, largely analogous includes_execute_generic,
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
           apply(subst cp_if_ocl)
           apply(subst StrictRefEq_vs_strongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_if_ocl[symmetric])

 have F: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
           (X->including(x)->excluding(y) \<tau>) = (X->excluding(y) \<tau>)"
           apply(drule StrongEq_L_sym)
           apply(rule foundation22[THEN iffD1])
           apply(erule StrongEq_L_subst2_rev,simp)
           by(simp add: excluding_charn2)

 show ?thesis
    apply(rule ext, rename_tac "\<tau>")
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<delta> X))", simp add:def_split_local,elim disjE A1 B1 A2 B2)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> x))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym)
    apply(simp add: foundation22 C)
    apply(case_tac "\<not> (\<tau> \<Turnstile> (\<upsilon> y))",
          simp add:foundation18 foundation22[symmetric],
          drule StrongEq_L_sym, simp add: foundation22 D, simp)
    apply(subst E,simp_all)
    apply(case_tac "\<tau> \<Turnstile> not (x \<triangleq> y)")
    apply(simp add: excluding_charn1[simplified foundation22]
                    excluding_charn2[simplified foundation22])
    apply(simp add: foundation9 F)
 done
qed

(* Hack to work around OF-Bug *)
schematic_lemma excluding_charn_exec_int[code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq_int_strict1 StrictRefEq_int_strict2
                                StrictRefEq_int_defined_args_valid
                             cp_StrictRefEq_int StrictRefEq_int_vs_strongEq], simp_all)

schematic_lemma excluding_charn_exec_bool[code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq_bool_strict1 StrictRefEq_bool_strict2
                                StrictRefEq_bool_defined_args_valid
                             cp_StrictRefEq_bool StrictRefEq_bool_vs_strongEq], simp_all)

schematic_lemma excluding_charn_exec_set[code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq_set_strict1 StrictRefEq_set_strict2
                                StrictRefEq_set_strictEq_valid_args_valid
                             cp_StrictRefEq_set strictRefEq_set_vs_strongEq], simp_all)

syntax
  "_OclFinset" :: "args => ('\<AA>,'a::null) Set"    ("Set{(_)}")
translations
  "Set{x, xs}" == "CONST OclIncluding (Set{xs}) x"
  "Set{x}"     == "CONST OclIncluding (Set{}) x "

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including(\<one>)->including(\<two>))"
by (rule refl)

lemma set_test1: "\<tau> \<Turnstile> (Set{\<two>,null}->includes(null))"
by(simp add: includes_execute_int)

lemma set_test2: "\<not>(\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes(null)))"
by(simp add: includes_execute_int)


text{* Here is an example of a nested collection. Note that we have
to use the abstract null (since we did not (yet) define a concrete
constant @{term null} for the non-existing Sets) :*}
lemma semantic_test2:
assumes H:"(Set{\<two>} \<doteq> null) = (false::('\<AA>)Boolean)"
shows   "(\<tau>::('\<AA>)st) \<Turnstile> (Set{Set{\<two>},null}->includes(null))"
by(simp add: includes_execute_set H)


lemma semantic_test3: "\<tau> \<Turnstile> (Set{null,\<two>}->includes(null))"
by(simp_all add: including_charn1 including_defined_args_valid)



(* legacy --- still better names ?
lemmas defined_charn = foundation16
lemmas definedD = foundation17
lemmas valid_charn =
lemmas validD = foundation19
lemmas valid_implies_defined = foundation20
 end legacy *)




lemma StrictRefEq_set_exec[simp,code_unfold] :
"((x::('\<AA>,'\<alpha>::null)Set) \<doteq> y) =
  (if \<delta> x then (if \<delta> y
                then ((x->forall(z| y->includes(z)) and (y->forall(z| x->includes(z)))))
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

 have defined_inject_true : "\<And>\<tau> P. \<not> (\<tau> \<Turnstile> \<delta> P) \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
 by(metis bot_fun_def defined_def foundation16 null_fun_def)

 have valid_inject_true : "\<And>\<tau> P. \<not> (\<tau> \<Turnstile> \<upsilon> P) \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
 by(metis bot_fun_def foundation18' valid_def)

 have valid_inject_defined : "\<And>\<tau> P. \<not> (\<tau> \<Turnstile> \<upsilon> P) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<delta> P)"
 by(metis foundation20)

 have null_simp : "\<And>\<tau> y. \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<delta> y) \<Longrightarrow> y \<tau> = null \<tau>"
 by (simp add: foundation16 foundation18' null_fun_def)

 have bot_in_set_0 : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_null_false : "\<And>\<tau>. (null \<tau> = false \<tau>) = False" by (metis defined4 foundation1 foundation16 null_fun_def)
 have discr_eq_null_true : "\<And>\<tau>. (null \<tau> = true \<tau>) = False" by (metis OclValid_def foundation4)
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis defined3 defined_def discr_eq_false_true)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False" by (metis bot_fun_def discr_eq_bot1_true)
 have discr_eq_bot1_false : "\<And>\<tau>. (\<bottom> \<tau> = false \<tau>) = False" by (metis OCL_core.bot_fun_def defined4 foundation1 foundation16)
 have discr_eq_bot2_false : "\<And>\<tau>. (\<bottom> = false \<tau>) = False" by (metis foundation1 foundation18' valid4)
 have discr_neq_false_true : "\<And>\<tau>. (false \<tau> \<noteq> true \<tau>) = True" by (metis discr_eq_false_true)
 have discr_neq_true_false : "\<And>\<tau>. (true \<tau> \<noteq> false \<tau>) = True" by (metis discr_eq_false_true)

 have not_bot_in_set : "\<And>\<tau> x e. (\<tau> \<Turnstile> \<delta> x) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)) \<Longrightarrow> e \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<Longrightarrow> False"
 (* use Set_inv_lemma2 *)
  apply(frule Set_inv_lemma)
  apply(erule disjE)
  apply(simp add: OclValid_def valid_def)
  apply(simp add: Abs_Set_0_inverse[OF bot_in_set_0])
  apply(split split_if_asm)
  apply(simp add: cp_defined[of x])
  apply(simp add: defined_def bot_option_def null_fun_def null_Set_0_def false_def true_def)
  apply(simp)

  apply(drule_tac Q = False and x = e in ballE, simp_all add: OclValid_def valid_def bot_fun_def)
 done

 have forall_exec_true : "\<And>\<tau> x y. \<tau> \<Turnstile> \<delta> x \<Longrightarrow>
                                  \<tau> \<Turnstile> \<delta> y \<Longrightarrow>
                     (\<tau> \<Turnstile> OclForall x (OclIncludes y)) = (\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>)"
 (* global ! et structurer ! bu *)
  apply(case_tac "\<tau> \<Turnstile> OclForall x (OclIncludes y)")
  (* *)
  apply(simp add: OclValid_def OclForall_def)
  apply(split split_if_asm, simp add: discr_eq_false_true discr_eq_bot1_true discr_eq_null_true)+
  apply(simp)
  apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> y->includes((\<lambda>_. x)))")
   prefer 2
   apply(simp add: OclValid_def)
   apply (metis (full_types) bot_fun_def bool_split invalid_def null_fun_def)
  apply(rule subsetI, rename_tac e)
  apply(drule bspec)
  apply(assumption)
  apply(erule_tac x = e and P = "\<lambda>x. (\<tau> \<Turnstile> y->includes((\<lambda>_. x)))" in ballE)
  apply(simp add: OclIncludes_def OclValid_def)
  apply(case_tac "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)", simp add: OclValid_def)
  apply(metis option.inject true_def)
  apply(simp add: OclValid_def bot_option_def true_def)
  apply(simp)

  (* *)
  apply(simp add: OclValid_def OclForall_def)
  apply(subgoal_tac "(\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>. (y->includes((\<lambda>_. x))) \<tau> = false \<tau>
                                           \<or> (y->includes((\<lambda>_. x))) \<tau> = \<bottom> \<tau>
                                           \<or> (y->includes((\<lambda>_. x))) \<tau> = null \<tau>)")
   prefer 2
   apply metis
  apply(erule bexE, rename_tac e)
  apply(simp add: OclIncludes_def)

  apply(case_tac "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)", simp add: OclValid_def)
  apply(erule disjE)
  apply(metis (mono_tags) discr_eq_false_true false_def set_mp true_def)
  apply(simp add: bot_fun_def bot_option_def null_fun_def null_option_def)

  apply(subgoal_tac False, simp)
  apply(rule not_bot_in_set)
   prefer 3
   apply(assumption, simp_all add: OclValid_def)
 done

 have forall_exec_false : "\<And>\<tau> x y. \<tau> \<Turnstile> \<delta> x \<Longrightarrow>
                                   \<tau> \<Turnstile> \<delta> y \<Longrightarrow>
                     (OclForall x (OclIncludes y) \<tau> = false \<tau>) = (\<not> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>)"

  apply(subgoal_tac "\<not> (OclForall x (OclIncludes y) \<tau> = false \<tau>) = (\<not> (\<not> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>))")
  apply(simp)
  apply(subst forall_exec_true[symmetric]) apply(simp)+
  apply(subst OclValid_def)
  apply(simp add: OclForall_def
                  discr_neq_false_true
                  discr_neq_true_false
                  discr_eq_bot1_false
                  discr_eq_bot2_false
                  discr_eq_bot1_true
                  discr_eq_bot2_true
                  discr_eq_null_false
                  discr_eq_null_true)
  apply(simp add: OclValid_def)
  apply(subgoal_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>. ((y->includes((\<lambda>_. x))) \<tau> = true \<tau> \<or> (y->includes((\<lambda>_. x))) \<tau> = false \<tau>))")
  apply(metis bot_fun_def discr_eq_bot2_true discr_eq_null_true null_fun_def)
  apply(rule ballI, rename_tac e)
  apply(simp add: OclIncludes_def, rule conjI)
  apply (metis (full_types) false_def true_def)

  apply(rule impI)
  apply(subgoal_tac False, simp)
  apply(rule not_bot_in_set)
   prefer 3
   apply(assumption, simp_all add: OclValid_def)
 done

 have strongeq_true : "\<And> \<tau> x y. (\<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = true \<tau>) = (x \<tau> = y \<tau>)"
 by(simp add: foundation22[simplified OclValid_def StrongEq_def])

 have strongeq_false : "\<And> \<tau> x y. (\<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = false \<tau>) = (x \<tau> \<noteq> y \<tau>)"
  apply(case_tac "x \<tau> \<noteq> y \<tau>", simp add: false_def)
  apply(simp add: false_def true_def)
 done

 have rep_set_inj : "\<And>\<tau>. (\<delta> x) \<tau> = true \<tau> \<Longrightarrow>
                         (\<delta> y) \<tau> = true \<tau> \<Longrightarrow>
                          x \<tau> \<noteq> y \<tau> \<Longrightarrow>
                          \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil> \<noteq> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>"
  apply(simp add: defined_def)
  apply(split split_if_asm, simp add: false_def true_def)+
  apply(simp add: null_fun_def null_Set_0_def bot_fun_def bot_Set_0_def)

  apply(case_tac "x \<tau>")
  apply(case_tac "ya", simp_all)
  apply(case_tac "a", simp_all)

  apply(case_tac "y \<tau>")
  apply(case_tac "yaa", simp_all)
  apply(case_tac "ab", simp_all)

  apply(simp add: Abs_Set_0_inverse)

  apply(blast)
 done

 show ?thesis
  apply(rule ext, rename_tac \<tau>)
  (* *)
  apply(simp add: cp_if_ocl[of "\<delta> x"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> x)")
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<delta> x)")
   prefer 2
   apply(metis foundation20)
  apply(simp add: defined_inject_true)
  apply(simp add: cp_if_ocl[symmetric] OclValid_def StrictRefEq_set)

  apply(simp)
  (* *)
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> y)")
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<delta> y)")
   prefer 2
   apply(metis foundation20)
  apply(simp add: defined_inject_true)
  apply(simp add: cp_if_ocl[symmetric] OclValid_def StrictRefEq_set)

  apply(simp)
  (* *)
  apply(simp add: cp_if_ocl[of "\<delta> y"])
  apply(simp add: cp_if_ocl[symmetric])

  (* *)
  apply(simp add: cp_if_ocl[of "\<delta> x"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> x)")
  apply(simp add: defined_inject_true)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_not[of "\<delta> y"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> y)")
  apply(simp add: defined_inject_true)
  apply(simp add: cp_not[symmetric])
  apply(metis (hide_lams, no_types) OclValid_def StrongEq_sym foundation22 null_fun_def null_simp strictRefEq_set_vs_strongEq true_def)
  apply(simp add: OclValid_def cp_not[symmetric])

  apply(simp add: null_simp[simplified OclValid_def, of x] StrictRefEq_set StrongEq_def false_def)
  apply(simp add: defined_def[of y])
  apply(metis discr_neq_true_false)
  (* *)
  apply(simp)
  apply(simp add: OclValid_def)
  apply(simp add: cp_if_ocl[of "\<delta> y"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> y)")
  apply(simp add: defined_inject_true)
  apply(simp add: cp_if_ocl[symmetric])

  apply(drule null_simp[simplified OclValid_def, of y])
  apply(simp add: OclValid_def)
  apply(simp add: cp_StrictRefEq_set[of x])
  apply(simp add: cp_StrictRefEq_set[symmetric])
  apply(simp add: null_simp[simplified OclValid_def, of y] StrictRefEq_set StrongEq_def false_def)
  apply(simp add: defined_def[of x])
  apply (metis discr_neq_true_false)

  (* *)
  apply(simp add: OclValid_def)


  apply(simp add: StrictRefEq_set StrongEq_def)

  (* ************************* *)
  apply(subgoal_tac "\<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = true \<tau> \<or> \<lfloor>\<lfloor>x \<tau> = y \<tau>\<rfloor>\<rfloor> = false \<tau>")
   prefer 2
   apply(case_tac "x \<tau> = y \<tau>")
   apply(rule disjI1, simp add: true_def)
   apply(rule disjI2, simp add: false_def)
  (* *)
  apply(erule disjE)
  apply(simp add: strongeq_true)

  apply(subgoal_tac "(\<tau> \<Turnstile> OclForall x (OclIncludes y)) \<and> (\<tau> \<Turnstile> OclForall y (OclIncludes x))")
  apply(simp add: cp_ocl_and[of "OclForall x (OclIncludes y)"] true_def OclValid_def)
  apply(simp add: OclValid_def)
  apply(simp add: forall_exec_true[simplified OclValid_def])

  (* *)
  apply(simp add: strongeq_false)

  apply(subgoal_tac "OclForall x (OclIncludes y) \<tau> = false \<tau> \<or> OclForall y (OclIncludes x) \<tau> = false \<tau>")
  apply(simp add: cp_ocl_and[of "OclForall x (OclIncludes y)"] false_def)
  apply(erule disjE)
   apply(simp)
   apply(subst cp_ocl_and[symmetric])
   apply(simp only: ocl_and_false1[simplified false_def])

   apply(simp)
   apply(subst cp_ocl_and[symmetric])
   apply(simp only: ocl_and_false2[simplified false_def])
  apply(simp add: forall_exec_false[simplified OclValid_def] rep_set_inj)
 done
qed



lemma forall_set_null_exec[simp,code_unfold] :
"(null->forall(z| P(z))) = invalid"
by(simp add: OclForall_def invalid_def false_def true_def)

lemma forall_set_mt_exec[simp,code_unfold] :
"((Set{})->forall(z| P(z))) = true"
apply(simp add: OclForall_def)
apply(subst mtSet_def)+
apply(subst Abs_Set_0_inverse, simp_all add: true_def)+
done

lemma exists_set_null_exec[simp,code_unfold] :
"(null->exists(z | P(z))) = invalid"
by(simp add: OclExists_def)

lemma exists_set_mt_exec[simp,code_unfold] :
"((Set{})->exists(z | P(z))) = false"
by(simp add: OclExists_def)

lemma forall_set_including_exec[simp,code_unfold] :
 assumes cp: "\<And>\<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
 shows "((S->including(x))->forall(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                 then P x and (S->forall(z | P(z)))
                                                 else invalid
                                                 endif)"
proof -

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done

 have d_and_v_destruct_defined : "\<And>\<tau> S x. \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> S"
  by (simp add: foundation5[THEN conjunct1])
 have d_and_v_destruct_valid  :"\<And>\<tau> S x. \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
  by (simp add: foundation5[THEN conjunct2])

 have forall_including_invert : "\<And>\<tau> f. (f x \<tau> = f (\<lambda> _. x \<tau>) \<tau>) \<Longrightarrow>
                                          \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                                          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>) =
                                          (f x \<tau> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>))"
  apply(simp add: OclIncluding_def)
  apply(subst Abs_Set_0_inverse)
  apply(rule insert_in_Set_0)
  apply(rule d_and_v_destruct_defined, assumption)
  apply(rule d_and_v_destruct_valid, assumption)
  apply(simp add: d_and_v_destruct_defined d_and_v_destruct_valid)
  apply(frule d_and_v_destruct_defined, drule d_and_v_destruct_valid)
  apply(simp add: OclValid_def)
 done

 have exists_including_invert : "\<And>\<tau> f. (f x \<tau> = f (\<lambda> _. x \<tau>) \<tau>) \<Longrightarrow>
                                          \<tau> \<Turnstile> (\<delta> S and \<upsilon> x) \<Longrightarrow>
                                          (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>) =
                                          (f x \<tau> \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. f (\<lambda>_. x) \<tau>))"
  apply(subst arg_cong[where f = "\<lambda>x. \<not>x",
                       OF forall_including_invert[where f = "\<lambda>x \<tau>. \<not> (f x \<tau>)"],
                       simplified])
 by simp_all

 have cp_eq : "\<And>\<tau> v. (P x \<tau> = v) = (P (\<lambda>_. x \<tau>) \<tau> = v)" by(subst cp, simp)
 have cp_not_eq : "\<And>\<tau> v. (P x \<tau> \<noteq> v) = (P (\<lambda>_. x \<tau>) \<tau> \<noteq> v)" by(subst cp, simp)

 have foundation10': "\<And>\<tau> x y. (\<tau> \<Turnstile> x) \<and> (\<tau> \<Turnstile> y) \<Longrightarrow> \<tau> \<Turnstile> (x and y)"
  apply(erule conjE)
  apply(subst foundation10)
  apply(rule foundation6, simp)
  apply(rule foundation6, simp)
 by simp

 have contradict_Rep_Set_0: "\<And>\<tau> S f.
         \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. f (\<lambda>_. x) \<tau> \<Longrightarrow>
         (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>)) = False"
 by(case_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) \<tau>)) = True", simp_all)

 show ?thesis

  apply(rule ext, rename_tac \<tau>)
  apply(simp add: if_ocl_def)
  apply(simp add: cp_defined[of "\<delta> S and \<upsilon> x"])
  apply(simp add: cp_defined[THEN sym])
  apply(rule conjI, rule impI)

  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S")
    prefer 2
    apply(drule foundation5[simplified OclValid_def], erule conjE)+ apply(simp add: OclValid_def)

  apply(subst OclForall_def)
  apply(simp add: cp_ocl_and[THEN sym] OclValid_def
                  foundation10'[where x = "\<delta> S" and y = "\<upsilon> x", simplified OclValid_def])

  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> x)")
    prefer 2
    apply(simp add: OclValid_def)

  (* false *)
    (* false YES *)
  apply(case_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau>", simp_all)
  apply(subst contradict_Rep_Set_0[where f = "\<lambda> x \<tau>. P x \<tau> = false \<tau>"], simp)+
  apply(simp add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = false \<tau>", OF cp_eq])

  apply(simp add: cp_ocl_and[of "P x"])
  apply(erule disjE)
  apply(simp only: cp_ocl_and[symmetric], simp)

  apply(subgoal_tac "OclForall S P \<tau> = false \<tau>")
  apply(simp only: cp_ocl_and[symmetric], simp)
  apply(simp add: OclForall_def)

    (* false NO *)
  apply(simp add: forall_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> \<noteq> false \<tau>", OF cp_not_eq],
        erule conjE)

  (* bot *)
    (* bot YES *)
  apply(case_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = bot \<tau>", simp_all)
  apply(subst contradict_Rep_Set_0[where f = "\<lambda> x \<tau>. P x \<tau> = bot \<tau>"], simp)+
  apply(simp add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = bot \<tau>", OF cp_eq])

  apply(simp add: cp_ocl_and[of "P x"])
  apply(erule disjE)

  apply(subgoal_tac "OclForall S P \<tau> \<noteq> false \<tau>")
  apply(simp only: cp_ocl_and[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

  apply(subgoal_tac "OclForall S P \<tau> = bot \<tau>")
  apply(simp only: cp_ocl_and[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

    (* bot NO *)
  apply(simp add: forall_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> \<noteq> bot \<tau>", OF cp_not_eq],
        erule conjE)

  (* null *)
    (* null YES *)
  apply(case_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau>", simp_all)
  apply(subst contradict_Rep_Set_0[where f = "\<lambda> x \<tau>. P x \<tau> = null \<tau>"], simp)+
  apply(simp add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = null \<tau>", OF cp_eq])

  apply(simp add: cp_ocl_and[of "P x"])
  apply(erule disjE)

  apply(subgoal_tac "OclForall S P \<tau> \<noteq> false \<tau> \<and> OclForall S P \<tau> \<noteq> bot \<tau>")
  apply(simp only: cp_ocl_and[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

  apply(subgoal_tac "OclForall S P \<tau> = null \<tau>")
  apply(simp only: cp_ocl_and[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

    (* null NO *)
  apply(simp add: forall_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> \<noteq> null \<tau>", OF cp_not_eq],
        erule conjE)

  (* true *)
  apply(simp add: cp_ocl_and[of "P x"] OclForall_def)
  apply(subgoal_tac "P x \<tau> = true \<tau>", simp)
  apply(metis bot_fun_def bool_split foundation18' foundation2 valid1)

  (* invalid *)
  by(metis OclForall_def including_defined_args_valid' invalid_def)
qed

lemma not_if[simp]:
"not(if P then C else E endif) = (if P then not C else not E endif)"
  (* non-trivial but elementary *)
  apply(rule not_inject, simp)
  apply(rule ext)
  apply(subst cp_not, simp add: if_ocl_def)
  apply(subst cp_not[symmetric] not_not)+
by simp

lemma exists_set_including_exec[simp,code_unfold] :
 assumes cp: "\<And>\<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
 shows "((S->including(x))->exists(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                 then P x or (S->exists(z | P(z)))
                                                 else invalid
                                                 endif)"
  apply(simp add: OclExists_def ocl_or_def)

  apply(rule not_inject)
  apply(simp)
  apply(rule forall_set_including_exec)
  apply(rule sym, subst cp_not)
  apply(simp only: cp[symmetric] cp_not[symmetric])
done



lemma set_test4 : "\<tau> \<Turnstile> (Set{\<two>,null,\<two>} \<doteq> Set{null,\<two>})"
proof -

 have cp_1: "\<And>x \<tau>. (if null \<doteq> x then true else if \<two> \<doteq> x then true else if \<upsilon> x then false else invalid endif endif endif) \<tau> =
                 (if null \<doteq> (\<lambda>_. x \<tau>) then true else if \<two> \<doteq> (\<lambda>_. x \<tau>) then true else if \<upsilon> (\<lambda>_. x \<tau>) then false else invalid endif endif endif) \<tau>"
  apply(subgoal_tac "(null \<doteq> x) \<tau> = (null \<doteq> (\<lambda>_. x \<tau>)) \<tau> \<and> (\<two> \<doteq> x) \<tau> = (\<two> \<doteq> (\<lambda>_. x \<tau>)) \<tau> \<and> (\<upsilon> x) \<tau> = (\<upsilon> (\<lambda>_. x \<tau>)) \<tau>")
  apply(subst cp_if_ocl[of "null \<doteq> x"])
  apply(subst cp_if_ocl[of "\<two> \<doteq> x"])
  apply(subst cp_if_ocl[of "\<upsilon> x"])
  apply(simp)

  apply(subst if_ocl_def)
  apply(rule sym, subst if_ocl_def)

  apply(simp only: cp_if_ocl[symmetric])
  apply(subgoal_tac "(\<delta> (null \<doteq> (\<lambda>_. x \<tau>))) \<tau> = (\<delta> (\<lambda>_. (null \<doteq> (\<lambda>_. x \<tau>)) \<tau>)) \<tau>")
  apply(simp only:)
  apply(rule cp_defined)

  apply(subst cp_StrictRefEq_int[of null x])
  apply(simp add: null_fun_def)

  apply(subst cp_StrictRefEq_int[of \<two> ])
  apply(simp add: ocl_two_def)

  apply(rule cp_valid)
 done

 have cp_2: "(\<And>x \<tau>. (if \<two> \<doteq> x then true else if null \<doteq> x then true else if \<two> \<doteq> x then true else if \<upsilon> x then false else invalid endif endif endif endif) \<tau> =
                 (if \<two> \<doteq> (\<lambda>_. x \<tau>) then true else if null \<doteq> (\<lambda>_. x \<tau>) then true else
                                                     if \<two> \<doteq> (\<lambda>_. x \<tau>) then true else if \<upsilon> (\<lambda>_. x \<tau>) then false else invalid endif endif endif endif) \<tau>)"
  apply(subgoal_tac "(null \<doteq> x) \<tau> = (null \<doteq> (\<lambda>_. x \<tau>)) \<tau> \<and> (\<two> \<doteq> x) \<tau> = (\<two> \<doteq> (\<lambda>_. x \<tau>)) \<tau> \<and> (\<upsilon> x) \<tau> = (\<upsilon> (\<lambda>_. x \<tau>)) \<tau>")
  apply(subst cp_if_ocl[of "\<two> \<doteq> x"])
  apply(subst cp_if_ocl[of "null \<doteq> x"])
  apply(subst cp_if_ocl[of "\<two> \<doteq> x"])
  apply(subst cp_if_ocl[of "\<upsilon> x"])
  apply(simp)

  apply(subst if_ocl_def)
  apply(rule sym, subst if_ocl_def)

  apply(simp only: cp_if_ocl[symmetric])
  apply(subgoal_tac "(\<delta> (\<two> \<doteq> (\<lambda>_. x \<tau>))) \<tau> = (\<delta> (\<lambda>_. (\<two> \<doteq> (\<lambda>_. x \<tau>)) \<tau>)) \<tau>")
  apply(simp only:)
  apply(rule cp_defined)

  apply(subst cp_StrictRefEq_int[of null x])
  apply(simp add: null_fun_def)

  apply(subst cp_StrictRefEq_int[of \<two> ])
  apply(simp add: ocl_two_def)

  apply(rule cp_valid)
 done

 show ?thesis
  apply(simp add: includes_execute_int)
  apply(simp add: forall_set_including_exec[where P = "\<lambda>z. if null \<doteq> z then true else if \<two> \<doteq> z then true else if \<upsilon> z then false else invalid endif endif endif",
                                            OF cp_1])
  apply(simp add: forall_set_including_exec[where P = "\<lambda>z. if \<two> \<doteq> z then true else if null \<doteq> z then true else if \<two> \<doteq> z then true else if \<upsilon> z then false else invalid endif endif endif endif",
                                            OF cp_2])
 done
qed

lemma OclSize_infinite:
assumes non_finite:"\<tau> \<Turnstile> not(\<delta>(S->size()))"
shows   "(\<tau> \<Turnstile> not(\<delta>(S))) \<or> \<not> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
apply(insert non_finite, simp)
apply(rule impI)
apply(simp add: OclSize_def OclValid_def defined_def)
apply(case_tac "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>",
      simp_all add:null_fun_def null_option_def bot_fun_def bot_option_def)
done

lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_infinite:
assumes non_finite: "\<tau> \<Turnstile> not(\<delta>(S->size()))"
shows "(OclIterate\<^isub>S\<^isub>e\<^isub>t S A F) \<tau> = invalid \<tau>"
apply(insert non_finite [THEN OclSize_infinite])
apply(erule disjE)
apply(simp_all add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def invalid_def)
apply(erule contrapos_np)
apply(simp add: OclValid_def)
done

lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_empty[simp]: "((Set{})->iterate(a; x = A | P a x)) = A"
proof -
 have A1 : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
 by (metis A1 Abs_Set_0_cases Abs_Set_0_inverse cp_defined defined_def false_def mtSet_def mtSet_defined null_fun_def null_option_def null_set_not_defined true_def)
 show ?thesis
      apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def mtSet_def Abs_Set_0_inverse valid_def C)
      apply(rule ext)
      apply(case_tac "A \<tau> = \<bottom> \<tau>", simp_all, simp add:true_def false_def bot_fun_def)
      apply(simp add: A1 Abs_Set_0_inverse)
 done
qed

text{* In particular, this does hold for A = null. *}


lemma cp_OclIterate\<^isub>S\<^isub>e\<^isub>t: "(X->iterate(a; x = A | P a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate(a; x = A | P a x)) \<tau>"
by(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def cp_defined[symmetric])

lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_including:
assumes S_finite:    "\<tau> \<Turnstile> \<delta>(S->size())"
and     F_valid_arg: "(\<upsilon> A) \<tau> = (\<upsilon> (F a A)) \<tau>"
and     F_commute:   "comp_fun_commute F"
and     F_cp:        "\<And> x y \<tau>. F x y \<tau> = F (\<lambda> _. x \<tau>) y \<tau>"
shows   "((S->including(a))->iterate(a; x =     A | F a x)) \<tau> =
         ((S->excluding(a))->iterate(a; x = F a A | F a x)) \<tau>"
proof -

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
  apply(simp add: valid_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P \<tau> = \<bottom>", simp_all add: true_def)

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done

 have insert_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set_0_def null_Set_0_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set_0_inject)
  apply(rule insert_in_Set_0, simp_all add: bot_option_def)

  apply(subst Abs_Set_0_inject)
  apply(rule insert_in_Set_0, simp_all add: null_option_def bot_option_def)
 done

 have remove_finite : "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite ((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: bot_option_def null_Set_0_def null_fun_def
                  foundation18 foundation16 invalid_def)
 done

 have remove_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set_0_def null_Set_0_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set_0_inject)
  apply(rule remove_in_Set_0, simp_all add: bot_option_def)

  apply(subst Abs_Set_0_inject)
  apply(rule remove_in_Set_0, simp_all add: null_option_def bot_option_def)
 done

 have abs_rep: "\<And>x. \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)\<rceil>\<rceil> = x"
 by(subst Abs_Set_0_inverse, simp_all)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 show ?thesis
  apply(simp only: cp_OclIterate\<^isub>S\<^isub>e\<^isub>t[of "S->including(a)"] cp_OclIterate\<^isub>S\<^isub>e\<^isub>t[of "S->excluding(a)"])
  apply(subst OclIncluding_def, subst OclExcluding_def)
  apply(case_tac "\<not> ((\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> a) \<tau> = true \<tau>)", simp)

  apply(subgoal_tac "OclIterate\<^isub>S\<^isub>e\<^isub>t (\<lambda>_. \<bottom>) A F \<tau> = OclIterate\<^isub>S\<^isub>e\<^isub>t (\<lambda>_. \<bottom>) (F a A) F \<tau>", simp)
  apply(rule conjI)
  apply(blast)
  apply(blast)
  apply(auto)

  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def) apply(auto)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)

  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def) apply(auto)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)

  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)

  apply(subst abs_rep[OF insert_in_Set_0[simplified OclValid_def], of \<tau>], simp_all)+
  apply(subst abs_rep[OF remove_in_Set_0[simplified OclValid_def], of \<tau>], simp_all)+
  apply(subst insert_defined, simp_all add: OclValid_def)+
  apply(subst remove_defined, simp_all add: OclValid_def)+

  apply(case_tac "\<not> ((\<upsilon> A) \<tau> = true \<tau>)", simp add: F_valid_arg)
  apply(simp add: valid_inject_true F_valid_arg)
  apply(rule impI)

  apply(subst Finite_Set.comp_fun_commute.fold_fun_comm[where f = F and z = A and x = a and A = "((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))", symmetric, OF F_commute])
  apply(rule remove_finite, simp)

  apply(subst image_set_diff[OF inject], simp)
  apply(subgoal_tac "Finite_Set.fold F A (insert (\<lambda>\<tau>'. a \<tau>) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)) \<tau> =
      F (\<lambda>\<tau>'. a \<tau>) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {\<lambda>\<tau>'. a \<tau>})) \<tau>")
  apply(subst F_cp)
  apply(simp)

  apply(subst Finite_Set.comp_fun_commute.fold_insert_remove[OF F_commute])
  apply(simp)+
 done
qed


lemma [simp]: "\<delta> (Set{} ->size()) = true"
proof -
 have A1 : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 have A2 : "None \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"  by(simp add: bot_option_def)
 have A3 : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def null_option_def)
 show ?thesis
  apply(rule ext)
  apply(simp add: defined_def mtSet_def OclSize_def
                  bot_Set_0_def bot_fun_def
                  null_Set_0_def null_fun_def)
  apply(subst Abs_Set_0_inject, simp_all add: A1 A2 A3 bot_option_def null_option_def) +
 by(simp add: A1 Abs_Set_0_inverse bot_fun_def bot_option_def null_fun_def null_option_def)
qed

lemma finite_including_exec :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert X_def x_val, frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclIncluding_def Abs_Set_0_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma finite_excluding_exec :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert X_def x_val, frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclExcluding_def Abs_Set_0_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma including_size_defined[simp]: "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have finite_including_exec : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_including_exec)
  apply(metis OclValid_def foundation5)+
 done

 have card_including_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> = (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
  apply(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)
 done

 show ?thesis

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->including(x)->size())) \<tau> = true \<tau>", simp)
  apply(subst cp_ocl_and)
  apply(subst cp_defined)
  apply(simp only: cp_defined[of "X->including(x)->size()"])
  apply(simp add: OclSize_def)
  apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil>)", simp)
  prefer 2
  apply(simp)
  apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def)
  apply(erule conjE)
  apply(simp add: finite_including_exec[simplified OclValid_def] card_including_exec
                  cp_ocl_and[of "\<delta> X" "\<upsilon> x"]
                  cp_ocl_and[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_ocl_and[THEN sym])

  apply(drule defined_inject_true[of "X->including(x)->size()"], simp)
  apply(simp only: cp_ocl_and[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->including(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def card_including_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: finite_including_exec[simplified OclValid_def] card_including_exec)
  apply(simp only: cp_ocl_and[THEN sym])
  apply(simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
  apply(simp add: finite_including_exec[simplified OclValid_def])
  apply(simp add: finite_including_exec[simplified OclValid_def] card_including_exec)
  apply(simp only: cp_ocl_and[THEN sym])
  apply(simp)
  apply(rule impI)
  apply(erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(drule valid_inject_true[of "x"], simp add: cp_ocl_and[of _ "\<upsilon> x"])
  apply(simp add: cp_ocl_and[THEN sym])
 done
qed

lemma excluding_size_defined[simp]: "\<delta> ((X ->excluding(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def
                      bot_option_def null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by(case_tac "P \<tau> = \<bottom>", simp_all add: true_def)


 have finite_excluding_exec : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                                     finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil> =
                                     finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_excluding_exec)
  apply(metis OclValid_def foundation5)+
 done

 have card_excluding_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> =
                                   (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
  apply(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)
 done

 show ?thesis

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->excluding(x)->size())) \<tau> = true \<tau>", simp)
  apply(subst cp_ocl_and)
  apply(subst cp_defined)
  apply(simp only: cp_defined[of "X->excluding(x)->size()"])
  apply(simp add: OclSize_def)
  apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil>)", simp)
  prefer 2
  apply(simp)
  apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def)
  apply(erule conjE)
  apply(simp add: finite_excluding_exec card_excluding_exec
                  cp_ocl_and[of "\<delta> X" "\<upsilon> x"]
                  cp_ocl_and[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_ocl_and[THEN sym])

  apply(drule defined_inject_true[of "X->excluding(x)->size()"], simp)
  apply(simp only: cp_ocl_and[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->excluding(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def finite_excluding_exec card_excluding_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: finite_excluding_exec card_excluding_exec)
  apply(simp only: cp_ocl_and[THEN sym])
  apply(simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
  apply(simp add: finite_excluding_exec)
  apply(simp add: finite_excluding_exec card_excluding_exec)
  apply(simp only: cp_ocl_and[THEN sym])
  apply(simp)
  apply(rule impI)
  apply(erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(drule valid_inject_true[of "x"], simp add: cp_ocl_and[of _ "\<upsilon> x"])
  apply(simp add: cp_ocl_and[THEN sym])
 done
qed

lemma size_defined:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> (X->size()) = \<delta> X"
 apply(rule ext, simp add: cp_defined[of "X->size()"] OclSize_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

lemma [simp]:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X) and \<upsilon>(x))"
by(simp add: size_defined[OF X_finite])

section{* Example *}
subsection{* Gogolla's Challenge on Sets *}

(*
Sequence{6,8}->iterate(i;r1:Sequence(Integer)=Sequence{9}|
  r1->iterate(j;r2:Sequence(Integer)=r1|
    r2->including(0)->including(i)->including(j)))
*)

text{* @{term OclIterate\<^isub>S\<^isub>e\<^isub>t} is defined with the function @{term Finite_Set.fold}.
So when proving properties where the term @{term OclIterate\<^isub>S\<^isub>e\<^isub>t} appears at some point,
most lemmas defined in
the library @{theory Finite_Set} could be helpful for the proof.
 However, for some part of the Gogolla's Challenge proof, it is required
to have this statement @{thm (concl) comp_fun_commute.fold_insert}
(coming from @{text comp_fun_commute.fold_insert}),
but @{text comp_fun_commute.fold_insert} requires @{text comp_fun_commute},
which is not trivial to prove on two OCL terms without extra hypothesis
(like finiteness on sets).
Thus, we overload here this @{text comp_fun_commute}. *}

definition "is_int x \<equiv> \<forall> \<tau>. \<tau> \<Turnstile> \<upsilon> x \<and> (\<forall>\<tau>0. x \<tau> = x \<tau>0)"

lemma int_is_valid : "\<And>x. is_int x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
by (metis foundation18' is_int_def)

definition "all_int_set S \<equiv> finite S \<and> (\<forall>x\<in>S. is_int x)"
definition "all_int \<tau> S \<equiv> (\<tau> \<Turnstile> \<delta> S) \<and> all_int_set \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
definition "all_defined_set \<tau> S \<equiv> finite S \<and> (\<forall>x\<in>S. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x)))"
definition "all_defined_set' \<tau> S \<equiv> finite S"
definition "all_defined \<tau> S \<equiv> (\<tau> \<Turnstile> \<delta> S) \<and> all_defined_set \<tau> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"

term "all_defined \<tau> (f \<zero> Set{\<zero>}) = (all_defined \<tau> Set{\<zero>})"
 (* we check here that all_defined could at least be applied to some useful value
    (i.e. we examine the type of all_defined) *)

locale EQ_comp_fun_commute000' =
  fixes f :: "('a state \<times> 'a state \<Rightarrow> int option option)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes cp_set : "\<And>x S \<tau>. f (\<lambda>_. \<lfloor>x\<rfloor>) S \<tau> = f (\<lambda>_. \<lfloor>x\<rfloor>) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>(x:: int option) y. (\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> (f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y)) = (\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<and> (\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> y))"
  assumes commute: "
                             \<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>x\<rfloor>) \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (\<lambda>_. \<lfloor>y\<rfloor>) (f (\<lambda>_. \<lfloor>x\<rfloor>) S) = f (\<lambda>_. \<lfloor>x\<rfloor>) (f (\<lambda>_. \<lfloor>y\<rfloor>) S)"
begin
 lemmas fun_left_comm = commute
end

locale EQ_comp_fun_commute000 =
  fixes f :: "('a state \<times> 'a state \<Rightarrow> int option option)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes cp_set : "\<And>x S \<tau>. f (\<lambda>(_::'a state \<times> 'a state). x) S \<tau> = f (\<lambda>(_::'a state \<times> 'a state). x) (\<lambda>_. S \<tau>) \<tau>"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f (\<lambda>(_::'a state \<times> 'a state). x) y)) = (is_int (\<lambda>(_ :: 'a state \<times> 'a state). x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y.
                             is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'a state \<times> 'a state). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f (\<lambda>(_::'a state \<times> 'a state). y) (f (\<lambda>(_::'a state \<times> 'a state). x) S) = f (\<lambda>(_::'a state \<times> 'a state). x) (f (\<lambda>(_::'a state \<times> 'a state). y) S)"
begin
 lemmas fun_left_comm = commute
end

locale EQ_comp_fun_commute =
  fixes f :: "('a state \<times> 'a state \<Rightarrow> int option option)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes cp_x : "\<And>x S \<tau>. f x S \<tau> = f (\<lambda>_. x \<tau>) S \<tau>"
  assumes cp_set : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen : "\<And>x S \<tau>1 \<tau>2. is_int x \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty : "\<And>x S \<tau>. (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>(x:: 'a state \<times> 'a state \<Rightarrow> int option option) y. all_defined \<tau> (f x y) = (\<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> y)"
  assumes commute: "
                             \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
                             \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                             all_defined \<tau> S \<Longrightarrow>
                             f y (f x S) \<tau> = f x (f y S) \<tau>"
begin
 lemma fun_left_comm: "\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>
                       \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
                       all_defined \<tau> S \<Longrightarrow>
                       f x (f y S) \<tau> = f y (f x S) \<tau>"
 by(rule commute, simp_all add: all_def)
end

lemma EQ_sym : "(x::'b state \<times> 'b state \<Rightarrow> int option option Set_0) = y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<doteq> y)"
  apply(simp add: OclValid_def)
done

text{* TODO add some comment on comparison with inductively constructed OCL term *}
(*
inductive EQ1_fold_graph :: "(('a state \<times> 'a state \<Rightarrow> int option option)
   \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
     \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)) \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Rightarrow> bool"
 for f and z where
  EQ1_emptyI [intro]: "EQ1_fold_graph f z Set{} z" |
  EQ1_insertI [intro]: "\<not> (\<tau> \<Turnstile> A->includes(x)) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow> all_defined \<tau> A \<Longrightarrow> EQ1_fold_graph f z A y
      \<Longrightarrow> EQ1_fold_graph f z (A->including(x)) (f x y)"

inductive_cases EQ1_empty_fold_graphE [elim!]: "EQ1_fold_graph f z Set{} x"
*)

(*
inductive EQ_fold_graph :: "(('a state \<times> 'a state \<Rightarrow> int option option)
                              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0))
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option) set
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
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

locale EQ_comp_fun_commute0 =
  fixes f :: "int option option
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes cp_set : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (\<lambda>(_::'a state \<times> 'a state). x) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y.
                             is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'a state \<times> 'a state). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"
begin
 lemma fun_left_comm:
                            "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow>
                             is_int (\<lambda>(_::'a state \<times> 'a state). y) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"
 by(rule commute, simp_all add: all_def)
end

lemma c0_of_c :
 assumes f_comm : "EQ_comp_fun_commute f"
   shows "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
proof - interpret EQ_comp_fun_commute f by (rule f_comm) show ?thesis thm all_def[THEN iffD1]
 apply(simp only: EQ_comp_fun_commute0_def)
 apply(rule conjI)+ apply(rule allI)+
 apply(rule cp_set)
 apply(rule allI)+ apply(rule impI)+
 apply(subst cp_gen, simp, blast, simp, simp)
 apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
 apply(rule notempty, blast, simp add: int_is_valid, simp)
 apply(rule conjI)+ apply(rule allI)+
 apply (metis (mono_tags) all_def is_int_def)
 apply(rule allI)+ apply(rule impI)+

 apply(rule ext, rename_tac \<tau>)
 apply(subst commute)
 apply (metis is_int_def)+
done
qed

locale EQ_comp_fun_commute0' =
  fixes f :: "int option
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes cp_set : "\<And>x S \<tau>. f x S \<tau> = f x (\<lambda>_. S \<tau>) \<tau>"
  assumes cp_gen' : "\<And>x S \<tau>1 \<tau>2. is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> S \<tau>1 = S \<tau>2 \<Longrightarrow> f x S \<tau>1 = f x S \<tau>2"
  assumes notempty' : "\<And>x S \<tau>. \<forall>\<tau>. all_defined \<tau> S \<Longrightarrow> is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (f x S \<tau>)\<rceil>\<rceil> \<noteq> {}"
  assumes all_def: "\<And>x y. (\<forall>\<tau>. all_defined \<tau> (f x y)) = (is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  assumes commute: "\<And>x y.
                             is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow>
                             is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"
begin
 lemma fun_left_comm: "
                             is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow>
                             is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>y\<rfloor>) \<Longrightarrow>
                             (\<And>\<tau>. all_defined \<tau> S) \<Longrightarrow>
                             f y (f x S) = f x (f y S)"
 by(rule commute, simp_all add: all_def)
end

lemma c0'_of_c0 :
 assumes "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
   shows "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
by(insert assms, simp only: EQ_comp_fun_commute0'_def EQ_comp_fun_commute0_def, blast)

lemma int_trivial : "\<And>a. is_int (\<lambda>_. \<lfloor>a\<rfloor>)" by(simp add: is_int_def OclValid_def valid_def bot_fun_def bot_option_def)

lemma c000_of_c0 : 
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. f (\<lambda>_. x))"
   shows "EQ_comp_fun_commute000 f"
sorry

lemma c000'_of_c0' : 
 assumes f_comm : "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "EQ_comp_fun_commute000' f"
sorry

context EQ_comp_fun_commute
begin

 lemmas F_cp = cp_x
 lemmas F_cp_set = cp_set

 lemma insertI_bis : "x \<notin> A \<Longrightarrow> \<tau> \<Turnstile> \<delta> x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> fold_graph f z (insert x A) (f x y)"
  apply(rule insertI, simp_all)
 done

 lemma fold_graph_insertE_aux:
   assumes y_defined : "all_defined \<tau> y"
   assumes a_valid : "\<tau> \<Turnstile> \<upsilon> a"
   shows
   "fold_graph f z A y \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>y'. y \<tau> = f a y' \<tau> \<and> all_defined \<tau> y' \<and> fold_graph f z (A - {a}) y'"
 apply(insert y_defined)
 proof (induct set: fold_graph)
   case (insertI x A y)
   assume "all_defined \<tau> (f x y)"
   then show "\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> all_defined \<tau> y \<Longrightarrow> ?case"
   proof (cases "x = a") assume "x = a" with insertI show "all_defined \<tau> y \<Longrightarrow> ?case" by (metis Diff_insert_absorb)
   next apply_end(simp)

     assume "x \<noteq> a \<and> all_defined \<tau> y"
     then obtain y' where y: "y \<tau> = f a y' \<tau>" and "all_defined \<tau> y'" and y': "fold_graph f z (A - {a}) y'"
      using insertI by (metis insert_iff)
     have "all_defined \<tau> y \<Longrightarrow> all_defined \<tau> y'"
       apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> a \<and> all_defined \<tau> y'") apply(simp)
       apply(simp add: all_def[where x = a and y = y', symmetric])
       apply(simp add: all_defined_def OclValid_def all_defined_set_def cp_defined[of y])
       unfolding y
       apply(simp add: cp_defined[symmetric])
     done
     moreover have "\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> all_defined \<tau> y' \<Longrightarrow> f x y \<tau> = f a (f x y') \<tau>"
       apply(simp add: F_cp_set[of x y])
       apply(subst F_cp_set[of a])
       apply(simp add: F_cp_set[of x y'])
       unfolding y
       apply(simp add: F_cp_set[symmetric])
     by(rule fun_left_comm, simp_all)
     moreover have "fold_graph f z (insert x A - {a}) (f x y')"
       using y' and `x \<noteq> a \<and> all_defined \<tau> y` and `x \<notin> A`
       by (simp add: insert_Diff_if fold_graph.insertI)
     apply_end(subgoal_tac "x \<noteq> a \<and> all_defined \<tau> y \<Longrightarrow> \<exists>y'. f x y \<tau> = f a y' \<tau> \<and> all_defined \<tau> y' \<and> fold_graph f z (insert x A - {a}) y'", blast)
     ultimately show "\<tau> \<Turnstile> \<upsilon> x \<and> x \<noteq> a \<and> all_defined \<tau> y \<Longrightarrow> ?case" apply(auto simp: a_valid)

    apply(rule_tac x = "f x y'" in exI, simp add: all_def foundation20)
    done
   apply_end(blast)
   qed
  apply_end(simp_all add: all_def)
 qed

 lemma fold_graph_insertE:
   assumes v_defined : "all_defined \<tau> v"
       and x_valid : "\<tau> \<Turnstile> \<upsilon> x"
       and "fold_graph f z (insert x A) v" and "x \<notin> A"
   obtains y where "v \<tau> = f x y \<tau>" and "\<tau> \<Turnstile> \<upsilon> x" and "all_defined \<tau> y" and "fold_graph f z A y"
 using assms by (auto dest: fold_graph_insertE_aux)

 lemma fold_graph_determ:
  assumes x_defined : "all_defined \<tau> x"
      and y_defined : "all_defined \<tau> y"
    shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y \<tau> = x \<tau>"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: fold_graph)
   case (insertI x A y v)
   from `all_defined \<tau> (f x y)`
   have "\<tau> \<Turnstile> \<upsilon> x" by(simp add: all_def)
   from `all_defined \<tau> v` and `\<tau> \<Turnstile> \<upsilon> x` and `fold_graph f z (insert x A) v` and `x \<notin> A`
   obtain y' where "v \<tau> = f x y' \<tau>" and "all_defined \<tau> y'" and "fold_graph f z A y'"
     by (rule fold_graph_insertE)
   from insertI have "all_defined \<tau> y" by (simp add: all_def)
   from `all_defined \<tau> y` and `all_defined \<tau> y'` and `fold_graph f z A y'` have "y' \<tau> = y \<tau>" by (metis insertI.hyps(3))
   with `v \<tau> = f x y' \<tau>` show "v \<tau> = f x y \<tau>" by (simp add: F_cp_set[of x y] F_cp_set[of x y'])
   apply_end(rule_tac f = f in empty_fold_graphE, auto)
 qed

 text{* TODO explain why the determinism property could not be obtained as comp_fun_commute *}
 term (*fold_graph_determ2:
  assumes x_defined : "all_defined \<tau> x"
    shows*) "fold_graph f z A x \<Longrightarrow> \<forall>y. fold_graph f z A y \<longrightarrow> all_defined \<tau> y"

 lemma det_init :
   assumes x_defined : "all_defined \<tau> x"
   shows "fold_graph f z A x \<Longrightarrow> all_defined \<tau> z"
  apply(insert x_defined)
  proof (induct set: fold_graph)
   apply_end(simp)
   apply_end(simp add: all_def)
 qed

 lemma det_init2 :
   assumes z_defined : "all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "fold_graph f z A x \<Longrightarrow> all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: fold_graph)
   apply_end(simp)
   apply_end(simp add: all_def all_int_set_def int_is_valid)
 qed

 lemma fold_graph_determ2 : (* WARNING \<forall> \<tau> is implicit *)
   assumes z_defined : "all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y \<tau> = x \<tau>"
  apply(insert z_defined A_int)
  apply(rule fold_graph_determ)
  apply(rule det_init2) apply(assumption)+
  apply(rule det_init2) apply(assumption)+
 done

 lemma fold_graph_determ3 : (* WARNING \<forall> \<tau> is implicit *)
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
  apply(rule ext, rename_tac \<tau>)
  apply(insert z_defined A_int)
  apply(rule fold_graph_determ)
  apply(rule det_init2) apply(assumption)+
  apply(rule det_init2) apply(assumption)+
 done

 lemma fold_graph_fold:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "fold_graph f z A (Finite_Set.fold f z A)"
 proof -
   from A_int[simplified all_int_set_def, THEN conjunct1] have "\<exists>x. fold_graph f z A x" by (rule finite_imp_fold_graph)
   moreover note fold_graph_determ3[OF z_defined A_int]
   ultimately have "\<exists>!x. fold_graph f z A x" by (rule ex_ex1I)
   then have "fold_graph f z A (The (fold_graph f z A))" by (rule theI')
   then show ?thesis by (unfold Finite_Set.fold_def)
 qed

 definition "Ex1_ocl \<tau> P \<equiv> \<exists>x. P x \<and> (\<forall>y \<tau>. P y \<longrightarrow> y \<tau> = x \<tau>)"

 lemma Ex1_oclE : "Ex1_ocl \<tau> P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> \<forall>y \<tau>. P y \<longrightarrow> y \<tau> = x \<tau> \<Longrightarrow> R) \<Longrightarrow> R"
 by(simp add: Ex1_ocl_def, blast)

 lemma inv_ext : "\<And>f g. f \<noteq> g \<Longrightarrow> \<exists>x. f x \<noteq> g x"
 by(blast)

 lemma fold_graph_fold_ : "fold_graph f z A x \<Longrightarrow> (\<And>\<tau>. x \<tau> = a \<tau>) \<Longrightarrow> fold_graph f z A a"
  apply(case_tac "x = a", simp)
  apply(drule inv_ext, blast)
 done

 lemma fold_equality:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "fold_graph f z A y \<Longrightarrow> Finite_Set.fold f z A = y"
  apply(rule fold_graph_determ3[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done

 lemma fold_insert:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set A"
       and x_int : "is_int x"
       and "x \<notin> A"
   shows "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z A)"
 proof (rule fold_equality)
   have "fold_graph f z A (Finite_Set.fold f z A)" by (rule fold_graph_fold[OF z_defined A_int])
   with `x \<notin> A`show "fold_graph f z (insert x A) (f x (Finite_Set.fold f z A))" by (rule fold_graph.insertI)
   apply_end (simp add: z_defined)
   apply_end (simp add: all_int_set_def x_int A_int[simplified all_int_set_def])
 qed

 lemma all_int_induct:
   assumes "all_int_set (F:: ('a state \<times> 'a state \<Rightarrow> int option option) set)"
   assumes "P {}"
     and insert: "\<And>x F. all_int_set F \<Longrightarrow> is_int x \<Longrightarrow> x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)"
   shows "P F"
 proof -
  have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                   all_int_set S"
  by(simp add: all_int_set_def)
  have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                            is_int x"
  by(simp add: all_int_set_def)

  from `all_int_set F` have "finite F" by (simp add: all_int_set_def)
  show "?thesis"
  using `finite F` and `all_int_set F`
  proof induct
    show "P {}" by fact
    fix x F show "finite F \<Longrightarrow> x \<notin> F \<Longrightarrow> (all_int_set F \<Longrightarrow> P F) \<Longrightarrow> all_int_set (insert x F) \<Longrightarrow> P (insert x F)"
    apply(frule invert_int)
    apply(simp add: invert_all_int_set)
    apply(drule invert_all_int_set)
    proof -
    assume x_int: "is_int x" and F_all : "all_int_set F" and F: "finite F" and P: "P F"
    show "P (insert x F)"
    proof cases
      assume "x \<in> F"
      hence "insert x F = F" by (rule insert_absorb)
      with P show ?thesis by (simp only:)
    next
      assume "x \<notin> F"
      from F_all x_int this P show ?thesis thm insert by (rule insert)
    qed
  qed
  apply_end(simp_all)
  qed
 qed

 lemma fold_def :
   assumes z_def : "\<And>\<tau>. all_defined \<tau> z"
   assumes F_int : "all_int_set F"
   shows "\<And>\<tau>. all_defined \<tau> (Finite_Set.fold f z F)"
 proof (induct rule: all_int_induct[OF F_int])
  apply_end(simp add:z_def)
  apply_end(simp add: fold_insert[OF z_def] all_def int_is_valid)
 qed

 lemma fold_fun_comm:
   assumes z_def : "\<And>\<tau>. all_defined \<tau> z"
   assumes A_int : "all_int_set A"
       and x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
     shows "f x (Finite_Set.fold f z A) = Finite_Set.fold f (f x z) A"
 proof -
  have fxz_def: "\<And>\<tau>. all_defined \<tau> (f x z)"
  by(simp add: all_def x_val z_def)
  show ?thesis
  proof (induct rule: all_int_induct[OF A_int])
   apply_end(simp)
   apply_end(rename_tac x' F)
   apply_end(simp add: fold_insert[OF z_def] fold_insert[OF fxz_def])
   apply_end(rule ext, rename_tac \<tau>)
   apply_end(subst fun_left_comm)
   apply_end(simp add: x_val)
   apply_end(simp add: int_is_valid)
   apply_end(subst fold_def[OF z_def], simp_all)
  qed
 qed

 lemma fold_rec:
    assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
        and A_int : "all_int_set A"
        and x_int : "is_int x"
        and "x \<in> A"
   shows "Finite_Set.fold f z A = f x (Finite_Set.fold f z (A - {x}))"
 proof -
   from A_int have A_int: "all_int_set (A - {x})" by(simp add: all_int_set_def)
   have A: "A = insert x (A - {x})" using `x \<in> A` by blast
   then have "Finite_Set.fold f z A = Finite_Set.fold f z (insert x (A - {x}))" by simp
   also have "\<dots> = f x (Finite_Set.fold f z (A - {x}))" by(rule fold_insert[OF z_defined A_int x_int]) simp
   finally show ?thesis .
 qed

 lemma fold_insert_remove:
    assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
        and A_int : "all_int_set A"
        and x_int : "is_int x"
   shows "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z (A - {x}))"
 proof -
   from A_int have "finite A" by (simp add: all_int_set_def)
   then have "finite (insert x A)" by auto
   moreover have "x \<in> insert x A" by auto
   moreover from A_int have A_int: "all_int_set (insert x A)" by(simp add: all_int_set_def x_int)
   ultimately have "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z (insert x A - {x}))"
   by (subst fold_rec[OF z_defined A_int x_int], simp_all)
   then show ?thesis by simp
 qed

 lemma finite_fold_insert :
  assumes z_defined : "\<forall>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set A"
      and x_int : "is_int x"
      and "x \<notin> A"
   shows "finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold f z (insert x A) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (f x (Finite_Set.fold f z A) \<tau>)\<rceil>\<rceil>"
   apply(subst fold_insert, simp_all add: assms)
 done
end

 inductive EQ_fold_graph :: "(('a state \<times> 'a state \<Rightarrow> int option option)
                              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0))
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option) set
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                            \<Rightarrow> bool"
  for F and z where
  EQ_emptyI [intro]: "EQ_fold_graph F z {} z" |
  EQ_insertI [intro]: "(\<lambda>(_ :: 'a state \<times> 'a state). x) \<notin> A \<Longrightarrow>
                       EQ_fold_graph F z A y \<Longrightarrow>
                       EQ_fold_graph F z (insert (\<lambda>(_ :: 'a state \<times> 'a state). x) A) (F (\<lambda>(_ :: 'a state \<times> 'a state). x) y)"

 inductive_cases EQ_empty_fold_graphE [elim!]: "EQ_fold_graph f z {} x"
 definition fold1 where "fold1 f z A = (THE y. EQ_fold_graph f z A y)"

 inductive EQ_fold_graph2 :: "(('a state \<times> 'a state \<Rightarrow> int option option)
                              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                              \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0))
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option) set
                            \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                            \<Rightarrow> bool"
  for F and z where
  EQ_emptyI2 [intro]: "EQ_fold_graph2 F z {} z" |
  EQ_insertI2 [intro]: "(\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> A \<Longrightarrow>
                       EQ_fold_graph2 F z A y \<Longrightarrow>
                       EQ_fold_graph2 F z (insert (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) A) (F (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y)"

 inductive_cases EQ_empty_fold_graph2E [elim!]: "EQ_fold_graph2 f z {} x"
 definition fold2 where "fold2 f z A = (THE y. EQ_fold_graph2 f z A y)"

lemma eq_fold_of_fold :
 assumes fold_g : "fold_graph F z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). (a::int option option)) ` A) y"
   shows "EQ_fold_graph F z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). (a::int option option)) ` A) y"
  apply(insert fold_g)
  apply(subgoal_tac "\<And>A'. fold_graph F z A' y \<Longrightarrow> A' \<subseteq> (\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A \<Longrightarrow> EQ_fold_graph F z A' y")
  apply(simp)
  proof - fix A' show "fold_graph F z A' y \<Longrightarrow> A' \<subseteq> (\<lambda>a \<tau>. a) ` A (*\<Longrightarrow> \<forall>\<tau>. all_defined \<tau> y*) \<Longrightarrow> EQ_fold_graph F z A' y"
  apply(induction set: fold_graph)
  apply(rule EQ_emptyI)
  apply(simp, erule conjE)
  apply(drule imageE) prefer 2 apply assumption
  apply(simp)
  apply(rule EQ_insertI, simp, simp)
 done
qed

lemma fold_of_eq_fold :
 assumes fold_g : "EQ_fold_graph F z (A:: ('a state \<times> 'a state \<Rightarrow> int option option) set) y"
   shows "fold_graph F z (A:: ('a state \<times> 'a state \<Rightarrow> int option option) set) y"
 apply(insert fold_g)
 apply(induction set: EQ_fold_graph)
 apply(rule emptyI)
 apply(simp add: insertI)
done

lemma eq_fold2_of_fold :
 assumes fold_g : "fold_graph F z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). (\<lfloor>a\<rfloor>::int option option)) ` A) y"
   shows "EQ_fold_graph2 F z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). (\<lfloor>a\<rfloor>::int option option)) ` A) y"
  apply(insert fold_g)
  apply(subgoal_tac "\<And>A'. fold_graph F z A' y \<Longrightarrow> A' \<subseteq> (\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A \<Longrightarrow> EQ_fold_graph2 F z A' y")
  apply(simp)
  proof - fix A' show "fold_graph F z A' y \<Longrightarrow> A' \<subseteq> (\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` A \<Longrightarrow> EQ_fold_graph2 F z A' y"
  apply(induction set: fold_graph)
  apply(rule EQ_emptyI2)
  apply(simp, erule conjE)
  apply(drule imageE) prefer 2 apply assumption
  apply(simp)
  apply(rule EQ_insertI2, simp, simp)
 done
qed

lemma fold_of_eq_fold2 :
 assumes fold_g : "EQ_fold_graph2 F z (A:: ('a state \<times> 'a state \<Rightarrow> int option option) set) y"
   shows "fold_graph F z (A:: ('a state \<times> 'a state \<Rightarrow> int option option) set) y"
 apply(insert fold_g)
 apply(induction set: EQ_fold_graph2)
 apply(rule emptyI)
 apply(simp add: insertI)
done

context EQ_comp_fun_commute000
begin

 lemmas F_cp_set = cp_set

 lemma insertI_bis : "x \<notin> A \<Longrightarrow> \<tau> \<Turnstile> \<delta> x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> fold_graph f z (insert x A) (f x y)"
  apply(rule insertI, simp_all)
 done

 lemma fold_graph_insertE_aux:
   assumes y_defined : "\<And>\<tau>. all_defined \<tau> y"
   assumes a_valid : "is_int (\<lambda>(_::'a state \<times> 'a state). a)"
   shows
   "EQ_fold_graph f z A y \<Longrightarrow> (\<lambda>(_::'a state \<times> 'a state). a) \<in> A \<Longrightarrow> \<exists>y'. y = f (\<lambda>(_::'a state \<times> 'a state). a) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQ_fold_graph f z (A - {(\<lambda>(_::'a state \<times> 'a state). a)}) y'"
 apply(insert y_defined)
 proof (induct set: EQ_fold_graph)
   case (EQ_insertI x A y)
   assume "\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_::'a state \<times> 'a state). x) y)"
   then show "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case"
   proof (cases "x = a") assume "x = a" with EQ_insertI show "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" by (metis Diff_insert_absorb all_def)
   next apply_end(simp)

     assume "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)"
     then obtain y' where y: "y = f (\<lambda>(_::'a state \<times> 'a state). a) y'" and "(\<forall>\<tau>. all_defined \<tau> y')" and y': "EQ_fold_graph f z (A - {(\<lambda>(_::'a state \<times> 'a state). a)}) y'"
      using EQ_insertI by (metis OCL_core.drop.simps insert_iff)
     have "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y')"
       apply(subgoal_tac "is_int (\<lambda>(_::'a state \<times> 'a state). a) \<and> (\<forall>\<tau>. all_defined \<tau> y')") apply(simp only:)
       apply(simp only: all_def[where x = a and y = y', symmetric])
       unfolding y
       apply(simp add: cp_defined[symmetric])
     done
     moreover have "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> is_int (\<lambda>(_::'a state \<times> 'a state). a) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y') \<Longrightarrow> f (\<lambda>(_::'a state \<times> 'a state). x) y = f (\<lambda>(_::'a state \<times> 'a state). a) (f (\<lambda>(_::'a state \<times> 'a state). x) y')"
       unfolding y
     by(rule fun_left_comm, simp_all)
     moreover have "EQ_fold_graph f z (insert (\<lambda>(_::'a state \<times> 'a state). x) A - {(\<lambda>(_::'a state \<times> 'a state). a)}) (f (\<lambda>(_::'a state \<times> 'a state). x) y')"
       using y' and `x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)` and `(\<lambda>(_::'a state \<times> 'a state). x) \<notin> A`
       apply (simp add: insert_Diff_if OCL_lib.EQ_insertI)
       by (metis option.inject)
     apply_end(subgoal_tac "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> \<exists>y'. f (\<lambda>(_::'a state \<times> 'a state). x) y = f (\<lambda>(_::'a state \<times> 'a state). a) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQ_fold_graph f z (insert (\<lambda>(_::'a state \<times> 'a state). x) A - {(\<lambda>(_::'a state \<times> 'a state). a)}) y'", blast)
     ultimately show "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<and> x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" apply(auto simp: a_valid)
    by (metis `\<forall>\<tau>. all_defined \<tau> y'` all_def)
    apply_end(blast)
   qed
  apply_end simp

  fix x :: "int option option" and y :: "'a state \<times> 'a state \<Rightarrow> int option option Set_0"
  show "(\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_ :: 'a state \<times> 'a state). x) y)) \<Longrightarrow> is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)"
   apply(rule all_def[where x = x and y = y, THEN iffD1, THEN conjunct1], simp) done
  apply_end blast
  fix x :: "int option option" and y :: "'a state \<times> 'a state \<Rightarrow> int option option Set_0" and \<tau> :: "'a state \<times> 'a state"
  show "(\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_ :: 'a state \<times> 'a state). x) y)) \<Longrightarrow> all_defined \<tau> y"
   apply(rule all_def[where x = x, THEN iffD1, THEN conjunct2, THEN spec], simp) done
  apply_end blast
 qed

 lemma fold_graph_insertE:
   assumes v_defined : "\<And>\<tau>. all_defined \<tau> v"
       and x_valid : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)"
       and "EQ_fold_graph f z (insert (\<lambda>(_ :: 'a state \<times> 'a state). x) A) v" and "(\<lambda>(_ :: 'a state \<times> 'a state). x) \<notin> A"
   obtains y where "v = f (\<lambda>(_ :: 'a state \<times> 'a state). x) y" and "is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)" and "\<And>\<tau>. all_defined \<tau> y" and "EQ_fold_graph f z A y"
  apply(insert fold_graph_insertE_aux[OF v_defined x_valid `EQ_fold_graph f z (insert (\<lambda>(_ :: 'a state \<times> 'a state). x) A) v` insertI1] x_valid `(\<lambda>(_ :: 'a state \<times> 'a state). x) \<notin> A`)
  apply(drule exE) prefer 2 apply assumption
  apply(drule Diff_insert_absorb, simp only:)
 done

 lemma fold_graph_determ:
  assumes x_defined : "\<And>\<tau>. all_defined \<tau> x"
      and y_defined : "\<And>\<tau>. all_defined \<tau> y"
    shows "EQ_fold_graph f z A x \<Longrightarrow> EQ_fold_graph f z A y \<Longrightarrow> y = x"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: EQ_fold_graph)
   case (EQ_insertI x A y v)
   from `\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_ :: 'a state \<times> 'a state). x) y)`
   have "is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)" by(metis all_def)
   from `\<And>\<tau>. all_defined \<tau> v` and `is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)` and `EQ_fold_graph f z (insert (\<lambda>(_ :: 'a state \<times> 'a state). x) A) v` and `(\<lambda>(_ :: 'a state \<times> 'a state). x) \<notin> A`
   obtain y' where "v = f (\<lambda>(_ :: 'a state \<times> 'a state). x) y'" and "\<And>\<tau>. all_defined \<tau> y'" and "EQ_fold_graph f z A y'"
     by (rule fold_graph_insertE, simp)
   from EQ_insertI have "\<And>\<tau>. all_defined \<tau> y" by (metis all_def)
   from `\<And>\<tau>. all_defined \<tau> y` and `\<And>\<tau>. all_defined \<tau> y'` and `EQ_fold_graph f z A y'` have "y' = y" by (metis EQ_insertI.hyps(3))
   with `v = f (\<lambda>(_ :: 'a state \<times> 'a state). x) y'` show "v = f (\<lambda>(_ :: 'a state \<times> 'a state). x) y" by (simp)
   apply_end(rule_tac f = f in EQ_empty_fold_graphE, auto)
 qed

 lemma det_init2 :
   assumes z_defined : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "EQ_fold_graph f z A x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: EQ_fold_graph)
   apply_end(simp)
   apply_end(subst all_def, simp add: all_int_set_def int_is_valid)
 qed

 lemma fold_graph_determ3 : (* WARNING \<forall> \<tau> is implicit *)
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "EQ_fold_graph f z A x \<Longrightarrow> EQ_fold_graph f z A y \<Longrightarrow> y = x"
  apply(insert z_defined A_int)
  apply(rule fold_graph_determ)
  apply(rule det_init2[THEN spec]) apply(blast)+
  apply(rule det_init2[THEN spec]) apply(blast)+
 done

 lemma fold_graph_fold:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)"
     shows "EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A) (fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A))"
 proof -
   have "finite ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)" by(insert A_int, simp add: all_int_set_def)
   then have "\<exists>x. fold_graph f z ((\<lambda>a \<tau>. a) ` A) x" by (rule finite_imp_fold_graph)
   then have "\<exists>x. EQ_fold_graph f z ((\<lambda>a \<tau>. a) ` A) x" by (metis eq_fold_of_fold)
   moreover note fold_graph_determ3[OF z_defined A_int]
   ultimately have "\<exists>!x. EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A) x" by (rule ex_ex1I)
   then have "EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A) (The (EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)))" by (rule theI')
   then show ?thesis by (unfold fold1_def)
 qed

 lemma fold_equality:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)"
     shows "EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A) y \<Longrightarrow> fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A) = y"
  apply(rule fold_graph_determ3[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done


 lemma fold_insert:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)"
       and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)"
       and x_nA : "(\<lambda>(_ :: 'a state \<times> 'a state). x) \<notin> (\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A"
   shows "fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` (insert x A)) = f (\<lambda>(_ :: 'a state \<times> 'a state). x) (fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A))"
 proof (rule fold_equality)
   have "EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) `A) (fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) `A))" by (rule fold_graph_fold[OF z_defined A_int])
   with x_nA show "EQ_fold_graph f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) `(insert x A)) (f (\<lambda>(_ :: 'a state \<times> 'a state). x) (fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) `A)))" apply(simp add: image_insert) by(rule EQ_insertI, simp, simp)
   apply_end (simp add: z_defined)
   apply_end (simp add: all_int_set_def int_is_valid[OF x_int] A_int[simplified all_int_set_def] x_int)
 qed

 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)"
      and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` (insert x A)) = f (\<lambda>(_ :: 'a state \<times> 'a state). x) (Finite_Set.fold f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A))"
  proof - 
   have eq_f : "\<And>A. Finite_Set.fold f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A) = fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A)"
    apply(simp add: Finite_Set.fold_def fold1_def)
   by (metis eq_fold_of_fold fold_of_eq_fold)

  have x_nA : "(\<lambda>(_ :: 'a state \<times> 'a state). x) \<notin> (\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A"
   apply(insert x_nA)
   apply(rule contrapos_pp[where Q = "x \<notin> A"], simp, simp)
   apply(simp add: image_iff)
   apply(drule bexE) prefer 2 apply assumption
   apply(drule fun_cong)
  by (metis OCL_core.drop.simps)

  have "fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` (insert x A)) = f (\<lambda>(_ :: 'a state \<times> 'a state). x) (fold1 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` A))" 
   apply(rule fold_insert) apply(simp add: assms x_nA)+
  done

  thus ?thesis by (subst (1 2) eq_f, simp)
 qed

end

context EQ_comp_fun_commute000'
begin

 lemmas F_cp_set = cp_set

 lemma insertI_bis : "x \<notin> A \<Longrightarrow> \<tau> \<Turnstile> \<delta> x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> fold_graph f z (insert x A) (f x y)"
  apply(rule insertI, simp_all)
 done

 lemma fold_graph_insertE_aux:
   assumes y_defined : "\<And>\<tau>. all_defined \<tau> y"
   assumes a_valid : "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>)"
   shows
   "EQ_fold_graph2 f z A y \<Longrightarrow> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) \<in> A \<Longrightarrow> \<exists>y'. y = f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQ_fold_graph2 f z (A - {(\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>)}) y'"
 apply(insert y_defined)
 proof (induct set: EQ_fold_graph2)
   case (EQ_insertI2 x A y)
   assume "\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) y)"
   then show "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case"
   proof (cases "x = a") assume "x = a" with EQ_insertI2 show "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" by (metis Diff_insert_absorb all_def)
   next apply_end(simp)

     assume "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)"
     then obtain y' where y: "y = f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) y'" and "(\<forall>\<tau>. all_defined \<tau> y')" and y': "EQ_fold_graph2 f z (A - {(\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>)}) y'"
      using EQ_insertI2 by (metis OCL_core.drop.simps insert_iff)
     have "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y')"
       apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y')") apply(simp only:)
       apply(simp only: all_def[where x = a and y = y', symmetric])
       unfolding y
       apply(simp add: cp_defined[symmetric])
     done
     moreover have "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y') \<Longrightarrow> f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) y = f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) (f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) y')"
       unfolding y
     by(rule fun_left_comm, simp_all)
     moreover have "EQ_fold_graph2 f z (insert (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) A - {(\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>)}) (f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) y')"
       using y' and `x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)` and `(\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> A`
       apply (simp add: insert_Diff_if OCL_lib.EQ_insertI2)
       by (metis option.inject)
     apply_end(subgoal_tac "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> \<exists>y'. f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) y = f (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> EQ_fold_graph2 f z (insert (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) A - {(\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>)}) y'", blast)
     ultimately show "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<and> x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" apply(auto simp: a_valid)
    by (metis `\<forall>\<tau>. all_defined \<tau> y'` all_def)
    apply_end(blast)
   qed
  apply_end simp
  fix x :: "int option" show "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. \<lfloor>x\<rfloor>)" apply(simp add: valid_def OclValid_def bot_fun_def bot_option_def) done
  fix x :: "int option" and y :: "'a state \<times> 'a state \<Rightarrow> int option option Set_0" and \<tau> :: "'a state \<times> 'a state"
  show "(\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y)) \<Longrightarrow> all_defined \<tau> y"
  apply(rule all_def[where x = x, THEN iffD1, THEN conjunct2, THEN spec], simp)
  done
 qed

 lemma fold_graph_insertE:
   assumes v_defined : "\<And>\<tau>. all_defined \<tau> v"
       and x_valid : "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
       and "EQ_fold_graph2 f z (insert (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) A) v" and "(\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> A"
   obtains y where "v = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y" and "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)" and "\<And>\<tau>. all_defined \<tau> y" and "EQ_fold_graph2 f z A y"
  apply(insert fold_graph_insertE_aux[OF v_defined x_valid `EQ_fold_graph2 f z (insert (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) A) v` insertI1] x_valid `(\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> A`)
  apply(drule exE) prefer 2 apply assumption
  apply(drule Diff_insert_absorb, simp only:)
 done


 lemma fold_graph_determ:
  assumes x_defined : "\<And>\<tau>. all_defined \<tau> x"
      and y_defined : "\<And>\<tau>. all_defined \<tau> y"
    shows "EQ_fold_graph2 f z A x \<Longrightarrow> EQ_fold_graph2 f z A y \<Longrightarrow> y = x"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: EQ_fold_graph2)
   case (EQ_insertI2 x A y v)
   from `\<And>\<tau>. all_defined \<tau> (f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y)`
   have "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)" by(metis all_def)
   from `\<And>\<tau>. all_defined \<tau> v` and `\<tau> \<Turnstile> \<upsilon> (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)` and `EQ_fold_graph2 f z (insert (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) A) v` and `(\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> A`
   obtain y' where "v = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y'" and "\<And>\<tau>. all_defined \<tau> y'" and "EQ_fold_graph2 f z A y'"
     by (rule fold_graph_insertE, simp)
   from EQ_insertI2 have "\<And>\<tau>. all_defined \<tau> y" by (metis all_def)
   from `\<And>\<tau>. all_defined \<tau> y` and `\<And>\<tau>. all_defined \<tau> y'` and `EQ_fold_graph2 f z A y'` have "y' = y" by (metis EQ_insertI2.hyps(3))
   with `v = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y'` show "v = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) y" by(simp)
   apply_end(rule_tac f = f in EQ_empty_fold_graph2E, auto)
 qed

 lemma det_init2 :
   assumes z_defined : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "EQ_fold_graph2 f z A x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: EQ_fold_graph2)
   apply_end(simp)
   apply_end(subst all_def[where \<tau> = \<tau>], simp add: all_int_set_def int_is_valid)
 qed

 lemma fold_graph_determ3 : (* WARNING \<forall> \<tau> is implicit *)
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set A"
     shows "EQ_fold_graph2 f z A x \<Longrightarrow> EQ_fold_graph2 f z A y \<Longrightarrow> y = x"
  apply(insert z_defined A_int)
  apply(rule fold_graph_determ)
  apply(rule det_init2[THEN spec]) apply(blast)+
  apply(rule det_init2[THEN spec]) apply(blast)+
 done

 lemma fold_graph_fold:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)"
     shows "EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A) (fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A))"
 proof -
   have "finite ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)" by(insert A_int, simp add: all_int_set_def)
   then have "\<exists>x. fold_graph f z ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` A) x" by (rule finite_imp_fold_graph)
   then have "\<exists>x. EQ_fold_graph2 f z ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` A) x" by (metis eq_fold2_of_fold)
   moreover note fold_graph_determ3[OF z_defined A_int]
   ultimately have "\<exists>!x. EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A) x" by (rule ex_ex1I)
   then have "EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A) (The (EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)))" by (rule theI')
   then show ?thesis by (unfold fold2_def)
 qed

 lemma fold_equality:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)"
     shows "EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A) y \<Longrightarrow> fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A) = y"
  apply(rule fold_graph_determ3[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done


 lemma fold_insert:
   assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
       and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)"
       and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
       and x_nA : "(\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> (\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A"
   shows "fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` (insert x A)) = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) (fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A))"
 proof (rule fold_equality)
   have "EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) `A) (fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) `A))" by (rule fold_graph_fold[OF z_defined A_int])
   with x_nA show "EQ_fold_graph2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) `(insert x A)) (f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) (fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) `A)))" apply(simp add: image_insert) by(rule EQ_insertI2, simp, simp)
   apply_end (simp add: z_defined)
   apply_end (simp add: all_int_set_def int_is_valid[OF x_int] A_int[simplified all_int_set_def] int_trivial)
 qed

 lemma fold_insert':
  assumes z_defined : "\<And>\<tau>. all_defined \<tau> z"
      and A_int : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)"
      and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
      and x_nA : "x \<notin> A"
    shows "Finite_Set.fold f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` (insert x A)) = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) (Finite_Set.fold f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A))"
  proof - 
   have eq_f : "\<And>A. Finite_Set.fold f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A) = fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A)"
    apply(simp add: Finite_Set.fold_def fold2_def)
   by (metis eq_fold2_of_fold fold_of_eq_fold2)

  have x_nA : "(\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<notin> (\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A"
   apply(insert x_nA)
   apply(rule contrapos_pp[where Q = "x \<notin> A"], simp, simp)
   apply(simp add: image_iff)
   apply(drule bexE) prefer 2 apply assumption
   apply(drule fun_cong)
  by (metis OCL_core.drop.simps)

  have "fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` (insert x A)) = f (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) (fold2 f z ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` A))" 
   apply(rule fold_insert) apply(simp add: assms x_nA)+
  done

  thus ?thesis by (subst (1 2) eq_f, simp)
 qed

end

context EQ_comp_fun_commute0
begin

 lemma fold_graph_insertE_aux:
   assumes y_defined : "\<And>\<tau>. all_defined \<tau> y"
   assumes a_valid : "is_int (\<lambda>(_::'a state \<times> 'a state). a)"
   shows
   "fold_graph f z A y \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>y'. y = f a y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> fold_graph f z (A - {a}) y'"
 apply(insert y_defined)
 proof (induct set: fold_graph)
   case (insertI x A y)
   assume "\<And>\<tau>. all_defined \<tau> (f x y)"
   then show "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case"
   proof (cases "x = a") assume "x = a" with insertI show "\<And>\<tau>. all_defined \<tau> y \<Longrightarrow> ?case" by (metis Diff_insert_absorb all_def)
   next apply_end(simp)

     assume "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)"
     then obtain y' where y: "y = f a y'" and "\<And>\<tau>. all_defined \<tau> y'" and y': "fold_graph f z (A - {a}) y'"
      using insertI by (metis insert_iff)
     have "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y')"
       apply(subgoal_tac "is_int (\<lambda>(_::'a state \<times> 'a state). a) \<and> (\<forall>\<tau>. all_defined \<tau> y')") apply blast
       apply(simp only: all_def[where x = a and y = y', symmetric])
       (*apply(simp add: all_defined_def OclValid_def all_defined_set_def cp_defined[of y])*)
       unfolding y
       apply(simp (*add: cp_defined[symmetric]*))
     done
     moreover have "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> is_int (\<lambda>(_::'a state \<times> 'a state). a) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y') \<Longrightarrow> f x y = f a (f x y')"
       unfolding y
     by(rule fun_left_comm, simp_all)
     moreover have "fold_graph f z (insert x A - {a}) (f x y')"
       using y' and `x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)` and `x \<notin> A`
       by (simp add: insert_Diff_if fold_graph.insertI)
     apply_end(subgoal_tac "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> \<exists>y'. f x y = f a y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> fold_graph f z (insert x A - {a}) y'", blast)
     ultimately show "is_int (\<lambda>(_::'a state \<times> 'a state). x) \<and> x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" apply(auto simp: a_valid)

    apply(rule_tac x = "f x y'" in exI, simp)
    by (metis `\<And>\<tau>. all_defined \<tau> y'` all_def)
   apply_end(blast)
   qed
  apply_end(simp_all (*add: all_def*))
  apply_end(metis all_def)+
 qed

 lemma fold_graph_insertE:
   assumes v_defined : "\<And>\<tau>. all_defined \<tau> v"
       and x_valid : "is_int (\<lambda>(_::'a state \<times> 'a state). x)"
       and "fold_graph f z (insert x A) v" and "x \<notin> A"
   obtains y where "v = f x y" and "is_int (\<lambda>(_::'a state \<times> 'a state). x)" and "\<And>\<tau>. all_defined \<tau> y" and "fold_graph f z A y"
  apply(insert fold_graph_insertE_aux[OF v_defined x_valid `fold_graph f z (insert x A) v` insertI1] x_valid `x \<notin> A`)
  apply(drule exE) prefer 2 apply assumption
  apply(drule Diff_insert_absorb, simp only:)
 done

 lemma fold_graph_determ:
  assumes x_defined : "\<And>\<tau>. all_defined \<tau> x"
      and y_defined : "\<And>\<tau>. all_defined \<tau> y"
    shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: fold_graph)
   case (insertI x A y v)
   from `\<And>\<tau>. all_defined \<tau> (f x y)`
   have "is_int (\<lambda>(_::'a state \<times> 'a state). x)" by(metis all_def)
   from `\<And>\<tau>. all_defined \<tau> v` and `is_int (\<lambda>(_::'a state \<times> 'a state). x)` and `fold_graph f z (insert x A) v` and `x \<notin> A`
   obtain y' where "v = f x y'" and "\<And>\<tau>. all_defined \<tau> y'" and "fold_graph f z A y'"
   by(rule fold_graph_insertE, simp)
   from insertI have "\<And>\<tau>. all_defined \<tau> y" by (metis all_def)
   from `\<And>\<tau>. all_defined \<tau> y` and `\<And>\<tau>. all_defined \<tau> y'` and `fold_graph f z A y'` have "y' = y" thm insertI.hyps(3) by (metis insertI.hyps(3))
   with `v = f x y'` show "v = f x y" by metis
   apply_end(rule_tac f = f in empty_fold_graphE, auto)
 qed

 lemma det_init :
   assumes x_defined : "\<forall>\<tau>. all_defined \<tau> x"
   shows "fold_graph f z A x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> z)"
  apply(insert x_defined)
  proof (induct set: fold_graph)
   apply_end(simp)
   apply_end(drule all_def[THEN iffD1], blast)
 qed

 lemma det_init2 :
   assumes z_defined : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set \<tau> A"
     shows "fold_graph f z A x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: fold_graph)
   apply_end(simp)
   apply_end(rule all_def[THEN iffD2], simp add: is_int_def all_defined_set_def)
 qed

 lemma fold_graph_determ':
  assumes z_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
      and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set \<tau> A"
    shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
  apply(rule fold_graph_determ)
  apply(rule det_init2[OF z_int A_int, THEN spec], simp)+
 by(assumption)+

 lemma fold_graph_fold:
  assumes z_int : "\<forall>\<tau>. all_defined \<tau> z"
      and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set \<tau> A"
  shows "fold_graph f z A (Finite_Set.fold f z A)"
 proof -

  from A_int[simplified all_defined_set_def] have "finite A" by simp
  then have "\<exists>x. fold_graph f z A x" by (rule finite_imp_fold_graph)
  moreover note fold_graph_determ'[OF z_int A_int]
  ultimately have "\<exists>!x. fold_graph f z A x" by(rule ex_ex1I)
  then have "fold_graph f z A (The (fold_graph f z A))" by (rule theI')
  then show ?thesis by(unfold Finite_Set.fold_def)
 qed

 lemma fold_equality:
   assumes z_defined : "\<forall>\<tau>. all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set \<tau> A"
     shows "fold_graph f z A y \<Longrightarrow> Finite_Set.fold f z A = y"
  apply(rule fold_graph_determ'[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done

 lemma fold_insert:
   assumes z_defined : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set \<tau> A"
       and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). x)"
       and "x \<notin> A"
   shows "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z A)"
 proof (rule fold_equality)
   have "fold_graph f z A (Finite_Set.fold f z A)" by (rule fold_graph_fold[OF z_defined A_int])
   with `x \<notin> A`show "fold_graph f z (insert x A) (f x (Finite_Set.fold f z A))" by (rule fold_graph.insertI)
   apply_end (simp add: z_defined)
   apply_end (simp add: all_defined_set_def int_is_valid[OF x_int] A_int[simplified all_defined_set_def])
 qed

end

context EQ_comp_fun_commute0'
begin
 lemma int_v : "\<tau> \<Turnstile> \<upsilon> (\<lambda>(_::'a state \<times> 'a state). (\<lfloor>a\<rfloor>:: int option option))"
 by (metis bot_option_def foundation18' option.distinct(1))

 lemma fold_graph_insertE_aux:
   assumes y_defined : "\<And>\<tau>. all_defined \<tau> y"
   assumes a_valid : "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a::int option\<rfloor>)"
   shows
   "fold_graph f z A y \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>y'. y = f a y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> fold_graph f z (A - {a}) y'"
 apply(insert y_defined)
 proof (induct set: fold_graph)
   case (insertI x A y)
   assume "\<And>\<tau>. all_defined \<tau> (f x y)"
   then show "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case"
   proof (cases "x = a") assume "x = a" with insertI show "\<And>\<tau>. all_defined \<tau> y \<Longrightarrow> ?case" by (metis Diff_insert_absorb all_def)
   next apply_end(simp)

     assume "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)"
     then obtain y' where y: "y = f a y'" and "\<And>\<tau>. all_defined \<tau> y'" and y': "fold_graph f z (A - {a}) y'"
      using insertI by (metis insert_iff)
     have "(\<And>\<tau>. all_defined \<tau> y) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y')"
       apply(subgoal_tac "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y')") apply blast
       apply(simp only: all_def[where x = a and y = y', symmetric])
       (*apply(simp add: all_defined_def OclValid_def all_defined_set_def cp_defined[of y])*)
       unfolding y
       apply(simp (*add: cp_defined[symmetric]*))
     done
     moreover have "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) \<Longrightarrow> (\<And>\<tau>. all_defined \<tau> y') \<Longrightarrow> f x y = f a (f x y')"
       unfolding y
     by(rule fun_left_comm, simp_all)
     moreover have "fold_graph f z (insert x A - {a}) (f x y')"
       using y' and `x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y)` and `x \<notin> A`
       by (simp add: insert_Diff_if fold_graph.insertI)
     apply_end(subgoal_tac "x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> \<exists>y'. f x y = f a y' \<and> (\<forall>\<tau>. all_defined \<tau> y') \<and> fold_graph f z (insert x A - {a}) y'", blast)
     ultimately show "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<and> x \<noteq> a \<and> (\<forall>\<tau>. all_defined \<tau> y) \<Longrightarrow> ?case" apply(auto simp: a_valid)

    apply(rule_tac x = "f x y'" in exI, simp)
    by (metis `\<And>\<tau>. all_defined \<tau> y'` all_def)
   apply_end(blast)
   qed
  apply_end(simp_all (*add: all_def*))
  apply_end(metis all_def)+
 qed

 lemma fold_graph_insertE:
   assumes v_defined : "\<And>\<tau>. all_defined \<tau> v"
       and x_valid : "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
       and "fold_graph f z (insert x A) v" and "x \<notin> A"
   obtains y where "v = f x y" and "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>)" and "\<And>\<tau>. all_defined \<tau> y" and "fold_graph f z A y"
  apply(insert fold_graph_insertE_aux[OF v_defined x_valid `fold_graph f z (insert x A) v` insertI1] x_valid `x \<notin> A`)
  apply(drule exE) prefer 2 apply assumption
  apply(drule Diff_insert_absorb, simp only:)
 done

 lemma fold_graph_determ:
  assumes x_defined : "\<And>\<tau>. all_defined \<tau> x"
      and y_defined : "\<And>\<tau>. all_defined \<tau> y"
    shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
 apply(insert x_defined y_defined)
 proof (induct arbitrary: y set: fold_graph)
   case (insertI x A y v)
   from `\<And>\<tau>. all_defined \<tau> (f x y)`
   have "is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>)" by(metis all_def)
   from `\<And>\<tau>. all_defined \<tau> v` and `is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>)` and `fold_graph f z (insert x A) v` and `x \<notin> A`
   obtain y' where "v = f x y'" and "\<And>\<tau>. all_defined \<tau> y'" and "fold_graph f z A y'"
   by(rule fold_graph_insertE, simp)
   from insertI have "\<And>\<tau>. all_defined \<tau> y" by (metis all_def)
   from `\<And>\<tau>. all_defined \<tau> y` and `\<And>\<tau>. all_defined \<tau> y'` and `fold_graph f z A y'` have "y' = y" thm insertI.hyps(3) by (metis insertI.hyps(3))
   with `v = f x y'` show "v = f x y" by metis
   apply_end(rule_tac f = f in empty_fold_graphE, auto)
 qed

 lemma det_init :
   assumes x_defined : "\<forall>\<tau>. all_defined \<tau> x"
   shows "fold_graph f z A x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> z)"
  apply(insert x_defined)
  proof (induct set: fold_graph)
   apply_end(simp)
   apply_end(drule all_def[THEN iffD1], blast)
 qed


 lemma det_init2 :
   assumes z_defined : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set' \<tau> A"
     shows "fold_graph f z A x \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> x"
  apply(insert z_defined A_int)
  proof (induct set: fold_graph)
   apply_end(simp)
   apply_end(rule all_def[THEN iffD2], simp add: is_int_def all_defined_set'_def int_v)
 qed

 lemma fold_graph_determ':
  assumes z_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
      and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set' \<tau> A"
    shows "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> y = x"
  apply(rule fold_graph_determ)
  apply(rule det_init2[OF z_int A_int, THEN spec], simp)+
 by(assumption)+

 lemma fold_graph_fold:
  assumes z_int : "\<forall>\<tau>. all_defined \<tau> z"
      and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set' \<tau> A"
  shows "fold_graph f z A (Finite_Set.fold f z A)"
 proof -

  from A_int[simplified all_defined_set'_def] have "finite A" by simp
  then have "\<exists>x. fold_graph f z A x" by (rule finite_imp_fold_graph)
  moreover note fold_graph_determ'[OF z_int A_int]
  ultimately have "\<exists>!x. fold_graph f z A x" by(rule ex_ex1I)
  then have "fold_graph f z A (The (fold_graph f z A))" by (rule theI')
  then show ?thesis by(unfold Finite_Set.fold_def)
 qed

 lemma fold_equality:
   assumes z_defined : "\<forall>\<tau>. all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set' \<tau> A"
     shows "fold_graph f z A y \<Longrightarrow> Finite_Set.fold f z A = y"
  apply(rule fold_graph_determ'[OF z_defined A_int], simp)
  apply(rule fold_graph_fold[OF z_defined A_int])
 done

 lemma fold_insert:
   assumes z_defined : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> z"
       and A_int : "\<forall>(\<tau> :: 'a state \<times> 'a state). all_defined_set' \<tau> A"
       and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
       and "x \<notin> A"
   shows "Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z A)"
 proof (rule fold_equality)
   have "fold_graph f z A (Finite_Set.fold f z A)" by (rule fold_graph_fold[OF z_defined A_int])
   with `x \<notin> A`show "fold_graph f z (insert x A) (f x (Finite_Set.fold f z A))" by (rule fold_graph.insertI)
   apply_end (simp add: z_defined)
   apply_end (simp add: all_defined_set'_def int_is_valid[OF x_int] A_int[simplified all_defined_set'_def])
 qed

 lemma fold_insert':
   assumes z_defined : "all_defined (\<tau> :: 'a state \<times> 'a state) z"
       and A_int : "all_defined_set' (\<tau> :: 'a state \<times> 'a state) A"
       and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
       and "x \<notin> A"
   shows "Finite_Set.fold f z (insert x A) \<tau> = f x (Finite_Set.fold f z A) \<tau>"
 sorry

 lemma fold_insert_':
   assumes z_defined : "all_defined (\<tau> :: 'a state \<times> 'a state) z"
       and A_int : "all_defined_set' (\<tau> :: 'a state \<times> 'a state) A"
       and x_int : "is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)"
       and "x \<notin> A"
   shows "Finite_Set.fold F z (insert (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) ((\<lambda>a _. \<lfloor>a\<rfloor>) ` A)) \<tau> =
          F (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) (Finite_Set.fold F z ((\<lambda>a _. \<lfloor>a\<rfloor>) ` A)) \<tau>"
 sorry

end

lemma EQ_OclIterate\<^isub>S\<^isub>e\<^isub>t_including:
 assumes S_all_int: "\<And>(\<tau>::'a state \<times> 'a state). all_int_set ((\<lambda> a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 assumes S_all_def:    "\<And>\<tau>. all_defined \<tau> (S:: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
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
  proof - fix \<tau> show "\<tau> \<Turnstile> \<upsilon> (F a A)"
  apply(insert
    F_commute[simplified EQ_comp_fun_commute_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
              THEN spec, of \<tau>, THEN spec, of a, THEN spec, of A,
              THEN iffD2]
    int_is_valid[OF a_int, of \<tau>]
    A_all_def[of \<tau>], simp add: all_defined1 foundation20)
  done
 qed

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
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

 have remove_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp)

 have inject : "inj (\<lambda>a \<tau>. a)"
 by(rule inj_fun, simp)

 have remove_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
  proof - fix \<tau> show "?thesis \<tau>"
   apply(insert S_all_int[of \<tau>], simp add: all_int_set_def, rule remove_finite)
   apply(erule conjE, drule finite_imageD)
   apply (metis inj_onI, simp)
  done
 qed

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: bot_option_def null_Set_0_def null_fun_def
                  foundation18 foundation16 invalid_def)
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

lemma StrictRefEq_set_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq_set OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma including_swap_ : "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> \<tau> \<Turnstile> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->including(i)->including(j) \<doteq> (S->including(j)->including(i)))"
proof -

 have ocl_and_true : "\<And>a b. \<tau> \<Turnstile> a \<Longrightarrow> \<tau> \<Turnstile> b \<Longrightarrow> \<tau> \<Turnstile> a and b"
 by (simp add: foundation10 foundation6)
 have discr_eq_false_true :  "(false \<tau> = true \<tau>) = False"
 by (metis OclValid_def foundation2)

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

 have not_bot_in_set : "\<And>\<tau> x e. (\<tau> \<Turnstile> \<delta> x) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)) \<Longrightarrow> e \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<Longrightarrow> False"
  apply(frule Set_inv_lemma)
  apply(erule disjE)
  apply(simp add: OclValid_def valid_def)
  apply(simp add: Abs_Set_0_inverse[OF bot_in_set_0])
  apply(split split_if_asm)
  apply(simp add: cp_defined[of x])
  apply(simp add: defined_def bot_option_def null_fun_def null_Set_0_def false_def true_def)
  apply(simp)

  apply(drule_tac Q = False and x = e in ballE, simp_all add: OclValid_def valid_def bot_fun_def)
 done

 have forall_includes : "\<And>a b. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> (OclForall S (OclIncludes S))"
  apply(simp add: OclForall_def OclValid_def discr_eq_false_true discr_eq_bot1_true discr_eq_null_true)
  apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (S->includes((\<lambda>_. x))) \<tau> = true \<tau>")
  apply(simp add: discr_neq_true_null discr_neq_true_bot discr_neq_true_false)
  apply(rule ballI)
  apply(simp add: OclIncludes_def true_def discr_eq_bot2_true[simplified true_def])
  apply(rule_tac Q = False in contrapos_np, simp_all)
  apply(rule not_bot_in_set[simplified OclValid_def true_def])
  apply(assumption)+
 done

 have including_includes : "\<And>(S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) x a.
    \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> S->includes(x) \<Longrightarrow> \<tau> \<Turnstile> (S->including(a)->includes(x))"
  apply(simp add: includes_execute_int)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S")
   prefer 2
   apply(simp add: OclIncludes_def OclValid_def)
   apply (metis discr_eq_bot2_true)
  apply(simp add: cp_if_ocl[of "\<delta> S"] OclValid_def if_ocl_def discr_neq_invalid_true discr_eq_invalid_true)
 by(metis OclValid_def StrictRefEq_int_defined_args_valid)

 have forall_includes2 : "\<And>a b. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> b \<Longrightarrow> \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> (OclForall S (OclIncludes (S->including(a)->including(b))))"
 proof -
  have consist : "\<And>x. (\<delta> S) \<tau> = true \<tau> \<Longrightarrow> x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> (\<upsilon> (\<lambda>_. x)) \<tau> = true \<tau>"
   apply(rule_tac Q = False in contrapos_np, simp_all)
   apply(rule not_bot_in_set[simplified OclValid_def])
   apply(assumption)+
  done
  show "\<And>a b. \<tau> \<Turnstile> \<upsilon> a \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> b \<Longrightarrow> \<tau> \<Turnstile> \<delta> S \<Longrightarrow> ?thesis a b"
   apply(simp add: OclForall_def OclValid_def discr_eq_false_true discr_eq_bot1_true discr_eq_null_true)
   apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (S->including(a)->including(b)->includes((\<lambda>_. x))) \<tau> = true \<tau>")
   apply(simp add: discr_neq_true_null discr_neq_true_bot discr_neq_true_false)
   apply(rule ballI)
   apply(rule including_includes[simplified OclValid_def], simp)
   apply(rule consist, simp_all)
   apply(rule including_includes[simplified OclValid_def], simp)
   apply(rule consist, simp_all)

   apply(simp add: OclIncludes_def true_def discr_eq_bot2_true[simplified true_def])
   apply(rule_tac Q = False in contrapos_np, simp_all)
   apply(rule not_bot_in_set[simplified OclValid_def true_def])
   apply(assumption)+
  done
 qed

 show "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ?thesis"
  apply(simp add:
   cp_if_ocl[of "\<delta> S and \<upsilon> i and \<upsilon> j"]
   cp_if_ocl[of "\<delta> S and \<upsilon> j and \<upsilon> i"]
   cp_not[of "\<delta> S and \<upsilon> j and \<upsilon> i"])
  apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) = (\<delta> S and \<upsilon> j and \<upsilon> i)")
   prefer 2
   apply (metis ocl_and_assoc ocl_and_commute)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S and \<upsilon> i and \<upsilon> j")
   prefer 2
   apply (metis foundation10 foundation6)
  apply(simp add: OclValid_def)
  apply(rule ocl_and_true[simplified OclValid_def])
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = j])
  apply(simp)
  apply(simp add:
   cp_if_ocl[of "\<delta> S and \<upsilon> i and \<upsilon> j"]
   cp_if_ocl[of "\<delta> S and \<upsilon> j and \<upsilon> i"]
   cp_not[of "\<delta> S and \<upsilon> j and \<upsilon> i"])
  apply(simp add: cp_if_ocl[symmetric])
  apply(rule ocl_and_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_if_ocl[of "\<delta> S and \<upsilon> j"] cp_if_ocl[of "i \<doteq> j"] cp_if_ocl[of "\<delta> S"] cp_if_ocl[of "if \<upsilon> j then true else invalid endif"] cp_if_ocl[of "\<upsilon> j"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> j)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: if_ocl_def discr_eq_invalid_true)
  apply (metis OclValid_def StrictRefEq_int_defined_args_valid)
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = i])
  apply(simp add:
   cp_if_ocl[of "\<delta> S and \<upsilon> i"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> i)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_if_ocl[symmetric])
  apply(rule ocl_and_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_if_ocl[of "\<delta> S and \<upsilon> j"] cp_if_ocl[of "i \<doteq> j"] cp_if_ocl[of "\<delta> S"] cp_if_ocl[of "if \<upsilon> i then true else invalid endif"] cp_if_ocl[of "\<upsilon> i"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> j)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_if_ocl[symmetric])
  (* *)
  apply(rule forall_includes2[simplified OclValid_def]) apply(simp) apply(simp) apply(simp)
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = i])
  apply(simp)
  apply(simp add:
   cp_if_ocl[of "\<delta> S and \<upsilon> i and \<upsilon> j"]
   cp_if_ocl[of "\<delta> S and \<upsilon> j and \<upsilon> i"])
  apply(simp add: cp_if_ocl[symmetric])
  apply(rule ocl_and_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_if_ocl[of "\<delta> S and \<upsilon> i"] cp_if_ocl[of "j \<doteq> i"] cp_if_ocl[of "\<delta> S"] cp_if_ocl[of "if \<upsilon> i then true else invalid endif"] cp_if_ocl[of "\<upsilon> i"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> i)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: if_ocl_def discr_eq_invalid_true)
  apply (metis OclValid_def StrictRefEq_int_defined_args_valid)
  (* *)
  apply(subst forall_set_including_exec)
  apply(simp add: cp_OclIncludes1[where x = j])
  apply(simp add:
   cp_if_ocl[of "\<delta> S and \<upsilon> j"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> j)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_if_ocl[symmetric])
  apply(rule ocl_and_true[simplified OclValid_def])
  apply(simp add: includes_execute_int)
  apply(simp add: cp_if_ocl[of "\<delta> S and \<upsilon> i"] cp_if_ocl[of "j \<doteq> i"] cp_if_ocl[of "\<delta> S"] cp_if_ocl[of "if \<upsilon> j then true else invalid endif"] cp_if_ocl[of "\<upsilon> j"])
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> i)")
   prefer 2
   apply (metis OclValid_def foundation10 foundation6)
  apply(simp add: cp_if_ocl[symmetric])
  (* *)
  apply(rule forall_includes2[simplified OclValid_def]) apply(simp) apply(simp) apply(simp)
 done
qed

lemma including_swap' : "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->including(i)->including(j) \<tau> = (S->including(j)->including(i)) \<tau>)"
 apply(frule including_swap_[where i = i and j = j], simp_all del: StrictRefEq_set_exec)
 apply(simp add: StrictRefEq_set OclValid_def del: StrictRefEq_set_exec)
 apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) \<tau> = true \<tau> \<and> (\<delta> S and \<upsilon> j and \<upsilon> i) \<tau> = true \<tau>")
  prefer 2
  apply(metis OclValid_def foundation3)
 apply(simp add: StrongEq_def true_def)
done

lemma including_swap : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->including(i)->including(j) = (S->including(j)->including(i)))"
 apply(rule ext, rename_tac \<tau>)
 apply(erule_tac x = \<tau> in allE)+
 apply(frule including_swap_[where i = i and j = j], simp_all del: StrictRefEq_set_exec)
 apply(simp add: StrictRefEq_set OclValid_def del: StrictRefEq_set_exec)
 apply(subgoal_tac "(\<delta> S and \<upsilon> i and \<upsilon> j) \<tau> = true \<tau> \<and> (\<delta> S and \<upsilon> j and \<upsilon> i) \<tau> = true \<tau>")
  prefer 2
  apply(metis OclValid_def foundation3)
 apply(simp add: StrongEq_def true_def)
done

lemma iterate_subst_set_rec :
 assumes A_defined : "\<forall>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute F"
   shows "\<And>x Fa. let Fa' = (\<lambda>a \<tau>. a) ` Fa
                    ; x' = \<lambda>\<tau>. x in
           x \<notin> Fa \<longrightarrow>
           all_int_set (insert x' Fa') \<longrightarrow>
           (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A Fa')) \<longrightarrow>
           (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A (insert x' Fa')))"
proof -
 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have fold_F  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: F_commute[simplified EQ_comp_fun_commute_def])

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show "\<And>x Fa. ?thesis x Fa"
  apply(simp only: Let_def) apply(rule impI)+
  apply(subst EQ_comp_fun_commute.fold_insert[OF F_commute])
  apply(simp add: A_defined)+
  apply(simp add: all_int_set_def)+
  apply(rule image_cong)
  apply(rule inject)
  apply(simp)

  apply(rule fold_F)
  apply(drule invert_int, simp add: is_int_def) apply (metis (no_types) foundation18')
 done
qed

lemma iterate_subst_set_rec0 :
 assumes A_defined : "\<forall>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. (F:: ('a state \<times> 'a state \<Rightarrow> int option option)
   \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) (\<lambda>_. x))"
   shows "\<And>x Fa.
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. x)) A (insert x Fa))"
proof -
 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have fold_F  : "\<And>x acc. is_int (\<lambda>(_:: 'a state \<times> 'a state). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F (\<lambda>_. x) acc)"
 proof - interpret EQ_comp_fun_commute0 "(\<lambda>x. F (\<lambda>_. x))" by (rule F_commute) show "\<And>x acc. is_int (\<lambda>(_:: 'a state \<times> 'a state). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F (\<lambda>_. x) acc)"
  by(metis all_def)
 qed

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show "\<And>x Fa.
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. (F:: ('a state \<times> 'a state \<Rightarrow> int option option)
   \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) (\<lambda>_. x)) A Fa) \<Longrightarrow> ?thesis x Fa"
  apply(subst EQ_comp_fun_commute0.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp, drule invert_int, simp add: is_int_def) apply(simp)

  apply(rule fold_F)
  apply(simp, drule invert_int, simp add: is_int_def) apply(simp)
 done
 apply_end(simp_all)
qed

lemma iterate_subst_set_rec0' :
 assumes A_defined : "\<forall>\<tau>. all_defined \<tau> A"
     and F_commute : "EQ_comp_fun_commute0' (\<lambda>x. (F:: ('a state \<times> 'a state \<Rightarrow> int option option)
   \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "\<And>x Fa.
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)) A Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)) A (insert x Fa))"
proof -
 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. \<lfloor>a\<rfloor>)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have fold_F  : "\<And>x acc. is_int (\<lambda>(_:: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F (\<lambda>_. \<lfloor>x\<rfloor>) acc)"
 proof - interpret EQ_comp_fun_commute0' "(\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))" by (rule F_commute) show "\<And>x acc. is_int (\<lambda>(_:: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F (\<lambda>_. \<lfloor>x\<rfloor>) acc)"
  by(metis all_def)
 qed

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show "\<And>x Fa.
       finite Fa \<Longrightarrow>
       x \<notin> Fa \<Longrightarrow>
       (\<And>\<tau>. all_defined \<tau> A) \<Longrightarrow>
       all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` insert x Fa) \<Longrightarrow>
       \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x. (F:: ('a state \<times> 'a state \<Rightarrow> int option option)
   \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) (\<lambda>_. \<lfloor>x\<rfloor>)) A Fa) \<Longrightarrow> ?thesis x Fa"
  apply(subst EQ_comp_fun_commute0'.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp, drule invert_int, simp add: is_int_def) apply(simp)

  apply(rule fold_F)
  apply(simp, drule invert_int, simp add: is_int_def) apply(simp)
 done
 apply_end(simp_all)
qed

lemma iterate_subst_set :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -

 have fold_F  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: F_commute[simplified EQ_comp_fun_commute_def])

 have fold_G  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (G x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: G_commute[simplified EQ_comp_fun_commute_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def, rule ext)
  proof -
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)

  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)", simp)

  apply(subst conjunct2[OF finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' = Finite_Set.fold G A set'"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp]])
   apply(simp add: S_finite)
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20)
   defer
   apply(simp add: S_all_int[simplified all_defined_def])
   apply(simp)

  apply(simp only: image_insert)
  apply(rule impI)+
  apply(drule mp, simp add: all_int_set_def)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF A_all_def[THEN allI] F_commute], simp, simp, simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF A_all_def[THEN allI] G_commute], simp, simp, simp)
  (* *)
  apply(subst EQ_comp_fun_commute.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(drule invert_int, simp add: is_int_def) apply (metis (no_types) foundation18')
   apply(simp add: all_defined_set_def)+
  done
 qed
qed

lemma img_fold :
 assumes g_comm : "EQ_comp_fun_commute0 (\<lambda>x. G (\<lambda>_. x))"
     and a_def : "\<forall>\<tau>. all_defined \<tau> A"
     and fini : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). a) ` Fa)"
   shows  "Finite_Set.fold (G :: ('a state \<times> 'a state \<Rightarrow> int option option)
                                  \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                                  \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) A ((\<lambda>a \<tau>. a) ` Fa) =
           Finite_Set.fold (\<lambda>x. G (\<lambda>_. x)) A Fa"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)
 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 interpret EQ_comp_fun_commute0 "\<lambda>x. G (\<lambda>_. x)" by (rule g_comm)
 show ?thesis
  apply(rule finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               Finite_Set.fold G A set' = Finite_Set.fold (\<lambda>x. G (\<lambda>_. x)) A set"
                  and F = Fa, simplified Let_def, THEN mp])
  apply(insert fini[simplified all_int_set_def, THEN conjunct1], rule finite_imageD, assumption)
  apply (metis inject subset_inj_on top_greatest)
  apply(simp)
  apply(rule impI)+

  apply(subgoal_tac "all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` F)", simp)

  apply(subst EQ_comp_fun_commute0.fold_insert[OF g_comm])
   apply(simp add: a_def)

   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
   apply(drule sym, simp only:)
   apply(subst EQ_comp_fun_commute000.fold_insert'[OF g_comm[THEN c000_of_c0[where f = G]], simplified], simp add: a_def, simp)
    apply(simp add: invert_int)
    apply(simp)
  apply(simp)

  apply(rule invert_all_int_set, simp)
  apply(simp add: fini)
 done
qed

lemma img_fold' :
 assumes g_comm : "EQ_comp_fun_commute0' (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>))"
     and a_def : "\<forall>\<tau>. all_defined \<tau> A"
     and fini : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` Fa)"
   shows  "Finite_Set.fold (G :: ('a state \<times> 'a state \<Rightarrow> int option option)
                                  \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                                  \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa) =
           Finite_Set.fold (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)) A Fa"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)
 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 interpret EQ_comp_fun_commute0' "\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule g_comm)
 show ?thesis
  apply(rule finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` set in
                                               all_int_set set' \<longrightarrow>
                                               Finite_Set.fold G A set' = Finite_Set.fold (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)) A set"
                  and F = Fa, simplified Let_def, THEN mp])
  apply(insert fini[simplified all_int_set_def, THEN conjunct1], rule finite_imageD, assumption)
  apply (metis (lifting) inj_on_def option.inject)
  apply(simp)
  apply(rule impI)+

  apply(subgoal_tac "all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` F)", simp)

  apply(subst EQ_comp_fun_commute0'.fold_insert[OF g_comm])
   apply(simp add: a_def)

   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
   apply(drule sym, simp only:)
   apply(subst EQ_comp_fun_commute000'.fold_insert'[OF g_comm[THEN c000'_of_c0'[where f = G]], simplified], simp add: a_def, simp)
    apply(simp add: invert_int)
    apply(simp)
    apply(simp)

  apply(rule invert_all_int_set, simp)
  apply(simp add: fini)
 done
qed

lemma img_fold'' :
 assumes g_comm : "EQ_comp_fun_commute0' (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>))"
     and a_def : "all_defined \<tau> A"
     and fini : "all_int_set ((\<lambda>a (\<tau> :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` Fa)"
   shows  "Finite_Set.fold (G :: ('a state \<times> 'a state \<Rightarrow> int option option)
                                  \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
                                  \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa) \<tau> =
           Finite_Set.fold (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)) A Fa \<tau>"
proof -
 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)
 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)
 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 interpret EQ_comp_fun_commute0' "\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule g_comm)
 show ?thesis
  apply(rule finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` set in
                                               all_int_set set' \<longrightarrow>
                                               Finite_Set.fold G A set' \<tau> = Finite_Set.fold (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)) A set \<tau>"
                  and F = Fa, simplified Let_def, THEN mp])
  apply(insert fini[simplified all_int_set_def, THEN conjunct1], rule finite_imageD, assumption)
  apply (metis (lifting) inj_on_def option.inject)
  apply(simp)
  apply(rule impI)+

  apply(subgoal_tac "all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` F)", simp)

  apply(subst EQ_comp_fun_commute0'.fold_insert'[OF g_comm])
   apply(simp add: a_def)

   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
   apply(subst EQ_comp_fun_commute0'.fold_insert_'[OF g_comm a_def],simp add: all_int_set_def all_defined_set'_def int_is_valid)
    apply(simp add: invert_int)
    apply(simp)
  apply(subst cp_set, simp, subst cp_set[symmetric], simp)

  apply(rule invert_all_int_set, simp)
  apply(simp add: fini)
 done
qed

lemma abs_rep_simp :
 assumes S_all_def : "all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
   shows "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 show ?thesis
  apply(insert S_all_def, simp add: all_defined_def all_defined_set_def OclValid_def defined_def)
  apply(rule mp[OF Abs_Set_0_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau> then false \<tau> else true \<tau>) = true \<tau> \<and>
          finite \<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil> \<and>
          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. (if x = \<bottom> \<tau> then false \<tau> else true \<tau>) = true \<tau>) \<longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]])
  apply(simp add: Abs_Set_0_inverse discr_eq_false_true)
  apply(case_tac y, simp)
  apply(simp add: bot_fun_def bot_Set_0_def)
  apply(case_tac a, simp)
  apply(simp add: null_fun_def null_Set_0_def)
  apply(simp)
  apply(simp)
 by (metis OCL_core.bot_fun_def valid_def)
qed

lemma iterate_subst_set' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -

 have fold_F  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: F_commute[simplified EQ_comp_fun_commute_def])

 have fold_G  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (G x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: G_commute[simplified EQ_comp_fun_commute_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)


 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have S_incl : "\<forall>(x :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
  apply(rule allI) apply(rule impI)+
  apply(rule ext, rename_tac \<tau>)
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(simp add: mtSet_def)
 by (metis abs_rep_simp)

 have G_cp : "\<And>x y \<tau>. G x y \<tau> = G (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>) \<tau>"
 by (metis EQ_comp_fun_commute.F_cp EQ_comp_fun_commute.F_cp_set G_commute)

 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def, rule ext)
  proof -
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)

  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)", simp)

  apply(subst conjunct2[OF finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               (\<forall> \<tau>1 \<tau>2. Finite_Set.fold G A set' \<tau>1 = Finite_Set.fold G A set' \<tau>2) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' = Finite_Set.fold G A set'"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp]])
   apply(simp add: S_finite)
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20 A_include)
   defer
   apply(simp add: S_all_int[simplified all_defined_def])
   apply(simp)

  apply(simp only: image_insert)
  apply(rule impI)+
  apply(drule mp, simp add: all_int_set_def)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
   apply(rule allI)
   apply(subst G_cp[of "(\<lambda>\<tau>. x)"], rule sym, subst G_cp[of "(\<lambda>\<tau>. x)"], rule sym)
   apply(drule_tac x = \<tau>1 in allE) prefer 2 apply assumption
   apply(drule_tac P = "\<lambda>\<tau>2. Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<tau>1 = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<tau>2" and x = \<tau>2 in allE) prefer 2 apply assumption
   apply(simp)
   apply(rule G_commute[simplified EQ_comp_fun_commute_def, THEN conjunct1, THEN conjunct2, THEN conjunct2, THEN spec, THEN spec, THEN spec, THEN spec, THEN mp, THEN mp, THEN mp])
   apply(drule invert_int, simp)
   apply(rule allI)
   apply(subgoal_tac "all_defined \<tau>2 (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))") prefer 2 apply(metis surj_pair)
   apply(simp add: all_defined_def all_defined_set_def)
   apply (metis (no_types) foundation16 foundation18')
   apply(simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF A_all_def[THEN allI] F_commute], simp, simp, simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF A_all_def[THEN allI] G_commute], simp, simp, simp)
  (* *)
  apply(subst EQ_comp_fun_commute.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(drule invert_int, simp add: is_int_def) apply (metis (no_types) foundation18')
    apply(rule allI)+
    apply(blast)
    apply(simp)
  done
 qed
qed

lemma iterate_subst_set'' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {}"
     and F_commute : "EQ_comp_fun_commute F"
     and G_commute : "EQ_comp_fun_commute G"
     and fold_eq : "\<And>x acc. is_int x \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> (\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {}) \<Longrightarrow> F x acc = G x acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -

 have fold_F  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (F x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: F_commute[simplified EQ_comp_fun_commute_def])

 have fold_G  : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> x)) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau>. all_defined \<tau> (G x acc)"
  apply(rule allI) apply(erule_tac x = \<tau> in allE)+
 by(simp add: G_commute[simplified EQ_comp_fun_commute_def])

 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)


 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def, rule ext)
  proof -
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)

  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)", simp)
  apply(subst conjunct2[OF finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold G A set' \<tau>)\<rceil>\<rceil> \<noteq> {}) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' = Finite_Set.fold G A set'"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp]])
   apply(simp add: S_finite)
   apply(insert A_all_def A_notempty, simp add: all_defined_set_def all_defined_def foundation20)
   defer
   apply(simp add: S_all_int[simplified all_defined_def])
   apply(simp)

  apply(simp only: image_insert)
  apply(rule impI)+
  apply(drule mp, simp add: all_int_set_def)

  apply(rule conjI, rule allI)
  apply(subst EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(rule G_commute[simplified EQ_comp_fun_commute_def, THEN conjunct2, THEN conjunct1, THEN spec, THEN spec, THEN spec, THEN mp, THEN mp, THEN mp])
  apply(simp)
  apply(drule invert_int, simp add: int_is_valid)
  apply blast

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF A_all_def[THEN allI] F_commute], simp, simp, simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN spec, OF A_all_def[THEN allI] G_commute], simp, simp, simp)
  (* *)
  apply(subst EQ_comp_fun_commute.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(subst EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: invert_all_int_set)
   apply(simp add: invert_int)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(drule invert_int, simp add: is_int_def) apply (metis (no_types) foundation18')
   apply(simp add: all_defined_set_def)+
  apply(metis surj_pair)
  apply(simp)
  done
 qed
qed

lemma cp_all_def : "all_defined \<tau> f = all_defined \<tau>' (\<lambda>_. f \<tau>)"
  apply(simp add: all_defined_def all_defined_set_def OclValid_def)
  apply(subst cp_defined)
 by (metis (no_types) OclValid_def cp_defined cp_valid defined2 defined_def foundation1 foundation16 foundation17 foundation18' foundation6 foundation9 not3 ocl_and_true1 ocl_and_true2 transform1_rev valid_def)

lemma cp_all_def' : "(\<forall>\<tau>. all_defined \<tau> f) = (\<forall>\<tau> \<tau>'. all_defined \<tau>' (\<lambda>_. f \<tau>))"
 apply(rule iffI)
 apply(rule allI) apply(erule_tac x = \<tau> in allE) apply(rule allI)
 apply(simp add: cp_all_def[THEN iffD1])
 apply(subst cp_all_def, blast)
done

lemma iterate_induct :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and P_0 : "P {}"
     and P_rec : "\<And>x F. let f_set = (\<lambda>x. (\<lambda>a (_ :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` x) in
      (finite F \<longrightarrow>
       x \<notin> F \<longrightarrow>
       is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<longrightarrow>
       all_int_set (f_set F) \<longrightarrow>
       all_int_set (f_set (insert x F)) \<longrightarrow>
       P (f_set F) \<longrightarrow> P (f_set (insert x F)))"
   shows "P ((\<lambda>a _. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
proof -
 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_lift : "\<exists>S'. (\<lambda>a (_::'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = (\<lambda>a (_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` S'"
  apply(rule_tac x = "(\<lambda>a. \<lceil>a\<rceil>) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>" in exI)
  apply(simp only: image_comp[symmetric])
  apply(simp add: comp_def)
  apply(subgoal_tac "\<forall>x\<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. \<lfloor>\<lceil>x\<rceil>\<rfloor> = x")
  apply(rule equalityI)
  (* *)
  apply(rule subsetI)
  apply(drule imageE) prefer 2 apply assumption
  apply(drule_tac x = a in ballE) prefer 3 apply assumption
  apply(drule_tac f = "\<lambda>x \<tau>. \<lfloor>\<lceil>x\<rceil>\<rfloor>" in imageI)
  apply(simp)
  apply(simp)
  (* *)
  apply(rule subsetI)
  apply(drule imageE) prefer 2 apply assumption
  apply(drule_tac x = xa in ballE) prefer 3 apply assumption
  apply(drule_tac f = "\<lambda>x \<tau>. x" in imageI)
  apply(simp)
  apply(simp)
  (* *)
  apply(rule ballI)

  apply(insert S_all_def[simplified all_defined_def all_defined_set_def, THEN conjunct2, THEN conjunct2, of \<tau>])
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply(case_tac x)
  apply (metis bot_option_def foundation18')
  apply(simp)
  apply(simp)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(rule S_lift[THEN exE], rename_tac S', simp)
  apply(subst finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` set in
                                               all_int_set set' \<longrightarrow>
                                               P set'"
                              and F = S', simplified Let_def, THEN mp])
   apply(cut_tac S_finite[where \<tau> = \<tau>, THEN finite_imageI[where h = "(\<lambda>a (_::'a state \<times> 'a state). a)"]], simp)
   apply(rule finite_imageD, assumption, metis (mono_tags) OCL_core.drop.simps inj_onI)
   apply(simp add: P_0)
   apply(rule impI)+
   apply(rule P_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN mp, THEN mp, THEN mp])
    apply(simp) apply(simp) apply(rule invert_int, simp) apply(rule invert_all_int_set, simp) apply(simp)
    apply(simp)
    apply(drule invert_all_int_set, simp)
   apply(drule sym, simp add: S_all_int)
   apply(simp)
 done
qed

lemma iterate_induct' :
 assumes S_all_def : "all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and P_0 : "P {}"
     and P_rec : "\<And>x F. let f_set = (\<lambda>x. (\<lambda>a (_ :: 'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` x) in
      (finite F \<longrightarrow>
       x \<notin> F \<longrightarrow>
       is_int (\<lambda>(_ :: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<longrightarrow>
       all_int_set (f_set F) \<longrightarrow>
       all_int_set (f_set (insert x F)) \<longrightarrow>
       P (f_set F) \<longrightarrow> P (f_set (insert x F)))"
   shows "P ((\<lambda>a _. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
proof -
 have S_finite : "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have all_def_to_all_int : "all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have S_all_int : "all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_lift : "\<exists>S'. (\<lambda>a (_::'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = (\<lambda>a (_::'a state \<times> 'a state). \<lfloor>a\<rfloor>) ` S'"
  apply(rule_tac x = "(\<lambda>a. \<lceil>a\<rceil>) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>" in exI)
  apply(simp only: image_comp[symmetric])
  apply(simp add: comp_def)
  apply(subgoal_tac "\<forall>x\<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. \<lfloor>\<lceil>x\<rceil>\<rfloor> = x")
  apply(rule equalityI)
  (* *)
  apply(rule subsetI)
  apply(drule imageE) prefer 2 apply assumption
  apply(drule_tac x = a in ballE) prefer 3 apply assumption
  apply(drule_tac f = "\<lambda>x \<tau>. \<lfloor>\<lceil>x\<rceil>\<rfloor>" in imageI)
  apply(simp)
  apply(simp)
  (* *)
  apply(rule subsetI)
  apply(drule imageE) prefer 2 apply assumption
  apply(drule_tac x = xa in ballE) prefer 3 apply assumption
  apply(drule_tac f = "\<lambda>x \<tau>. x" in imageI)
  apply(simp)
  apply(simp)
  (* *)
  apply(rule ballI)

  apply(insert S_all_def[simplified all_defined_def all_defined_set_def, THEN conjunct2, THEN conjunct2])
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply(case_tac x)
  apply (metis bot_option_def foundation18')
  apply(simp)
  apply(simp)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
   apply(rule S_lift[THEN exE], rename_tac S', simp)
   apply(subst finite_induct[where P = "\<lambda>set.
                                                 let set' = (\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` set in
                                                 all_int_set set' \<longrightarrow>
                                                 P set'"
                                and F = S', simplified Let_def, THEN mp])
   apply(cut_tac S_finite[THEN finite_imageI[where h = "(\<lambda>a (_::'a state \<times> 'a state). a)"]], simp)
   apply(rule finite_imageD, assumption, metis (mono_tags) OCL_core.drop.simps inj_onI)
   apply(simp add: P_0)
   apply(rule impI)+
   apply(rule P_rec[simplified Let_def, THEN mp, THEN mp, THEN mp, THEN mp, THEN mp, THEN mp])
    apply(simp) apply(simp) apply(rule invert_int, simp) apply(rule invert_all_int_set, simp) apply(simp)
    apply(simp)
    apply(drule invert_all_int_set, simp)
   apply(drule sym, simp add: S_all_int)
   apply(simp)
 done
qed

lemma cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1':
 assumes f_comm : "EQ_comp_fun_commute0' (\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>))"
   shows "(X->iterate(a; x = X | f a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate(a; x = (\<lambda>_. X \<tau>) | f a x)) \<tau>"
proof -
 interpret EQ_comp_fun_commute0' "\<lambda>x. f (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have all_defined2 : "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> all_defined \<tau> X"
  apply(simp add: OclValid_def)
  apply(frule Set_inv_lemma[simplified OclValid_def])
  apply(drule disjE) prefer 3 apply assumption
  apply(simp add: defined_def bot_Set_0_def null_Set_0_def null_fun_def bot_fun_def bot_option_def false_def true_def)
  apply(simp add: all_defined_def all_defined_set_def OclValid_def)
 by (metis OCL_core.bot_fun_def valid_def)

 show ?thesis
  apply(subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t[symmetric])
  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def cp_valid[symmetric])
  apply(case_tac "\<not>((\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> X) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)", blast)
  apply(simp)
  apply(erule conjE)+
  apply(drule all_defined2[simplified OclValid_def], simp)

  apply(rule iterate_induct'[where P = "\<lambda>set'. Finite_Set.fold f X set' \<tau> = Finite_Set.fold f (\<lambda>_. X \<tau>) set' \<tau>"
                           , simplified Let_def])
  apply(simp)
  apply(simp add: all_defined_def all_defined_set_def)

  apply(rule impI)+
   apply(subst img_fold''[OF f_comm], simp, simp)

   apply(subst EQ_comp_fun_commute0'.fold_insert'[OF f_comm])
   apply(simp)
    apply(simp add: all_int_set_def all_defined_set'_def int_is_valid)
    apply(simp)
    apply(simp)

   apply(subst img_fold''[OF f_comm], subst cp_all_def[symmetric], simp, simp)
   apply(subst EQ_comp_fun_commute0'.fold_insert'[OF f_comm])
   apply(subst cp_all_def[symmetric], simp, simp)
    apply(simp add: all_int_set_def all_defined_set'_def int_is_valid)
    apply(simp)
    apply(simp)

  apply(subst (1 2) cp_set)
  apply(subst img_fold''[where G = f, OF f_comm, symmetric], simp, simp)
  apply(subst img_fold''[where G = f, OF f_comm, symmetric])
   apply(subst cp_all_def[symmetric], simp, simp)

  apply(subst (1 2) cp_set)
  apply(simp)
 done
qed

lemma iterate_subst_set0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. G (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. (\<forall>\<tau>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>(_:: 'a state \<times> 'a state). x))) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> F (\<lambda>_. x) acc = G (\<lambda>_. x) acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -
 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def, rule ext)
  proof -
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)
  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)", simp)

  apply(subst conjunct2[OF finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' = Finite_Set.fold G A set'"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp]])
   apply(simp add: S_finite)
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20)
   defer
   apply(simp add: S_all_int[simplified all_defined_def])
   apply(simp)

  apply(rule impI)+
  apply(drule mp, simp add: all_int_set_def)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0[OF A_all_def[THEN allI] F_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)


  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0[OF A_all_def[THEN allI] G_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)
  (* *)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(simp, drule invert_int, simp add: is_int_def)

  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(simp)
  done
 qed
qed

lemma iterate_subst_set'0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. G (\<lambda>_. x))"
     and fold_eq : "\<And>x acc \<tau>. is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> F (\<lambda>_. x) acc = G (\<lambda>_. x) acc"
   shows "(S->iterate(x;acc=A|F x acc)) = (S->iterate(x;acc=A|G x acc))"
proof -
 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)


 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have S_incl : "\<forall>(x :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
  apply(rule allI) apply(rule impI)+
  apply(rule ext, rename_tac \<tau>)
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(drule_tac x = \<tau> in allE) prefer 2 apply assumption
  apply(simp add: mtSet_def)
 by (metis abs_rep_simp)

 have G_cp : "\<And>x y \<tau>. G (\<lambda>_. x) y \<tau> = G (\<lambda>_. x) (\<lambda>_. y \<tau>) \<tau>"
 proof - fix x y \<tau> 
  interpret EQ_comp_fun_commute0 "(\<lambda>x. G (\<lambda>_. x))" by (rule G_commute) show "G (\<lambda>_. x) y \<tau> = G (\<lambda>_. x) (\<lambda>_. y \<tau>) \<tau>"
  by (metis cp_set)
 qed

 show ?thesis
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def, rule ext)
  proof -
  interpret EQ_comp_fun_commute0 "(\<lambda>x. G (\<lambda>_. x))" by (rule G_commute)
  fix \<tau>
  show "(if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>) =
        (if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> then Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> else \<bottom>)"
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)

  apply(subgoal_tac "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)", simp)

  apply(subst conjunct2[OF finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               (\<forall> \<tau>1 \<tau>2. Finite_Set.fold G A set' \<tau>1 = Finite_Set.fold G A set' \<tau>2) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' = Finite_Set.fold G A set'"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp]])
   apply(simp add: S_finite)
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20 A_include)
   defer
   apply(simp add: S_all_int[simplified all_defined_def])
   apply(simp)

  apply(rule impI)+
  apply(drule mp, simp add: all_int_set_def)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
   apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
   apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
   apply(rule allI)
   apply(subst G_cp[of "x"], rule sym, subst G_cp[of "x"], rule sym)
   apply(drule_tac x = \<tau>1 in allE) prefer 2 apply assumption
   apply(drule_tac P = "\<lambda>\<tau>2. Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<tau>1 = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<tau>2" and x = \<tau>2 in allE) prefer 2 apply assumption
   apply(simp)
   apply(rule cp_gen')
   apply(drule invert_int, simp)
   apply(subgoal_tac "all_defined \<tau>2 (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))") prefer 2 apply(metis surj_pair)
   apply(simp add: all_defined_def all_defined_set_def)
   apply (metis (no_types) foundation16 foundation18')
   apply(simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+

  apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0[OF A_all_def[THEN allI] F_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0[OF A_all_def[THEN allI] G_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)
  (* *)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(simp)
   apply(drule invert_int, simp add: is_int_def) apply(simp)
    apply(rule allI)+
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)

    apply(blast)

  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(simp)
  done
 qed
qed

lemma iterate_subst_set''0 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and G_commute : "EQ_comp_fun_commute0 (\<lambda>x. G (\<lambda>_. x))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'a state \<times> 'a state). x) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> F (\<lambda>_. x) acc \<tau> = G (\<lambda>_. x) acc \<tau>"
   shows "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A|F x acc)) \<tau> = (S->iterate(x;acc=A|G x acc)) \<tau>"
proof -
 have all_def_to_all_int_ : "\<And>set \<tau>. all_defined_set \<tau> set \<Longrightarrow> all_int_set ((\<lambda>a \<tau>. a) ` set)"
  apply(simp add: all_defined_set_def all_int_set_def is_int_def)
 by (metis foundation18')

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)


 have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
 by(rule all_def_to_all_int, simp add: assms)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 interpret EQ_comp_fun_commute0 "\<lambda>x. G (\<lambda>_. x)" by (rule G_commute)
 show "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)

  apply(subst conjunct2[OF finite_induct[where P = "\<lambda>set.
                                               let set' = (\<lambda>a \<tau>. a) ` set in
                                               all_int_set set' \<longrightarrow>
                                               \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold G A set' \<tau>)\<rceil>\<rceil> \<noteq> {} \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' \<tau> = Finite_Set.fold G A set' \<tau>"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp]])
   apply(simp add: S_finite)
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20)
   defer
   apply(simp add: S_all_int[simplified all_defined_def])
   apply(simp)

  apply(rule impI)+
  apply(drule mp, simp add: all_int_set_def)

  apply(rule conjI)
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(rule notempty', blast)
  apply(simp)
  apply(drule invert_int, simp add: int_is_valid)
  apply blast

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0[OF A_all_def[THEN allI] F_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0[OF A_all_def[THEN allI] G_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)
  (* *)
  apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst img_fold[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(simp, drule invert_int, simp add: is_int_def)
   apply(simp add: all_defined_set_def)+
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  apply(subst img_fold[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp)
  proof - 
  interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)
  fix Fa x show "Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) \<tau> = Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<tau> \<Longrightarrow>
           F (\<lambda>_. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<tau> = F (\<lambda>_. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa)) \<tau>"
  apply(subst cp_set, simp add:cp_set[symmetric])
  done
  apply_end(simp_all)
 qed 
qed

lemma iterate_subst_set___ :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_include : "\<And>\<tau>1 \<tau>2. A \<tau>1 = A \<tau>2"
     and F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and G_commute : "EQ_comp_fun_commute0' (\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>))"
     and fold_eq : "\<And>x acc. is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow> (\<forall>\<tau>. all_defined \<tau> acc) \<Longrightarrow> \<forall>\<tau> \<tau>'. acc \<tau> = acc \<tau>' \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> F (\<lambda>_. \<lfloor>x\<rfloor>) acc \<tau> = G (\<lambda>_. \<lfloor>x\<rfloor>) acc \<tau>"
   shows "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A|F x acc)) \<tau> = (S->iterate(x;acc=A|G x acc)) \<tau>"
proof -
 have A_defined : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 have G_cp : "\<And>x y \<tau>. G (\<lambda>_. \<lfloor>x\<rfloor>) y \<tau> = G (\<lambda>_. \<lfloor>x\<rfloor>) (\<lambda>_. y \<tau>) \<tau>"
 proof - fix x y \<tau> 
  interpret EQ_comp_fun_commute0' "(\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>))" by (rule G_commute) show "G (\<lambda>_. \<lfloor>x\<rfloor>) y \<tau> = G (\<lambda>_. \<lfloor>x\<rfloor>) (\<lambda>_. y \<tau>) \<tau>"
  by (metis cp_set)
 qed

 interpret EQ_comp_fun_commute0' "\<lambda>x. G (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule G_commute)
 show "\<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ?thesis"
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined[THEN spec, of \<tau>], simplified OclValid_def]
             del: StrictRefEq_set_exec)
  apply(rule iterate_induct[where P = "\<lambda>set'. ((\<forall> \<tau>1 \<tau>2. Finite_Set.fold G A set' \<tau>1 = Finite_Set.fold G A set' \<tau>2) \<and>
                                               \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold G A set' \<tau>)\<rceil>\<rceil> \<noteq> {} \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set')) \<and>
                                               (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold G A set')) \<and>
                                               Finite_Set.fold F A set' \<tau> = Finite_Set.fold G A set' \<tau>)"
                              , where \<tau> = \<tau>, OF S_all_def, simplified Let_def, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20 A_include)

  apply(rule impI)+
  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold'[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0'.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
  apply(subst img_fold'[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0'.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
   apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp)
   apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp)
   apply(rule allI)
   apply(subst G_cp[of "x"], rule sym, subst G_cp[of "x"], rule sym)
   apply(drule_tac x = \<tau>1 in allE) prefer 2 apply assumption
   apply(drule_tac P = "\<lambda>\<tau>2. Finite_Set.fold G A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa) \<tau>1 = Finite_Set.fold G A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa) \<tau>2" and x = \<tau>2 in allE) prefer 2 apply assumption
   apply(simp)
   apply(rule cp_gen')
   apply(drule invert_int, simp)
   apply(subgoal_tac "all_defined \<tau>2 (Finite_Set.fold G A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa))") prefer 2 apply(metis surj_pair)
   apply(simp add: all_defined_def all_defined_set_def)
   apply (metis (no_types) foundation16 foundation18')
   apply(simp)

  apply(rule conjI)
  apply(subst img_fold'[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0'.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)
  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp)
  apply(rule notempty', blast)
  apply(simp)
  apply blast

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold'[OF F_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0'[OF A_all_def[THEN allI] F_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold'[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, simp)

  apply(rule conjI, rule allI)
  apply(erule conjE)+
  apply(subst img_fold'[OF G_commute], simp add: A_all_def, simp)
  apply(rule iterate_subst_set_rec0'[OF A_all_def[THEN allI] G_commute, THEN spec], simp, simp, simp, simp, simp)
  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, simp)
  (* *)
  apply(subst img_fold'[OF F_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0'.fold_insert[OF F_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst img_fold'[OF G_commute], simp add: A_all_def, simp)
  apply(subst EQ_comp_fun_commute0'.fold_insert[OF G_commute])
   apply(simp)
   apply(simp add: image_cong)
   apply(drule invert_all_int_set, simp add: all_int_set_def all_defined_set'_def int_is_valid)
   apply(simp add: invert_int)
   apply(simp)

  apply(subst fold_eq[symmetric])
   apply(simp)
   apply(simp add: all_defined_set_def)+
  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, simp)
  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, simp)
  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, simp)

  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp, simp)
  apply(subst img_fold'[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp)
  apply(subst img_fold'[where G = G, OF G_commute, symmetric], simp add: A_all_def, simp)
  proof - 
  interpret EQ_comp_fun_commute0' "\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule F_commute)
  fix Fa x show "Finite_Set.fold F A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa) \<tau> = Finite_Set.fold G A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa) \<tau> \<Longrightarrow>
           F (\<lambda>_. \<lfloor>x\<rfloor>) (Finite_Set.fold F A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa)) \<tau> = F (\<lambda>_. \<lfloor>x\<rfloor>) (Finite_Set.fold G A ((\<lambda>a \<tau>. \<lfloor>a\<rfloor>) ` Fa)) \<tau>"
  apply(subst cp_set , simp add:cp_set[symmetric])
  done
  apply_end(simp)
 qed 
qed

lemma including_subst_set : "(s::('\<AA>,'a::null)Set) = t \<Longrightarrow> s->including(x) = (t->including(x))"
by(simp)

lemma including_subst_set' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including(x) \<doteq> (t->including(x)))"
proof -
 have cp: "cp (\<lambda>s. (s->including(x)))"
  apply(simp add: cp_def, subst cp_OclIncluding)
 by (rule_tac x = "(\<lambda>xab ab. ((\<lambda>_. xab)->including(\<lambda>_. x ab)) ab)" in exI, simp)

 show "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> ?thesis"
  apply(rule_tac P = "\<lambda>s. (s->including(x))" in StrictRefEq_set_L_subst1)
  apply(rule cp)
  apply(simp add: foundation20) apply(simp add: foundation20)
  apply (simp add: foundation10 foundation6)+
 done
qed

lemma including_subst_set'' : "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> (s::('\<AA>,'a::null)Set) \<tau> = t \<tau> \<Longrightarrow> s->including(x) \<tau> = (t->including(x)) \<tau>"
 apply(frule including_subst_set'[where s = s and t = t and x = x], simp_all del: StrictRefEq_set_exec)
 apply(simp add: StrictRefEq_set OclValid_def del: StrictRefEq_set_exec)
 apply (metis (hide_lams, no_types) OclValid_def foundation20 foundation22)
by (metis cp_OclIncluding)

lemma including_id' :
                     "\<And>(S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) x.
                      all_defined \<tau> S \<Longrightarrow>
                      x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->including(\<lambda>\<tau>. x) \<tau> = S \<tau>"
proof -
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "\<And>S x.
                      all_defined \<tau> S \<Longrightarrow>
                      x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      ?thesis S x"
  apply(simp add: OclIncluding_def all_defined1[simplified OclValid_def] OclValid_def insert_absorb abs_rep_simp del: StrictRefEq_set_exec)
 by (metis (lifting) OCL_core.bot_fun_def all_defined_def all_defined_set_def foundation18' valid_def)
qed

lemma including_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
   shows "            \<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->including(\<lambda>\<tau>. x) = S"
proof -
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have abs_rep_simp : "\<And>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
 proof - fix \<tau> show "?thesis \<tau>"
  apply(insert S_all_def[where \<tau> = \<tau>])
  apply(simp add: all_defined_def all_defined_set_def OclValid_def defined_def)
  apply(rule mp[OF Abs_Set_0_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau> then false \<tau> else true \<tau>) = true \<tau> \<and>
          finite \<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil> \<and>
          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. (if x = \<bottom> \<tau> then false \<tau> else true \<tau>) = true \<tau>) \<longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]])
  apply(simp add: Abs_Set_0_inverse discr_eq_false_true)
  apply(case_tac y, simp)
  apply(simp add: bot_fun_def bot_Set_0_def)
  apply(case_tac a, simp)
  apply(simp add: null_fun_def null_Set_0_def)
  apply(simp)
  apply(simp)
  by (metis OCL_core.bot_fun_def valid_def)
 qed

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have ball_to_all : "\<And>S P. (\<forall>x\<in>S. P x) \<Longrightarrow> (\<forall>x. x\<in>S \<longrightarrow> P x)"
 by(simp)

 have x_val : "\<And>\<tau>. (\<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
               \<tau> \<Turnstile> \<upsilon> (\<lambda>\<tau>. x)"
  apply(insert S_all_def)
  apply(simp add: all_defined_def all_defined_set_def)
 by (metis (no_types) foundation18')

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "               (\<forall>\<tau>. x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<Longrightarrow>
                      ?thesis"
  apply(rule ext, rename_tac \<tau>', simp add: OclIncluding_def)
  apply(subst insert_absorb) apply (metis (full_types) surj_pair)
  apply(subst abs_rep_simp, simp)
  proof - fix \<tau>' show "\<forall>a b. x \<in> \<lceil>\<lceil>Rep_Set_0 (S (a, b))\<rceil>\<rceil> \<Longrightarrow> ((\<delta> S) \<tau>' = true \<tau>' \<longrightarrow> (\<upsilon> (\<lambda>\<tau>. x)) \<tau>' \<noteq> true \<tau>') \<longrightarrow> \<bottom> = S \<tau>'"
  apply(frule x_val[simplified, where \<tau> = \<tau>'])
  apply(insert S_all_def[where \<tau> = \<tau>'])
  apply(subst all_defined1[simplified OclValid_def], simp)
  by (metis OclValid_def)
 qed
 apply_end(simp)
qed

lemma excluding_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and x_int : "is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x)"
   shows "            \<forall>\<tau>. x \<notin> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      S->excluding(\<lambda>\<tau>. x) = S"
proof -

 have S_incl : "\<forall>(x :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
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
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def])
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

lemma cons_all_def :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> (x :: 'a state \<times> 'a state \<Rightarrow> int option option)"
    shows "\<And>\<tau>. all_defined \<tau> S->including(x)"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"

          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>, THEN foundation17]
                       x_val[of \<tau>, THEN foundation19] Set_inv_lemma[OF S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
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

 have invert_all_defined_aux : "\<And>
   (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)
   (x :: 'a state \<times> 'a state \<Rightarrow> int option option) \<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
  fix \<tau>
  show "?thesis \<tau>"
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def OclIncluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux[where S = S and x = x and \<tau> = \<tau>]]
                S_all_def[simplified all_defined_def, of \<tau>]
                x_val[of \<tau>], simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>"])
   apply(simp add: all_defined_set_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

lemma cons_all_def_e :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> (x :: 'a state \<times> 'a state \<Rightarrow> int option option)"
    shows "\<And>\<tau>. all_defined \<tau> S->excluding(x)"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"

          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>, THEN foundation17]
                       x_val[of \<tau>, THEN foundation19] Set_inv_lemma[OF S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
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

 have invert_all_defined_aux : "\<And>
   (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)
   (x :: 'a state \<times> 'a state \<Rightarrow> int option option) \<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
  fix \<tau>
  show "?thesis \<tau>"
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def OclExcluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux[where S = S and x = x and \<tau> = \<tau>]]
                S_all_def[simplified all_defined_def, of \<tau>]
                x_val[of \<tau>], simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor>"])
   apply(simp add: all_defined_set_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

lemma cons_all_def' :
  assumes S_all_def : "all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
  assumes x_val : "\<tau> \<Turnstile> \<upsilon> (x :: 'a state \<times> 'a state \<Rightarrow> int option option)"
    shows "all_defined \<tau> (S->including(x))"
proof -

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"

          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation17]
                       x_val[THEN foundation19] Set_inv_lemma[OF S_all_def[simplified all_defined_def, THEN conjunct1]])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
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

 have invert_all_defined_aux : "\<And>
   (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)
   (x :: 'a state \<times> 'a state \<Rightarrow> int option option). (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
  show ?thesis
   apply(subgoal_tac "\<tau> \<Turnstile> \<upsilon> x") prefer 2 apply(simp add: x_val)
   apply(simp add: all_defined_def OclIncluding_def OclValid_def)
   apply(simp add: x_val[simplified OclValid_def] S_all_def[simplified all_defined_def OclValid_def])
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux[where S = S and x = x]]
                S_all_def[simplified all_defined_def]
                x_val, simp)
   apply(simp add: cp_defined[of "\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau> then Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<union> {x \<tau>}\<rfloor>\<rfloor> else \<bottom>"])
   apply(simp add: all_defined_set_def OclValid_def)
   apply(simp add: cp_valid[symmetric] x_val[simplified OclValid_def])
   apply(rule G)
 done
qed

lemma mtSet_all_def : "\<And>\<tau>. all_defined \<tau> Set{}"
proof -
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 show "\<And>\<tau>. ?thesis \<tau>"
  apply(simp add: all_defined_def all_defined_set_def mtSet_def Abs_Set_0_inverse B)
 by (metis (no_types) foundation16 mtSet_def mtSet_defined transform1)
qed

lemma invert_all_defined : "\<And>
   (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)
   (x :: 'a state \<times> 'a state \<Rightarrow> int option option) \<tau>.
   all_defined \<tau> (S->including(x)) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> all_defined \<tau> S"
 proof -
 have invert_all_defined_aux : "\<And>
   (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)
   (x :: 'a state \<times> 'a state \<Rightarrow> int option option) \<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done

 have finite_including_exec : "\<And>\<tau> X x. \<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_including_exec)
  apply(metis OclValid_def foundation5)+
 done

 fix S x \<tau>
  show "all_defined \<tau> (S->including(x)) \<Longrightarrow> ?thesis S x \<tau>"
   apply(simp add: all_defined_def all_defined_set_def)
   apply(erule conjE, frule finite_including_exec[of \<tau> S x], simp)
   apply(rule conjI, metis foundation5)+
   apply(rule ballI, erule conjE, rename_tac x')
   apply(unfold OclIncluding_def)
   apply(drule_tac x = x' in ballE) prefer 3 apply assumption
   apply(simp)
   apply(subgoal_tac False, simp)
   apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau>", simp)
   apply(rename_tac x', subgoal_tac "(\<upsilon> x) \<tau> = true \<tau>", simp)
   apply(insert Abs_Set_0_inverse[OF invert_all_defined_aux[where S = S and x = x and \<tau> = \<tau>], simplified OclValid_def], simp)
   apply(metis OclValid_def foundation5)
   apply(metis OclValid_def foundation5)
  done
qed

lemma invert_all_defined' : "\<And>
   (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)
   (x :: int option option).
   (\<forall>\<tau>. all_defined \<tau> (S->including(\<lambda>(_:: 'a state \<times> 'a state). x))) \<Longrightarrow> is_int (\<lambda> (_:: 'a state \<times> 'a state). x) \<and> (\<forall>\<tau>. all_defined \<tau> S)"
   apply(rule conjI)
   apply(simp only: is_int_def, rule allI)
   apply(erule_tac x = \<tau> in allE, simp)
   apply(drule invert_all_defined, simp)
   apply(rule allI)
   apply(erule_tac x = \<tau> in allE)
   apply(drule invert_all_defined, simp)
done

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

lemma including_notempty :
  assumes S_def : "\<tau> \<Turnstile> \<delta> S"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
      and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
    shows "\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -
 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
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
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
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

lemma iterate_cp_all :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: 'a state \<times> 'a state) = S \<tau>2"
   shows "OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>1 = OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>2"
proof -
 interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  S_cp)

  apply(subst finite_induct[where P = "\<lambda>set.
                                      let set' = (\<lambda>a \<tau>. a) ` set in all_int_set set' \<longrightarrow>
                                      (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F S set')) \<and>
                                      (Finite_Set.fold F S set' \<tau>1 = Finite_Set.fold F S set' \<tau>2)"
                             and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>2)\<rceil>\<rceil>"
                           , simplified Let_def, THEN mp])
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def all_defined_set_def])
  apply(simp add: S_cp A_all_def)
  apply(rule impI)+
    apply(drule mp, simp add: all_int_set_def)

    apply(rule conjI, rule allI)
    apply(erule conjE)+
    apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
    apply(rule iterate_subst_set_rec0[OF A_all_def F_commute, THEN spec], simp, simp, simp, simp add: A_all_def, simp)
    apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(simp)
  apply(frule invert_all_int_set)
  apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], simp add: A_all_def, simp)
   apply(rule invert_int, simp, simp)
  apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], simp add: A_all_def, simp)
   apply(rule invert_int, simp, simp)

  apply(rule cp_gen')
   apply(rule invert_int, simp, simp)
  apply(simp)
  apply(simp add: A_all_def')
  apply(simp)
 done
qed

lemma iterate_cp_all' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_cp : "S (\<tau>1 :: 'a state \<times> 'a state) = S \<tau>2"
   shows "OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>1 = OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>2"
proof -
 interpret EQ_comp_fun_commute0' "\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule F_commute)

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  S_cp)
  apply(rule iterate_induct[where P = "\<lambda>set'.
                                      (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F S set')) \<and>
                                      (Finite_Set.fold F S set' \<tau>1 = Finite_Set.fold F S set' \<tau>2)"

                           , simplified Let_def, THEN conjunct2])
  apply(simp add: S_cp A_all_def)
  apply(simp add: S_cp A_all_def)

  apply(rule impI)+

    apply(rule conjI, rule allI)
    apply(erule conjE)+
    apply(subst img_fold'[OF F_commute], simp add: A_all_def, simp)
    apply(rule iterate_subst_set_rec0'[OF A_all_def F_commute, THEN spec], simp, simp, simp, simp add: A_all_def, simp)
    apply(subst img_fold'[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, simp)

  apply(simp)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], simp add: A_all_def, simp, simp, simp)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], simp add: A_all_def, simp, simp, simp)

  apply(rule cp_gen')
   apply(rule invert_int, simp, simp)
  apply(simp)
 done
qed

lemma iterate_notempty :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
   shows "\<lceil>\<lceil>Rep_Set_0 (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 interpret EQ_comp_fun_commute0 "\<lambda>x. F (\<lambda>_. x)" by (rule F_commute)
 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(insert S_notempty)

  apply(subst finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` set in all_int_set set' \<longrightarrow>
                                      (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F S set')) \<and>
                                      \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F S (set') \<tau>)\<rceil>\<rceil> \<noteq> {}"
                      and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp])

  apply(simp add: A_all_def[THEN spec, simplified all_defined_def all_defined_set_def])
  apply(simp add: A_all_def)
  apply(rule impI)+
    apply(drule mp, simp add: all_int_set_def)

    apply(rule conjI, rule allI)
    apply(erule conjE)+
    apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
    apply(rule iterate_subst_set_rec0[OF A_all_def F_commute, THEN spec], simp, simp, simp, simp add: A_all_def, simp)
    apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)

  apply(simp)
  apply(frule invert_all_int_set)
  apply(subst EQ_comp_fun_commute000.fold_insert'[OF F_commute[THEN c000_of_c0[where f = F]], simplified], simp add: A_all_def, simp)
   apply(rule invert_int, simp, simp)

  apply(rule notempty')
  apply(simp add: A_all_def)
  apply(insert A_all_def', drule_tac x = \<tau> in allE) prefer 2 apply assumption apply(simp add: all_int_set_def)
  apply(simp)
  apply(blast, simp)
 done
qed

lemma iterate_notempty' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> S"
     and S_notempty : "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
   shows "\<lceil>\<lceil>Rep_Set_0 (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F \<tau>)\<rceil>\<rceil> \<noteq> {}"
proof -

 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 interpret EQ_comp_fun_commute0' "\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule F_commute)
 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[THEN spec, simplified all_defined_def OclValid_def]
                  A_all_def[THEN spec, simplified all_defined_def all_defined_set_def]
                  A_all_def[THEN spec, simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(insert S_notempty)

  apply(rule iterate_induct[where P = "\<lambda>set'.
                                      (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F S set')) \<and>
                                      \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F S (set') \<tau>)\<rceil>\<rceil> \<noteq> {}"
                           , simplified Let_def, THEN conjunct2])
  apply(simp add: A_all_def)
  apply(simp add: A_all_def)
  apply(rule impI)+

    apply(rule conjI, rule allI)
    apply(erule conjE)+
    apply(subst img_fold'[OF F_commute], simp add: A_all_def, simp)
    apply(rule iterate_subst_set_rec0'[OF A_all_def F_commute, THEN spec], simp, simp, simp, simp add: A_all_def, simp)
    apply(subst img_fold'[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, simp)

  apply(simp)
  apply(frule invert_all_int_set)
  apply(subst EQ_comp_fun_commute000'.fold_insert'[OF F_commute[THEN c000'_of_c0'[where f = F]], simplified], simp add: A_all_def, simp, simp, simp)

  apply(rule notempty')
  apply(simp add: A_all_def)
  apply(insert A_all_def', drule_tac x = \<tau> in allE) prefer 2 apply assumption apply(simp add: all_int_set_def)
  apply(simp)
 done
qed

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

  fix x :: "'a state \<times> 'a state \<Rightarrow> int option option" fix S :: "'a state \<times> 'a state \<Rightarrow> int option option Set_0" fix \<tau>1 \<tau>2
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

lemma including_commute : "EQ_comp_fun_commute (\<lambda>j r2. (r2->including(j)))"
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
   shows "EQ_comp_fun_commute (\<lambda>x acc. ((acc->including(x))->including(i)))"
 apply(rule including_commute_gen_var)
 apply(rule including_commute)
 apply(rule including_swap', simp_all add: i_int)
done

lemma including_commute3 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x acc. acc->including(i)->including(x))"
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
   shows "EQ_comp_fun_commute (\<lambda>x acc. acc->including(i)->including(x)->including(j))"
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
   shows "EQ_comp_fun_commute (\<lambda>x acc. acc->including(x)->including(j)->including(i))"
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
   shows "EQ_comp_fun_commute (\<lambda>x acc. acc->including(i)->including(j)->including(x))"
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

lemma i_cons_all_def :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> S"
   shows "all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
proof -
 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: A_all_def)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: A_all_def[simplified all_defined_def OclValid_def]
                  A_all_def[simplified all_defined_def all_defined_set_def]
                  A_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(subgoal_tac "\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold F S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))", metis (lifting, no_types) foundation16 all_defined_def)
  apply(rule finite_induct[where P = "\<lambda>set. let set' = (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` set in all_int_set set' \<longrightarrow>
                                      (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F S set'))"
                      and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simplified Let_def, THEN mp])
  apply(simp add: A_all_def[simplified all_defined_def all_defined_set_def])
  apply(simp add: A_all_def)
  apply(rule impI)+
    apply(drule mp, simp add: all_int_set_def)

    apply(subst img_fold[OF F_commute], simp add: A_all_def, simp)
    apply(rule iterate_subst_set_rec0[OF _ F_commute], simp add: A_all_def, simp, simp, simp add: A_all_def, simp)
    apply(subst img_fold[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, rule invert_all_int_set, simp, simp)
   apply(simp add: A_all_def')
 done
qed

lemma i_cons_all_def'' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and S_all_def : "\<And>\<tau>. all_defined \<tau> S"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
   shows "all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S A F)"
proof -
 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

 have A_all_def' : "\<forall>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(rule allI, rule all_def_to_all_int, simp add: S_all_def)
 done

 have invert_all_int_set : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                                  all_int_set S"
 by(simp add: all_int_set_def)

 have invert_int : "\<And>x S. all_int_set (insert x S) \<Longrightarrow>
                           is_int x"
 by(simp add: all_int_set_def)

 show ?thesis
  apply(unfold OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def OclValid_def]
                  S_all_def[simplified all_defined_def all_defined_set_def]
                  A_all_def[simplified all_defined_def, THEN conjunct1, THEN foundation20, simplified OclValid_def]
                  )
  apply(subgoal_tac "\<forall>\<tau>'. all_defined \<tau>' (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))", metis (lifting, no_types) foundation16 all_defined_def)
  apply(rule iterate_induct[where P = "\<lambda>set'.
                                      (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold F A set'))"
                           , simplified Let_def])
  apply(simp add: S_all_def)
  apply(simp add: A_all_def)
  apply(rule impI)+

    apply(subst img_fold'[OF F_commute], simp add: A_all_def, simp)
    apply(rule iterate_subst_set_rec0'[OF _ F_commute], simp add: A_all_def, simp, simp, simp add: A_all_def, simp)
    apply(subst img_fold'[where G = F, OF F_commute, symmetric], simp add: A_all_def, simp, simp)
 done
qed

lemma i_cons_all_def' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> S"
   shows "all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
by(rule i_cons_all_def'', simp_all add: assms)

lemma i_invert_all_defined_not :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<exists>\<tau>. \<not> all_defined \<tau> S"
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
   apply(simp add: all_defined_set_def )
   apply(case_tac "S \<tau>", simp)
   apply(erule disjE, simp add: bot_option_def)
   apply (metis (hide_lams, no_types) OclValid_def bot_Set_0_def foundation18')
   apply(erule disjE, simp add: null_option_def Abs_Set_0_inverse[OF B] bot_option_def Abs_Set_0_inverse[OF C])
   apply (metis OclValid_def foundation17 null_Set_0_def null_option_def)
   apply(subgoal_tac "Rep_Set_0 (Abs_Set_0 y) = y", simp add: valid_def OclValid_def bot_option_def bot_fun_def false_def true_def)
   apply (metis option.distinct(1) true_def)
   apply(rule Abs_Set_0_inverse)
   apply(simp)

   apply(subst all_defined_def)
   apply(subst defined_def)
   apply(simp only: OclValid_def)
   apply(simp)
  by (metis OCL_core.bot_fun_def OclValid_def foundation2 null_fun_def)
 qed
qed

lemma i_invert_all_defined_not' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<exists>\<tau>. \<not> all_defined \<tau> S"
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
   apply(simp add: all_defined_set_def )
   apply(case_tac "S \<tau>", simp)
   apply(erule disjE, simp add: bot_option_def)
   apply (metis (hide_lams, no_types) OclValid_def bot_Set_0_def foundation18')
   apply(erule disjE, simp add: null_option_def Abs_Set_0_inverse[OF B] bot_option_def Abs_Set_0_inverse[OF C])
   apply (metis OclValid_def foundation17 null_Set_0_def null_option_def)
   apply(subgoal_tac "Rep_Set_0 (Abs_Set_0 y) = y", simp add: valid_def OclValid_def bot_option_def bot_fun_def false_def true_def)
   apply (metis option.distinct(1) true_def)
   apply(rule Abs_Set_0_inverse)
   apply(simp)

   apply(subst all_defined_def)
   apply(subst defined_def)
   apply(simp only: OclValid_def)
   apply(simp)
  by (metis OCL_core.bot_fun_def OclValid_def foundation2 null_fun_def)
 qed
qed

lemma i_invert_all_defined :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   shows "all_defined \<tau> S"
by (metis A_all_def F_commute i_invert_all_defined_not)

lemma i_invert_all_defined' :
 assumes F_commute : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   shows "\<forall>\<tau>. all_defined \<tau> S"
by (metis A_all_def F_commute i_invert_all_defined)

lemma i_invert_all_defined0 :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   shows "all_defined \<tau> S"
by (metis A_all_def F_commute i_invert_all_defined_not')

lemma i_invert_all_defined0' :
 assumes F_commute : "EQ_comp_fun_commute0' (\<lambda>x. F (\<lambda>_. \<lfloor>x\<rfloor>))"
     and A_all_def : "\<forall>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)"
   shows "\<forall>\<tau>. all_defined \<tau> S"
by (metis A_all_def F_commute i_invert_all_defined_not')

lemma i_including_id :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
 assumes S_include : "\<And>\<tau> \<tau>'. \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (S \<tau>')\<rceil>\<rceil>"
   shows "                  \<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                            (Finite_Set.fold (\<lambda>j r2. r2->including(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)) = S"
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

 show "\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) = S"
  apply(subst finite_induct[where P = "\<lambda>set. all_defined_set \<tau> set \<and> \<lfloor>\<lfloor>set\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<longrightarrow>
                                             (\<forall>(s :: 'a state \<times> 'a state \<Rightarrow> _). (\<forall>\<tau>. all_defined \<tau> s) \<longrightarrow>
                                                  (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set)))) \<and>
                                             (\<forall>(s :: 'a state \<times> 'a state \<Rightarrow> _). (\<forall>\<tau>. all_defined \<tau> s) \<and> (\<forall>\<tau>. set \<subseteq> \<lceil>\<lceil>Rep_Set_0 (s \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                                                  (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set)) = s)"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def])
  apply(simp)
  defer
  apply(insert S_all_def[simplified all_defined_def all_defined_set_def, where \<tau> = \<tau>])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def] all_defined_set_def) apply(rule disjI2)+
  apply(insert S_all_def[simplified all_defined_def all_defined_set_def, where \<tau> = \<tau>])
  apply(metis (mono_tags) foundation18')
  apply(metis S_all_def S_include)
  apply(simp)

  (* *)
  apply(rule impI) apply(erule conjE)+
  apply(drule invert_set_0, simp del: StrictRefEq_set_exec)
  apply(frule invert_all_def_set, simp del: StrictRefEq_set_exec)
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
  apply(subst EQ_comp_fun_commute.fold_insert[where f = "(\<lambda>j r2. r2->including(j))", OF including_commute])
  apply(metis PairE)
  apply(simp)+
  apply(rule invert_int, simp)

   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  apply(simp)
  apply(rule including_id)
  apply(metis prod.exhaust)
  apply(auto)
 done
 apply_end(simp)
qed

lemma iterate_commute' :
 assumes f_comm : "\<And>a. EQ_comp_fun_commute0' (\<lambda>x. (F:: int option \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option)
   \<Rightarrow> ('a state \<times> 'a state \<Rightarrow> int option option Set_0)
     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option Set_0) a (\<lambda>_. \<lfloor>x\<rfloor>))"

 assumes f_notempty : "\<And>S x y \<tau>. is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow>
            is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>y\<rfloor>) \<Longrightarrow>
            (\<forall>(\<tau>::'a state \<times> 'a state). all_defined \<tau> S) \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            OclIterate\<^isub>S\<^isub>e\<^isub>t (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x)) (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F x)) (F y) \<tau> =
            OclIterate\<^isub>S\<^isub>e\<^isub>t (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F y)) (OclIterate\<^isub>S\<^isub>e\<^isub>t S S (F y)) (F x) \<tau>"

 shows "EQ_comp_fun_commute0' (\<lambda>x S. S ->iterate(j;S=S | F x j S))"
 proof - interpret EQ_comp_fun_commute0' "\<lambda>x. F a (\<lambda>_. \<lfloor>x\<rfloor>)" by (rule f_comm)
 apply_end(simp only: EQ_comp_fun_commute0'_def)
 apply_end(rule conjI)+
 apply_end(subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm], simp)
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
 show "(\<forall>\<tau>. all_defined \<tau> (OclIterate\<^isub>S\<^isub>e\<^isub>t y y (F x))) = (is_int (\<lambda>(_:: 'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<and> (\<forall>\<tau>. all_defined \<tau> y))"
  apply(rule iffI, rule conjI) apply(simp add: is_int_def OclValid_def valid_def bot_fun_def bot_option_def)
  apply(rule i_invert_all_defined0'[where F = "F x", OF f_comm], simp)
  apply(rule allI, rule i_cons_all_def'[where F = "F x", OF f_comm], blast)
 done

 apply_end(rule allI)+ apply_end(rule impI)+
 apply_end(rule ext, rename_tac \<tau>)
 fix S:: "'a state \<times> 'a state \<Rightarrow> int option option Set_0" and x :: "int option" and y:: "int option" and \<tau>
 show " is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>x\<rfloor>) \<Longrightarrow>
             is_int (\<lambda>(_::'a state \<times> 'a state). \<lfloor>y\<rfloor>) \<Longrightarrow>
             (\<forall>(\<tau>::'a state \<times> 'a state). all_defined \<tau> S) \<Longrightarrow>
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

  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm])
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm])
  apply(simp)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm, symmetric])
  apply(simp)


  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm])
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm])
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm, symmetric])
  apply(rule f_notempty, simp_all)

 done
qed

lemma i_including_id' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
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
                                             (\<forall>(s :: 'a state \<times> 'a state \<Rightarrow> _). (\<forall>\<tau>. all_defined \<tau> s) \<longrightarrow>
                                                  (\<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set)))) \<and>
                                             (\<forall>(s :: 'a state \<times> 'a state \<Rightarrow> _). (\<forall>\<tau>. all_defined \<tau> s) \<and> (set \<subseteq> \<lceil>\<lceil>Rep_Set_0 (s \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                                                  (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set)) \<tau> = s \<tau>)"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def])
  apply(simp)
  defer
  apply(insert S_all_def[simplified all_defined_def all_defined_set_def, where \<tau> = \<tau>])
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def] all_defined_set_def) apply(rule disjI2)+
  apply(insert S_all_def[simplified all_defined_def all_defined_set_def, where \<tau> = \<tau>])
  apply(metis (mono_tags) foundation18')
  apply (metis assms order_refl)
  apply(simp)

  (* *)
  apply(rule impI) apply(erule conjE)+
  apply(drule invert_set_0, simp del: StrictRefEq_set_exec)
  apply(frule invert_all_def_set, simp del: StrictRefEq_set_exec)
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
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     shows "(S ->iterate(j;r2=S | r2->including(j))) = S"
  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def OclValid_def del: StrictRefEq_set_exec, rule ext)
  apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq_set_exec)
   prefer 2
   proof -
   fix \<tau>
   show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
   apply(simp add: S_all_def[of \<tau>, simplified all_defined_def OclValid_def all_defined_set_def]
                   foundation20[simplified OclValid_def])
   done
  apply_end(subst i_including_id', simp_all add: S_all_def)
qed

lemma preserved_defined :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
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
  apply(simp add: S_all_def[where \<tau> = \<tau>, simplified all_defined_def all_defined_set_def])
  apply(simp add: A_all_def)
  apply(rule impI, simp only: image_insert, rule iterate_subst_set_rec[simplified Let_def, THEN mp, THEN mp, THEN mp])
  apply(simp add: A_all_def)
  apply(simp add: including_commute)
  apply(simp)
  apply(simp)
  apply(drule invert_all_int_set, simp)

  apply(simp add: all_int_set_def is_int_def, insert S_all_def[simplified all_defined_def all_defined_set_def], simp)
 by (metis (no_types) foundation18')
qed

lemma iterate_including_commute :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: 'a state \<times> 'a state). x) \<Longrightarrow>
            is_int (\<lambda>(_:: 'a state \<times> 'a state). y) \<Longrightarrow>
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: 'a state \<times> 'a state). x} Set{\<lambda>(_:: 'a state \<times> 'a state). x} F->including(\<lambda>(_:: 'a state \<times> 'a state). y) =
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: 'a state \<times> 'a state). y} Set{\<lambda>(_:: 'a state \<times> 'a state). y} F->including(\<lambda>(_:: 'a state \<times> 'a state). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: 'a state \<times> 'a state). x) \<Longrightarrow>
            is_int (\<lambda>(_:: 'a state \<times> 'a state). y) \<Longrightarrow>
            \<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (OclIterate\<^isub>S\<^isub>e\<^isub>t ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: 'a state \<times> 'a state). x)) ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: 'a state \<times> 'a state). x)) F)->including(\<lambda>(_:: 'a state \<times> 'a state). y) \<tau> =
                (OclIterate\<^isub>S\<^isub>e\<^isub>t ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: 'a state \<times> 'a state). y)) ((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(\<lambda>(_:: 'a state \<times> 'a state). y)) F)->including(\<lambda>(_:: 'a state \<times> 'a state). x) \<tau> "
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | F j r2)->including(\<lambda>(_:: 'a state \<times> 'a state). x))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)


 show ?thesis
  apply(simp only: EQ_comp_fun_commute0_def)
  apply(rule conjI)+ apply(rule allI)+
  apply(subst cp_OclIncluding, subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0]], subst cp_OclIncluding[symmetric], simp)
  apply(rule allI)+ apply(rule impI)+
  apply(rule including_cp_all, simp, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast)
  apply(rule iterate_cp_all, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+ apply(rule impI)+
  apply(rule including_notempty, rule all_defined1, rule i_cons_all_def, simp add: f_comm, blast, simp add: int_is_valid)
  apply(rule iterate_notempty, simp add: f_comm, simp, simp)
  apply(rule conjI)+ apply(rule allI)+
  apply(rule iffI)
  apply(drule invert_all_defined', erule conjE, rule conjI, simp)
  apply(rule i_invert_all_defined'[where F = F, OF f_comm], simp)
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
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0]])
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0]])
  apply(simp)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0], symmetric], simp)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding[symmetric])
  apply(subst f_empty, simp_all)

  apply(rule com, simp_all)
 done
qed

lemma destruct_int : "\<And>i. is_int i \<Longrightarrow> \<exists>! j. i = (\<lambda>_. j)"
 proof - fix \<tau> show "\<And>i. is_int i \<Longrightarrow> ?thesis i"
  apply(rule_tac a = "i \<tau>" in ex1I)
  apply(rule ext, simp add: is_int_def)
  apply (metis surj_pair)
  apply(simp)
 done
 apply_end(simp)
qed

lemma iterate_including_commute_var :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. F (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: 'a state \<times> 'a state). x) \<Longrightarrow>
            is_int (\<lambda>(_:: 'a state \<times> 'a state). y) \<Longrightarrow>
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: 'a state \<times> 'a state). x, a} Set{\<lambda>(_:: 'a state \<times> 'a state). x, a} F->including(\<lambda>(_:: 'a state \<times> 'a state). y) =
                OclIterate\<^isub>S\<^isub>e\<^isub>t Set{\<lambda>(_:: 'a state \<times> 'a state). y, a} Set{\<lambda>(_:: 'a state \<times> 'a state). y, a} F->including(\<lambda>(_:: 'a state \<times> 'a state). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: 'a state \<times> 'a state). x) \<Longrightarrow>
            is_int (\<lambda>(_:: 'a state \<times> 'a state). y) \<Longrightarrow>
            \<forall>(\<tau> :: 'a state \<times> 'a state). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (OclIterate\<^isub>S\<^isub>e\<^isub>t (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: 'a state \<times> 'a state). x)) (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: 'a state \<times> 'a state). x)) F)->including(\<lambda>(_:: 'a state \<times> 'a state). y) \<tau> =
                (OclIterate\<^isub>S\<^isub>e\<^isub>t (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: 'a state \<times> 'a state). y)) (((OclIterate\<^isub>S\<^isub>e\<^isub>t S S F)->including(a))->including(\<lambda>(_:: 'a state \<times> 'a state). y)) F)->including(\<lambda>(_:: 'a state \<times> 'a state). x) \<tau> "
     and a_int : "is_int a"
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. (((r1 ->iterate(j;r2=r1 | F j r2))->including(a))->including(\<lambda>(_:: 'a state \<times> 'a state). x)))"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)
 show ?thesis
  apply(simp only: EQ_comp_fun_commute0_def)
  apply(rule conjI)+ apply(rule allI)+
  apply(subst (1 2) cp_OclIncluding, subst (1 2 3 4) cp_OclIncluding, subst cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0]], simp)
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
  apply(rule i_invert_all_defined'[where F = F, OF f_comm], simp)
  apply(rule allI, rule cons_all_def, rule cons_all_def, rule i_cons_all_def[OF f_comm], blast) apply(simp add: int_is_valid a_int)+
  apply(rule allI)+ apply(rule impI)+ apply(rule allI)+ apply(rule impI)+

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
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0]])
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8 9 10 11 12) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0]])
  apply(simp)
  apply(subst (1 2 3 4 5 6) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF f_comm[THEN c0'_of_c0], symmetric], simp)
  apply(subst (1 2 3 4 5 6 7 8 9 10 11 12) cp_OclIncluding[symmetric])

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

lemma including_out1 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and i_int : "is_int i"
     shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->iterate(x;acc=A | acc->including(x)->including(i))) \<tau> = (S->iterate(x;acc=A | acc->including(x))->including(i)) \<tau>"
proof -

 have i_valid : "\<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i"
 by (metis i_int int_is_valid)

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have S_finite : "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

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
  apply(subgoal_tac "(\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<notin> (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` F")
  prefer 2
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)

  apply(simp)
  apply(rule invert_all_defined[THEN conjunct2, of _ _ "\<lambda>\<tau>. x"], simp)
  done
 qed

 have i_out : "\<And>i' x F. i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
          (((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A
            ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))->including(i) =
           (((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))"
 proof - fix i' x F show "i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow> ?thesis i' x F"
  apply(simp)
  apply(subst including_id[where S = "((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(\<lambda>_. i')"])
  apply(rule cons_all_def)+
  apply(case_tac \<tau>'', simp)
  apply (metis (no_types) foundation18' is_int_def)
  apply(insert i_int, simp add: is_int_def)
  apply (metis (no_types) foundation18')
  apply(rule allI)
  proof - fix \<tau> show "is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
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

  apply(rule all_def_to_all_int_[where \<tau> = \<tau>]) apply(simp add: S_all_def[simplified all_defined_def])
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
          is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow>
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
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def] all_defined1[OF S_all_def, simplified OclValid_def] all_defined1[OF A_all_def, THEN foundation20, simplified OclValid_def])
  apply(drule i_out1)
  apply(simp add: cp_OclIncluding[of _ i])
 done
qed

lemma including_out2 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and i_int : "is_int i"
     and x0_int : "is_int x0"
     shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->iterate(x;acc=A | acc->including(x0)->including(x)->including(i))) \<tau> = (S->iterate(x;acc=A | acc->including(x0)->including(x))->including(i)) \<tau>"
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
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

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
  apply(subgoal_tac "(\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<notin> (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` F")
  prefer 2
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)

  apply(simp)
  apply(rule invert_all_defined[THEN conjunct2, of _ _ "\<lambda>\<tau>. x"], simp)
  done
 qed

 have i_out : "\<And>i i' x F. is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
          (((Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A
            ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))->including(i) =
           (((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(i))"
 proof - fix i i' x F show "is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow> ?thesis i i' x F"
  apply(simp)
  apply(subst including_id[where S = "((Finite_Set.fold (\<lambda>j r2. (r2->including(j))) A ((\<lambda>a \<tau>. a) ` F))->including(\<lambda>\<tau>. x))->including(\<lambda>_. i')"])
  apply(rule cons_all_def)+
  apply(case_tac \<tau>'', simp)
  apply (metis (no_types) foundation18' is_int_def)
  apply(simp add: is_int_def)
  apply (metis (no_types) foundation18')
  apply(rule allI)
  proof - fix \<tau> show "is_int i \<Longrightarrow> i = (\<lambda>_. i') \<Longrightarrow> is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow> \<forall>a b. all_defined (a, b) (Finite_Set.fold (\<lambda>x acc. acc->including(x)) A ((\<lambda>a \<tau>. a) ` F)) \<Longrightarrow>
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

  apply(rule all_def_to_all_int_[where \<tau> = \<tau>]) apply(simp add: S_all_def[simplified all_defined_def])
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
          is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). x) \<Longrightarrow>
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
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def] all_defined1[OF S_all_def, simplified OclValid_def] all_defined1[OF A_all_def, THEN foundation20, simplified OclValid_def])
  apply(simp add: i_out1)
  apply(simp add: cp_OclIncluding[of _ i] cp_OclIncluding[of _ x0])
 done
qed

lemma Ocl_insert_Diff :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and x_mem : "\<And>\<tau>. x \<in> (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
     and x_int : "is_int x"
   shows "S->excluding(x)->including(x) = S"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(frule Set_inv_lemma)
  apply(simp add: bot_option_def null_Set_0_def null_fun_def
                  foundation18 foundation16 invalid_def)
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

lemma excluding_unfold :
  assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
      and x_val : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
    shows "\<lceil>\<lceil>Rep_Set_0 (S->excluding(x) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}"
proof -
 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have C : "\<And>\<tau>. \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {x \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  proof - fix \<tau> show "?thesis \<tau>"
          apply(insert S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>, THEN foundation17]
                       x_val[of \<tau>, THEN foundation19] Set_inv_lemma[OF S_all_def[simplified all_defined_def, THEN conjunct1, of \<tau>]])
          apply(simp add: bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
  qed
 show ?thesis
  apply(simp add: OclExcluding_def all_defined1[OF S_all_def, simplified OclValid_def] x_val[simplified OclValid_def] Abs_Set_0_inverse[OF C])
 done
qed

lemma i_including_id00 :
 assumes S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<tau>)\<rceil>\<rceil>)"
   shows "\<And>\<tau>. \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ; set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x) in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>(j:: 'a state \<times> 'a state \<Rightarrow> _) r2.
                (r2->including((f:: ('a state \<times> 'a state \<Rightarrow> int option option)
                                     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option) j))) Set{} set') = S')"
proof -
 have S_incl : "\<forall>(x :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0). (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow> (\<forall>\<tau>. \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> = {}) \<longrightarrow> Set{} = x"
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

 have rec : "\<And>(x:: 'a state \<times> 'a state \<Rightarrow> int option option) (F:: ('a state \<times> 'a state \<Rightarrow> int option option) set). all_int_set F \<Longrightarrow>
            is_int x \<Longrightarrow>
            x \<notin> F \<Longrightarrow>
            \<forall>x. (\<forall>\<tau>. all_defined \<tau> x) \<longrightarrow>
                (let img = op ` (\<lambda>a \<tau>. a); set' = F; f = \<lambda>x. x
                 in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = x) \<Longrightarrow>
            \<forall>xa. (\<forall>\<tau>. all_defined \<tau> xa) \<longrightarrow>
                 (let img = op ` (\<lambda>a \<tau>. a); set' = insert x F; f = \<lambda>x. x
                  in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (xa \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = xa)"
  apply(simp only: Let_def image_ident)

  proof - fix \<tau> fix x:: "'a state \<times> 'a state \<Rightarrow> int option option" fix F:: "('a state \<times> 'a state \<Rightarrow> int option option) set"
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
 show "\<forall>S'.  (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a); set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x)  in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>(j:: 'a state \<times> 'a state \<Rightarrow> _) r2.
                (r2->including((f:: ('a state \<times> 'a state \<Rightarrow> int option option)
                                     \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option) j))) Set{} set') = S')"
  apply(rule allI)
  proof - fix S' :: "'a state \<times> 'a state \<Rightarrow> int option option Set_0" show "(\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = op ` (\<lambda>a \<tau>. a); set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>; f = \<lambda>x. x
           in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = S')"
   apply(simp add: Let_def, rule impI)
   apply(subgoal_tac "(let img = op ` (\<lambda>a \<tau>. a); set' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>; f = \<lambda>x. x
    in (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set' = S')") prefer 2

   apply(subst EQ_comp_fun_commute.all_int_induct[where P = "\<lambda>set.
   \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: 'a state \<times> 'a state). a)
     ; set' = set ; f = (\<lambda>x. x) in
                 (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
                 (Finite_Set.fold (\<lambda>(j:: 'a state \<times> 'a state \<Rightarrow> _) r2.
                   (r2->including((f:: ('a state \<times> 'a state \<Rightarrow> int option option)
                                        \<Rightarrow> 'a state \<times> 'a state \<Rightarrow> int option option) j))) Set{} set') = S')"
                                 and F = "(\<lambda>a (\<tau>:: 'a state \<times> 'a state). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", OF including_commute, THEN spec, of S'])
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
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
       and S_incl : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
     shows "(S->iterate(j;r2=Set{} | r2->including(j))) = S"
 apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def OclValid_def del: StrictRefEq_set_exec, rule ext)
 apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq_set_exec)
 prefer 2
  proof -
   have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                  all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
    apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
   by (metis (no_types) OclValid_def foundation18' true_def)

   have S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
   by(rule all_def_to_all_int, simp add: assms)

   fix \<tau>
   show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
     apply(simp add: S_all_def[of \<tau>, simplified all_defined_def OclValid_def all_defined_set_def]
                     foundation20[simplified OclValid_def])
  done
 fix \<tau> show "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> Finite_Set.fold (\<lambda>j r2. r2->including(j)) Set{} ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau> = S \<tau>"
  apply(subst i_including_id00[simplified Let_def image_ident, where S = S and \<tau> = \<tau>])
   prefer 4
   apply(rule refl)
   apply(simp add: S_all_int S_all_def)+
 by (metis S_incl)
qed

lemma flatten_int' :
  assumes a_all_def : "\<And>\<tau>. all_defined \<tau> Set{\<lambda>(\<tau>:: 'a state \<times> 'a state). a}"
      and a_int : "is_int (\<lambda>(\<tau>:: 'a state \<times> 'a state). a)"
    shows "let a = \<lambda>(\<tau>:: 'a state \<times> 'a state). (a :: int option option) in Set{a,a} = Set{a}"
proof -
 have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 have B' : "\<lfloor>\<lfloor>{a}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
  apply(simp) apply(rule disjI2)+ apply(insert int_is_valid[OF a_int]) by (metis foundation18')
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
 by (metis B Abs_Set_0_cases Abs_Set_0_inverse cp_defined defined_def false_def mtSet_def mtSet_defined null_fun_def null_option_def null_set_not_defined true_def)

 show ?thesis
  apply(simp add: Let_def)
  apply(rule including_id, simp add: a_all_def)
  apply(rule allI, simp add: OclIncluding_def int_is_valid[OF a_int, simplified OclValid_def] mtSet_def Abs_Set_0_inverse[OF B] C Abs_Set_0_inverse[OF B'])
 done
qed

lemma flatten_int :
  assumes a_int : "is_int (a :: 'a state \<times> 'a state \<Rightarrow> int option option)"
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

lemma including_out0 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
       and S_include : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
       and S_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
       and a_int : "is_int a"
     shows "(S->iterate(x;acc=Set{a} | acc->including(x))) = (S->including(a))"

 apply(rule ex1E[OF destruct_int[OF a_int]], rename_tac a', simp)
 apply(case_tac "\<forall>\<tau>. a' \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>")
proof -
 have all_def_to_all_int : "\<And>\<tau>. all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) \<Longrightarrow>
                                all_int_set ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)"
  apply(simp add: all_defined_def all_defined_set_def all_int_set_def is_int_def defined_def OclValid_def)
 by (metis (no_types) OclValid_def foundation18' true_def)

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

lemma iterate_including_id_out :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
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
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(j)->including(a))) \<tau> = S->including(a) \<tau>"
  apply(subst including_out1) apply(simp add: S_def a_int)+
  apply(subst iterate_including_id, simp add: S_def, simp)
done

lemma iterate_including_id_out'''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
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
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
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

lemma GogollasChallenge_on_sets:
      "(Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j)))) = Set{\<zero>, \<six>, \<eight>, \<nine>}"
proof -
 have all_defined_68 : "\<And>\<tau>. all_defined \<tau> Set{\<six>, \<eight>}"
   apply(rule cons_all_def)+
   apply(simp add: all_defined_def all_defined_set_def mtSet_def Abs_Set_0_inverse mtSet_defined[simplified mtSet_def])
   apply(simp)+
 done
 have all_defined_9 : "\<And>\<tau>. all_defined \<tau> Set{\<nine>}"
   apply(rule cons_all_def)+
   apply(simp add: all_defined_def all_defined_set_def mtSet_def Abs_Set_0_inverse mtSet_defined[simplified mtSet_def])
   apply(simp)+
 done

 have all_defined1 : "\<And>r2 \<tau>. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 have zero_int : "is_int \<zero>" by (metis StrictRefEq_int_strict' foundation1 is_int_def null_non_zero ocl_zero_def valid4)
 have six_int : "is_int \<six>" by (metis StrictRefEq_int_strict' foundation1 is_int_def null_non_six ocl_six_def valid4)
 have eight_int : "is_int \<eight>" by (metis StrictRefEq_int_strict' foundation1 is_int_def null_non_eight ocl_eight_def valid4)
 have nine_int : "is_int \<nine>" by (metis StrictRefEq_int_strict' foundation1 is_int_def null_non_nine ocl_nine_def valid4)

 have commute8: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(x))" apply(rule including_commute3) by (simp add: zero_int)
 have commute7: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(x)->including(\<zero>))" apply(rule including_commute2) by (simp add: zero_int)
 have commute4: "\<And>x acc. is_int x \<Longrightarrow> EQ_comp_fun_commute (\<lambda>xa acc. acc->including(\<zero>)->including(xa)->including(x))" apply(rule including_commute4) by(simp add: zero_int, blast)
 have commute3: "\<And>x acc. is_int x \<Longrightarrow> EQ_comp_fun_commute (\<lambda>xa acc. acc->including(\<zero>)->including(x)->including(xa))" apply(rule including_commute6) by(simp add: zero_int, blast)

 have swap1 : "\<And>(S:: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) y x.
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

 have commute5: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(\<lambda>(_:: 'a state \<times> 'a state). x))"
  apply(rule iterate_including_commute, rule commute8[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst iterate_including_id_out)
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: zero_int)
   apply (metis including_notempty' is_int_def)
  apply(rule sym, subst cp_OclIncluding)
  apply(subst iterate_including_id_out)
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: zero_int)
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
   apply(simp add: int_is_valid)+
  (* *)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF including_commute3[THEN c0_of_c, THEN c0'_of_c0]], simp add: zero_int)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)

  apply(subst (1 2 3 4 5) iterate_including_id_out)

  apply(metis surj_pair, simp add: zero_int, simp)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule i_cons_all_def, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: zero_int)

  apply(rule including_notempty)
  apply(rule all_defined1, rule cp_all_def[THEN iffD1], rule i_cons_all_def, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: zero_int)
  apply(rule iterate_notempty, rule commute8[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: zero_int)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: zero_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: zero_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1) apply(metis surj_pair, simp add: zero_int, simp add: int_is_valid)

  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute6: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(\<lambda>(_:: 'a state \<times> 'a state). x))"
  apply(rule iterate_including_commute, rule commute7[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst iterate_including_id_out')
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: zero_int)
   apply (metis including_notempty' is_int_def)
  apply(rule sym, subst cp_OclIncluding)
  apply(subst iterate_including_id_out')
   apply (metis cons_all_def' is_int_def mtSet_all_def)
   apply(simp add: zero_int)
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
   apply(simp add: int_is_valid)+
  (* *)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1'[OF including_commute2[THEN c0_of_c, THEN c0'_of_c0]], simp add: zero_int)
  apply(subst (1 2 3 4 5 6) cp_OclIncluding)

  apply(subst (1 2 3 4 5) iterate_including_id_out')

  apply(metis surj_pair, simp add: zero_int, simp)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1])
  apply(rule cons_all_def', rule i_cons_all_def, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: zero_int)

  apply(rule including_notempty)
  apply(rule all_defined1, rule cp_all_def[THEN iffD1], rule i_cons_all_def, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: zero_int)
  apply(rule iterate_notempty, rule commute7[THEN c0_of_c], metis surj_pair, simp add: int_is_valid, simp add: zero_int)
  apply(subst cp_OclIncluding[symmetric], rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: zero_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1, rule cp_all_def[THEN iffD1]) apply(rule cons_all_def)+ apply(metis surj_pair, simp add: zero_int, simp add: int_is_valid)
  apply(rule including_notempty, rule all_defined1) apply(metis surj_pair, simp add: zero_int, simp add: int_is_valid)

  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding)
  apply(subst (1 2 3 4 5 6 7 8) cp_OclIncluding[symmetric])
  apply(subst swap1, simp_all)
 done

 have commute9: "EQ_comp_fun_commute0 (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(\<lambda>_. x))"
  apply(rule iterate_including_commute_var, rule including_commute[THEN c0_of_c])
  apply(rule ext, rename_tac \<tau>)
  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) iterate_including_id)
   apply (metis StrictRefEq_int_strict' cons_all_def' foundation1 is_int_def mtSet_all_def null_non_zero valid4)
   apply (metis StrictRefEq_int_strict' cons_all_def' foundation1 is_int_def mtSet_all_def null_non_zero valid4)

    apply(subst (1 2) cp_OclIncluding[symmetric])
    apply(rule including_swap')
    apply (metis (hide_lams, no_types) all_defined1 including_defined_args_valid int_is_valid mtSet_all_def zero_int)
     apply(simp add: int_is_valid)+

  apply(subst (1 2) cp_OclIncluding)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1', rule including_commute[THEN c0_of_c, THEN c0'_of_c0])
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
  apply(rule including_swap') apply(rule all_defined1, rule cons_all_def, metis surj_pair) apply(simp add: int_is_valid zero_int)+
 done

 have commute1: "EQ_comp_fun_commute0' (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(\<lambda>(_:: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)->including(j)))"
  apply(rule iterate_commute')
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: zero_int, simp add: int_trivial)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1')
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: zero_int, simp)
   apply(rule including_commute6[THEN c0_of_c, THEN c0'_of_c0], simp add: zero_int, simp)
  apply(subst (1 2 3 4 5) iterate_including_id_out''')
  apply(simp_all add: zero_int)
  apply(metis surj_pair)
  apply(subst cp_all_def[symmetric])
  apply(rule i_cons_all_def)
   apply(rule including_commute6[THEN c0_of_c], simp add: zero_int, simp)
   apply(metis surj_pair)
  apply(rule iterate_notempty)
   apply(rule including_commute6[THEN c0_of_c], simp add: zero_int, simp)
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

 have commute2: "EQ_comp_fun_commute0' (\<lambda>x r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(\<lambda>(_:: 'a state \<times> 'a state). \<lfloor>x\<rfloor>)))"
  apply(rule iterate_commute')
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: zero_int, simp add: int_trivial)
  apply(subst (1 2) cp_OclIterate\<^isub>S\<^isub>e\<^isub>t1')
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: zero_int, simp)
   apply(rule including_commute4[THEN c0_of_c, THEN c0'_of_c0], simp add: zero_int, simp)
  apply(subst (1 2 3 4 5) iterate_including_id_out'''')
  apply(simp_all add: zero_int)
  apply(metis surj_pair)
  apply(subst cp_all_def[symmetric])
  apply(rule i_cons_all_def)
   apply(rule including_commute4[THEN c0_of_c], simp add: zero_int, simp)
   apply(metis surj_pair)
  apply(rule iterate_notempty)
   apply(rule including_commute4[THEN c0_of_c], simp add: zero_int, simp)
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

 have set68_notempty : "\<And>(\<tau>:: 'a state \<times> 'a state). \<lceil>\<lceil>Rep_Set_0 (Set{\<six>, \<eight>} \<tau>)\<rceil>\<rceil> \<noteq> {}"
  apply(rule including_notempty)
  apply(simp add: mtSet_all_def)
  apply(simp add: int_is_valid)
  apply(rule including_notempty')
 by(simp add: int_is_valid)
 have set9_notempty : "\<And>(\<tau>:: 'a state \<times> 'a state). \<lceil>\<lceil>Rep_Set_0 (Set{\<nine>} \<tau>)\<rceil>\<rceil> \<noteq> {}"
  apply(rule including_notempty')
 by(simp add: int_is_valid)
 have set68_cp : "\<And>(\<tau>:: 'a state \<times> 'a state) (\<tau>':: 'a state \<times> 'a state). Set{\<six>, \<eight>} \<tau> = Set{\<six>, \<eight>} \<tau>'"
  apply(rule including_cp_all) apply(simp add: six_int) apply(simp add: mtSet_all_def)
  apply(rule including_cp_all) apply(simp add: eight_int) apply(simp add: mtSet_all_def)
 by (simp add: mtSet_def)
 have set9_cp : "\<And>(\<tau>1:: 'a state \<times> 'a state) (\<tau>2:: 'a state \<times> 'a state). Set{\<nine>} \<tau>1 = Set{\<nine>} \<tau>2"
  apply(rule including_cp_all) apply(simp add: nine_int) apply(simp add: mtSet_all_def)
 by (simp add: mtSet_def)

 show ?thesis
  (* *)
  apply(rule ext, rename_tac \<tau>)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(i))"])
   apply(simp add: all_defined_68, simp add: all_defined_9, simp add: set9_cp, simp add: commute1, simp add: commute2)
  apply(subst iterate_subst_set[where G = "\<lambda>j r2. r2->including(\<zero>)->including(j)->including(\<lambda>_. \<lfloor>x\<rfloor>)"]) apply(blast)+
   apply(simp add: commute3, simp add: commute4)
  apply(rule including_swap) apply (metis (hide_lams, mono_tags) StrictRefEq_int_strict' all_defined_def including_defined_args_valid' null_non_zero ocl_and_true1 transform1_rev valid4)
  apply(simp add: int_is_valid)+
  apply(simp add: set9_notempty)
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(i)"])
   apply(simp add: all_defined_68, simp add: all_defined_9, simp add: set9_cp, simp add: commute2, simp add: commute5[THEN c0'_of_c0])
  apply(rule including_out2)
  apply(blast) apply(blast) apply(blast)
  apply(simp add: zero_int)
  apply(simp)
  apply(simp add: set9_notempty)
  (* *)
  apply(subst iterate_subst_set___[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(i)"])
   apply(simp add: all_defined_68, simp add: all_defined_9, simp add: set9_cp, simp add: commute5[THEN c0'_of_c0], simp add: commute6[THEN c0'_of_c0])
  apply(rule including_subst_set'')
   apply(rule all_defined1, rule i_cons_all_def, rule including_commute3[THEN c0_of_c], simp add: zero_int, blast)
   apply(rule all_defined1, rule i_cons_all_def, rule including_commute2[THEN c0_of_c], simp add: zero_int, blast)
   apply(simp add: int_is_valid)
  apply(subst iterate_subst_set[where G = "\<lambda>j r2. r2->including(j)->including(\<zero>)"]) apply(blast)+
   apply(simp add: commute8, simp add: commute7)
  apply(rule including_swap) apply(simp add: all_defined1) apply(simp) apply(simp only: foundation20, simp)
  apply(simp)
  apply(simp add: set9_notempty)
  (* *)
  apply(subst iterate_subst_set''0[where G = "\<lambda>i r1. r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(i)"])
   apply(simp add: all_defined_68 all_defined_9 commute9 commute6 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute9 commute6 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute9 commute6 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute9 commute6 del: StrictRefEq_set_exec)
  apply(rule including_subst_set'')
   apply(rule all_defined1) apply(rule i_cons_all_def, rule including_commute2[THEN c0_of_c], simp add: zero_int, blast)
   apply(rule all_defined1) apply(rule cons_all_def, rule i_cons_all_def, rule including_commute[THEN c0_of_c], blast, simp, simp add: int_is_valid)
  apply(rule including_out1)
  apply(blast) apply(blast)
  apply(simp add: zero_int)
  apply(simp)
  apply(simp add: set9_notempty)
  (* *)
  apply(subst iterate_subst_set'0[where G = "\<lambda>i r1. r1->including(\<zero>)->including(i)"])
   apply(simp add: all_defined_68 all_defined_9 commute8[THEN c0_of_c] commute9 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute8[THEN c0_of_c] commute9 del: StrictRefEq_set_exec)
   apply(simp add: set9_cp)
   apply(simp add: all_defined_68 all_defined_9 commute8[THEN c0_of_c] commute9 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute8[THEN c0_of_c] commute9 del: StrictRefEq_set_exec)
  apply(rule including_subst_set)+
  apply(rule iterate_including_id) apply(blast)+
  (* *)
  apply(subst iterate_subst_set[where G = "\<lambda>i r1. r1->including(i)->including(\<zero>)"])
   apply(simp add: all_defined_68 all_defined_9 commute7 commute8 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute7 commute8 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute7 commute8 del: StrictRefEq_set_exec)
   apply(simp add: all_defined_68 all_defined_9 commute7 commute8 del: StrictRefEq_set_exec)
  apply(rule including_swap) apply(simp add: all_defined1) apply(simp) apply(simp only: foundation20, simp)
  (* *)
  apply(subst including_out1)
   apply(simp add: all_defined_68)
   apply(simp add: all_defined_9)
   apply(simp add: zero_int)
   apply(simp add: set68_notempty)
  (* *)
  apply(rule including_subst_set'')
   apply(rule all_defined1, rule i_cons_all_def'', rule including_commute[THEN c0_of_c, THEN c0'_of_c0], simp add: all_defined_68, simp add: all_defined_9)
   apply (metis (hide_lams, no_types) all_defined1 all_defined_68 all_defined_9 including_defined_args_valid)
   apply(simp)
  (* *)
  apply(subst including_out0)
   apply(simp add: all_defined_68)
   apply(simp add: set68_cp)
   apply(simp add: set68_notempty)
   apply(simp add: nine_int)
  (* *)
  apply(subst including_swap[where i = \<six>])
  apply(simp)+
  (* *)
  apply(subst including_swap)
  apply(simp)+
 done
qed


subsection{* Test Statements *}

lemma short_cut'[simp]: "(\<eight> \<doteq> \<six>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq_int StrongEq_def ocl_eight_def ocl_six_def
                 true_def false_def invalid_def bot_option_def)
 apply(simp only: ocl_eight_def[THEN sym] ocl_six_def[THEN sym])
 apply(simp add: true_def)
done

text{* Elementary computations on Sets.*}
value "\<not> (\<tau>\<^isub>0 \<Turnstile> \<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set))"
value    "\<tau>\<^isub>0 \<Turnstile> \<upsilon>(null::('\<AA>,'\<alpha>::null) Set)"
value "\<not> (\<tau>\<^isub>0 \<Turnstile> \<delta>(null::('\<AA>,'\<alpha>::null) Set))"
value    "\<tau>\<^isub>0 \<Turnstile> \<upsilon>(Set{})"
value    "\<tau>\<^isub>0 \<Turnstile> \<upsilon>(Set{Set{\<two>},null})"
value    "\<tau>\<^isub>0 \<Turnstile> \<delta>(Set{Set{\<two>},null})"
value    "\<tau>\<^isub>0 \<Turnstile> (Set{\<two>,\<one>}->includes(\<one>))"
value "\<not> (\<tau>\<^isub>0 \<Turnstile> (Set{\<two>}->includes(\<one>)))"
value "\<not> (\<tau>\<^isub>0 \<Turnstile> (Set{\<two>,\<one>}->includes(null)))"
value    "\<tau>\<^isub>0 \<Turnstile> (Set{\<two>,null}->includes(null))"
(*
value    "\<tau> \<Turnstile> ((Set{\<two>,\<one>})->forall(z | \<zero> \<prec> z))"
value "\<not> (\<tau> \<Turnstile> ((Set{\<two>,\<one>})->exists(z | z \<prec> \<zero> )))"

value "\<not> (\<tau> \<Turnstile> ((Set{\<two>,null})->forall(z | \<zero> \<prec> z)))"
value    "\<tau> \<Turnstile> ((Set{\<two>,null})->exists(z | \<zero> \<prec> z))"

value    "\<tau> \<Turnstile> (Set{\<two>,null,\<two>} \<doteq> Set{null,\<two>})"
value    "\<tau> \<Turnstile> (Set{\<one>,null,\<two>} <> Set{null,\<two>})"

value    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} \<doteq> Set{Set{null,\<two>}})"
value    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} <> Set{Set{null,\<two>},null})"
*)
end
