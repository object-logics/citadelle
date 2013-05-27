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

section{* Basic Types like Void, Boolean and Integer *}

text{* Since Integer is again a basic type, we define its semantic domain
as the valuations over @{typ "int option option"}*}
type_synonym ('\<AA>)Integer = "('\<AA>,int option option) val"


type_synonym ('\<AA>)Void = "('\<AA>,unit option) val"
text {* Note that this \emph{minimal} OCL type contains only two elements:
undefined and null. For technical reasons, he does not contain to the null-class yet.*}

subsection{* Strict equalities on Basic Types. *}

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

defs   StrictRefEq_int[code_unfold] :
      "(x::('\<AA>)Integer) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y) \<tau>
                                    else invalid \<tau>"

defs   StrictRefEq_bool[code_unfold] :
      "(x::('\<AA>)Boolean) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y)\<tau>
                                    else invalid \<tau>"


subsection{* Logic and algebraic layer  on Basic Types. *}

lemma RefEq_int_refl[simp,code_unfold] :
"((x::('\<AA>)Integer) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq_int if_ocl_def)

lemma RefEq_bool_refl[simp,code_unfold] :
"((x::('\<AA>)Boolean) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq_bool if_ocl_def)

lemma StrictRefEq_int_strict1[simp] : "((x::('\<AA>)Integer) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strict2[simp] : "(invalid \<doteq> (x::('\<AA>)Integer)) = invalid"
by(rule ext, simp add: StrictRefEq_int true_def false_def)

lemma StrictRefEq_int_strictEq_valid_args_valid:
"(\<tau> \<Turnstile> \<delta> ((x::('\<AA>)Integer) \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
proof -
   have A: "\<tau> \<Turnstile> \<delta> (x \<doteq> y) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> \<tau> \<Turnstile> \<upsilon> y"
           apply(simp add: StrictRefEq_int valid_def OclValid_def defined_def)
           apply(simp add: invalid_def bot_fun_def split: split_if_asm)
           done
   have B: "(\<tau> \<Turnstile> \<upsilon> x) \<and> (\<tau> \<Turnstile> \<upsilon> y) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (x \<doteq> y)"
           apply(simp add: StrictRefEq_int, elim conjE)
           apply(drule foundation13[THEN iffD2],drule foundation13[THEN iffD2])
           apply(rule cp_validity[THEN iffD2])
           apply(subst cp_defined, simp add: foundation22)
           apply(simp add: cp_defined[symmetric] cp_validity[symmetric])
           done
   show ?thesis by(auto intro!: A B)
qed

lemma StrictRefEq_bool_strict1[simp] : "((x::('\<AA>)Boolean) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strict2[simp] : "(invalid \<doteq> (x::('\<AA>)Boolean)) = invalid"
by(rule ext, simp add: StrictRefEq_bool true_def false_def)

lemma StrictRefEq_bool_strictEq_valid_args_valid:
"(\<tau> \<Turnstile> \<delta> ((x::('\<AA>)Boolean) \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
proof -
   have A: "\<tau> \<Turnstile> \<delta> (x \<doteq> y) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<and> \<tau> \<Turnstile> \<upsilon> y"
           apply(simp add: StrictRefEq_bool valid_def OclValid_def defined_def)
           apply(simp add: invalid_def bot_fun_def split: split_if_asm)
           done
   have B: "(\<tau> \<Turnstile> \<upsilon> x) \<and> (\<tau> \<Turnstile> \<upsilon> y) \<Longrightarrow> \<tau> \<Turnstile> \<delta> (x \<doteq> y)"
           apply(simp add: StrictRefEq_bool, elim conjE)
           apply(drule foundation13[THEN iffD2],drule foundation13[THEN iffD2])
           apply(rule cp_validity[THEN iffD2])
           apply(subst cp_defined, simp add: foundation22)
           apply(simp add: cp_defined[symmetric] cp_validity[symmetric])
           done
   show ?thesis by(auto intro!: A B)
qed

lemma strictEqBool_vs_strongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)Boolean) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq_bool OclValid_def)
apply(subst cp_StrongEq)back
by simp


lemma strictEqInt_vs_strongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)Integer) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq_int OclValid_def)
apply(subst cp_StrongEq)back
by simp


lemma strictEqBool_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Boolean) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq_bool OclValid_def true_def invalid_def
             bot_option_def
        split: bool.split_asm HOL.split_if_asm)

lemma strictEqInt_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Integer) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> (\<upsilon> y))"
by(simp add: StrictRefEq_int OclValid_def true_def invalid_def valid_def bot_option_def
           split: bool.split_asm HOL.split_if_asm)

lemma strictEqBool_valid_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)Boolean) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq_bool OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)

lemma strictEqInt_valid_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)Integer) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq_int OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)


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

lemma StrictRefEq_int_strict'' : "\<delta> ((x::('\<AA>)Integer) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 strictEqInt_valid_args_valid)

lemma StrictRefEq_bool_strict'' : "\<delta> ((x::('\<AA>)Boolean) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 strictEqBool_valid_args_valid)


lemma cp_StrictRefEq_bool:
"((X::('\<AA>)Boolean) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_bool StrongEq_def defined_def valid_def  cp_defined[symmetric])

lemma cp_StrictRefEq_int:
"((X::('\<AA>)Integer) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq_int StrongEq_def valid_def  cp_defined[symmetric])


lemmas cp_intro[simp,intro!] =
       cp_intro
       cp_StrictRefEq_bool[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]
       cp_StrictRefEq_int[THEN allI[THEN allI[THEN allI[THEN cpI2]],  of "StrictRefEq"]]



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

text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to "True".*}

subsection{* Test Statements on Basic Types. *}

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


(* plus all the others ...*)

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


section {* Example for Complex Types: The Set-Collection Type *}

no_notation None ("\<bottom>")
notation bot ("\<bottom>")

subsection {* The construction of the Set-Collection Type *}

text{* For the semantic construction of the collection types, we have two goals:
\begin{enumerate}
\item we want the types to be \emph{fully abstract}, i.e. the type should not
      contain junk-elements that are not representable by OCL expressions.
\item We want a possibility to nest collection types (so, we want the
      potential to talking about @{text "Set(Set(Sequences(Pairs(X,Y))))"}), and
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


lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_strict1[simp]:"invalid->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^isub>S\<^isub>e\<^isub>t_def defined_def valid_def false_def true_def)

lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_null1[simp]:"null->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^isub>S\<^isub>e\<^isub>t_def defined_def valid_def false_def true_def)


lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_strict2[simp]:"S->iterate(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^isub>S\<^isub>e\<^isub>t_def defined_def valid_def false_def true_def)

text{* An open question is this ... *}
lemma OclIterate\<^isub>S\<^isub>e\<^isub>t_null2[simp]:"S->iterate(a; x = null | P a x) = invalid"
oops
text{* In the definition above, this does not hold in general.
       And I believe, this is how it should be ... *}

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


(* TODO later
lemmas cp_intro''[simp,intro!] =
       cp_intro'
       cp_OclIncludes  [THEN allI[THEN allI[THEN allI[THEN cp'I2]], of "OclIncludes"]]
       cp_OclIncluding [THEN allI[THEN allI[THEN allI[THEN cp'I2]], of "OclIncluding"]]
*)

subsection{* Logic and Algebraic Layer on Set Operations*}

lemma including_strict1[simp,code_unfold]:"(invalid->including(x)) = invalid"
by(simp add: bot_fun_def OclIncluding_def invalid_def defined_def valid_def false_def true_def)

lemma including_strict2[simp,code_unfold]:"(X->including(invalid)) = invalid"
by(simp add: OclIncluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma including_strict3[simp,code_unfold]:"(null->including(x)) = invalid"
by(simp add: OclIncluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)


lemma excluding_strict1[simp,code_unfold]:"(invalid->excluding(x)) = invalid"
by(simp add: bot_fun_def OclExcluding_def invalid_def defined_def valid_def false_def true_def)

lemma excluding_strict2[simp,code_unfold]:"(X->excluding(invalid)) = invalid"
by(simp add: OclExcluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma excluding_strict3[simp,code_unfold]:"(null->excluding(x)) = invalid"
by(simp add: OclExcluding_def invalid_def bot_fun_def defined_def valid_def false_def true_def)



lemma includes_strict1[simp,code_unfold]:"(invalid->includes(x)) = invalid"
by(simp add: bot_fun_def OclIncludes_def invalid_def defined_def valid_def false_def true_def)

lemma includes_strict2[simp,code_unfold]:"(X->includes(invalid)) = invalid"
by(simp add: OclIncludes_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

lemma includes_strict3[simp,code_unfold]:"(null->includes(x)) = invalid"
by(simp add: OclIncludes_def invalid_def bot_fun_def defined_def valid_def false_def true_def)

(*  forall ? exists ?*)

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

subsubsection{* Some computational laws:*}

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
and     strictEq_vs_strongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
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
           apply(subst strictEq_vs_strongEq[THEN foundation22[THEN iffD1]])
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

subsection{* Strict Equality on Sets *}

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

subsection{* Algebraic Properties on Strict Equality on Sets *}

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
                                    strictEqInt_vs_strongEq], simp_all)


schematic_lemma includes_execute_bool[code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq_bool_strict1 StrictRefEq_bool_strict2
                                 cp_StrictRefEq_bool
                                    strictEqBool_vs_strongEq], simp_all)


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
 and     strictEq_valid_args_valid: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
                                     (\<tau> \<Turnstile> \<delta> (x \<doteq> y)) = ((\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> \<upsilon> y))"
 and     cp_StrictRefEq: "\<And> (X::('\<AA>,'a::null)val) Y \<tau>. (X \<doteq> Y) \<tau> = ((\<lambda>_. X \<tau>) \<doteq> (\<lambda>_. Y \<tau>)) \<tau>"
 and     strictEq_vs_strongEq: "\<And> (x::('\<AA>,'a::null)val) y \<tau>.
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
            apply(subst cp_OclIncludes, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_OclIncluding[symmetric] cp_OclIncludes[symmetric])
            by simp

 have B1: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow>
            (X->including(x)->includes(y)) \<tau> = invalid  \<tau>"
            apply(subst cp_OclIncludes, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_OclIncluding[symmetric] cp_OclIncludes[symmetric])
            by simp

 have A2: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> invalid) \<Longrightarrow> X->including(x)->excluding(y) \<tau> = invalid \<tau>"
            apply(subst cp_OclExcluding, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_OclIncluding[symmetric] cp_OclExcluding[symmetric])
            by simp

 have B2: "\<And>\<tau>. \<tau> \<Turnstile> (X \<triangleq> null) \<Longrightarrow> X->including(x)->excluding(y) \<tau> = invalid \<tau>"
            apply(subst cp_OclExcluding, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_OclIncluding[symmetric] cp_OclExcluding[symmetric])
            by simp

 have C: "\<And>\<tau>. \<tau> \<Turnstile> (x \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->excluding(y)) \<tau> =
           (if x \<doteq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau>"
            apply(subst cp_if_ocl, subst cp_StrictRefEq)
            apply(subst cp_OclIncluding, subst cp_OclExcluding, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_if_ocl[symmetric] cp_OclIncluding[symmetric]
                             cp_StrictRefEq[symmetric] cp_OclExcluding[symmetric] )
            by (simp add: strict2)

 have D: "\<And>\<tau>. \<tau> \<Turnstile> (y \<triangleq> invalid) \<Longrightarrow>
           (X->including(x)->excluding(y)) \<tau> =
           (if x \<doteq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau>"
            apply(subst cp_if_ocl, subst cp_StrictRefEq)
            apply(subst cp_OclIncluding, subst cp_OclExcluding, subst cp_OclIncluding)
            apply(drule foundation22[THEN iffD1], simp)
            apply(simp only: cp_if_ocl[symmetric] cp_OclIncluding[symmetric]
                             cp_StrictRefEq[symmetric] cp_OclExcluding[symmetric] )
            by (simp add: strict1)

 have E: "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow>
              (if x \<doteq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau> =
              (if x \<triangleq> y then X->excluding(y) else X->excluding(y)->including(x) endif) \<tau>"
           apply(subst cp_if_ocl)
           apply(subst strictEq_vs_strongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_if_ocl[symmetric])

 have F: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<triangleq> y) \<Longrightarrow>
           (X->including(x)->excluding(y) \<tau>) = (X->excluding(y) \<tau>)"
           apply(simp add: cp_OclExcluding[of "X->including(x)"] cp_OclExcluding[of X])
           apply(drule foundation22[THEN iffD1], drule sym, simp)
           by(simp add: cp_OclExcluding[symmetric] excluding_charn2[simplified foundation22])

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
                                StrictRefEq_int_strictEq_valid_args_valid
                             cp_StrictRefEq_int strictEqInt_vs_strongEq], simp_all)

schematic_lemma excluding_charn_exec_bool[code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq_bool_strict1 StrictRefEq_bool_strict2
                                StrictRefEq_bool_strictEq_valid_args_valid
                             cp_StrictRefEq_bool strictEqBool_vs_strongEq], simp_all)

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

(* example by bu ... *)

 have C : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done

(* example by bu cont ... *)
term (*have finite_including_exec' :*)
    "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
(*  apply(simp add: OclIncluding_def Abs_Set_0_inverse C)
  apply(drule foundation13[THEN iffD2, THEN foundation22[THEN iffD1]], simp)+
  done
*)
(* ... and even more succinct : *)
term (*finite_including_exec'' :*)
     "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
(*  by(auto simp: OclIncluding_def Abs_Set_0_inverse C
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
*)
(* just equivalence, to show that this premise corresponds to the final statement in the logical
chain ...*)
term "\<And>xa. (\<delta> X and \<upsilon> x) xa = true xa"
term "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> "
term "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x) \<triangleq> true"
term "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x)  "
term "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> X) \<and> \<tau> \<Turnstile>(\<upsilon> x)  "

(* and now compare to your original proof *)
 have finite_including_exec : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(simp add: OclIncluding_def)
  apply(subst Abs_Set_0_inverse)
  apply(simp)
  apply(rule disjI2)+
  apply(rule conjI)
  apply(simp add: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_valid[of x] valid_def)
  apply(rule notI, simp add: bot_fun_def )
  apply(simp add: cp_ocl_and[THEN sym])
  apply(simp add: false_def true_def)

  apply(rule disjE[OF Set_inv_lemma[OF foundation5[of _ "\<delta> X" "\<upsilon> x", THEN conjunct1]]])
  apply(simp add: OclValid_def cp_ocl_and[THEN sym])

  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_defined[of x] defined_def)
  apply(split split_if_asm)
  apply(simp only: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(simp)
  apply(simp add: false_def true_def)

  apply(simp add: bot_option_def null_Set_0_def null_fun_def)
  apply(assumption)

  apply(simp)
  apply(case_tac "(\<delta> X) \<tau> = true \<tau>", simp)
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(drule defined_inject_true[of X _])
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(simp add: false_def true_def)
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
  apply(simp add: finite_including_exec card_including_exec
                  cp_ocl_and[of "\<delta> X" "\<upsilon> x"]
                  cp_ocl_and[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_ocl_and[THEN sym])

  apply(drule defined_inject_true[of "X->including(x)->size()"], simp)
  apply(simp only: cp_ocl_and[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->including(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def finite_including_exec card_including_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: finite_including_exec card_including_exec)
  apply(simp only: cp_ocl_and[THEN sym])
  apply(simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
  apply(simp add: finite_including_exec)
  apply(simp add: finite_including_exec card_including_exec)
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
  apply(simp add: OclExcluding_def)
  apply(subst Abs_Set_0_inverse)
  apply(simp)
  apply(rule disjI2)+
  (* *)
  apply(rule disjE[OF Set_inv_lemma[OF foundation5[of _ "\<delta> X" "\<upsilon> x", THEN conjunct1]]])
  apply(simp add: OclValid_def cp_ocl_and[THEN sym])

  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_defined[of x] defined_def)
  apply(split split_if_asm)
  apply(simp only: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(simp)
  apply(simp add: false_def true_def)

  apply(simp add: bot_option_def null_Set_0_def null_fun_def)
  apply(rule ballI)
  apply(drule_tac Q = "xa \<noteq> \<bottom>" and x = xa in ballE)
  apply(assumption)
  apply(simp)

  apply(simp)
  apply(case_tac "(\<delta> X) \<tau> = true \<tau>", simp)
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(drule defined_inject_true[of X _])
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(simp add: false_def true_def)
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
but @{text comp_fun_commute.fold_insert} contains as hypothesis @{text comp_fun_commute},
defined with the ``@{text "="}'' operator.
Because comparing with the ``@{text "="}'' operator might be a too strong result to establish 
on two arbitrary OCL terms,
we would like to reason with a weaken operator, for instance ``@{text "\<doteq>"}''.
Then the following part develops a small library similar as @{theory Finite_Set}, but
the commutation function becomes this simple definition
@{term "\<tau> \<Turnstile> ((f y (f x z)) \<doteq> (f x (f y z)))"}. *}

locale EQ_comp_fun_commute =
  fixes f :: "'a \<Rightarrow> ('b state \<times> 'b state \<Rightarrow> int option option Set_0) \<Rightarrow> ('b state \<times> 'b state \<Rightarrow> int option option Set_0)"
  assumes preserved_valid: "\<And>y. (*\<tau> \<Turnstile> \<upsilon> x \<Longrightarrow>*) \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (f x y)"
  assumes comp_fun_commute: "\<tau> \<Turnstile> ((f y (f x z)) \<doteq> (f x (f y z)))"
begin end

lemma EQ_sym : "(x::'b state \<times> 'b state \<Rightarrow> int option option Set_0) = y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (x \<doteq> y)"
  apply(simp add: OclValid_def)
done

lemma StrictRefEq_set_L_subst1_bool : "cp P \<Longrightarrow> (\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x) \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>)Boolean) \<doteq> P y"
 apply(simp only: StrictRefEq_set StrictRefEq_bool OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma StrictRefEq_set_L_subst2_bool : "cp P \<Longrightarrow> (\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x) \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>)Boolean) \<Longrightarrow> \<tau> \<Turnstile> P y"
 apply(drule_tac \<tau> = \<tau> and x = x and y = y in StrictRefEq_set_L_subst1_bool)
 apply(simp) apply(simp)
by (metis OclValid_def StrictRefEq_bool foundation22 strictEqBool_defargs)

context EQ_comp_fun_commute
begin
lemma EQ_fold_graph_insertE_aux:
  "fold_graph f z A y \<Longrightarrow> a \<in> A \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<exists>y'. (\<tau> \<Turnstile> (y \<doteq> f a y')) \<and> fold_graph f z (A - {a}) y'"
proof (induct set: fold_graph)
  case (insertI x A y) show ?case
  proof (cases "x = a")
    assume "x = a" with insertI show ?case
     apply(rule_tac x = y in exI)
     apply(simp only: EQ_sym)
    by (auto)
  next
    assume "x \<noteq> a"
    then obtain y' where y: "\<tau> \<Turnstile> y \<doteq> f a y'" and y': "fold_graph f z (A - {a}) y'"
      using insertI sorry (* by auto *)
    have "\<tau> \<Turnstile> f x y \<doteq> f a (f x y')"
      unfolding y sorry (* by (rule comp_fun_commute) *)
    moreover have "fold_graph f z (insert x A - {a}) (f x y')"
      using y' and `x \<noteq> a` and `x \<notin> A`
      by (simp add: insert_Diff_if fold_graph.insertI)
    ultimately show ?case by fast
  qed
qed fast

lemma fold_graph_insertE:
  assumes "fold_graph f z (insert x A) v" and "x \<notin> A"
  obtains y where "\<tau> \<Turnstile> v \<doteq> f x y" and "fold_graph f z A y"
using assms sorry (*by (auto dest: fold_graph_insertE_aux [OF _ insertI1])*)

thm empty_fold_graphE
lemma EQ_empty_fold_graphE: "fold_graph f z {} x \<Longrightarrow> (\<tau> \<Turnstile> x \<doteq> z \<Longrightarrow> P) \<Longrightarrow> P " sorry

lemma fold_graph_determ:
  "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> y \<doteq> x"
proof (induct arbitrary: y set: fold_graph)
  case (insertI x A y v)
  from `fold_graph f z (insert x A) v` and `x \<notin> A`
  obtain y' where "\<tau> \<Turnstile> v \<doteq> f x y'" and "fold_graph f z A y'"
    by (rule fold_graph_insertE)
  from `fold_graph f z A y'` have "\<tau> \<Turnstile> y' \<doteq> y" sorry (* by (rule insertI)*)
  with `\<tau> \<Turnstile> v \<doteq> f x y'` show "\<tau> \<Turnstile> v \<doteq> f x y" sorry (*by simp*)
  apply_end (elim empty_fold_graphE)
  apply_end(rule EQ_sym, simp_all)
qed

lemma fold_equality:
  "fold_graph f z A y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> Finite_Set.fold f z A \<doteq> y"
sorry
(*by (unfold Finite_Set.fold_def) (blast intro: fold_graph_determ)*)

lemma fold_graph_fold:
  assumes "finite A"
  shows "fold_graph f z A (Finite_Set.fold f z A)"
proof -
  from assms have "\<exists>x. fold_graph f z A x" by (rule finite_imp_fold_graph)
  moreover note fold_graph_determ
  ultimately have "\<exists>!x. fold_graph f z A x" sorry (* by (rule ex_ex1I) *)
  then have "fold_graph f z A (The (fold_graph f z A))" by (rule theI')
  then show ?thesis by (unfold Finite_Set.fold_def)
qed

lemma fold_insert [simp]:
  assumes "finite A" and "x \<notin> A" and "\<tau> \<Turnstile> \<upsilon> (Finite_Set.fold f z A)"
  shows "\<tau> \<Turnstile> Finite_Set.fold f z (insert x A) \<doteq> f x (Finite_Set.fold f z A)"
proof (rule fold_equality)
  from `finite A` have "fold_graph f z A (Finite_Set.fold f z A)" by (rule fold_graph_fold)
  with `x \<notin> A`show "fold_graph f z (insert x A) (f x (Finite_Set.fold f z A))" by (rule fold_graph.insertI)
  apply_end (rule preserved_valid)
  apply_end (rule assms)
qed

text{* Note that in this @{text "fold_insert"} 
the same result with the ``@{text "="}'' operator may not be proved 
(compare with @{text "comp_fun_commute.fold_insert"}). *}

lemma finite_fold_insert :
  assumes "finite A" and "x \<notin> A" and "\<tau> \<Turnstile> \<upsilon> (Finite_Set.fold f z A)"
  shows "finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold f z (insert x A) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (f x (Finite_Set.fold f z A) \<tau>)\<rceil>\<rceil>"
proof -
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have cp_finite : "cp (\<lambda>x \<tau>. \<lfloor>\<lfloor>finite \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)" by(simp add: cp_def, auto)
 have valid_finite : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> (\<lambda>\<tau>. \<lfloor>\<lfloor>finite \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)"
  apply(simp add: valid_def)
  apply(case_tac "x \<tau> = \<bottom> \<tau>")
  apply(simp add: bot_fun_def bot_option_def)
  apply(simp add: OclValid_def discr_eq_false_true)
 by (metis (hide_lams, mono_tags) OCL_core.bot_fun_def false_def foundation1 foundation18' true_def valid1 valid5 valid_def)

 show ?thesis
  apply(subgoal_tac "\<tau> \<Turnstile> ((\<lambda>\<tau>. \<lfloor>\<lfloor>finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold f z (insert x A) \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>) \<doteq> (\<lambda>\<tau>. \<lfloor>\<lfloor>finite \<lceil>\<lceil>Rep_Set_0 (f x (Finite_Set.fold f z A) \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>))")
  apply(simp add:StrictRefEq_bool StrongEq_def OclValid_def)
  apply(split split_if_asm)
  apply(simp add:StrongEq_def true_def)
  apply(simp add: discr_eq_invalid_true)

  apply(rule StrictRefEq_set_L_subst1_bool)
  apply(simp add: cp_finite)
  apply(simp add: valid_finite)
  apply(rule fold_insert)
  apply(simp_all add: assms)
 done
qed

end


lemma StrictRefEq_set_sym : "\<tau> \<Turnstile> ((s::('\<AA>,'\<alpha>::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (t \<doteq> s)"
 apply(simp only: StrictRefEq_set OclValid_def)
by (metis StrongEq_sym)

lemma StrictRefEq_set_trans : "\<tau> \<Turnstile> ((r::('\<AA>,'\<alpha>::null)Set) \<doteq> s) \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (r \<doteq> t)"
 apply(simp only: StrictRefEq_set OclValid_def)
by (metis (hide_lams, no_types) OclValid_def bot_option_def foundation22 invalid_def option.simps(3) true_def)

lemma StrictRefEq_set_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq_set OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma StrictRefEq_set_L_subst1_ : "cp P \<Longrightarrow> (\<And>x. \<upsilon> x = \<upsilon> P x) \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq_set OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma StrictRefEq_set_L_subst2 : "cp P \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> P x \<Longrightarrow> \<tau> \<Turnstile> P y"
 apply(simp only: StrictRefEq_set OclValid_def)
 apply(case_tac "(\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>", simp)
 apply(rule StrongEq_L_subst2[simplified OclValid_def, where P = P and x = x], simp_all)
by (simp add: invalid_def bot_option_def true_def)

lemma including_swap : "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> \<tau> \<Turnstile> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->including(i)->including(j) \<doteq> (S->including(j)->including(i)))"
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
 by(metis OclValid_def strictEqInt_valid_args_valid)

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
  apply (metis OclValid_def strictEqInt_valid_args_valid)
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
  apply (metis OclValid_def strictEqInt_valid_args_valid)
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

lemma including_out0 : "\<tau> \<Turnstile> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->iterate(x;acc=Set{a} | acc->including(x)) \<doteq> (S->including(a)))"
sorry

lemma including_out1 : "\<tau> \<Turnstile> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->iterate(x;acc=A | acc->including(x)->including(i)) \<doteq> (S->iterate(x;acc=A | acc->including(x))->including(i)))"
sorry

lemma including_out2 : "\<tau> \<Turnstile> ((S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)->iterate(x;acc=A | acc->including(x0)->including(x)->including(i)) \<doteq>
                            (S->iterate(x;acc=A | acc->including(x0)->including(x))->including(i)))"
sorry

definition all_defined_set_def :
 "all_defined_set \<tau> S \<equiv> finite S \<and> (\<forall>x\<in>S. (\<tau> \<Turnstile> (\<delta> (\<lambda>_. x))))"

definition all_defined_def :
 "all_defined \<tau> S \<equiv> \<tau> \<Turnstile> \<delta> S \<and> all_defined_set \<tau> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"

lemma iterate_subst_set_rec :
assumes F_commute : "EQ_comp_fun_commute F"
    and fold_F : "\<And>x acc. \<tau> \<Turnstile> \<delta> x \<Longrightarrow> all_defined \<tau> acc \<Longrightarrow> all_defined \<tau> (F x acc)"
  shows "\<And>x Fa.       finite Fa \<Longrightarrow>
                       x \<notin> Fa \<Longrightarrow>
                       all_defined_set \<tau> (insert x Fa) \<Longrightarrow>
                       all_defined \<tau> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<Longrightarrow>
                       all_defined \<tau> (Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa)))"
proof -
 have CP_d : "cp defined"
  apply(simp add: cp_def, subst cp_defined)
 by(rule_tac x = "\<lambda> xab ab. (\<delta> (\<lambda>_. xab)) ab" in exI, simp)

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "\<And>x Fa. finite Fa \<Longrightarrow>
                       x \<notin> Fa \<Longrightarrow>
                       all_defined_set \<tau> (insert x Fa) \<Longrightarrow>
                       all_defined \<tau> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<Longrightarrow> ?thesis x Fa"
  apply(subst all_defined_def, subst all_defined_set_def)
  apply(rule conjI)
  proof -
   fix x Fa
   show "finite Fa \<Longrightarrow>
         x \<notin> Fa \<Longrightarrow>
         all_defined_set \<tau> (insert x Fa) \<Longrightarrow>
         all_defined \<tau> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<Longrightarrow>
         \<tau> \<Turnstile> \<delta> Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa))"
    apply(rule StrictRefEq_set_L_subst2[OF CP_d, where x = "F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa))"])
    apply(rule StrictRefEq_set_sym)
    apply(rule EQ_comp_fun_commute.fold_insert[where f = F and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. x)", OF F_commute])
    apply(simp)
    apply(rule image_cong)
    apply(rule inject)
    apply(simp)
    apply(simp add: foundation20 all_defined1)
    apply(subgoal_tac "all_defined \<tau> (F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)))")
    apply(simp add: foundation20 all_defined1 del: StrictRefEq_set_exec)+
    apply(rule fold_F, simp_all)
    apply(simp add: all_defined_set_def)
   done
   apply_end(simp_all)
   apply_end(rule conjI)
   fix x Fa
   show "finite Fa \<Longrightarrow>
        x \<notin> Fa \<Longrightarrow>
        all_defined_set \<tau> (insert x Fa) \<Longrightarrow>
        all_defined \<tau> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<Longrightarrow>
        finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa)) \<tau>)\<rceil>\<rceil>"

    apply(simp add: all_defined_def all_defined_set_def)
    apply(subst EQ_comp_fun_commute.finite_fold_insert[OF F_commute])
    apply(simp)
    apply(rule image_cong)
    apply(rule inject)
    apply(simp)
    apply(simp add: foundation20)
    apply(rule fold_F[simplified all_defined_def all_defined_set_def, THEN conjunct2, THEN conjunct1], simp)
    apply(simp)
   done
   apply_end(simp_all)
   apply_end(simp add: all_defined_def all_defined_set_def)
   apply_end(subgoal_tac "\<tau> \<Turnstile> \<lambda>\<tau>. \<lfloor>\<lfloor>\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa)) \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> \<delta> (\<lambda>_. x)\<rfloor>\<rfloor>")
   apply_end(simp add: OclValid_def true_def)
   fix x Fa

   have cp: "cp (\<lambda>y \<tau>. \<lfloor>\<lfloor>\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> \<delta> (\<lambda>_. x)\<rfloor>\<rfloor>)"
    apply(simp add: cp_def)
   by(rule_tac x = "\<lambda> xab ab. \<lfloor>\<lfloor>\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 xab\<rceil>\<rceil>. ab \<Turnstile> \<delta> (\<lambda>_. x)\<rfloor>\<rfloor>" in exI, simp)

   show "finite Fa \<Longrightarrow>
            x \<notin> Fa \<Longrightarrow>
            \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<and> (\<forall>x\<in>Fa. \<tau> \<Turnstile> \<delta> (\<lambda>_. x)) \<Longrightarrow>
            \<tau> \<Turnstile> \<delta> Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) \<and>
            finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) \<tau>)\<rceil>\<rceil> \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> \<delta> (\<lambda>_. x)) \<Longrightarrow>
            \<tau> \<Turnstile> \<lambda>\<tau>. \<lfloor>\<lfloor>\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa)) \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> \<delta> (\<lambda>_. x)\<rfloor>\<rfloor>"
    apply(rule StrictRefEq_set_L_subst2_bool[where \<tau> = \<tau>
        and P = "\<lambda>y \<tau>. \<lfloor>\<lfloor> \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> \<delta> (\<lambda>_. x)) \<rfloor>\<rfloor>"
        and y = "Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa))" ])
    apply(rule cp)
    apply(simp add: valid_def bot_fun_def bot_option_def)
     apply(rule StrictRefEq_set_sym)
     apply(rule EQ_comp_fun_commute.fold_insert[where f = F and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. x)", OF F_commute])
     apply(simp)
     apply(rule image_cong)
     apply(rule inject)
     apply(simp)
     apply(simp add: foundation20 all_defined1)
     apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<tau>)\<rceil>\<rceil>. \<tau> \<Turnstile> \<delta> (\<lambda>_. x)")
      apply(simp add: OclValid_def true_def)
     apply(rule fold_F[simplified all_defined_def all_defined_set_def, THEN conjunct2, THEN conjunct2])
     apply(simp_all)
   done
   apply_end(simp_all)
  qed
  apply_end(simp_all)
qed

lemma iterate_subst_set :
assumes S_all_def : "all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
    and A_all_def : "all_defined \<tau> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
    and F_commute : "EQ_comp_fun_commute F"
    and G_commute : "EQ_comp_fun_commute G"
    and F_cp : "\<And>x. cp (F (\<lambda>\<tau>. x))"
    and fold_F  : "\<And>x acc. \<tau> \<Turnstile> \<delta> x \<Longrightarrow> all_defined \<tau> acc \<Longrightarrow> all_defined \<tau> (F x acc)"
    and fold_G  : "\<And>x acc. \<tau> \<Turnstile> \<delta> x \<Longrightarrow> all_defined \<tau> acc \<Longrightarrow> all_defined \<tau> (G x acc)"
    and fold_eq : "\<And>x acc. \<tau> \<Turnstile> \<delta> x \<Longrightarrow> all_defined \<tau> acc \<Longrightarrow> \<tau> \<Turnstile> (F x acc \<doteq> G x acc)"
shows "\<tau> \<Turnstile> (S->iterate(x;acc=A|F x acc) \<doteq> S->iterate(x;acc=A|G x acc))"
proof -
 have S_finite : "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 by(simp add: S_all_def[simplified all_defined_def all_defined_set_def])

 have A_defined : "\<tau> \<Turnstile> \<delta> A"
 by(simp add: A_all_def[simplified all_defined_def])

 have image_cong : "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show ?thesis
  apply(subst OclValid_def)
  apply(simp only: cp_StrictRefEq_set[of "OclIterate\<^isub>S\<^isub>e\<^isub>t S A F"])
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(simp add: S_all_def[simplified all_defined_def all_defined_set_def OclValid_def]
                  A_all_def[simplified all_defined_def OclValid_def]
                  foundation20[OF A_defined, simplified OclValid_def]
             del: StrictRefEq_set_exec)
  apply(simp add: cp_StrictRefEq_set[symmetric]
             del: StrictRefEq_set_exec)
  apply(subst conjunct2[OF mp[OF finite_induct[where P = "\<lambda>set. all_defined_set \<tau> set \<longrightarrow>
                                               all_defined \<tau> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set)) \<and>
                                               all_defined \<tau> (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` set)) \<and>
                                               (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set) \<doteq> Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` set)) \<tau> = true \<tau>"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"]]])
   apply(simp add: S_finite)
   apply(insert A_all_def, simp add: all_defined_set_def all_defined_def foundation20)
   defer
   apply(insert S_all_def, simp add: all_defined_set_def all_defined_def foundation20)
   apply(simp)

  apply(simp del: StrictRefEq_set_exec)
  apply(rule impI)
  apply(drule mp, simp add: all_defined_set_def)
  apply(rule conjI, rule iterate_subst_set_rec[OF F_commute, OF fold_F], simp_all del: StrictRefEq_set_exec)
  apply(rule conjI, rule iterate_subst_set_rec[OF G_commute, OF fold_G], simp_all del: StrictRefEq_set_exec)

  (* *)
  apply(subgoal_tac "\<tau> \<Turnstile> (Finite_Set.fold F A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa)) \<doteq> Finite_Set.fold G A (insert (\<lambda>\<tau>. x) ((\<lambda>a \<tau>. a) ` Fa)))", simp add: OclValid_def)
  apply(rule_tac s = "F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa))" in StrictRefEq_set_trans)
  apply(rule EQ_comp_fun_commute.fold_insert[OF F_commute])
   apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(simp add: foundation20 all_defined1)
   (* *)
  apply(rule_tac s = "G (\<lambda>\<tau>. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))" in StrictRefEq_set_trans)
   prefer 2
  apply(rule StrictRefEq_set_sym)
  apply(rule EQ_comp_fun_commute.fold_insert[OF G_commute])
   apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
   apply(simp add: foundation20 all_defined1)
   (* *)
  proof -
   fix x Fa
   show "all_defined_set \<tau> (insert x Fa) \<Longrightarrow>
         all_defined \<tau> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<and>
         all_defined \<tau> (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa)) \<and>
         \<tau> \<Turnstile> (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) \<doteq> Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa)) \<Longrightarrow>
         \<tau> \<Turnstile> F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<doteq> G (\<lambda>\<tau>. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))"
    apply(rule StrictRefEq_set_trans[where s = "F (\<lambda>\<tau>. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))"])
    apply(rule StrictRefEq_set_L_subst1[where P = "F (\<lambda>\<tau>. x)"])
    apply(rule F_cp)
    apply(simp add: foundation20 all_defined1 del: StrictRefEq_set_exec)+
     (* *)
    apply(subgoal_tac "all_defined \<tau> (F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)))")
    apply(simp add: foundation20 all_defined1 del: StrictRefEq_set_exec)+
    apply(rule fold_F) apply(simp add: all_defined_set_def, simp)
     (* *)
    apply(subgoal_tac "all_defined \<tau> (F (\<lambda>\<tau>. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa)))")
    apply(simp add: foundation20 all_defined1 del: StrictRefEq_set_exec)+
    apply(rule fold_F) apply(simp add: all_defined_set_def, simp)

    apply(simp)

    apply(rule fold_eq)
    apply(simp add: all_defined_set_def, simp)
   done

   apply_end(simp_all add: OclValid_def del: StrictRefEq_set_exec)
  qed
qed

text{* Note that @{text iterate_subst_set} could be proved
 with a stronger assumption about commutation. *}
(* Historically, this stronger proof was defined before @{text iterate_subst_set}. 
Note: it does not use @{text all_defined}.
*)
lemma
assumes S_defined : "\<tau> \<Turnstile> \<delta> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
    and S_finite : "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
    and S_elt_valid : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (\<delta> (\<lambda>_. x)) \<tau> = (\<upsilon> (\<lambda>_. x)) \<tau>"
    and A_defined : "\<tau> \<Turnstile> \<delta> (A :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
    and A_finite : "finite \<lceil>\<lceil>Rep_Set_0 (A \<tau>)\<rceil>\<rceil>"
    and F_commute : "comp_fun_commute F"
    and F_cp : "\<And>x. cp (F (\<lambda>\<tau>. x))"
    and F_valid : "\<And>e x. \<upsilon> x = \<upsilon> F (\<lambda>\<tau>. e) x"
    and G_defined : "\<And>e x. \<delta> x = \<delta> G (\<lambda>\<tau>. e) x"
    and G_commute : "comp_fun_commute G"
    and fold_finite : "\<And>x acc. finite \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite \<lceil>\<lceil>Rep_Set_0 (G x acc \<tau>)\<rceil>\<rceil>"
    and fold_eq : "\<And>x acc. \<tau> \<Turnstile> \<delta> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> acc \<Longrightarrow> finite \<lceil>\<lceil>Rep_Set_0 (acc \<tau>)\<rceil>\<rceil> \<Longrightarrow> \<tau> \<Turnstile> (F x acc \<doteq> G x acc)"
shows "\<tau> \<Turnstile> (S->iterate(x;acc=A|F x acc) \<doteq> S->iterate(x;acc=A|G x acc))"
proof -
 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)
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

 show ?thesis
  apply(subst OclValid_def)
  apply(simp only: cp_StrictRefEq_set[of "OclIterate\<^isub>S\<^isub>e\<^isub>t S A F"])
  apply(simp only: OclIterate\<^isub>S\<^isub>e\<^isub>t_def)
  apply(case_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq_set_exec)
  apply(simp only: cp_StrictRefEq_set[symmetric])
  apply(erule conjE)+
  apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> \<delta> (\<lambda>_. x))")
  prefer 2
  apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> \<upsilon> (\<lambda>_. x))")
  prefer 2
  apply(rule ballI)
  apply(rule_tac Q = False in contrapos_np, simp)
  apply(rule_tac e = x and x = S in not_bot_in_set) apply(simp add: OclValid_def) apply(simp) apply(simp)
  apply(rule ballI)
  apply(drule_tac x = x in ballE) prefer 3 apply(assumption)
  apply(insert S_elt_valid)
  apply(drule_tac x = x in ballE) prefer 3 apply(assumption)
  apply(simp add: OclValid_def)
  apply(simp) apply(simp)

  apply(subst conjunct2[OF mp[ OF mp[OF finite_induct[where P = "\<lambda>set. finite set \<longrightarrow>
                                              (\<forall>x\<in>set. (\<tau> \<Turnstile> \<delta> (\<lambda>_. x))) \<longrightarrow>
                                              (\<tau> \<Turnstile> (\<delta> (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` set))) \<and>
                                               finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` set) \<tau>)\<rceil>\<rceil> \<and>
                                               (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` set) \<doteq> Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` set)) \<tau> = true \<tau>)"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"]]]])
   apply(simp)
   apply(simp del: StrictRefEq_set_exec)
   apply(simp add: cp_if_ocl[of "\<upsilon> A"]) apply(simp add: cp_if_ocl[symmetric])
   apply(simp add: A_defined A_finite)
   defer
   apply(simp)
   apply(simp)
   apply(simp del: StrictRefEq_set_exec)
   apply(rule conjI) apply(blast)
   apply(rule conjI) apply(blast)
   apply(simp add: OclValid_def S_finite)

   apply(insert A_defined[THEN foundation20] A_defined[simplified OclValid_def] S_defined[simplified OclValid_def])
   apply(simp add: OclValid_def del: StrictRefEq_set_exec)


  apply(simp del: StrictRefEq_set_exec)
  apply(rule impI, erule conjE, rule conjI)
  (* *)

  apply(subst comp_fun_commute.fold_insert[where f = G and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. x)", OF G_commute])
   apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
   apply(simp add: G_defined[symmetric])
  (* *)
  apply(rule conjI)
  apply(subst comp_fun_commute.fold_insert[where f = G and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. x)", OF G_commute])
   apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
   apply(simp add: fold_finite)
  (* *)
  apply(subst comp_fun_commute.fold_insert[where f = F and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. x)", OF F_commute])
   apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
   apply(simp add: fold_finite del: StrictRefEq_set_exec)
   (* *)
  apply(subst comp_fun_commute.fold_insert[where f = G and z = A and A = "((\<lambda>a \<tau>. a) ` Fa)" and x = "(\<lambda>\<tau>. x)", OF G_commute])
   apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)

  proof -
   fix x
   fix Fa
   show "\<tau> \<Turnstile> \<delta> Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<and>
         finite \<lceil>\<lceil>Rep_Set_0 (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa) \<tau>)\<rceil>\<rceil> \<and>
         (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa) \<doteq> Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa)) \<tau> = true \<tau> \<Longrightarrow>
         \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow>
         \<forall>x\<in>Fa. \<tau> \<Turnstile> \<delta> (\<lambda>_. x) \<Longrightarrow>
         (F (\<lambda>\<tau>. x) (Finite_Set.fold F A ((\<lambda>a \<tau>. a) ` Fa)) \<doteq> G (\<lambda>\<tau>. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))) \<tau> =
              true \<tau>"
    apply(rule StrictRefEq_set_trans[simplified OclValid_def, where s = "F (\<lambda>\<tau>. x) (Finite_Set.fold G A ((\<lambda>a \<tau>. a) ` Fa))"])
    apply(subst StrictRefEq_set_L_subst1_[simplified OclValid_def, where P = "F (\<lambda>\<tau>. x)"], simp_all del: StrictRefEq_set_exec)
    apply(rule F_cp)
    apply(rule F_valid)
    apply(rule fold_eq[simplified OclValid_def])
    apply(simp add: OclValid_def del: StrictRefEq_set_exec)+
   done
  qed
qed


lemma including_subst_set :
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

lemma including_id : "\<And>(S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) x.
                      all_defined \<tau> S \<Longrightarrow>
                      \<tau> \<Turnstile> \<upsilon> (\<lambda>\<tau>. x) \<Longrightarrow>
                      x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      \<tau> \<Turnstile> (S->including(\<lambda>\<tau>. x) \<doteq> S)"
proof -
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)

 have abs_rep_simp : "\<And>(S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0).
                      all_defined \<tau> S \<Longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
  apply(simp add: all_defined_def all_defined_set_def OclValid_def defined_def)
  apply(rule mp[OF Abs_Set_0_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau> then false \<tau> else true \<tau>) = true \<tau> \<and>
          finite \<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil> \<and>
          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. (if x = \<bottom> \<tau> \<or> x = null \<tau> then false \<tau> else true \<tau>) = true \<tau>) \<longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]])
  apply(simp add: Abs_Set_0_inverse discr_eq_false_true)
  apply(case_tac y, simp)
  apply(simp add: bot_fun_def bot_Set_0_def)
  apply(case_tac a, simp)
  apply(simp add: null_fun_def null_Set_0_def)
  apply(simp)
  apply(simp)
 done

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "\<And>S x.
                      all_defined \<tau> S \<Longrightarrow>
                      \<tau> \<Turnstile> \<upsilon> (\<lambda>\<tau>. x) \<Longrightarrow>
                      x \<in> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow>
                      ?thesis S x"
  apply(subst OclValid_def)
  apply(simp add: OclIncluding_def all_defined1 del: StrictRefEq_set_exec)

  apply(subst cp_StrictRefEq_set, simp add: insert_absorb del: StrictRefEq_set_exec)
  apply(subst StrictRefEq_set)
  apply(simp add: StrongEq_def discr_eq_invalid_true del: StrictRefEq_set_exec)

  apply(simp add: abs_rep_simp discr_eq_invalid_true all_defined1[simplified OclValid_def] del: StrictRefEq_set_exec)
  apply(simp add: cp_valid[symmetric] OclValid_def all_defined1[simplified OclValid_def] foundation20[simplified OclValid_def] true_def)
 done
 apply_end(simp_all)
qed

lemma iterate_including_id :
   assumes S_all_def : "all_defined \<tau> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0)"
   shows "all_defined \<tau> S \<Longrightarrow> \<tau> \<Turnstile> (S ->iterate(j;r2=S | r2->including(j)) \<doteq> S)"
proof -

 have rep_set_inj : "\<And>x y \<tau>. (\<delta> x) \<tau> = true \<tau> \<Longrightarrow>
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
  apply(case_tac "yb", simp_all)
  apply(case_tac "ab", simp_all)

  apply(simp add: Abs_Set_0_inverse)

  apply(blast)
 done

 have inject : "\<And> s1 s2. \<tau> \<Turnstile> \<delta> s1 \<Longrightarrow> \<tau> \<Turnstile> \<delta> s2 \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (s1 \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (s2 \<tau>)\<rceil>\<rceil> \<Longrightarrow> s1 \<tau> = s2 \<tau>"
  apply(rule_tac Q = "\<lceil>\<lceil>Rep_Set_0 (s1 \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (s2 \<tau>)\<rceil>\<rceil>" in contrapos_pp) prefer 2
  apply(rule rep_set_inj) apply(simp add: OclValid_def)+
 done

 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)
 have invert_set_0 : "\<And>x F. \<lfloor>\<lfloor>insert x F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<Longrightarrow> \<lfloor>\<lfloor>F\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
 by(auto simp: bot_option_def null_option_def)

 have invert_all_def_set : "\<And>x F. all_defined_set \<tau> (insert x F) \<Longrightarrow> all_defined_set \<tau> F"
  apply(simp add: all_defined_set_def)
 done

 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)

 have commute :  "EQ_comp_fun_commute (\<lambda>j r2. r2->including(j))" sorry
 have def_preserved : "\<And>acc xa. (\<tau> \<Turnstile> \<delta> xa) \<Longrightarrow> all_defined \<tau> acc \<Longrightarrow> all_defined \<tau> acc->including(xa)" sorry

 have cp : "\<And>x. cp (\<lambda>S. S->including(\<lambda>\<tau>. x))" sorry

 have image_cong: "\<And>x Fa f. inj f \<Longrightarrow> x \<notin> Fa \<Longrightarrow> f x \<notin> f ` Fa"
  apply(simp add: image_def)
  apply(rule ballI)
  apply(case_tac "x = xa", simp)
  apply(simp add: inj_on_def)
  apply(blast)
 done

 have inject : "inj (\<lambda>a \<tau>. a)" by(rule inj_fun, simp)
 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" by(simp add: all_defined_def)

 show "all_defined \<tau> S \<Longrightarrow> ?thesis"
  apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def OclValid_def del: StrictRefEq_set_exec)
  apply(subst cp_StrictRefEq_set)
  apply(subgoal_tac "(\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> S) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>", simp del: StrictRefEq_set_exec)
   prefer 2
   apply(simp add: all_defined_def all_defined_set_def OclValid_def foundation20[simplified OclValid_def])
  apply(simp add: cp_StrictRefEq_set[symmetric]
             del: StrictRefEq_set_exec)
  apply(case_tac "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = {}", simp)
  apply(simp add: all_defined_def foundation20)

  apply(subgoal_tac "\<And>s. \<lceil>\<lceil>Rep_Set_0 (s \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> all_defined \<tau> s \<Longrightarrow> \<tau> \<Turnstile> (Finite_Set.fold (\<lambda>j r2. r2->including(j)) s ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<doteq> s)")
  apply(simp add: OclValid_def del: StrictRefEq_set_exec)

  apply(subst finite_induct[where P = "\<lambda>set. all_defined_set \<tau> set \<and> \<lfloor>\<lfloor>set\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)} \<longrightarrow>
                                             (\<forall>s. all_defined \<tau> s \<longrightarrow> all_defined \<tau> (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set))) \<and>
                                             (\<forall>s. all_defined \<tau> s \<and>
                                               set \<subseteq> \<lceil>\<lceil>Rep_Set_0 (s \<tau>)\<rceil>\<rceil> \<longrightarrow>
                                               \<tau> \<Turnstile> (Finite_Set.fold (\<lambda>j r2. (r2->including(j))) s ((\<lambda>a \<tau>. a) ` set) \<doteq> s))"
                              and F = "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"])
  apply(simp)
  apply(simp add: all_defined_set_def all_defined_def)
  apply(simp add: foundation20[simplified OclValid_def] OclValid_def)
  defer
  apply(simp add: all_defined_def) apply(rule disjI2)+
  apply(simp add: all_defined_def all_defined_set_def)
   apply(rule ballI, erule conjE)
   apply(drule_tac x = x and Q = "x\<noteq>bot" in ballE)
   apply (metis (no_types) foundation17)
   apply(simp) apply(simp) apply(simp add: all_defined_set_def all_defined_def) apply(simp)
  apply(rule impI) apply(erule conjE)+
  apply(drule invert_set_0, simp del: StrictRefEq_set_exec)
  apply(frule invert_all_def_set, simp del: StrictRefEq_set_exec)
  apply(erule conjE)+

  (* *)
  apply(rule conjI)
  apply(rule allI, rename_tac SSS, rule impI)
  apply(rule iterate_subst_set_rec[OF commute])
  apply(rule def_preserved)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(drule invert_all_def_set, simp del: StrictRefEq_set_exec)
  (* *)
  apply(rule allI, rename_tac SS, rule impI)
  apply(erule conjE)+
  apply(rule_tac s = "Finite_Set.fold (\<lambda>j r2. r2->including(j)) SS ((\<lambda>a \<tau>. a) ` F)->including(\<lambda>\<tau>. x)" in StrictRefEq_set_trans)
  apply(rule EQ_comp_fun_commute.fold_insert[where f = "(\<lambda>j r2. r2->including(j))", OF commute])
  apply(simp)
   apply(rule image_cong)
   apply(rule inject)
   apply(simp)
  apply(simp add: foundation20 all_defined1)

  apply(subgoal_tac " \<tau> \<Turnstile> (\<upsilon> (\<lambda>\<tau>. x))")
   prefer 2
   apply(simp only: all_defined_def all_defined_set_def foundation20)
  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> SS)")
   prefer 2
   apply(simp add: all_defined_def)
  apply(rule_tac s = "SS->including(\<lambda>\<tau>. x)" in StrictRefEq_set_trans)
  apply(rule_tac P = "\<lambda>S. S->including(\<lambda>\<tau>. x)" in StrictRefEq_set_L_subst1)
  apply(rule cp)
  apply(simp add: foundation20 all_defined1)
  apply(simp add: foundation20 all_defined1)
  apply(rule foundation20)
  apply(subgoal_tac "\<And>v. v = Finite_Set.fold (\<lambda>j r2. r2->including(j)) SS ((\<lambda>a \<tau>. a) ` F) \<Longrightarrow> (\<tau> \<Turnstile> (\<delta> v->including(\<lambda>\<tau>. x)))", simp add: Let_def)
  apply(simp add: OclValid_def del: StrictRefEq_set_exec)
  apply(subst cp_ocl_and)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> Finite_Set.fold (\<lambda>j r2. r2->including(j)) SS ((\<lambda>a \<tau>. a) ` F) \<and> \<tau> \<Turnstile> (\<upsilon> (\<lambda>\<tau>. x))")
  apply (metis OclValid_def ocl_and_idem)
  apply(rule conjI)
  apply(simp add: all_defined1)
  apply(simp add: OclValid_def)
  apply(simp add: all_defined_def all_defined1 del: StrictRefEq_set_exec)
  apply (simp add: foundation10 foundation6)
  apply(simp)
  (* *)
  apply(rule including_id, simp_all)
 done
 apply_end(simp_all)
qed

lemma GogollasChallenge_on_sets:
      "\<tau> \<Turnstile> (Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j))) \<doteq> Set{\<zero>, \<six>, \<eight>, \<nine>})"
proof -

 have CP : "cp (\<lambda>a. a \<doteq> Set{\<zero>, \<six>, \<eight>, \<nine>})"
  apply(simp add: cp_def del: StrictRefEq_set_exec)
  apply(subst cp_StrictRefEq_set)
  apply(auto)
 done

 have def_including : "\<And> (S :: 'a state \<times> 'a state \<Rightarrow> int option option Set_0) a. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<delta> S->including(a)" sorry

 have all_defined_68 : "all_defined \<tau> Set{\<six>, \<eight>}" sorry
 have all_defined_9 : "all_defined \<tau> Set{\<nine>}" sorry

 have all_defined1 : "\<And>r2. all_defined \<tau> r2 \<Longrightarrow> \<tau> \<Turnstile> \<delta> r2" sorry

 have commute1: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(\<zero>)->including(j)->including(x)))" sorry
 have commute2: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(\<zero>)->including(x)->including(j)))" sorry
 have commute3: "\<And>i. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(x)->including(i))" sorry
 have commute4: "\<And>i. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(i)->including(x))" sorry
 have commute5: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(\<zero>)->including(j))->including(x))" sorry
 have commute6: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(j)->including(\<zero>))->including(x))" sorry
 have commute7: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(x)->including(\<zero>))" sorry
 have commute8: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(x))" sorry
 have commute9: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(j))->including(\<zero>)->including(x))" sorry
 have commute10: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(j)->including(\<zero>))->including(x))" sorry
 have commute11: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(x))" sorry
 have commute12: "EQ_comp_fun_commute (\<lambda>x acc. acc ->iterate(j;r2=acc | r2->including(j))->including(\<zero>)->including(x))" sorry
 have commute13: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(x)->including(\<zero>))" apply(simp add:EQ_comp_fun_commute_def del: StrictRefEq_set_exec) sorry
 have commute14: "EQ_comp_fun_commute (\<lambda>x acc. acc->including(\<zero>)->including(x))" apply(simp add:EQ_comp_fun_commute_def del: StrictRefEq_set_exec) sorry

 have cp1: "\<And>i. cp (\<lambda>acc. acc ->iterate(j;r2=acc | r2->including(\<zero>)->including(j)->including(\<lambda>\<tau>. i)))" sorry
 have cp2: "\<And>i j. cp (\<lambda>acc. acc->including(\<zero>)->including(\<lambda>\<tau>. j)->including(i))" sorry
 have cp3: "\<And>i. cp (\<lambda>acc. acc ->iterate(j;r2=acc | r2->including(\<zero>)->including(j))->including(\<lambda>\<tau>. i))" sorry
 have cp4: "\<And>i. cp (\<lambda>acc. acc ->iterate(j;r2=acc | r2->including(j)->including(\<zero>))->including(\<lambda>\<tau>. i))" sorry
 have cp5: "\<And>j. cp (\<lambda>acc. acc->including(\<lambda>\<tau>. j)->including(\<zero>))" sorry
 have cp6: "\<And>i. cp (\<lambda>acc. acc ->iterate(j;r2=acc | r2->including(j))->including(\<zero>)->including(\<lambda>\<tau>. i))" sorry
 have cp7: "\<And>i. cp (\<lambda>acc. acc->including(\<zero>)->including(\<lambda>\<tau>. i))" sorry
 have cp8: "\<And>i. cp (\<lambda>acc. acc->including(\<lambda>\<tau>. i)->including(\<zero>))" sorry

 have all_def_1 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> (r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(i)))" sorry
 have all_def_2 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> (r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(i)->including(j)))" sorry
 have all_def_3 : "\<And>i j r2. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> \<tau> \<Turnstile> \<delta> j \<Longrightarrow> all_defined \<tau> r2 \<Longrightarrow> all_defined \<tau> r2->including(\<zero>)->including(j)->including(i)" sorry
 have all_def_4 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(i)" sorry
 have all_def_5 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> (r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(i)))" sorry
 have all_def_6 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(i)" sorry
 have all_def_7 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(i)" sorry
 have all_def_8 : "\<And>j r2. \<tau> \<Turnstile> \<delta> j \<Longrightarrow> all_defined \<tau> r2 \<Longrightarrow> all_defined \<tau> r2->including(j)->including(\<zero>)" sorry
 have all_def_9 : "\<And>j r2. \<tau> \<Turnstile> \<delta> j \<Longrightarrow> all_defined \<tau> r2 \<Longrightarrow> all_defined \<tau> r2->including(\<zero>)->including(j)" sorry
 have all_def_10 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(i)" sorry
 have all_def_11 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(i)" sorry
 have all_def_12 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1->including(\<zero>)->including(i)" sorry
 have all_def_13 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(i)" sorry
 have all_def_14: "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1->including(i)->including(\<zero>)" sorry
 have all_def_15 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> all_defined \<tau> r1->including(\<zero>)->including(i)" sorry

 have all_incl1 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> \<tau> \<Turnstile> \<delta> (r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>)))" sorry
 have all_incl2 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> \<tau> \<Turnstile> \<delta> (r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)))" sorry
 have all_incl3 : "\<And>i r1. \<tau> \<Turnstile> \<delta> i \<Longrightarrow> all_defined \<tau> r1 \<Longrightarrow> \<tau> \<Turnstile> \<delta> (r1 ->iterate(j;r2=r1 | r2->including(j)))" sorry
 have all_incl4 : "\<tau> \<Turnstile> \<delta> (Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(i)))" sorry

 show ?thesis
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(i)->including(j)))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(i)))"])

  apply(rule iterate_subst_set) apply(simp add: all_defined_68 all_defined_9 commute1 commute2 cp1 all_def_1 all_def_2
                                            del: StrictRefEq_set_exec)+
  apply(rule iterate_subst_set) apply(simp add: commute3 commute4 cp2 all_def_3
                                            del: StrictRefEq_set_exec)+
  apply(rule including_swap[OF def_including]) apply(simp add: all_defined1) apply(simp only: foundation20)+
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j)->including(i)))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(i))"])
  apply(rule iterate_subst_set) apply(simp add: all_defined_68 all_defined_9 commute5 commute1 cp3 all_def_4 all_def_5
                                            del: StrictRefEq_set_exec)+

  apply(rule StrictRefEq_set_sym)
  apply(rule including_out2)
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(\<zero>)->including(j))->including(i))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(i))"])
  apply(rule iterate_subst_set) apply(simp add: all_defined_68 all_defined_9 commute6 commute5 cp4 all_def_6 all_def_7
                                            del: StrictRefEq_set_exec)+
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl2 foundation20 del: StrictRefEq_set_exec)+
  apply(rule iterate_subst_set) apply(simp add: commute8 commute7 cp5 all_def_8 all_def_9
                                            del: StrictRefEq_set_exec)+
  apply(rule including_swap) apply(simp add: all_defined1) apply(simp only: foundation20)+ apply(simp)
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(j)->including(\<zero>))->including(i))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(i))"])
  apply(rule iterate_subst_set)+ apply(simp add: all_defined_68 all_defined_9 commute9 commute10 cp6 all_def_10 all_def_11
                                            del: StrictRefEq_set_exec)+
  apply(rule StrictRefEq_set_sym)
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl3 foundation20 del: StrictRefEq_set_exec)+
  apply(rule including_out1)
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1 ->iterate(j;r2=r1 | r2->including(j))->including(\<zero>)->including(i))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(\<zero>)->including(i))"])
  apply(rule iterate_subst_set)+ apply(simp add: all_defined_68 all_defined_9 commute11 commute12 cp7 all_def_12 all_def_13
                                            del: StrictRefEq_set_exec)+
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl3 foundation20 all_defined1 del: StrictRefEq_set_exec)+
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl3 foundation20 all_defined1 del: StrictRefEq_set_exec)+
  apply(rule StrictRefEq_set_sym)
  apply(rule iterate_including_id) apply(simp del: StrictRefEq_set_exec)+
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(\<zero>)->including(i))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(i)->including(\<zero>))"])
  apply(rule iterate_subst_set)+ apply(simp add: all_defined_68 all_defined_9 commute13 commute14 cp8 all_def_14 all_def_15
                                            del: StrictRefEq_set_exec)+
  apply(rule including_swap) apply(simp add: all_defined1) apply(simp only: foundation20)+ apply(simp)
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(i)->including(\<zero>))"
                                               and x = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(i))->including(\<zero>)"])
  apply(rule StrictRefEq_set_sym)
  apply(rule including_out1)
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<six>, \<eight>} ->iterate(i;r1=Set{\<nine>} | r1->including(i))->including(\<zero>)"
                                               and x = "Set{\<six>, \<eight>} ->including(\<nine>)->including(\<zero>)"])
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl4 all_incl3 foundation20 all_defined1 del: StrictRefEq_set_exec)+
  apply(rule StrictRefEq_set_sym)
  apply(rule including_out0)
  (* *)
  apply(rule StrictRefEq_set_L_subst2[OF CP, where y = "Set{\<zero>, \<nine>, \<six>, \<eight>}"
                                               and x = "Set{\<zero>, \<six>, \<nine>, \<eight>}"])
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl4 all_incl3 foundation20 all_defined1 del: StrictRefEq_set_exec)+
  apply(rule including_swap) apply(simp del: StrictRefEq_set_exec)+
  (* *)
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl4 all_incl3 foundation20 all_defined1 del: StrictRefEq_set_exec)+
  (* *)
  apply(rule including_subst_set) apply(simp add: all_incl1 all_incl4 all_incl3 foundation20 all_defined1 del: StrictRefEq_set_exec)+
  (* *)
  apply(rule including_swap) apply(simp del: StrictRefEq_set_exec)+
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
