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

definition ten_nine ::"('\<AA>)Integer" ("\<one>\<zero>")
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
                  apply(simp_all add: Set_0_def bot_Set_0_def
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
                  apply(simp_all add: Set_0_def bot_Set_0_def
                                      null_option_def bot_option_def)
                  done
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Set  = "('\<AA>, '\<alpha> Set_0) val"

lemma Set_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> (X \<tau> = Abs_Set_0 \<lfloor>bot\<rfloor>)
                                     \<or> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot)"
apply(insert OCL_lib.Set_0.Rep_Set_0 [of "X \<tau>"], simp add:Set_0_def)
apply(auto simp: OclValid_def defined_def false_def true_def cp_def
                 bot_fun_def bot_Set_0_def null_Set_0_def null_fun_def
           split:split_if_asm)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = bot"])
apply(subst Abs_Set_0_inject[symmetric], simp add:Rep_Set_0)
apply(simp add: Set_0_def)
apply(simp add: Rep_Set_0_inverse bot_Set_0_def bot_option_def)
apply(erule contrapos_pp [of "Rep_Set_0 (X \<tau>) = null"])
apply(subst Abs_Set_0_inject[symmetric], simp add:Rep_Set_0)
apply(simp add: Set_0_def)
apply(simp add: Rep_Set_0_inverse  null_option_def)
done

lemma invalid_set_not_defined [simp,code_unfold]:"\<delta>(invalid::('\<AA>,'\<alpha>::null) Set) = false" by simp
lemma null_set_not_defined [simp,code_unfold]:"\<delta>(null::('\<AA>,'\<alpha>::null) Set) = false"
by(simp add: defined_def null_fun_def)
lemma invalid_set_valid [simp,code_unfold]:"\<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set) = false"
by simp
lemma null_set_valid [simp,code_unfold]:"\<upsilon>(null::('\<AA>,'\<alpha>::null) Set) = true"
apply(simp add: valid_def null_fun_def bot_fun_def bot_Set_0_def null_Set_0_def)
apply(subst Abs_Set_0_inject,simp_all add: Set_0_def null_option_def bot_option_def)
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
apply(simp_all add: Abs_Set_0_inject Set_0_def bot_option_def null_Set_0_def null_option_def)
done

lemma mtSet_valid[simp,code_unfold]:"\<upsilon>(Set{}) = true"
apply(rule ext,auto simp: mtSet_def valid_def null_Set_0_def
                          bot_Set_0_def bot_fun_def null_fun_def)
apply(simp_all add: Abs_Set_0_inject Set_0_def bot_option_def null_Set_0_def null_option_def)
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
                                 then if (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda> _. x) \<tau> = true \<tau>)
                                      then true \<tau>
                                      else if (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = true \<tau> \<or>
                                                                      P(\<lambda> _. x) \<tau> = false \<tau>)
                                           then false \<tau>
                                           else \<bottom>
                                 else \<bottom>)"
syntax
  "_OclForall" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forall'(_|_')")
translations
  "X->forall(x | P)" == "CONST OclForall X (%x. P)"

definition OclForall2     :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"
where     "OclForall2 S P = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau>
                                 then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = false \<tau>)
                                      then false \<tau>
                                      else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = \<bottom> \<tau>) 
                                           then \<bottom> \<tau>
                                           else if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = null \<tau>) 
                                                then null \<tau>
                                                else true \<tau>
                                 else \<bottom>)"
syntax
  "_OclForall2" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->forall2'(_|_')")
translations
  "X->forall2(x | P)" == "CONST OclForall2 X (%x. P)"


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

lemma cp_OclForall:
"(X->forall(x | P x)) \<tau> = ((\<lambda> _. X \<tau>)->forall(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclForall_def cp_defined[symmetric])

lemma cp_OclForall2:
"(X->forall2(x | P x)) \<tau> = ((\<lambda> _. X \<tau>)->forall2(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclForall2_def cp_defined[symmetric])

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
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(frule Set_inv_lemma)
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<delta>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->including(x)))"
          apply(frule C, simp)
          apply(auto simp: OclIncluding_def OclValid_def true_def false_def StrongEq_def
                           defined_def invalid_def valid_def bot_fun_def null_fun_def
                     split: bool.split_asm HOL.split_if_asm option.split)
          apply(simp_all add: null_Set_0_def bot_Set_0_def bot_option_def)
          apply(simp_all add: Abs_Set_0_inject A B bot_option_def[symmetric],
                simp_all add: bot_option_def)
          done
show ?thesis by(auto dest:D intro:E)
qed



lemma including_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->including(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(frule Set_inv_lemma)
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<upsilon>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->including(x)))"
          apply(frule C, simp)
          apply(auto simp: OclIncluding_def OclValid_def true_def false_def StrongEq_def
                           defined_def invalid_def valid_def bot_fun_def null_fun_def
                     split: bool.split_asm HOL.split_if_asm option.split)
          apply(simp_all add: null_Set_0_def bot_Set_0_def bot_option_def)
          apply(simp_all add: Abs_Set_0_inject A B bot_option_def[symmetric],
                simp_all add: bot_option_def)
          done
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
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>} \<rfloor>\<rfloor> \<in> Set_0"
          apply(frule Set_inv_lemma)
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<delta>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->excluding(x)))"
          apply(frule C, simp)
          apply(auto simp: OclExcluding_def OclValid_def true_def false_def StrongEq_def
                           defined_def invalid_def valid_def bot_fun_def null_fun_def
                     split: bool.split_asm HOL.split_if_asm option.split)
          apply(simp_all add: null_Set_0_def bot_Set_0_def bot_option_def)
          apply(simp_all add: Abs_Set_0_inject A B bot_option_def[symmetric],
                simp_all add: bot_option_def)
          done
show ?thesis by(auto dest:D intro:E)
qed


lemma excluding_valid_args_valid:
"(\<tau> \<Turnstile> \<upsilon>(X->excluding(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {x \<tau>} \<rfloor>\<rfloor> \<in> Set_0"
          apply(frule Set_inv_lemma)
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<upsilon>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->excluding(x)))"
          apply(frule C, simp)
          apply(auto simp: OclExcluding_def OclValid_def true_def false_def StrongEq_def
                           defined_def invalid_def valid_def bot_fun_def null_fun_def
                     split: bool.split_asm HOL.split_if_asm option.split)
          apply(simp_all add: null_Set_0_def bot_Set_0_def bot_option_def)
          apply(simp_all add: Abs_Set_0_inject A B bot_option_def[symmetric],
                simp_all add: bot_option_def)
          done
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
apply(auto simp: mtSet_def OCL_lib.Set_0.Abs_Set_0_inverse Set_0_def)
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
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 show ?thesis
   apply(insert def_X[THEN foundation17] val_x[THEN foundation19])
   apply(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def false_def true_def
                    invalid_def defined_def valid_def
                    bot_Set_0_def null_fun_def null_Set_0_def bot_option_def)
   apply(simp_all add: Abs_Set_0_inject A B C bot_option_def[symmetric],
         simp_all add: bot_option_def Abs_Set_0_inverse C)
   done
qed



lemma including_charn2:
assumes def_X:"\<tau> \<Turnstile> (\<delta> X)"
and     val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
and     val_y:"\<tau> \<Turnstile> (\<upsilon> y)"
and     neq  :"\<tau> \<Turnstile> not(x \<triangleq> y)"
shows         "\<tau> \<Turnstile> (X->including(x)->includes(y)) \<triangleq> (X->includes(y))"
proof -
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 have D : "y \<tau> \<noteq> x \<tau>"
          apply(insert neq)
          by(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def
                        false_def true_def defined_def valid_def bot_Set_0_def
                        null_fun_def null_Set_0_def StrongEq_def not_def)
 show ?thesis
  apply(insert def_X[THEN foundation17] val_x[THEN foundation19])
  apply(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def false_def true_def
                   invalid_def defined_def valid_def bot_Set_0_def null_fun_def null_Set_0_def
                   StrongEq_def)
  apply(simp_all add: Abs_Set_0_inject Abs_Set_0_inverse A B C D)
  apply(simp_all add: Abs_Set_0_inject A B C bot_option_def[symmetric],
        simp_all add: bot_option_def Abs_Set_0_inverse C)
  done
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
  have A : "\<lfloor>None\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
  have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
  show ?thesis using val_x
    apply(auto simp: OclValid_def OclIncludes_def not_def false_def true_def StrongEq_def
                     OclExcluding_def mtSet_def defined_def bot_fun_def null_fun_def null_Set_0_def)
    apply(auto simp: mtSet_def Set_0_def  OCL_lib.Set_0.Abs_Set_0_inverse
                     OCL_lib.Set_0.Abs_Set_0_inject[OF B, OF A])
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
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 have D: "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<in> Set_0"
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def invalid_def)
          done
 have E : "x \<tau> \<noteq> y \<tau>"
          apply(insert neq)
          by(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def
                        false_def true_def defined_def valid_def bot_Set_0_def
                        null_fun_def null_Set_0_def StrongEq_def not_def)
 have G : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def  )
          by(simp_all add: Abs_Set_0_inject A B C bot_option_def[symmetric],
             simp_all add: bot_option_def)
 have H : "(\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
          apply(auto simp: OclValid_def false_def true_def defined_def
                           bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def  )
          by(simp_all add: Abs_Set_0_inject A B D bot_option_def[symmetric],
             simp_all add: bot_option_def)
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
 have A : "\<bottom> \<in> Set_0" by(simp add: Set_0_def bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)
 have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0 "
          apply(insert def_X[THEN foundation17] val_x[THEN foundation19] Set_inv_lemma[OF def_X])
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def invalid_def)
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
   apply(simp_all add: Abs_Set_0_inject A B C bot_option_def[symmetric],
         simp_all add: bot_option_def Abs_Set_0_inverse C)
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

 have defined_inject_true : "\<And>xa P. (\<delta> P) xa \<noteq> true xa \<Longrightarrow> (\<delta> P) xa = false xa"
  apply(simp add: defined_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P xa = \<bottom> \<or> P xa = null", simp_all add: true_def)

 have valid_inject_true : "\<And>xa P. (\<upsilon> P) xa \<noteq> true xa \<Longrightarrow> (\<upsilon> P) xa = false xa"
  apply(simp add: valid_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P xa = \<bottom>", simp_all add: true_def)

 have valid_inject_defined : "\<And>xa P. (\<upsilon> P) xa \<noteq> true xa \<Longrightarrow> (\<delta> P) xa = false xa"
  apply(simp add: valid_def defined_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P xa = \<bottom>", simp_all add: true_def)

 have null_simp : "\<And>xa y. (\<upsilon> y) xa = true xa \<Longrightarrow> (\<delta> y) xa = false xa \<Longrightarrow> y xa = null xa"
  apply(simp add: valid_def defined_def)
  apply(split split_if_asm, simp add: false_def true_def)+
  apply(simp add: false_def true_def)
 done

 have bot_in_set_0 : "\<lfloor>\<bottom>\<rfloor> \<in> Set_0" by(simp add: Set_0_def null_option_def bot_option_def)

 have forall_exec_true : "\<And>xa x y. (\<delta> x) xa = true xa \<Longrightarrow>
                          (\<delta> y) xa = true xa \<Longrightarrow>
                     (OclForall x (OclIncludes y) xa = true xa) = (\<lceil>\<lceil>Rep_Set_0 (x xa)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y xa)\<rceil>\<rceil>)"

  apply(subst OclForall_def, simp)
  apply(rule conjI) apply(rule impI)+
  apply(rule conjI, rule impI)
  apply(simp add: OclIncludes_def)
  apply(rule subsetI)
  apply(drule bspec)
  apply(assumption)
  apply(split split_if_asm)
  apply(drule_tac f = "\<lambda>x. \<lceil>\<lceil>x\<rceil>\<rceil>" in arg_cong)+
  apply(simp add: true_def)
  apply(simp add: bot_option_def true_def)

  apply(rule impI)
  apply(simp add: true_def false_def)
  apply(rule notI)
  apply(drule_tac Q = False in bexE) prefer 2 apply(assumption)
  apply(drule_tac Q = False and x = xb in ballE) prefer 3 apply(assumption) prefer 2 apply(simp)
  apply(drule_tac R = False in disjE) apply(simp) prefer 2 apply(simp)
  apply(drule_tac c = xb in subsetD)
  apply(simp)
  apply(simp add: OclIncludes_def true_def)
  apply(split split_if_asm, simp)
  apply(simp add: bot_option_def)

  apply(rule impI, rule conjI)
  apply(blast)


  apply(simp add: bot_option_def true_def false_def, rule impI)

  apply(rule notI)
  apply(frule_tac Q = False in bexE) prefer 2 apply(assumption)
  apply(drule_tac c = xb in subsetD)
  apply(simp)
  apply(simp add: OclIncludes_def true_def)
  apply(case_tac "(\<upsilon> (\<lambda>_. xb)) xa = \<lfloor>\<lfloor>True\<rfloor>\<rfloor>", simp)
  apply(simp add: valid_def)
  apply(frule Set_inv_lemma[simplified OclValid_def true_def])
  apply(erule disjE)
  apply(simp)
  apply(simp add: Abs_Set_0_inverse[OF bot_in_set_0])
  apply(split split_if_asm)
  apply(simp add: cp_defined[of x])
  apply(simp add: defined_def bot_option_def null_fun_def null_Set_0_def false_def)

  apply(simp add: bot_fun_def false_def true_def)
 done

 have forall_exec_false : "\<And>xa x y. (\<delta> x) xa = true xa \<Longrightarrow>
                          (\<delta> y) xa = true xa \<Longrightarrow>
                     (OclForall x (OclIncludes y) xa = false xa) = (\<not> \<lceil>\<lceil>Rep_Set_0 (x xa)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y xa)\<rceil>\<rceil>)"

  apply(subgoal_tac "\<not> (OclForall x (OclIncludes y) xa = false xa) = (\<not> (\<not> \<lceil>\<lceil>Rep_Set_0 (x xa)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y xa)\<rceil>\<rceil>))")
  apply(simp)
  apply(subst forall_exec_true[symmetric]) apply(simp)+
  apply(simp add: OclForall_def false_def true_def bot_option_def)
  apply(rule impI)

  apply(frule Set_inv_lemma[simplified OclValid_def true_def])
  apply(erule disjE)
  apply(simp)
  apply(simp add: Abs_Set_0_inverse[OF bot_in_set_0])
  apply(rule ballI)
  apply(simp add: defined_def bot_option_def null_fun_def null_Set_0_def false_def)

  apply(drule_tac Q = False in bexE)
  apply(drule_tac Q = False and x = xb in ballE)
  apply(simp add: OclIncludes_def valid_def bot_fun_def true_def)
  apply(simp)+
 done

 have strongeq_true : "\<And> xa x y. (\<lfloor>\<lfloor>x xa = y xa\<rfloor>\<rfloor> = true xa) = (x xa = y xa)"
 by(simp add: foundation22[simplified OclValid_def StrongEq_def] )

 have strongeq_false : "\<And> xa x y. (\<lfloor>\<lfloor>x xa = y xa\<rfloor>\<rfloor> = false xa) = (x xa \<noteq> y xa)"
  apply(case_tac "x xa \<noteq> y xa", simp add: false_def)
  apply(simp add: false_def true_def)
 done

 have rep_set_inj : "\<And>xa. (\<delta> x) xa = true xa \<Longrightarrow>
                         (\<delta> y) xa = true xa \<Longrightarrow>
                          x xa \<noteq> y xa \<Longrightarrow>
                          \<lceil>\<lceil>Rep_Set_0 (y xa)\<rceil>\<rceil> \<noteq> \<lceil>\<lceil>Rep_Set_0 (x xa)\<rceil>\<rceil>"
  apply(simp add: defined_def)
  apply(split split_if_asm, simp add: false_def true_def)+
  apply(simp add: null_fun_def null_Set_0_def bot_fun_def bot_Set_0_def)

  apply(case_tac "x xa")
  apply(case_tac "ya", simp_all)
  apply(case_tac "a", simp_all)

  apply(case_tac "y xa")
  apply(case_tac "yaa", simp_all)
  apply(case_tac "ab", simp_all)

  apply(simp add: Abs_Set_0_inverse)

  apply(blast)
 done

 show ?thesis
  apply(rule ext)

  apply(simp add: cp_if_ocl[of "\<delta> x"])
  apply(case_tac "(\<upsilon> x) xa \<noteq> true xa")
  apply(simp add: valid_inject_defined[of "x"])
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_if_ocl[of "\<upsilon> x"])
  apply(subst valid_inject_true[of "x"])
  apply(simp)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: valid_def)
  apply(case_tac "x xa = \<bottom> xa")
  apply(simp add: valid_def)
  apply(simp add: cp_StrictRefEq_set[of "x"])
  apply(simp add: cp_StrictRefEq_set[symmetric])
  apply(simp add: invalid_def)
  apply(simp add: fun_cong[OF StrictRefEq_set_strict2[simplified invalid_def, of y]] bot_fun_def)
  apply(simp)

  apply(case_tac "(\<delta> x) xa \<noteq> true xa")

  apply(subgoal_tac "(\<delta> x) xa = false xa")
   prefer 2
   apply(rule defined_inject_true)
   apply(simp)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_if_ocl[of "\<upsilon> x"])
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: StrictRefEq_set)
  apply(simp add: cp_if_ocl[of "\<upsilon> y"])
  apply(case_tac "(\<upsilon> y) xa \<noteq> true xa")
  apply(simp add: valid_inject_true)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_not[of "\<delta> y"])
  apply(case_tac "(\<delta> y) xa = true xa")
  apply(simp add: cp_not[symmetric])
  apply(simp add: valid_def defined_def false_def true_def bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)
  apply(split split_if_asm, simp add: false_def true_def bot_fun_def bot_option_def null_fun_def null_option_def )+
  apply(subgoal_tac "y xa \<noteq> null")
  apply(simp)+
  apply(simp add: defined_inject_true)
  apply(simp add: cp_not[symmetric])
  apply(drule defined_inject_true)
  apply(simp add: null_simp[of x] null_simp[of y] StrongEq_def true_def)

  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_if_ocl[of "\<delta> y"])
  apply(case_tac "(\<upsilon> y) xa \<noteq> true xa")
  apply(frule valid_inject_true)
  apply(simp add: valid_inject_defined)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_if_ocl[of "\<upsilon> y"])
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: StrictRefEq_set)

  apply(case_tac "(\<delta> y) xa \<noteq> true xa")
  apply(drule defined_inject_true, simp)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: cp_if_ocl[of "\<upsilon> y"])
  apply(simp add: cp_if_ocl[symmetric])


  apply(simp add: null_simp[of y] StrictRefEq_set StrongEq_def false_def)
  apply(simp add: valid_def[of x] defined_def[of x])
  apply(split split_if_asm, simp add: false_def true_def)+
  apply(blast)

  apply(simp)
  apply(simp add: cp_if_ocl[symmetric])
  apply(simp add: StrictRefEq_set StrongEq_def)

  (* ************************* *)
  apply(subgoal_tac "\<lfloor>\<lfloor>x xa = y xa\<rfloor>\<rfloor> = true xa \<or> \<lfloor>\<lfloor>x xa = y xa\<rfloor>\<rfloor> = false xa")
   prefer 2
   apply(case_tac "x xa = y xa")
   apply(rule disjI1, simp add: true_def)
   apply(rule disjI2, simp add: false_def)
  (* *)
  apply(erule disjE)
  apply(simp add: strongeq_true)

  apply(subgoal_tac "OclForall x (OclIncludes y) xa = true xa \<and> OclForall y (OclIncludes x) xa = true xa")
  apply(simp add: cp_ocl_and true_def)
  apply(simp add: forall_exec_true)

  (* *)
  apply(simp add: strongeq_false)

  apply(subgoal_tac "OclForall x (OclIncludes y) xa = false xa \<or> OclForall y (OclIncludes x) xa = false xa")
  apply(simp add: cp_ocl_and[of "OclForall x (OclIncludes y)"] false_def)
  apply(erule disjE)
   apply(simp)
   apply(subst cp_ocl_and[symmetric])
   apply(simp only: ocl_and_false1[simplified false_def])

   apply(simp)
   apply(subst cp_ocl_and[symmetric])
   apply(simp only: ocl_and_false2[simplified false_def])

  apply(simp add: forall_exec_false rep_set_inj)
 done
qed



lemma forall_set_null_exec[simp,code_unfold] :
"(null->forall(z| P(z))) = invalid"
by(simp add: OclForall_def invalid_def false_def true_def)

lemma forall_set_mt_exec[simp,code_unfold] :
"((Set{})->forall(z| P(z))) = true"
apply(simp add: OclForall_def, simp add: mtSet_def)
apply(subst Abs_Set_0_inverse)
apply(simp_all add: Set_0_def true_def)
done

lemma exists_set_null_exec[simp,code_unfold] :
"(null->exists(z | P(z))) = invalid"
by(simp add: OclExists_def)

lemma exists_set_mt_exec[simp,code_unfold] :
"((Set{})->exists(z | P(z))) = false"
by(simp add: OclExists_def)

lemma forall_set_including_exec[simp,code_unfold] :
 assumes cp: "\<And>\<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
 shows "((S->including(x))->forall(z | P(z))) = (if \<upsilon> x and \<delta> (P x) and \<upsilon> (S->forall(z | P(z)))
                                                 then P x and (S->forall(z | P(z)))
                                                 else invalid
                                                 endif)"
proof -

 have defined_inject_true : "\<And>xa P. (\<delta> P) xa \<noteq> true xa \<Longrightarrow> (\<delta> P) xa = false xa"
  apply(simp add: defined_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P xa = \<bottom> \<or> P xa = null", simp_all add: true_def)

 have valid_inject_true : "\<And>xa P. (\<upsilon> P) xa \<noteq> true xa \<Longrightarrow> (\<upsilon> P) xa = false xa"
  apply(simp add: valid_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P xa = \<bottom>", simp_all add: true_def)

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
  apply(frule Set_inv_lemma)
  apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                  foundation18 foundation16 invalid_def)
 done

 have d_and_v_destruct_defined : "\<And>S x xa. (\<delta> S and \<upsilon> x) xa = true xa \<Longrightarrow> xa \<Turnstile> \<delta> S"
  apply(rule foundation5[THEN conjunct1])
  apply(simp add: OclValid_def)
 done

 have d_and_v_destruct_valid  :"\<And>S x xa. (\<delta> S and \<upsilon> x) xa = true xa \<Longrightarrow> xa \<Turnstile> \<upsilon> x"
  apply(rule foundation5[THEN conjunct2])
  apply(simp add: OclValid_def)
 done

 have forall_including_invert : "\<And> f xa. (f x xa = f (\<lambda> _. x xa) xa) \<Longrightarrow>
                                          (\<delta> S and \<upsilon> x) xa = true xa \<Longrightarrow>
                                          (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. f (\<lambda>_. x) xa) =
                                          (f x xa \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S xa)\<rceil>\<rceil>. f (\<lambda>_. x) xa))"
  apply(simp add: OclIncluding_def)
  apply(subst Abs_Set_0_inverse)
  apply(rule insert_in_Set_0)
  apply(rule d_and_v_destruct_defined, assumption)
  apply(rule d_and_v_destruct_valid, assumption)
  apply(simp add: d_and_v_destruct_defined d_and_v_destruct_valid)
  apply(frule d_and_v_destruct_defined, drule d_and_v_destruct_valid)
  apply(simp add: OclValid_def)
 done

 have exists_including_invert : "\<And> f xa. (f x xa = f (\<lambda> _. x xa) xa) \<Longrightarrow>
                                          (\<delta> S and \<upsilon> x) xa = true xa \<Longrightarrow>
                                          (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. f (\<lambda>_. x) xa) =
                                          (f x xa \<or> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S xa)\<rceil>\<rceil>. f (\<lambda>_. x) xa))"
  apply(subst arg_cong[where f = "\<lambda>x. \<not>x",
                       OF forall_including_invert[where f = "\<lambda>x xa. \<not> (f x xa)"],
                       simplified])
 by simp_all

 have cp_true : "\<And>xa. (P x xa = true xa) = (P (\<lambda>_. x xa) xa = true xa)"
 by(subst cp, simp)

 have cp_not_true : "\<And>xa. (P x xa \<noteq> true xa) = (P (\<lambda>_. x xa) xa \<noteq> true xa)"
 by(subst cp, simp)

 have cp_true_or_false : "\<And>xa. (P x xa = true xa \<or> P x xa = false xa) = (P (\<lambda>_. x xa) xa = true xa \<or> P (\<lambda>_. x xa) xa = false xa)"
  apply(subst cp)
  apply(subst disj_commute)
  apply(subst cp)
  apply(subst disj_commute)
 by(simp)

 have cp_not_true_and_not_false : "\<And>xa. (P x xa \<noteq> true xa \<and> P x xa \<noteq> false xa) = (P (\<lambda>_. x xa) xa \<noteq> true xa \<and> P (\<lambda>_. x xa) xa \<noteq> false xa)"
  apply(subst cp)
  apply(subst conj_commute)
  apply(subst cp)
  apply(subst conj_commute)
 by(simp)

 have recurse_to_false : "\<And>xa.
   (\<delta> S and \<upsilon> x) xa = true xa \<Longrightarrow>
   \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa \<noteq> true xa \<Longrightarrow>
   \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa = true xa \<or> P (\<lambda>_. x) xa = false xa \<Longrightarrow>
   false xa = (P x and OclForall S P) xa"
  apply(frule exists_including_invert[where f = "\<lambda>g xa. P g xa \<noteq> true xa", OF cp_not_true], simp)
  apply(frule forall_including_invert[where f = "\<lambda>g xa. P g xa = true xa \<or> P g xa = false xa", OF cp_true_or_false], simp)
  apply(erule conjE)
  apply(drule disjE)
  prefer 3
  apply(assumption)
  defer
  apply(simp only: cp_ocl_and[of "P x"])
  apply(simp add: cp_ocl_and[of "false", THEN sym])

  apply(drule mp, simp)
  apply(simp only: cp_ocl_and[of "P x"])
  apply(simp add: OclForall_def d_and_v_destruct_defined[simplified OclValid_def])
  apply(simp add: cp_ocl_and[of "true", THEN sym])
 by (simp add: false_def true_def)

 have foundation6': "\<And>\<tau> P. \<tau> \<Turnstile> P \<Longrightarrow> (\<tau> \<Turnstile> \<delta> P) \<and> (\<tau> \<Turnstile> P)"
  apply(rule conjI)
  apply(simp add: foundation6)
 by simp

 have foundation10': "\<And>\<tau> x y. (\<tau> \<Turnstile> x) \<and> (\<tau> \<Turnstile> y) \<Longrightarrow> \<tau> \<Turnstile> (x and y)"
  apply(erule conjE)
  apply(subst foundation10)
  apply(rule foundation6, simp)
  apply(rule foundation6, simp)
 by simp

 have recurse_to_true : "\<And>xa. (\<delta> S and \<upsilon> x) xa = true xa \<Longrightarrow>
   \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa = true xa \<Longrightarrow>
   true xa = (P x and OclForall S P) xa"
  apply(frule forall_including_invert[where f = "\<lambda>g xa. P g xa = true xa", OF cp_true], simp)
  apply(rule foundation10'[simplified OclValid_def, THEN sym], simp add: OclForall_def)
  apply(rule impI, drule defined_inject_true)
  apply(simp add: d_and_v_destruct_defined[simplified OclValid_def] false_def true_def)
 done

 have contradict_Rep_Set_0: "\<And>xa S f.
         \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. f (\<lambda>_. x) xa \<Longrightarrow>
         \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>. \<not> (f (\<lambda>_. x) xa) \<Longrightarrow>
         False"
  apply(drule bexE[where Q = False])
  apply(drule bspec)
  apply(assumption)
 by(simp)

 have recurse_to_absurde : "\<And>xa.
         (\<upsilon> OclForall S P) xa = true xa \<Longrightarrow>
         \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa \<noteq> true xa \<and> P (\<lambda>_. x) xa \<noteq> false xa \<Longrightarrow>
         False"
  apply(simp add: cp_valid[of "OclForall S P"])
  apply(simp add: OclForall_def)
  apply(case_tac "(\<delta> S) xa = true xa", simp)
  apply(case_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa = true xa")
  apply(split split_if_asm, simp)
  apply(drule bexE) apply(simp)+
  apply(split split_if_asm)
  apply(drule contradict_Rep_Set_0) apply(simp)+
  apply(simp add: valid_def true_def bot_option_def bot_fun_def false_def)

  apply(drule defined_inject_true, simp)
  apply(simp add: valid_def true_def bot_option_def bot_fun_def false_def)
 done

 have invert_3and : "\<And>xa. ((\<upsilon> x and \<delta> P x) and \<upsilon> OclForall S P) xa \<noteq> true xa \<Longrightarrow>
                           ((\<upsilon> x) xa = false xa) \<or>
                            ((\<delta> P x) xa = false xa) \<or>
                            ((\<upsilon> OclForall S P) xa = false xa)"
  apply(simp add: ocl_and_def)
  apply(case_tac "(\<upsilon> x) xa = true xa", simp add: true_def)
  apply(case_tac "(\<delta> P x) xa = true xa", simp add: true_def)
  apply(case_tac "(\<upsilon> OclForall S P) xa = true xa", simp add: true_def)
  apply(simp add: valid_inject_true false_def)
  apply(drule valid_inject_true, simp add: false_def)
  apply(drule defined_inject_true, simp add: false_def)
  apply(drule valid_inject_true, simp add: false_def)
 done

 have "\<And>\<tau>. (\<delta> P x) \<tau> = false \<tau>" sorry
 have "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> P x) \<triangleq> false " sorry

 have "\<And>\<tau>. \<not> \<tau> \<Turnstile> (\<delta> P x)" sorry  (* are all equivalent !!! *)

 have case_not_defined : "\<And>xa. (\<delta> P x) xa = false xa \<Longrightarrow>
                                (P x xa = true xa \<or> P x xa = false xa) \<Longrightarrow>
                                False"
  apply(simp add: defined_def bot_option_def null_option_def bot_fun_def null_fun_def true_def false_def)
  apply(split split_if_asm)
  apply(simp add: defined_def bot_option_def null_option_def bot_fun_def null_fun_def true_def false_def)
  apply(erule disjE)+ apply(simp_all)
  apply(simp add: true_def false_def)
 done

 show ?thesis

  apply(rule ext)
  apply(simp add: if_ocl_def)
  apply(simp add: cp_defined[of "\<upsilon> x and \<delta> P x and \<upsilon> OclForall S P"])
  apply(simp add: cp_defined[THEN sym])
  apply(rule conjI, rule impI)
  apply(drule foundation5[simplified OclValid_def], erule conjE)+
  apply(subgoal_tac "(\<delta> S) xa = true xa")

  apply(simp only: cp_ocl_and[of "P x"])

  apply(subst OclForall_def)
  apply(simp only: cp_ocl_and[THEN sym])

  apply(simp)
  apply(subgoal_tac "(\<delta> S and \<upsilon> x) xa = true xa", simp)
  apply(case_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa = true xa", simp)
  apply(rule recurse_to_true) apply(simp)+


  apply(case_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>. P (\<lambda>_. x) xa = true xa \<or> P (\<lambda>_. x) xa = false xa") apply(simp)

  apply(rule conjI, rule impI, simp)
  apply(rule conjI)
  apply(rule recurse_to_false) apply(simp)+

  apply(rule impI, rule conjI, rule impI, simp)

  apply(drule contradict_Rep_Set_0) apply(simp)+
  apply(rule conjI, rule impI)
  apply(drule contradict_Rep_Set_0) apply(simp)+
  apply(rule conjI, rule impI)
  apply(drule contradict_Rep_Set_0) apply(simp)+

  apply(drule bexE) apply(assumption)
  apply(drule exists_including_invert[where f = "\<lambda>g xa. P g xa \<noteq> true xa \<and> P g xa \<noteq> false xa", OF cp_not_true_and_not_false], simp)
  apply(simp add: cp_ocl_and[of "P x"])
  apply(erule disjE)
  apply(simp only: def_split_local[simplified OclValid_def, of "P x" ])
  apply(subgoal_tac "P x xa = invalid xa \<or> P x xa = null xa \<or> P x xa = true xa \<or> P x xa = false xa ")
  apply(erule conjE)
  apply(simp add: true_def false_def bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def invalid_def null_def)
  apply(rule bool_split)

  apply(drule recurse_to_absurde) apply(simp)+

  apply(subst conjI[THEN foundation10'[simplified OclValid_def], of "\<delta> S" xa "\<upsilon> x"]) apply(simp) apply(simp) apply(simp)

  apply(simp add: cp_valid[of "OclForall S P"])
  apply(simp add: OclForall_def)

  apply(case_tac "(\<delta> S) xa = true xa", simp)
  apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def null_fun_def null_option_def)
  apply(rule impI, drule invert_3and)
  apply(erule disjE)
  apply(subst OclForall_def)
  apply(case_tac "(\<delta> (S->including(x))) xa = true xa")
  apply(simp)

  apply(simp add: cp_ocl_and[of "\<delta> S" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[THEN sym])
  apply(simp add: false_def true_def)
  apply(simp)

  apply(simp add: invalid_def)
  apply(erule disjE)

  apply(subst OclForall_def)

  apply(case_tac "(\<delta> (S->including(x))) xa = true xa", simp)
  apply(case_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) xa)\<rceil>\<rceil>.
                P (\<lambda>_. x) xa = true xa \<or> P (\<lambda>_. x) xa = false xa)", simp)
  apply(frule forall_including_invert[where f = "\<lambda>g xa. P g xa = true xa \<or> P g xa = false xa", OF cp_true_or_false], simp)
  apply(drule case_not_defined)
  apply(simp)+

  apply(simp add: invalid_def)
  apply(rule conjI, rule impI)
  apply(drule contradict_Rep_Set_0) apply(simp)+
  apply(rule impI)

  apply(frule exists_including_invert[where f = "\<lambda>g xa. P g xa = true xa \<or> P g xa = false xa", OF cp_true_or_false], simp)

  apply(simp add: invalid_def)

  apply(simp add: cp_valid[of "OclForall S P"])
  apply(simp add: OclForall_def[of S])

  apply(case_tac "(\<delta> S) xa = true xa", simp)
  apply(case_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S xa)\<rceil>\<rceil>.
                P (\<lambda>_. x) xa = true xa)", simp)
  apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def null_fun_def null_option_def)
  apply(split split_if_asm, simp)
  apply(case_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (S xa)\<rceil>\<rceil>.
                P (\<lambda>_. x) xa = true xa \<or> P (\<lambda>_. x) xa = false xa)", simp)
  apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def null_fun_def null_option_def)
  apply(split split_if_asm, simp)
  apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def null_fun_def null_option_def)

  apply(subst OclForall_def)
  apply(case_tac "(\<upsilon> x) xa = true xa")
  apply(subgoal_tac "(\<delta> S and \<upsilon> x) xa = true xa")
  apply(simp)

  apply(rule conjI,rule impI)
  apply(frule forall_including_invert[where f = "\<lambda>g xa. P g xa = true xa \<or> P g xa = false xa", OF cp_true_or_false], simp)

  apply(drule contradict_Rep_Set_0)
  apply(erule conjE)
  apply(simp add: false_def true_def)
  apply(drule contradict_Rep_Set_0) apply(simp)+

  apply(rule impI, rule conjI, rule impI)
  apply(frule forall_including_invert[where f = "\<lambda>g xa. P g xa = true xa", OF cp_true], simp)
  apply(simp add: invalid_def)
  apply(rule foundation10'[simplified OclValid_def])
  apply(simp add: true_def)

  apply(drule valid_inject_true)

  apply(case_tac "(\<delta> (S->including(x))) xa = true xa", simp)
  apply(simp only: cp_ocl_and[of "\<delta> S"])
  apply(simp add: false_def true_def ocl_and_def)
  apply(simp add: invalid_def)

  apply(simp add: valid_inject_true valid_def)
  apply(drule defined_inject_true)
  apply(simp add: OclForall_def invalid_def)
  apply(subgoal_tac "(\<delta> S and \<upsilon> x) xa = false xa")
  apply(simp add: true_def false_def bot_option_def bot_fun_def null_option_def null_fun_def)

  apply(simp only: cp_ocl_and[of "\<delta> S"])
  apply(simp add: cp_ocl_and[THEN sym])

 done
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
 shows "((S->including(x))->exists(z | P(z))) = (if \<upsilon> x and \<delta> (P x) and \<upsilon> (S->exists(z | (P(z))))
                                                 then P x or (S->exists(z | P(z)))
                                                 else invalid
                                                 endif)"
  apply(simp add: OclExists_def ocl_or_def)

  apply(rule not_inject)
  apply(subst not_not)
  apply(simp add: OclExists_def ocl_or_def)
  apply(subst forall_set_including_exec)
  apply(rule sym, subst cp_not, rule sym)
  apply(simp only: cp[THEN sym] cp_not[THEN sym])

  apply(rule ext)
  apply(simp add: cp_if_ocl[of "\<upsilon> x and \<delta> (not (P x)) and \<upsilon> (S->forall(z|not (P z)))"])
  apply(simp add: cp_if_ocl[of "\<upsilon> x and \<delta> (P x) and \<upsilon> (not (S->forall(z|not (P z))))"])
  apply(simp add: cp_ocl_and[of "\<upsilon> x and \<delta> (not (P x))"])
  apply(simp add: cp_ocl_and[of "\<upsilon> x and \<delta> (P x)"])
  apply(simp add: cp_ocl_and[of "\<upsilon> x"])

  apply(subgoal_tac "(\<delta> not (P x)) xa = (\<delta> P x) xa \<and> (\<upsilon> (S->forall(z|not (P z)))) xa = (\<upsilon> (not (S->forall(X|not (P X))))) xa", simp)
  apply(rule conjI)
  apply(auto simp: not_def null_def invalid_def defined_def valid_def OclValid_def
                  true_def false_def bot_option_def null_option_def null_fun_def bot_fun_def
             split: option.split_asm HOL.split_if_asm)

  apply(auto simp: not_def null_def invalid_def defined_def valid_def OclValid_def
                  true_def false_def bot_option_def null_option_def null_fun_def bot_fun_def
          split: option.split_asm option.split HOL.split_if_asm)
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
 have A1 : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> Set_0" by(simp add: Set_0_def)
 have A2 : "None \<in> Set_0"  by(simp add: Set_0_def bot_option_def)
 have A3 : "\<lfloor>None\<rfloor> \<in> Set_0" by(simp add: Set_0_def bot_option_def null_option_def)
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
             by(simp add: defined_def  bot_Set_0_def null_Set_0_def
                          bot_fun_def null_fun_def A1 A2 A3 Abs_Set_0_inject)
 show ?thesis
      apply(simp add: OclIterate\<^isub>S\<^isub>e\<^isub>t_def mtSet_def Abs_Set_0_inverse Set_0_def valid_def C)
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
shows   "((S->including(a))->iterate(a; x = A     | F a x)) \<tau> =
         ((S->excluding(a))->iterate(a; x = F a A | F a x)) \<tau>"
proof -

 have valid_inject_true : "\<And>xa P. (\<upsilon> P) xa \<noteq> true xa \<Longrightarrow> (\<upsilon> P) xa = false xa"
  apply(simp add: valid_def true_def false_def
                  bot_fun_def bot_option_def
                  null_fun_def null_option_def)
 by (case_tac " P xa = \<bottom>", simp_all add: true_def)

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
  apply(frule Set_inv_lemma)
  apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                  foundation18 foundation16 invalid_def)
 done

 have insert_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>insert (a \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set_0_def null_Set_0_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set_0_inject)
  apply(rule insert_in_Set_0, simp_all add: Set_0_def bot_option_def)

  apply(subst Abs_Set_0_inject)
  apply(rule insert_in_Set_0, simp_all add: Set_0_def null_option_def bot_option_def)
 done

 have remove_finite : "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<Longrightarrow> finite ((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))"
 by(simp add: Set_0_def)

 have remove_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow> \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor> \<in> Set_0"
  apply(frule Set_inv_lemma)
  apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                  foundation18 foundation16 invalid_def)
 done

 have remove_defined : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> a)) \<Longrightarrow>
            (\<delta> (\<lambda>_. Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
  apply(subst defined_def)
  apply(simp add: bot_fun_def bot_option_def bot_Set_0_def null_Set_0_def null_option_def null_fun_def false_def true_def)
  apply(subst Abs_Set_0_inject)
  apply(rule remove_in_Set_0, simp_all add: Set_0_def bot_option_def)

  apply(subst Abs_Set_0_inject)
  apply(rule remove_in_Set_0, simp_all add: Set_0_def null_option_def bot_option_def)
 done

 have abs_rep: "\<And>x. \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<in> Set_0 \<Longrightarrow> \<lceil>\<lceil>Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>x\<rfloor>\<rfloor>)\<rceil>\<rceil> = x"
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


(*
Sequence{6,8}->iterate(i;r1:Sequence(Integer)=Sequence{9}|
  r1->iterate(j;r2:Sequence(Integer)=r1|
    r2->including(0)->including(i)->including(j)))
*)

lemma [simp]: "\<delta> (Set{} ->size()) = true"
proof -
 have A1 : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> Set_0" by(simp add: Set_0_def)
 have A2 : "None \<in> Set_0"  by(simp add: Set_0_def bot_option_def)
 have A3 : "\<lfloor>None\<rfloor> \<in> Set_0" by(simp add: Set_0_def bot_option_def null_option_def)
 show ?thesis
  apply(rule ext)
  apply(simp add: defined_def mtSet_def OclSize_def
                  bot_Set_0_def bot_fun_def
                  null_Set_0_def null_fun_def)
  apply(subst Abs_Set_0_inject, simp_all add: A1 A2 A3) +
 by(simp add: A1 Abs_Set_0_inverse bot_fun_def bot_option_def null_fun_def null_option_def)
qed


lemma including_size_defined[simp]: "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -

 have defined_inject_true : "\<And>xa P. (\<delta> P) xa \<noteq> true xa \<Longrightarrow> (\<delta> P) xa = false xa"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P xa = \<bottom> \<or> P xa = null", simp_all add: true_def)

 have valid_inject_true : "\<And>xa P. (\<upsilon> P) xa \<noteq> true xa \<Longrightarrow> (\<upsilon> P) xa = false xa"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P xa = \<bottom>", simp_all add: true_def)

(* example by bu ... *)

 have C : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> Set_0"
          apply(frule Set_inv_lemma)
          apply(simp add: Set_0_def bot_option_def null_Set_0_def null_fun_def
                          foundation18 foundation16 invalid_def)
          done

(* example by bu cont ... *)
have finite_including_exec' : 
    "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(simp add: OclIncluding_def Abs_Set_0_inverse C)
  apply(drule foundation13[THEN iffD2, THEN foundation22[THEN iffD1]], simp)+
  done

(* ... and even more succinct : *)
have finite_including_exec'' : 
     "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  by(auto simp: OclIncluding_def Abs_Set_0_inverse C
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
 
(* just equivalence, to show that this premise corresponds to the final statement in the logical 
chain ...*)
have "\<And>xa. (\<delta> X and \<upsilon> x) xa = true xa" sorry
have "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> "   sorry
have "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x) \<triangleq> true"   sorry
have "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> X and \<upsilon> x)  "        sorry
have "\<And>\<tau>. \<tau> \<Turnstile> (\<delta> X) \<and> \<tau> \<Turnstile>(\<upsilon> x)  "    sorry

(* and now compare to your original proof *)
 have finite_including_exec : "\<And>xa. (\<delta> X and \<upsilon> x) xa = true xa \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) xa)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>"
  apply(simp add: OclIncluding_def)
  apply(subst Abs_Set_0_inverse)
  apply(simp add: Set_0_def)
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
  apply(case_tac "(\<delta> X) xa = true xa", simp)
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(drule defined_inject_true[of X _])
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(simp add: false_def true_def)
 done

 have card_including_exec : "\<And>xa. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->including(x) xa)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) xa = (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) xa"
  apply(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)
 done

 show ?thesis

  apply(rule ext)
  apply(case_tac "(\<delta> (X->including(x)->size())) xa = true xa", simp)
  apply(subst cp_ocl_and)
  apply(subst cp_defined)
  apply(simp only: cp_defined[of "X->including(x)->size()"])
  apply(simp add: OclSize_def)
  apply(case_tac "((\<delta> X and \<upsilon> x) xa = true xa \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) xa)\<rceil>\<rceil>)", simp)
  prefer 2
  apply(simp)
  apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def)
  apply(erule conjE)
  apply(simp add: finite_including_exec card_including_exec
                  cp_ocl_and[of "\<delta> X" "\<upsilon> x"]
                  cp_ocl_and[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) xa = true xa \<and> (\<upsilon> x) xa = true xa", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_ocl_and[THEN sym])

  apply(drule defined_inject_true[of "X->including(x)->size()"], simp)
  apply(simp only: cp_ocl_and[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->including(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def finite_including_exec card_including_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) xa = true xa \<and> finite \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>",
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
  apply(case_tac "(\<upsilon> x) xa = true xa", simp add: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(drule valid_inject_true[of "x"], simp add: cp_ocl_and[of _ "\<upsilon> x"])
  apply(simp add: cp_ocl_and[THEN sym])
 done
qed

lemma excluding_size_defined[simp]: "\<delta> ((X ->excluding(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -

 have defined_inject_true : "\<And>xa P. (\<delta> P) xa \<noteq> true xa \<Longrightarrow> (\<delta> P) xa = false xa"
      apply(simp add: defined_def true_def false_def bot_fun_def 
                      bot_option_def null_fun_def null_option_def)
      by (case_tac " P xa = \<bottom> \<or> P xa = null", simp_all add: true_def)

 have valid_inject_true : "\<And>xa P. (\<upsilon> P) xa \<noteq> true xa \<Longrightarrow> (\<upsilon> P) xa = false xa"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by(case_tac "P xa = \<bottom>", simp_all add: true_def)


 have finite_excluding_exec : "\<And>xa. (\<delta> X and \<upsilon> x) xa = true xa \<Longrightarrow>
                                     finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) xa)\<rceil>\<rceil> = 
                                     finite \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>"
  apply(simp add: OclExcluding_def)
  apply(subst Abs_Set_0_inverse)
  apply(simp add: Set_0_def)
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
  apply(drule_tac Q = "xb \<noteq> \<bottom>" and x = xb in ballE)
  apply(assumption)
  apply(simp)

  apply(simp)
  apply(case_tac "(\<delta> X) xa = true xa", simp)
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(drule defined_inject_true[of X _])
  apply(simp only: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(simp add: cp_ocl_and[of _ "\<upsilon> x", THEN sym])
  apply(simp add: false_def true_def)
 done

 have card_excluding_exec : "\<And>xa. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) xa)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) xa = 
                                   (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) xa"
  apply(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)
 done

 show ?thesis

  apply(rule ext)
  apply(case_tac "(\<delta> (X->excluding(x)->size())) xa = true xa", simp)
  apply(subst cp_ocl_and)
  apply(subst cp_defined)
  apply(simp only: cp_defined[of "X->excluding(x)->size()"])
  apply(simp add: OclSize_def)
  apply(case_tac "((\<delta> X and \<upsilon> x) xa = true xa \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) xa)\<rceil>\<rceil>)", simp)
  prefer 2
  apply(simp)
  apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def)
  apply(erule conjE)
  apply(simp add: finite_excluding_exec card_excluding_exec
                  cp_ocl_and[of "\<delta> X" "\<upsilon> x"]
                  cp_ocl_and[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) xa = true xa \<and> (\<upsilon> x) xa = true xa", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_ocl_and[THEN sym])

  apply(drule defined_inject_true[of "X->excluding(x)->size()"], simp)
  apply(simp only: cp_ocl_and[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->excluding(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def finite_excluding_exec card_excluding_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) xa = true xa \<and> finite \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>",
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
  apply(case_tac "(\<upsilon> x) xa = true xa", simp add: cp_ocl_and[of "\<delta> X" "\<upsilon> x"])
  apply(drule valid_inject_true[of "x"], simp add: cp_ocl_and[of _ "\<upsilon> x"])
  apply(simp add: cp_ocl_and[THEN sym])
 done
qed

lemma size_defined:
 assumes X_finite: "\<And>xa. finite \<lceil>\<lceil>Rep_Set_0 (X xa)\<rceil>\<rceil>"
 shows "\<delta> (X->size()) = \<delta> X"
 apply(rule ext, simp add: cp_defined[of "X->size()"] OclSize_def)
 apply(simp add: defined_def bot_option_def bot_fun_def null_option_def null_fun_def X_finite)
done

lemma [simp]:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X) and \<upsilon>(x))"
by(simp add: size_defined[OF X_finite])

subsection{* Test Statements *}

lemma short_cut'[simp]: "(\<eight> \<doteq> \<six>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq_int StrongEq_def ocl_eight_def ocl_six_def 
                 true_def false_def invalid_def bot_option_def)
 apply(simp only: ocl_eight_def[THEN sym] ocl_six_def[THEN sym])
 apply(simp add: true_def)
done



lemma GogollasChallenge_on_sets:
      "\<tau> \<Turnstile> (Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j))) \<doteq> Set{\<zero>, \<six>, \<eight>, \<nine>})"
proof -

 have GogollasChallenge : 
            "Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j))) = Set{\<zero>, \<eight>, \<zero>, \<six>, \<eight>, \<zero>, \<nine>, \<eight>, \<zero>, \<nine>, \<six>, \<zero>, \<nine>}"
(*  apply(rule ext,
        simp add: excluding_charn_exec OclIterate\<^isub>S\<^isub>e\<^isub>t_including excluding_charn0_exec)*)
 sorry

 show ?thesis
  apply(simp add: GogollasChallenge)

 sorry (* should be simple to fix this. *)
qed


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
