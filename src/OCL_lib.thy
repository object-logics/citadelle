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

section{* Basic Types: Void, Integer *}
subsection{* The construction of the Void Type *}
(* subsection{* Basic Constants *} *)
type_synonym ('\<AA>)Void = "('\<AA>,unit option) val"
(* For technical reasons, he does not contain to the null-class yet. *)
text {* This \emph{minimal} OCL type contains only two elements:
@{term "undefined"} and @{term "null"}.
@{term "Void"} could initially be defined as @{typ "unit option option"},
however the cardinal of this type is more than two, so it would have the cost to consider
 @{text "Some None"} and @{text "Some (Some ())"} seemingly everywhere.*}

subsection{* The construction of the Integer Type *}
text{* Since @{term "Integer"} is again a basic type, we define its semantic domain
as the valuations over @{typ "int option option"}. *}
type_synonym ('\<AA>)Integer = "('\<AA>,int option option) val"

text{* Although the remaining part of this library reasons about
integers abstractly, we provide here some shortcuts to some usual integers. *}

definition OclInt0 ::"('\<AA>)Integer" ("\<zero>")
where      "\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>0::int\<rfloor>\<rfloor>)"

definition OclInt1 ::"('\<AA>)Integer" ("\<one>")
where      "\<one> = (\<lambda> _ . \<lfloor>\<lfloor>1::int\<rfloor>\<rfloor>)"

definition OclInt2 ::"('\<AA>)Integer" ("\<two>")
where      "\<two> = (\<lambda> _ . \<lfloor>\<lfloor>2::int\<rfloor>\<rfloor>)"

definition OclInt3 ::"('\<AA>)Integer" ("\<three>")
where      "\<three> = (\<lambda> _ . \<lfloor>\<lfloor>3::int\<rfloor>\<rfloor>)"

definition OclInt4 ::"('\<AA>)Integer" ("\<four>")
where      "\<four> = (\<lambda> _ . \<lfloor>\<lfloor>4::int\<rfloor>\<rfloor>)"

definition OclInt5 ::"('\<AA>)Integer" ("\<five>")
where      "\<five> = (\<lambda> _ . \<lfloor>\<lfloor>5::int\<rfloor>\<rfloor>)"

definition OclInt6 ::"('\<AA>)Integer" ("\<six>")
where      "\<six> = (\<lambda> _ . \<lfloor>\<lfloor>6::int\<rfloor>\<rfloor>)"

definition OclInt7 ::"('\<AA>)Integer" ("\<seven>")
where      "\<seven> = (\<lambda> _ . \<lfloor>\<lfloor>7::int\<rfloor>\<rfloor>)"

definition OclInt8 ::"('\<AA>)Integer" ("\<eight>")
where      "\<eight> = (\<lambda> _ . \<lfloor>\<lfloor>8::int\<rfloor>\<rfloor>)"

definition OclInt9 ::"('\<AA>)Integer" ("\<nine>")
where      "\<nine> = (\<lambda> _ . \<lfloor>\<lfloor>9::int\<rfloor>\<rfloor>)"

definition OclInt10 ::"('\<AA>)Integer" ("\<one>\<zero>")
where      "\<one>\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>10::int\<rfloor>\<rfloor>)"

subsection{* Validity and Definedness Properties *}

lemma  "\<delta>(null::('\<AA>)Integer) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)Integer) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:defined_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) = true"
by(simp add:valid_def true_def
               bot_fun_def bot_option_def)

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]:"\<delta> \<zero> = true" by(simp add:OclInt0_def)
lemma [simp,code_unfold]:"\<upsilon> \<zero> = true" by(simp add:OclInt0_def)
lemma [simp,code_unfold]:"\<delta> \<one> = true" by(simp add:OclInt1_def)
lemma [simp,code_unfold]:"\<upsilon> \<one> = true" by(simp add:OclInt1_def)
lemma [simp,code_unfold]:"\<delta> \<two> = true" by(simp add:OclInt2_def)
lemma [simp,code_unfold]:"\<upsilon> \<two> = true" by(simp add:OclInt2_def)
lemma [simp,code_unfold]: "\<delta> \<six> = true" by(simp add:OclInt6_def)
lemma [simp,code_unfold]: "\<upsilon> \<six> = true" by(simp add:OclInt6_def)
lemma [simp,code_unfold]: "\<delta> \<eight> = true" by(simp add:OclInt8_def)
lemma [simp,code_unfold]: "\<upsilon> \<eight> = true" by(simp add:OclInt8_def)
lemma [simp,code_unfold]: "\<delta> \<nine> = true" by(simp add:OclInt9_def)
lemma [simp,code_unfold]: "\<upsilon> \<nine> = true" by(simp add:OclInt9_def)

subsection{* Arithmetical Operations on Integer *}

subsubsection{* Definition *}
text{* Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot). *}
text{* Note that we can not follow the lexis of standard OCL for Isabelle-
technical reasons; these operators are heavily overloaded in the library
that a further overloading would lead to heavy technical buzz in this
document... *}
definition OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "+\<^sub>o\<^sub>c\<^sub>l" 40)
where "x +\<^sub>o\<^sub>c\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> + \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "


definition OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>o\<^sub>c\<^sub>l" 40)
where "x <\<^sub>o\<^sub>c\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "

definition OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r ::"('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>o\<^sub>c\<^sub>l" 40)
where "x \<le>\<^sub>o\<^sub>c\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else invalid \<tau> "

abbreviation OclAdd_\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r (infix "+\<^sub>I" 40) where "x +\<^sub>I y \<equiv> x +\<^sub>o\<^sub>c\<^sub>l y"
abbreviation OclLess_\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r (infix "<\<^sub>I" 40) where "x <\<^sub>I y \<equiv> x <\<^sub>o\<^sub>c\<^sub>l y"
abbreviation OclLe_\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r (infix "\<le>\<^sub>I" 40) where "x \<le>\<^sub>I y \<equiv> x \<le>\<^sub>o\<^sub>c\<^sub>l y"

subsubsection{* Basic properties *}

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_commute: "(X +\<^sub>o\<^sub>c\<^sub>l Y) = (Y +\<^sub>o\<^sub>c\<^sub>l X)"
  by(rule ext,auto simp:true_def false_def OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def invalid_def
                   split: option.split option.split_asm
                          bool.split bool.split_asm)

subsubsection{* Execution with invalid or null or zero as argument *}

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict1[simp,code_unfold] : "(x +\<^sub>o\<^sub>c\<^sub>l invalid) = invalid"
by(rule ext, simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def true_def false_def)

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2[simp,code_unfold] : "(invalid +\<^sub>o\<^sub>c\<^sub>l x) = invalid"
by(rule ext, simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def true_def false_def)

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_zero1[simp,code_unfold] : "(x +\<^sub>o\<^sub>c\<^sub>l \<zero>) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
 apply(rule ext, rename_tac \<tau>)
 proof - fix \<tau> show "(x +\<^sub>I \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
  apply(case_tac "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau>")
  apply(subst OclIf_true', simp add: OclValid_def)
  apply (metis OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclNot_defargs OclValid_def foundation5 foundation9)
  apply(subst OclIf_false')
  apply (metis OclValid_def defined5 defined6 defined_and_I defined_not_I foundation9)
  (* *)
  apply(simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclInt0_def)
  apply(rule conjI)
  apply(case_tac "x \<tau>")
  apply (metis OCL_core.bot_fun_def OCL_core.drop.simps bot_option_def defined_def false_def true_def)
  apply(simp)
  apply(case_tac a)
  apply(simp)
  apply (metis OclValid_def bot_option_def foundation17 null_option_def)
  apply(simp)
 by (metis OclValid_def foundation10 foundation18' foundation6 foundation7 invalid_def)
qed

lemma OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_zero2[simp,code_unfold] : "(\<zero> +\<^sub>o\<^sub>c\<^sub>l x) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
by(subst OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_commute, simp)

subsubsection{* Context Passing *}

lemma cp_OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r:"(X +\<^sub>o\<^sub>c\<^sub>l Y) \<tau> = ((\<lambda> _. X \<tau>) +\<^sub>o\<^sub>c\<^sub>l (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def cp_defined[symmetric])

lemma cp_OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r:"(X <\<^sub>o\<^sub>c\<^sub>l Y) \<tau> = ((\<lambda> _. X \<tau>) <\<^sub>o\<^sub>c\<^sub>l (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def cp_defined[symmetric])

lemma cp_OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r:"(X \<le>\<^sub>o\<^sub>c\<^sub>l Y) \<tau> = ((\<lambda> _. X \<tau>) \<le>\<^sub>o\<^sub>c\<^sub>l (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def cp_defined[symmetric])

subsubsection{* Test Statements *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}

value "  \<tau> \<Turnstile> ( \<nine> \<le>\<^sub>o\<^sub>c\<^sub>l \<one>\<zero> )"
value "  \<tau> \<Turnstile> (( \<four> +\<^sub>o\<^sub>c\<^sub>l \<four> ) \<le>\<^sub>o\<^sub>c\<^sub>l \<one>\<zero> )"
value "\<not>(\<tau> \<Turnstile> (( \<four> +\<^sub>o\<^sub>c\<^sub>l ( \<four> +\<^sub>o\<^sub>c\<^sub>l \<four> )) <\<^sub>o\<^sub>c\<^sub>l \<one>\<zero> ))"
value "  \<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>o\<^sub>c\<^sub>l \<one>)) "

section{* Fundamental Predicates on Boolean and Integer: Strict Equality *}

subsection{* Definition *}

text{* The strict equality on basic types (actually on all types)
must be exceptionally defined on @{term "null"} --- otherwise the entire concept of
null in the language does not make much sense. This is an important exception
from the general rule that null arguments --- especially if passed as "self"-argument ---
lead to invalid results. *}

consts StrictRefEq :: "[('\<AA>,'a)val,('\<AA>,'a)val] \<Rightarrow> ('\<AA>)Boolean" (infixl "\<doteq>" 30)

syntax
  "notequal"        :: "('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean \<Rightarrow> ('\<AA>)Boolean"   (infix "<>" 40)
translations
  "a <> b" == "CONST OclNot( a \<doteq> b)"

defs   StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[code_unfold] :
      "(x::('\<AA>)Boolean) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y)\<tau>
                                    else invalid \<tau>"

defs   StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[code_unfold] :
      "(x::('\<AA>)Integer) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y) \<tau>
                                    else invalid \<tau>"

lemma [simp, code_unfold] : "(true \<doteq> false) = false"
by(simp add:StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)
lemma [simp, code_unfold] : "(false \<doteq> true) = false"
by(simp add:StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)

value "\<tau> \<Turnstile> \<one> <> \<two>"
value "\<tau> \<Turnstile> \<two> <> \<one>"
value "\<tau> \<Turnstile> \<two> \<doteq> \<two>"
value "\<tau> \<Turnstile> true <> false"
value "\<tau> \<Turnstile> false <> true "

subsection{* Logic and Algebraic Layer on Basic Types *}

subsubsection{* Validity and Definedness Properties (I) *}

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)Boolean) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)

lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>((x::('\<AA>)Integer) \<doteq> y)) = ((\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y)))"
by(auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r OclValid_def true_def valid_def false_def StrongEq_def
              defined_def invalid_def null_fun_def bot_fun_def null_option_def bot_option_def
        split: bool.split_asm HOL.split_if_asm option.split)

subsubsection{* Validity and Definedness Properties (II) *}

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Boolean) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def true_def invalid_def
             bot_option_def
        split: bool.split_asm HOL.split_if_asm)

lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defargs:
"\<tau> \<Turnstile> ((x::('\<AA>)Integer) \<doteq> y) \<Longrightarrow> (\<tau> \<Turnstile> (\<upsilon> x)) \<and> (\<tau> \<Turnstile> (\<upsilon> y))"
by(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r OclValid_def true_def invalid_def valid_def bot_option_def
           split: bool.split_asm HOL.split_if_asm)

subsubsection{* Validity and Definedness Properties (III) Miscellaneous *}

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict'' : "\<delta> ((x::('\<AA>)Boolean) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_defined_args_valid)

lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict'' : "\<delta> ((x::('\<AA>)Integer) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
by(auto intro!: transform2_rev defined_and_I simp:foundation10 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid)

(* Probably not very useful *)
lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict :
  assumes A: "\<upsilon> (x::('\<AA>)Integer) = true"
  and     B: "\<upsilon> y = true"
  shows   "\<upsilon> (x \<doteq> y) = true"
  apply(insert A B)
  apply(rule ext, simp add: StrongEq_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r true_def valid_def defined_def
                            bot_fun_def bot_option_def)
  done


(* Probably not very useful *)
lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' :
  assumes A: "\<upsilon> (((x::('\<AA>)Integer)) \<doteq> y) = true"
  shows      "\<upsilon> x = true \<and> \<upsilon> y = true"
  apply(insert A, rule conjI)
  apply(rule ext, drule_tac x=xa in fun_cong)
  prefer 2
  apply(rule ext, drule_tac x=xa in fun_cong)
  apply(simp_all add: StrongEq_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r
                            false_def true_def valid_def defined_def)
  apply(case_tac "y xa", auto)
  apply(simp_all add: true_def invalid_def bot_fun_def)
  done

subsubsection{* Reflexivity *}

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_refl[simp,code_unfold] :
"((x::('\<AA>)Boolean) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclIf_def)

lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl[simp,code_unfold] :
"((x::('\<AA>)Integer) \<doteq> x) = (if (\<upsilon> x) then true else invalid endif)"
by(rule ext, simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r OclIf_def)

subsubsection{* Execution with invalid or null as argument *}

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict1[simp,code_unfold] : "((x::('\<AA>)Boolean) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n true_def false_def)

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict2[simp,code_unfold] : "(invalid \<doteq> (x::('\<AA>)Boolean)) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n true_def false_def)

lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict1[simp,code_unfold] : "((x::('\<AA>)Integer) \<doteq> invalid) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r true_def false_def)

lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2[simp,code_unfold] : "(invalid \<doteq> (x::('\<AA>)Integer)) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r true_def false_def)

lemma true_non_null [simp,code_unfold]:"(true \<doteq> null) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
by (metis defined3 foundation1 foundation16 null_fun_def)

lemma null_non_true [simp,code_unfold]:"(null \<doteq> true) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
by (metis defined3 foundation1 foundation16 null_fun_def)

lemma false_non_null [simp,code_unfold]:"(false \<doteq> null) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
by (metis OCL_core.drop.simps null_Boolean_def option.distinct(1))

lemma null_non_false [simp,code_unfold]:"(null \<doteq> false) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
by (metis OCL_core.drop.simps null_Boolean_def option.distinct(1))

lemma integer_non_null [simp]: "((\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>) \<doteq> (null::('\<AA>)Integer)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma null_non_integer [simp]: "((null::('\<AA>)Integer) \<doteq> (\<lambda>_. \<lfloor>\<lfloor>n\<rfloor>\<rfloor>)) = false"
by(rule ext,auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def
                         bot_fun_def bot_option_def null_fun_def null_option_def StrongEq_def)

lemma OclInt0_non_null [simp,code_unfold]: "(\<zero> \<doteq> null) = false" by(simp add: OclInt0_def)
lemma null_non_OclInt0 [simp,code_unfold]: "(null \<doteq> \<zero>) = false" by(simp add: OclInt0_def)
lemma OclInt1_non_null [simp,code_unfold]: "(\<one> \<doteq> null) = false" by(simp add: OclInt1_def)
lemma null_non_OclInt1 [simp,code_unfold]: "(null \<doteq> \<one>) = false" by(simp add: OclInt1_def)
lemma OclInt2_non_null [simp,code_unfold]: "(\<two> \<doteq> null) = false" by(simp add: OclInt2_def)
lemma null_non_OclInt2 [simp,code_unfold]: "(null \<doteq> \<two>) = false" by(simp add: OclInt2_def)
lemma OclInt6_non_null [simp,code_unfold]: "(\<six> \<doteq> null) = false" by(simp add: OclInt6_def)
lemma null_non_OclInt6 [simp,code_unfold]: "(null \<doteq> \<six>) = false" by(simp add: OclInt6_def)
lemma OclInt8_non_null [simp,code_unfold]: "(\<eight> \<doteq> null) = false" by(simp add: OclInt8_def)
lemma null_non_OclInt8 [simp,code_unfold]: "(null \<doteq> \<eight>) = false" by(simp add: OclInt8_def)
lemma OclInt9_non_null [simp,code_unfold]: "(\<nine> \<doteq> null) = false" by(simp add: OclInt9_def)
lemma null_non_OclInt9 [simp,code_unfold]: "(null \<doteq> \<nine>) = false" by(simp add: OclInt9_def)

(* plus all the others ...*)


subsubsection{* Behavior vs StrongEq *}

lemma StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_vs_StrongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)Boolean) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n OclValid_def)
apply(subst cp_StrongEq)back
by simp


lemma StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_vs_StrongEq:
"\<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> (\<tau> \<Turnstile> (((x::('\<AA>)Integer) \<doteq> y) \<triangleq> (x \<triangleq> y)))"
apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r OclValid_def)
apply(subst cp_StrongEq)back
by simp


subsubsection{* Context Passing *}

lemma cp_StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n:
"((X::('\<AA>)Boolean) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def defined_def valid_def  cp_defined[symmetric])

lemma cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r:
"((X::('\<AA>)Integer) \<doteq> Y) \<tau> = ((\<lambda> _. X \<tau>) \<doteq> (\<lambda> _. Y \<tau>)) \<tau>"
by(auto simp: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def valid_def  cp_defined[symmetric])


lemmas cp_intro'[simp,intro!,code_unfold] =
       cp_intro'
       cp_StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "StrictRefEq"]]
       cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[THEN allI[THEN allI[THEN allI[THEN cpI2]],  of "StrictRefEq"]]
       cp_OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r"]]
       cp_OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r"]]
       cp_OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r"]]


subsection{* Test Statements on Basic Types. *}

text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}

text{* Elementary computations on Booleans *}
value "\<tau> \<Turnstile> \<upsilon>(true)"
value "\<tau> \<Turnstile> \<delta>(false)"
value "\<not>(\<tau> \<Turnstile> \<delta>(null))"
value "\<not>(\<tau> \<Turnstile> \<delta>(invalid))"
value "\<tau> \<Turnstile> \<upsilon>((null::('\<AA>)Boolean))"
value "\<not>(\<tau> \<Turnstile> \<upsilon>(invalid))"
value "\<tau> \<Turnstile> (true and true)"
value "\<tau> \<Turnstile> (true and true \<triangleq> true)"
value "\<tau> \<Turnstile> ((null or null) \<triangleq> null)"
value "\<tau> \<Turnstile> ((null or null) \<doteq> null)"
value "\<tau> \<Turnstile> ((true \<triangleq> false) \<triangleq> false)"
value "\<tau> \<Turnstile> ((invalid \<triangleq> false) \<triangleq> false)"
value "\<tau> \<Turnstile> ((invalid \<doteq> false) \<triangleq> invalid)"


text{* Elementary computations on Integer *}
value "  \<tau> \<Turnstile> \<upsilon> \<four>"
value "  \<tau> \<Turnstile> \<delta> \<four>"
value "  \<tau> \<Turnstile> \<upsilon> (null::('\<AA>)Integer)"
value "  \<tau> \<Turnstile> (invalid \<triangleq> invalid)"
value "  \<tau> \<Turnstile> (null \<triangleq> null)"
value "  \<tau> \<Turnstile> (\<four> \<triangleq> \<four>)"
value "\<not>(\<tau> \<Turnstile> (\<nine> \<triangleq> \<one>\<zero>))"
value "\<not>(\<tau> \<Turnstile> (invalid \<triangleq> \<one>\<zero>))"
value "\<not>(\<tau> \<Turnstile> (null \<triangleq> \<one>\<zero>))"
value "\<not>(\<tau> \<Turnstile> (invalid \<doteq> (invalid::('\<AA>)Integer)))" (* Without typeconstraint not executable.*)
value "\<not>(\<tau> \<Turnstile> \<upsilon> (invalid \<doteq> (invalid::('\<AA>)Integer)))" (* Without typeconstraint not executable.*)
value "\<not>(\<tau> \<Turnstile> (invalid <> (invalid::('\<AA>)Integer)))" (* Without typeconstraint not executable.*)
value "\<not>(\<tau> \<Turnstile> \<upsilon> (invalid <> (invalid::('\<AA>)Integer)))" (* Without typeconstraint not executable.*)
value "  \<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)Integer) )" (* Without typeconstraint not executable.*)
value "  \<tau> \<Turnstile> (null \<doteq> (null::('\<AA>)Integer) )" (* Without typeconstraint not executable.*)
value "  \<tau> \<Turnstile> (\<four> \<doteq> \<four>)"
value "\<not>(\<tau> \<Turnstile> (\<four> <> \<four>))"
value "\<not>(\<tau> \<Turnstile> (\<four> \<doteq> \<one>\<zero>))"
value "  \<tau> \<Turnstile> (\<four> <> \<one>\<zero>)"
value "\<not>(\<tau> \<Turnstile> (\<zero> <\<^sub>o\<^sub>c\<^sub>l null))"
value "\<not>(\<tau> \<Turnstile> (\<delta> (\<zero> <\<^sub>o\<^sub>c\<^sub>l null)))"


section{* Complex Types: The Set-Collection Type (I) Core *}

subsection{* The construction of the Set Type *}

no_notation None ("\<bottom>")
notation bot ("\<bottom>")

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

subsection{* Validity and Definedness Properties *}

text{* Every element in a defined set is valid. *}

lemma Set_inv_lemma: "\<tau> \<Turnstile> (\<delta> X) \<Longrightarrow> \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> bot"
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
by (metis bot_option_def null_Set_0_def null_option_def)

lemma Set_inv_lemma' :
 assumes x_def : "\<tau> \<Turnstile> \<delta> X"
     and e_mem : "e \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
   shows "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)"
 apply(rule Set_inv_lemma[OF x_def, THEN ballE[where x = e]])
 apply (metis foundation18')
by (metis e_mem)

lemma abs_rep_simp' :
 assumes S_all_def : "\<tau> \<Turnstile> \<delta> S"
   shows "Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> = S \<tau>"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 show ?thesis
  apply(insert S_all_def, simp add: OclValid_def defined_def)
  apply(rule mp[OF Abs_Set_0_induct[where P = "\<lambda>S. (if S = \<bottom> \<tau> \<or> S = null \<tau> then false \<tau> else true \<tau>) = true \<tau> \<longrightarrow> Abs_Set_0 \<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 S\<rceil>\<rceil>\<rfloor>\<rfloor> = S"]])
  apply(simp add: Abs_Set_0_inverse discr_eq_false_true)
  apply(case_tac y) apply(simp add: bot_fun_def bot_Set_0_def)+
  apply(case_tac a) apply(simp add: null_fun_def null_Set_0_def)+
 done
qed

lemma S_lift' :
 assumes S_all_def : "(\<tau> :: '\<AA> st) \<Turnstile> \<delta> S"
   shows "\<exists>S'. (\<lambda>a (_::'\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = (\<lambda>a (_::'\<AA> st). \<lfloor>a\<rfloor>) ` S'"
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
  apply(drule Set_inv_lemma'[OF S_all_def])
  apply(case_tac x, simp add: bot_option_def foundation18')
  apply(simp)
done

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

lemma mtSet_rep_set: "\<lceil>\<lceil>Rep_Set_0 (Set{} \<tau>)\<rceil>\<rceil> = {}"
 apply(simp add: mtSet_def, subst Abs_Set_0_inverse)
by(simp add: bot_option_def)+

text{* Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid. *}

section{* Complex Types: The Set-Collection Type (II) Library *}

text{* This part provides a collection of operators for the Set type. *}

subsection{* Computational Operations on Set *}

subsubsection{* Definition *}

definition OclIncluding   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> ('\<AA>,'\<alpha>) Set"
where     "OclIncluding x y = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then Abs_Set_0 \<lfloor>\<lfloor> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>  \<union> {y \<tau>} \<rfloor>\<rfloor>
                                    else \<bottom> )"
notation   OclIncluding   ("_->including'(_')")

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
notation   OclIncludes    ("_->includes'(_')" [66,65]65)

definition OclExcludes   :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<alpha>) val] \<Rightarrow> '\<AA> Boolean"
where     "OclExcludes x y = (not(OclIncludes x y))"
notation   OclExcludes    ("_->excludes'(_')" [66,65]65)

text{* The case of the size definition is somewhat special, we admit
explicitly in Featherweight OCL the possibility of infinite sets. For
the size definition, this requires an extra condition that assures
that the cardinality of the set is actually a defined integer. *}

definition OclSize     :: "('\<AA>,'\<alpha>::null)Set \<Rightarrow> '\<AA> Integer"
where     "OclSize x = (\<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> finite(\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>)
                             then \<lfloor>\<lfloor> int(card \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>) \<rfloor>\<rfloor>
                             else \<bottom> )"
notation  (* standard ascii syntax *)
           OclSize        ("_->size'(')" [66])

text{* The following definition follows the requirement of the
standard to treat null as neutral element of sets. It is
a well-documented exception from the general strictness
rule and the rule that the distinguished argument self should
be non-null. *}
definition OclIsEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclIsEmpty x =  ((\<upsilon> x and not (\<delta> x)) or ((OclSize x) \<doteq> \<zero>))"
notation   OclIsEmpty     ("_->isEmpty'(')" [66])

definition OclNotEmpty   :: "('\<AA>,'\<alpha>::null) Set \<Rightarrow> '\<AA> Boolean"
where     "OclNotEmpty x =  not(OclIsEmpty x)"
notation   OclNotEmpty    ("_->notEmpty'(')" [66])

(* Slight breach of naming convention in order to avoid naming conflict on constant.*)
definition Ocl_Any   :: "[('\<AA>,'\<alpha>::null) Set] \<Rightarrow> ('\<AA>,'\<alpha>) val"
where     "Ocl_Any x = (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau>
                            then if (\<delta> x and OclNotEmpty x) \<tau> = true \<tau> then SOME y. y \<in> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>
                                 else null \<tau>
                            else \<bottom> )"
notation   Ocl_Any   ("_->any'(')")
(* actually, this definition covers only: X->any(true) of the standard, which foresees
a (totally correct) high-level definition
source->any(iterator | body) =
source->select(iterator | body)->asSequence()->first(). Since we don't have sequences,
we have to go for a direct --- restricted ---  definition. *)


text{* The definition of OclForall mimics the one of @{term "OclAnd"}:
OclForall is not a strict operation. *}
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

definition OclIterate\<^sub>S\<^sub>e\<^sub>t :: "[('\<AA>,'\<alpha>::null) Set,('\<AA>,'\<beta>::null)val,
                             ('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>,'\<beta>)val\<Rightarrow>('\<AA>,'\<beta>)val] \<Rightarrow> ('\<AA>,'\<beta>)val"
where "OclIterate\<^sub>S\<^sub>e\<^sub>t S A F = (\<lambda> \<tau>. if (\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> A) \<tau> = true \<tau> \<and> finite\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>
                                  then (Finite_Set.fold (F) (A) ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>))\<tau>
                                  else \<bottom>)"
syntax
  "_OclIterate"  :: "[('\<AA>,'\<alpha>::null) Set, idt, idt, '\<alpha>, '\<beta>] => ('\<AA>,'\<gamma>)val"
                        ("_ ->iterate'(_;_=_ | _')" [71,100,70]50)
translations
  "X->iterate(a; x = A | P)" == "CONST OclIterate\<^sub>S\<^sub>e\<^sub>t X A (%a. (% x. P))"

definition OclSelect\<^sub>s\<^sub>e\<^sub>t :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>)Set"
where "OclSelect\<^sub>s\<^sub>e\<^sub>t S P = (\<lambda>\<tau>. if (\<delta> S) \<tau> = true \<tau>
                              then if (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P(\<lambda> _. x) \<tau> = \<bottom> \<tau>)
                                   then \<bottom>
                                   else Abs_Set_0 \<lfloor>\<lfloor> { x\<in>\<lceil>\<lceil> Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau> } \<rfloor>\<rfloor>
                              else \<bottom>)"
syntax
  "_OclSelect" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->select'(_|_')")
translations
  "X->select(x | P)" == "CONST OclSelect\<^sub>s\<^sub>e\<^sub>t X (% x. P)"

definition OclReject\<^sub>s\<^sub>e\<^sub>t :: "[('\<AA>,'\<alpha>::null)Set,('\<AA>,'\<alpha>)val\<Rightarrow>('\<AA>)Boolean] \<Rightarrow> ('\<AA>,'\<alpha>::null)Set"
where "OclReject\<^sub>s\<^sub>e\<^sub>t S P = OclSelect\<^sub>s\<^sub>e\<^sub>t S (not o P)"
syntax
  "_OclReject" :: "[('\<AA>,'\<alpha>::null) Set,id,('\<AA>)Boolean] \<Rightarrow> '\<AA> Boolean"    ("(_)->reject'(_|_')")
translations
  "X->reject(x | P)" == "CONST OclReject\<^sub>s\<^sub>e\<^sub>t X (% x. P)"

subsubsection{* Definition (futur operators) *}

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

subsection{* Validity and Definedness Properties *}

subsubsection{* OclIncluding *}

lemma including_defined_args_valid:
"(\<tau> \<Turnstile> \<delta>(X->including(x))) = ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
proof -
 have A : "\<bottom> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: bot_option_def)
 have B : "\<lfloor>\<bottom>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
 have C : "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<delta>(X->including(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclIncluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->including(x)))"
          apply(subst OclIncluding_def, subst OclValid_def, subst defined_def)
          apply(auto simp: OclValid_def null_Set_0_def bot_Set_0_def null_fun_def bot_fun_def)
          apply(frule Abs_Set_0_inject[OF C A, simplified OclValid_def, THEN iffD1], simp_all add: bot_option_def)
          apply(frule Abs_Set_0_inject[OF C B, simplified OclValid_def, THEN iffD1], simp_all add: bot_option_def)
          done
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
          apply(simp add: foundation18 invalid_def)
          done
 have D: "(\<tau> \<Turnstile> \<delta>(X->excluding(x))) \<Longrightarrow> ((\<tau> \<Turnstile>(\<delta> X)) \<and> (\<tau> \<Turnstile>(\<upsilon> x)))"
          by(auto simp: OclExcluding_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have E: "(\<tau> \<Turnstile>(\<delta> X)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> (\<tau> \<Turnstile> \<delta>(X->excluding(x)))"
          apply(subst OclExcluding_def, subst OclValid_def, subst defined_def)
          apply(auto simp: OclValid_def null_Set_0_def bot_Set_0_def null_fun_def bot_fun_def)
          apply(frule Abs_Set_0_inject[OF C A, simplified OclValid_def, THEN iffD1], simp_all add: bot_option_def)
          apply(frule Abs_Set_0_inject[OF C B, simplified OclValid_def, THEN iffD1], simp_all add: bot_option_def)
          done
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

subsubsection{* OclNotEmpty *}

lemma notempty_has_elt : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                          \<tau> \<Turnstile> X->notEmpty() \<Longrightarrow>
                          \<exists>e. e \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 apply(simp add: OclNotEmpty_def OclIsEmpty_def deMorgan1 deMorgan2, drule foundation5)
 apply(subst (asm) (2) OclNot_def,
       simp add: OclValid_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def
            split: split_if_asm)
 prefer 2
 apply(simp add: invalid_def bot_option_def true_def)
 apply(simp add: OclSize_def valid_def split: split_if_asm, simp_all add: false_def true_def bot_option_def bot_fun_def OclInt0_def)
by (metis equals0I)

subsubsection{* Ocl Any *}

lemma any_valid_args_valid[simp,code_unfold]:
"(\<tau> \<Turnstile> \<upsilon>(X->any())) = (\<tau> \<Turnstile> \<upsilon> X)"
proof -
 have A: "(\<tau> \<Turnstile> \<upsilon>(X->any())) \<Longrightarrow> ((\<tau> \<Turnstile>(\<upsilon> X)))"
          by(auto simp: Ocl_Any_def OclValid_def true_def valid_def false_def StrongEq_def
                        defined_def invalid_def bot_fun_def null_fun_def
                  split: bool.split_asm HOL.split_if_asm option.split)
 have B: "(\<tau> \<Turnstile>(\<upsilon> X)) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(X->any()))"
           apply(auto simp: Ocl_Any_def OclValid_def true_def false_def StrongEq_def
                            defined_def invalid_def valid_def bot_fun_def null_fun_def
                            bot_option_def null_option_def null_is_valid
                            OclAnd_def
                      split: bool.split_asm HOL.split_if_asm option.split)
           apply(frule Set_inv_lemma[OF foundation16[THEN iffD2], OF conjI], simp)
           apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau>")
             prefer 2
             apply (metis (hide_lams, no_types) OclValid_def foundation16)
           apply(simp add: true_def)
           apply(drule notempty_has_elt[simplified OclValid_def true_def], simp)
           apply(drule exE) prefer 2 apply(simp)
           proof - fix e show "X \<tau> \<noteq> null \<Longrightarrow>
                               (SOME y. y \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>) = \<bottom> \<Longrightarrow>
                               \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. x \<noteq> \<bottom> \<Longrightarrow> e \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> False"
            apply(subgoal_tac "(SOME x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>) \<noteq> \<bottom>")
            prefer 2
            apply(rule someI2[where Q = "\<lambda>x. x \<noteq> \<bottom>" and P = "\<lambda>y. y \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>" and a = e], simp)
            apply(simp)
            apply(simp)
           done
           apply_end(simp)+
          qed
 show ?thesis by(auto dest:A intro:B)
qed

lemma any_valid_args_valid''[simp,code_unfold]:
"\<upsilon>(X->any()) = (\<upsilon> X)"
by(auto intro!: transform2_rev)

(* and many more, forall exists. *)


subsection{* Execution with invalid or null as argument *}


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

subsubsection{* OclSize *}

lemma size_strict1[simp,code_unfold]:"(invalid->size()) = invalid"
by(simp add: bot_fun_def OclSize_def invalid_def defined_def valid_def false_def true_def)

lemma size_strict3[simp,code_unfold]:"(null->size()) = invalid"
by(rule ext,
   simp add: bot_fun_def null_fun_def null_is_valid OclSize_def
             invalid_def defined_def valid_def false_def true_def)

subsubsection{* OclIsEmpty *}

lemma isEmpty_strict1[simp,code_unfold]:"(invalid->isEmpty()) = invalid"
by(simp add: OclIsEmpty_def)

lemma isEmpty_strict3[simp,code_unfold]:"(null->isEmpty()) = true"
by(simp add: OclIsEmpty_def)

subsubsection{* OclNotEmpty *}

lemma notEmpty_strict1[simp,code_unfold]:"(invalid->notEmpty()) = invalid"
by(simp add: OclNotEmpty_def)

lemma notEmpty_strict3[simp,code_unfold]:"(null->notEmpty()) = false"
by(simp add: OclNotEmpty_def)

subsubsection{* Ocl Any *}

lemma any_strict1[simp,code_unfold]:"(invalid->any()) = invalid"
by(simp add: bot_fun_def Ocl_Any_def invalid_def defined_def valid_def false_def true_def)

lemma any_strict3[simp,code_unfold]:"(null->any()) = null"
by(simp add: Ocl_Any_def false_def true_def)

(*  forall ? exists ?*)

subsubsection{* OclIterate *}

lemma OclIterate\<^sub>S\<^sub>e\<^sub>t_strict1[simp,code_unfold]:"invalid->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^sub>S\<^sub>e\<^sub>t_def defined_def valid_def false_def true_def)

lemma OclIterate\<^sub>S\<^sub>e\<^sub>t_null1[simp,code_unfold]:"null->iterate(a; x = A | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^sub>S\<^sub>e\<^sub>t_def defined_def valid_def false_def true_def)


lemma OclIterate\<^sub>S\<^sub>e\<^sub>t_strict2[simp,code_unfold]:"S->iterate(a; x = invalid | P a x) = invalid"
by(simp add: bot_fun_def invalid_def OclIterate\<^sub>S\<^sub>e\<^sub>t_def defined_def valid_def false_def true_def)

text{* An open question is this ... *}
lemma (*OclIterate\<^sub>S\<^sub>e\<^sub>t_null2[simp]:*) "S->iterate(a; x = null | P a x) = invalid"
oops
(* In the definition above, this does not hold in general.
       And I believe, this is how it should be ... *)



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
"(X->includes(x)) \<tau> = (OclIncludes (\<lambda> _. X \<tau>) (\<lambda> _. x \<tau>) \<tau>)"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclIncludes1:
"(X->includes(x)) \<tau> = (OclIncludes X (\<lambda> _. x \<tau>) \<tau>)"
by(auto simp: OclIncludes_def StrongEq_def invalid_def
                 cp_defined[symmetric] cp_valid[symmetric])

lemma cp_OclSize: "X->size() \<tau> = (\<lambda>_. X \<tau>)->size() \<tau>"
by(simp add: OclSize_def cp_defined[symmetric])

lemma cp_OclIsEmpty: "X->isEmpty() \<tau> = (\<lambda>_. X \<tau>)->isEmpty() \<tau>"
 apply(simp add: OclIsEmpty_def)
 apply(subst (2) cp_OclOr)
 apply(subst cp_OclAnd)
 apply(subst cp_OclNot)
 apply(subst cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r)
 apply(simp add: cp_defined[symmetric] cp_valid[symmetric]
  cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[symmetric] cp_OclSize[symmetric] cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
done

lemma cp_OclNotEmpty: "X->notEmpty() \<tau> = (\<lambda>_. X \<tau>)->notEmpty() \<tau>"
 apply(simp add: OclNotEmpty_def)
 apply(subst (2) cp_OclNot)
 apply(simp add: cp_OclNot[symmetric] cp_OclIsEmpty[symmetric])
done

lemma cp_Ocl_Any: "X->any() \<tau> = (\<lambda>_. X \<tau>)->any() \<tau>"
 apply(simp only: Ocl_Any_def)
 apply(subst (2) cp_OclAnd)
 apply(simp only: cp_OclAnd[symmetric] cp_defined[symmetric] cp_valid[symmetric] cp_OclNotEmpty[symmetric])
done

lemma cp_OclForall:
"(S->forAll(x | P x)) \<tau> = ((\<lambda> _. S \<tau>)->forAll(x | P (\<lambda> _. x \<tau>))) \<tau>"
by(simp add: OclForall_def cp_defined[symmetric])

(* first-order version !*)
lemma cp_OclForall1 [simp,intro!]:
"cp S \<Longrightarrow> cp (\<lambda>X. ((S X)->forAll(x | P x)))"
apply(simp add: cp_def)
apply(erule exE, rule exI, rule allI, rule allI, rule allI)
apply(erule_tac x=X in allE)
apply(subst cp_OclForall)
apply(simp)
done

lemma cp_OclForall2 [simp,intro!]:
"cp (\<lambda>X St x. P (\<lambda>\<tau>. x) X St) \<Longrightarrow> cp S \<Longrightarrow> cp (\<lambda>X. (S X)->forAll(x|P x X)) "
apply(simp only: cp_def)
oops

lemma cp_OclForall:
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


lemma cp_OclIterate\<^sub>S\<^sub>e\<^sub>t: "(X->iterate(a; x = A | P a x)) \<tau> =
                ((\<lambda> _. X \<tau>)->iterate(a; x = A | P a x)) \<tau>"
by(simp add: OclIterate\<^sub>S\<^sub>e\<^sub>t_def cp_defined[symmetric])

(* Why does this not work syntactically ???
   lemma cp_OclIncludes: "(X->includes(x)) \<tau> = (((\<lambda> _. X \<tau>)->includes( \<lambda> _. x \<tau>)) \<tau>)" *)

lemmas cp_intro''[simp,intro!,code_unfold] =
       cp_intro'
       cp_OclIncluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncluding"]]
       cp_OclExcluding [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclExcluding"]]
       cp_OclIncludes  [THEN allI[THEN allI[THEN allI[THEN cpI2]], of "OclIncludes"]]
       cp_OclSize      [THEN allI[THEN allI[THEN cpI1], of "OclSize"]]
       cp_Ocl_Any       [THEN allI[THEN allI[THEN cpI1], of "Ocl_Any"]]

section{* Fundamental Predicates on Set: Strict Equality *}

subsection{* Definition *}

text{* After the part of foundational operations on sets, we detail here equality on sets.
Strong Equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:*}

defs   StrictRefEq\<^sub>S\<^sub>e\<^sub>t :
      "(x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                         then (x \<triangleq> y)\<tau>
                                         else invalid \<tau>"

text{* One might object here that for the case of objects, this is an empty definition.
The answer is no, we will restrain later on states and objects such that any object
has its id stored inside the object (so the ref, under which an object can be referenced
in the store will represented in the object itself). For such well-formed stores that satisfy
this invariant (the WFF - invariant), the referential equality and the strong equality ---
and therefore the strict equality on sets in the sense above) coincides.*}

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

subsubsection{* Execution with invalid or null as argument *}

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
           apply(rule cp_validity[THEN iffD2])
           apply(subst cp_defined, simp add: foundation22)
           apply(simp add: cp_defined[symmetric] cp_validity[symmetric])
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




section{* Execution on Set's Operators *}

subsection{* OclIncluding *}


lemma including_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> not(Set{}->includes(x))"
using val_x
apply(auto simp: OclValid_def OclIncludes_def OclNot_def false_def true_def)
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
          apply(insert val_x Set_inv_lemma[OF def_X])
          apply(simp add: foundation18 invalid_def)
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
          apply(insert val_x Set_inv_lemma[OF def_X])
          apply(simp add: foundation18 invalid_def)
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


(* Hack to work around OF-Bug *)
schematic_lemma includes_execute_int[simp,code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict1 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2
                                 cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r
                                    StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_vs_StrongEq], simp_all)


schematic_lemma includes_execute_bool[simp,code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict1 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict2
                                 cp_StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n
                                    StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_vs_StrongEq], simp_all)


schematic_lemma includes_execute_set[simp,code_unfold]: "?X"
by(rule includes_execute_generic[OF StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict1 StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict2
                                 cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t
                                    StrictRefEq\<^sub>S\<^sub>e\<^sub>t_vs_StrongEq], simp_all)

lemma finite_including_rep_set :
  assumes X_def : "\<tau> \<Turnstile> \<delta> X"
      and x_val : "\<tau> \<Turnstile> \<upsilon> x"
    shows "finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 proof -
  have C : "\<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert X_def x_val, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 show "?thesis"
  by(insert X_def x_val,
     auto simp: OclIncluding_def Abs_Set_0_inverse[OF C]
          dest: foundation13[THEN iffD2, THEN foundation22[THEN iffD1]])
qed

lemma including_includes_generic :
 assumes includes_execute_generic [simp] : "\<And>X x y. (X->including(x::('\<AA>,'a::null)val)->includes(y)) =
       (if \<delta> X then if x \<doteq> y then true else X->includes(y) endif else invalid endif)"
     and StrictRefEq_strict'' : "\<And>x y. \<delta> ((x::('\<AA>,'a::null)val) \<doteq> y) = (\<upsilon>(x) and \<upsilon>(y))"
     and a_val : "\<tau> \<Turnstile> \<upsilon> a"
     and x_val : "\<tau> \<Turnstile> \<upsilon> x"
     and S_incl : "\<tau> \<Turnstile> (S)->includes((x::('\<AA>,'a::null)val))"
   shows "\<tau> \<Turnstile> S->including((a::('\<AA>,'a::null)val))->includes(x)"
proof -
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis OCL_core.bot_fun_def foundation1 foundation18' valid3)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False" by (metis bot_fun_def discr_eq_bot1_true)
 have discr_neq_invalid_true : "\<And>\<tau>. (invalid \<tau> \<noteq> true \<tau>) = True" by (metis discr_eq_bot2_true invalid_def)
 have discr_eq_invalid_true : "\<And>\<tau>. (invalid \<tau> = true \<tau>) = False" by (metis bot_option_def invalid_def option.simps(2) true_def)
show ?thesis
  apply(simp)
  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S")
   prefer 2
   apply(insert S_incl[simplified OclIncludes_def], simp add:  OclValid_def)
   apply(metis discr_eq_bot2_true)
  apply(simp add: cp_OclIf[of "\<delta> S"] OclValid_def OclIf_def discr_neq_invalid_true discr_eq_invalid_true x_val[simplified OclValid_def])
 by (metis OclValid_def S_incl StrictRefEq_strict'' a_val foundation10 foundation6 x_val)
qed

lemmas including_includes = including_includes_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict'']

lemma including_rep_set:
 assumes S_def: "\<tau> \<Turnstile> \<delta> S"
   shows "\<lceil>\<lceil>Rep_Set_0 (S->including(\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) \<tau>)\<rceil>\<rceil> = insert \<lfloor>\<lfloor>x\<rfloor>\<rfloor> \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
 apply(simp add: OclIncluding_def S_def[simplified OclValid_def])
 apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF S_def], metis bot_option_def not_Some_eq)
by(simp)

lemma including_notempty_rep_set:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
  shows "\<lceil>\<lceil>Rep_Set_0 (X->including(a) \<tau>)\<rceil>\<rceil> \<noteq> {}"
 apply(simp add: OclIncluding_def X_def[simplified OclValid_def] a_val[simplified OclValid_def])
 apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF X_def], metis a_val foundation18')
by(simp)

lemma including_includes_simp:
 assumes "\<tau> \<Turnstile> X->includes(x)"
   shows "X->including(x) \<tau> = X \<tau>"
proof -
 have includes_def: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
 by (metis OCL_core.bot_fun_def OclIncludes_def OclValid_def defined3 foundation16)

 have includes_val: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
 by (metis (hide_lams, no_types) foundation6 includes_valid_args_valid' including_valid_args_valid including_valid_args_valid'')

 show ?thesis
  apply(insert includes_def[OF assms] includes_val[OF assms] assms, simp add: OclIncluding_def OclIncludes_def OclValid_def true_def)
  apply(drule insert_absorb, simp, subst abs_rep_simp')
 by(simp_all add: OclValid_def true_def)
qed

subsection{* OclExcluding *}

lemma excluding_charn0[simp]:
assumes val_x:"\<tau> \<Turnstile> (\<upsilon> x)"
shows         "\<tau> \<Turnstile> ((Set{}->excluding(x))  \<triangleq>  Set{})"
proof -
  have A : "\<lfloor>None\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: null_option_def bot_option_def)
  have B : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)

  show ?thesis using val_x
    apply(auto simp: OclValid_def OclIncludes_def OclNot_def false_def true_def StrongEq_def
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
      apply(simp add: cp_OclIf[symmetric] cp_OclExcluding[symmetric] cp_valid[symmetric] A)
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
          apply(insert def_X val_x, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 have D : "\<lfloor>\<lfloor>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> - {y \<tau>}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(insert def_X val_x, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
          done
 have E : "x \<tau> \<noteq> y \<tau>"
          apply(insert neq)
          by(auto simp: OclValid_def bot_fun_def OclIncluding_def OclIncludes_def
                        false_def true_def defined_def valid_def bot_Set_0_def
                        null_fun_def null_Set_0_def StrongEq_def OclNot_def)

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
  apply(subst cp_defined, simp)+
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
          apply(insert def_X val_x, frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
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

lemma excluding_charn_exec:
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
           apply(subst cp_OclIf)
           apply(subst StrictRefEq_vs_StrongEq[THEN foundation22[THEN iffD1]])
           by(simp_all add: cp_OclIf[symmetric])

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
schematic_lemma excluding_charn_exec_int[simp,code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict1 StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2
                                StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid
                             cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_vs_StrongEq], simp_all)

schematic_lemma excluding_charn_exec_bool[simp,code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict1 StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_strict2
                                StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_defined_args_valid
                             cp_StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n_vs_StrongEq], simp_all)

schematic_lemma excluding_charn_exec_set[simp,code_unfold]: "?X"
by(rule excluding_charn_exec[OF StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict1 StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strict2
                                StrictRefEq\<^sub>S\<^sub>e\<^sub>t_strictEq_valid_args_valid
                             cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrictRefEq\<^sub>S\<^sub>e\<^sub>t_vs_StrongEq], simp_all)


lemma finite_excluding_rep_set :
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

lemma excluding_rep_set:
 assumes S_def: "\<tau> \<Turnstile> \<delta> S"
   shows "\<lceil>\<lceil>Rep_Set_0 (S->excluding(\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>) \<tau>)\<rceil>\<rceil> = \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {\<lfloor>\<lfloor>x\<rfloor>\<rfloor>}"
 apply(simp add: OclExcluding_def S_def[simplified OclValid_def])
 apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
 apply(insert Set_inv_lemma[OF S_def], metis Diff_iff bot_option_def not_None_eq)
by(simp)

subsection{* OclSize *}

lemma OclSize_infinite:
assumes non_finite:"\<tau> \<Turnstile> not(\<delta>(S->size()))"
shows   "(\<tau> \<Turnstile> not(\<delta>(S))) \<or> \<not> finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>"
apply(insert non_finite, simp)
apply(rule impI)
apply(simp add: OclSize_def OclValid_def defined_def)
apply(case_tac "finite \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>",
      simp_all add:null_fun_def null_option_def bot_fun_def bot_option_def)
done

lemma [simp,code_unfold]: "Set{} ->size() = \<zero>"
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
 by(simp add: A1 Abs_Set_0_inverse bot_fun_def bot_option_def null_fun_def null_option_def OclInt0_def)
qed

lemma [simp,code_unfold]: "\<delta> (Set{} ->size()) = true"
by simp


lemma including_size_defined[simp,code_unfold]: "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac "P \<tau> = \<bottom>", simp_all add: true_def)

 have finite_including_rep_set : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                 finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil> = finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_including_rep_set)
  apply(metis OclValid_def foundation5)+
 done

 have card_including_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> = (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
  apply(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)
 done

 show ?thesis

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->including(x)->size())) \<tau> = true \<tau>", simp)
  apply(subst cp_OclAnd)
  apply(subst cp_defined)
  apply(simp only: cp_defined[of "X->including(x)->size()"])
  apply(simp add: OclSize_def)
  apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->including(x) \<tau>)\<rceil>\<rceil>)", simp)
  prefer 2
  apply(simp)
  apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def)
  apply(erule conjE)
  apply(simp add: finite_including_rep_set[simplified OclValid_def] card_including_exec
                  cp_OclAnd[of "\<delta> X" "\<upsilon> x"]
                  cp_OclAnd[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_OclAnd[THEN sym])

  apply(drule defined_inject_true[of "X->including(x)->size()"], simp)
  apply(simp only: cp_OclAnd[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->including(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def card_including_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: finite_including_rep_set[simplified OclValid_def] card_including_exec)
  apply(simp only: cp_OclAnd[THEN sym])
  apply(simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
  apply(simp add: finite_including_rep_set[simplified OclValid_def])
  apply(simp add: finite_including_rep_set[simplified OclValid_def] card_including_exec)
  apply(simp only: cp_OclAnd[THEN sym])
  apply(simp)
  apply(rule impI)
  apply(erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_OclAnd[of "\<delta> X" "\<upsilon> x"])
  apply(drule valid_inject_true[of "x"], simp add: cp_OclAnd[of _ "\<upsilon> x"])
 done
qed

lemma including_size_exec[code_unfold]:
 "((X ->including(x)) ->size()) = (if \<delta> X and \<upsilon> x then
                                     X ->size() +\<^sub>o\<^sub>c\<^sub>l if X ->includes(x) then \<zero> else \<one> endif
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
  have includes_notin: "\<not> \<tau> \<Turnstile> X->includes(x) \<Longrightarrow> (\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau> \<Longrightarrow> x \<tau> \<notin> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  by(simp add: OclIncludes_def OclValid_def true_def)

  have includes_def: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<delta> X"
  by (metis OCL_core.bot_fun_def OclIncludes_def OclValid_def defined3 foundation16)

  have includes_val: "\<tau> \<Turnstile> X->includes(x) \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x"
  by (metis (hide_lams, no_types) foundation6 includes_valid_args_valid' including_valid_args_valid including_valid_args_valid'')

  show "X->including(x)->size() \<tau> = (if \<delta> X and \<upsilon> x then X->size() +\<^sub>I if X->includes(x) then \<zero> else \<one> endif else invalid endif) \<tau>"
    apply(case_tac "\<tau> \<Turnstile> \<delta> X and \<upsilon> x")
    apply(simp)
    apply(subst cp_OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r)
    apply(case_tac "\<tau> \<Turnstile> X->includes(x)", simp)

    apply(simp add: cp_OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r[symmetric])
    apply(case_tac "\<tau> \<Turnstile> ((\<upsilon> (X->size())) and not (\<delta> (X->size())))", simp)
    apply(drule foundation5[where P = "\<upsilon> X->size()"], erule conjE)
    apply(drule OclSize_infinite)
    apply(frule includes_def, drule includes_val)
    apply(simp)
    apply(subst OclSize_def, subst finite_including_rep_set, assumption, assumption)
    apply (metis (hide_lams, no_types) invalid_def)

    apply(subst OclIf_false')
    apply (metis (hide_lams, no_types) defined5 defined6 defined_and_I defined_not_I foundation1 foundation9)
    apply(subst cp_OclSize)
    apply(simp add: including_includes_simp cp_OclSize[symmetric])
    (* *)
    apply(subst OclIf_false', subst foundation9)
    apply (metis (hide_lams, no_types) includes_valid_args_valid', simp)
    apply(simp add: OclSize_def)
    apply(subst (1 2) finite_including_rep_set)
    apply (metis OclValid_def foundation5)
    apply (metis OclValid_def foundation5)
    apply(subst (1 2) cp_OclAnd, subst (1 2) cp_OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r)
    apply(simp)
    apply(rule conjI)
    apply(simp add: OclIncluding_def)
    apply(subst Abs_Set_0_inverse, simp add: bot_option_def null_option_def)
    apply (metis (hide_lams, no_types) Set_inv_lemma foundation18' foundation5)
    apply(drule foundation5)
    apply(subst (asm) (2 3) OclValid_def)
    apply(simp add: OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def OclInt1_def)
    apply(rule impI)
    apply(drule Finite_Set.card.insert[where x = "x \<tau>"])
    apply(rule includes_notin, simp)
    apply(simp)
    apply (metis Suc_eq_plus1 int_1 of_nat_add)


    apply(subst (1 2) OclAdd\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict2[simplified invalid_def], simp)
    apply(subst finite_including_rep_set)
    apply (metis OclValid_def foundation5)
    apply (metis OclValid_def foundation5)
    apply (metis OclValid_def foundation5)
    (* *)
    apply(subst OclIf_false')
    apply (metis (hide_lams, no_types) defined6 excluding_valid_args_valid'' foundation1 foundation9)
  by (metis cp_OclSize foundation18' including_valid_args_valid'' invalid_def size_strict1)
 qed
qed

lemma excluding_size_defined[simp,code_unfold]: "\<delta> ((X ->excluding(x)) ->size()) = (\<delta>(X->size()) and \<upsilon>(x))"
proof -

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def
                      bot_option_def null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have valid_inject_true : "\<And>\<tau> P. (\<upsilon> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
      apply(simp add: valid_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by(case_tac "P \<tau> = \<bottom>", simp_all add: true_def)


 have finite_excluding_rep_set : "\<And>\<tau>. (\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<Longrightarrow>
                                     finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil> =
                                     finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(rule finite_excluding_rep_set)
  apply(metis OclValid_def foundation5)+
 done

 have card_excluding_exec : "\<And>\<tau>. (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau> =
                                   (\<delta> (\<lambda>_. \<lfloor>\<lfloor>int (card \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)\<rfloor>\<rfloor>)) \<tau>"
  apply(simp add: defined_def bot_fun_def bot_option_def null_fun_def null_option_def)
 done

 show ?thesis

  apply(rule ext, rename_tac \<tau>)
  apply(case_tac "(\<delta> (X->excluding(x)->size())) \<tau> = true \<tau>", simp)
  apply(subst cp_OclAnd)
  apply(subst cp_defined)
  apply(simp only: cp_defined[of "X->excluding(x)->size()"])
  apply(simp add: OclSize_def)
  apply(case_tac "((\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X->excluding(x) \<tau>)\<rceil>\<rceil>)", simp)
  prefer 2
  apply(simp)
  apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def)
  apply(erule conjE)
  apply(simp add: finite_excluding_rep_set card_excluding_exec
                  cp_OclAnd[of "\<delta> X" "\<upsilon> x"]
                  cp_OclAnd[of "true", THEN sym])
  apply(subgoal_tac "(\<delta> X) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>", simp)
  apply(rule foundation5[of _ "\<delta> X" "\<upsilon> x", simplified OclValid_def], simp only: cp_OclAnd[THEN sym])

  apply(drule defined_inject_true[of "X->excluding(x)->size()"], simp)
  apply(simp only: cp_OclAnd[of "\<delta> (X->size())" "\<upsilon> x"])
  apply(simp add: cp_defined[of "X->excluding(x)->size()" ] cp_defined[of "X->size()" ])
  apply(simp add: OclSize_def finite_excluding_rep_set card_excluding_exec)
  apply(case_tac "(\<delta> X and \<upsilon> x) \<tau> = true \<tau> \<and> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>",
        simp add: finite_excluding_rep_set card_excluding_exec)
  apply(simp only: cp_OclAnd[THEN sym])
  apply(simp add: defined_def bot_fun_def)

  apply(split split_if_asm)
  apply(simp add: finite_excluding_rep_set)
  apply(simp add: finite_excluding_rep_set card_excluding_exec)
  apply(simp only: cp_OclAnd[THEN sym])
  apply(simp)
  apply(rule impI)
  apply(erule conjE)
  apply(case_tac "(\<upsilon> x) \<tau> = true \<tau>", simp add: cp_OclAnd[of "\<delta> X" "\<upsilon> x"])
  apply(drule valid_inject_true[of "x"], simp add: cp_OclAnd[of _ "\<upsilon> x"])
 done
qed

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

lemma [simp]:
 assumes X_finite: "\<And>\<tau>. finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 shows "\<delta> ((X ->including(x)) ->size()) = (\<delta>(X) and \<upsilon>(x))"
by(simp add: size_defined[OF X_finite])

subsection{* OclIsEmpty *}

lemma [simp,code_unfold]: "Set{}->isEmpty() = true"
by(simp add: OclIsEmpty_def)

lemma including_not_isempty [simp]:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and X_finite: "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
shows "X->including(a)->isEmpty() \<tau> = false \<tau>"
proof -
 have A1 : "\<And>\<tau> X. X \<tau> = true \<tau> \<or> X \<tau> = false \<tau> \<Longrightarrow> (X and not X) \<tau> = false \<tau>"
 by (metis (no_types) OclAnd_false1 OclAnd_idem OclImplies_def OclNot3 OclNot_not OclOr_false1 cp_OclAnd cp_OclNot deMorgan1 deMorgan2)

 have defined_inject_true : "\<And>\<tau> P. (\<delta> P) \<tau> \<noteq> true \<tau> \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
      apply(simp add: defined_def true_def false_def bot_fun_def bot_option_def
                      null_fun_def null_option_def)
      by (case_tac " P \<tau> = \<bottom> \<or> P \<tau> = null", simp_all add: true_def)

 have B : "\<And>X \<tau>. \<tau> \<Turnstile> \<upsilon> X \<Longrightarrow> X \<tau> \<noteq> \<zero> \<tau> \<Longrightarrow> (X \<doteq> \<zero>) \<tau> = false \<tau>"
 by (metis OclAnd_true2 OclValid_def Sem_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict'' StrongEq_sym bool_split foundation16 foundation22 invalid_def null_fun_def null_non_OclInt0 valid4)

 show ?thesis
  apply(simp add: OclIsEmpty_def)
  apply(subst cp_OclOr)
  apply(subst A1)
  apply(metis (hide_lams, no_types) defined_inject_true excluding_valid_args_valid')
  apply(simp add: cp_OclOr[symmetric])
  apply(rule B)
  apply(rule foundation20, simp)
  apply (metis (hide_lams, no_types) X_finite X_def a_val foundation10 foundation6 size_defined')
  apply(simp add: OclSize_def finite_including_rep_set[OF X_def a_val] X_finite OclInt0_def)
 by (metis OclValid_def X_def a_val foundation10 foundation6 including_notempty_rep_set[OF X_def a_val])
qed

subsection{* OclNotEmpty *}

lemma [simp,code_unfold]: "Set{}->notEmpty() = false"
by(simp add: OclNotEmpty_def)

lemma including_notempty_true [simp,code_unfold]:
assumes X_def: "\<tau> \<Turnstile> \<delta> X"
    and X_finite: "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
    and a_val: "\<tau> \<Turnstile> \<upsilon> a"
shows "X->including(a)->notEmpty() \<tau> = true \<tau>"
 apply(simp add: OclNotEmpty_def)
 apply(subst cp_OclNot, subst including_not_isempty, simp_all add: assms)
by (metis OclNot4 cp_OclNot)

subsection{* Ocl Any *}

lemma [simp,code_unfold]: "Set{}->any() = null"
 apply(rule ext, simp add: Ocl_Any_def)
 apply(rule impI)
 apply(simp add: false_def true_def)
done

lemma any_exec[simp,code_unfold]:
      "(Set{}->including(a))->any() = a"
 apply(rule ext, rename_tac \<tau>, simp add: mtSet_def Ocl_Any_def)
 apply(case_tac "\<tau> \<Turnstile> \<upsilon> a")
 apply(simp add: OclValid_def mtSet_defined[simplified mtSet_def] mtSet_valid[simplified mtSet_def] mtSet_rep_set[simplified mtSet_def])
 apply(subst (1 2) cp_OclAnd,
       subst (1 2) including_notempty_true[where X = "Set{}", simplified mtSet_def])
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
 apply(subst (1 2 3 4) cp_OclAnd, simp add: mtSet_defined[simplified mtSet_def] valid_def bot_fun_def)
 apply(simp add: cp_OclAnd[symmetric], rule impI, simp add: false_def true_def)
done

lemma any_exec_unfold[simp,code_unfold]:
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

 have notempty': "\<And>\<tau> X. \<tau> \<Turnstile> \<delta> X \<Longrightarrow> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> not (X->isEmpty()) \<tau> \<noteq> true \<tau> \<Longrightarrow> X \<tau> = Set{} \<tau>"
  apply(case_tac "X \<tau>", simp add: mtSet_def Abs_Set_0_inject)
  apply(erule disjE, metis (hide_lams, no_types) bot_Set_0_def bot_option_def foundation17)
  apply(erule disjE, metis (hide_lams, no_types) bot_option_def
                                                 null_Set_0_def null_option_def foundation17)
  apply(case_tac y, simp, metis (hide_lams, no_types) bot_Set_0_def foundation17)
  apply(case_tac a, simp)
  apply (metis (hide_lams, no_types) foundation17 null_Set_0_def)
  apply(simp add: OclIsEmpty_def OclSize_def)
    apply(subst (asm) cp_OclNot, subst (asm) cp_OclOr, subst (asm) cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r, subst (asm) cp_OclAnd, subst (asm) cp_OclNot)
    apply(simp only: OclValid_def foundation20[simplified OclValid_def]
                    cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
  apply(simp add: Abs_Set_0_inverse split: split_if_asm)
 by(simp add: true_def OclInt0_def OclNot_def StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def)

 have B: "\<And>X \<tau>. \<not> finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> (\<delta> (X->size())) \<tau> = false \<tau>"
  apply(subst cp_defined)
  apply(simp add: OclSize_def)
 by (metis OCL_core.bot_fun_def defined_def)

 show ?thesis
  apply(rule ext, rename_tac \<tau>, simp only: OclIncludes_def Ocl_Any_def)
  apply(subst cp_OclIf, subst (2) cp_valid)
  apply(case_tac "(\<delta> X) \<tau> = true \<tau>", simp only: foundation20[simplified OclValid_def] cp_OclIf[symmetric], simp,
        subst (1 2) cp_OclAnd, simp add: cp_OclAnd[symmetric])
  apply(case_tac "finite \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>")
  apply(frule size_defined'[THEN iffD2, simplified OclValid_def], assumption)
  apply(subst (1 2 3 4) cp_OclIf) apply(simp)
  apply(subst (1 2 3 4) cp_OclIf[symmetric], simp)
  apply(case_tac "(X->notEmpty()) \<tau> = true \<tau>", simp)
  apply(frule notempty_has_elt[simplified OclValid_def], simp)
  apply(simp add: OclNotEmpty_def cp_OclIf[symmetric])
  apply(subgoal_tac "(SOME y. y \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>) \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>", simp add: true_def)
  apply(metis OclValid_def Set_inv_lemma foundation18' null_option_def true_def)
  apply(rule someI_ex, simp)
  apply(simp add: OclNotEmpty_def cp_valid[symmetric])
  apply(subgoal_tac "\<not> (null \<tau> \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)", simp)
  apply(subst OclIsEmpty_def, simp add: OclSize_def)
  apply(subst cp_OclNot, subst cp_OclOr, subst cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r, subst cp_OclAnd, subst cp_OclNot,
        simp add: OclValid_def foundation20[simplified OclValid_def]
                  cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
  apply(frule notempty'[simplified OclValid_def], (simp add: mtSet_def Abs_Set_0_inverse OclInt0_def false_def)+)
  apply(drule notempty'[simplified OclValid_def], simp, simp)
  apply (metis (hide_lams, no_types) empty_iff mtSet_rep_set)
  (* *)
  apply(frule B)
  apply(subst (1 2 3 4) cp_OclIf)
  apply(simp)
   apply(subst (1 2 3 4) cp_OclIf[symmetric], simp)
  apply(case_tac "(X->notEmpty()) \<tau> = true \<tau>", simp)
  apply(frule notempty_has_elt[simplified OclValid_def], simp)
  apply(simp add: OclNotEmpty_def OclIsEmpty_def)
  apply(subgoal_tac "X->size() \<tau> = \<bottom>")
  prefer 2
  apply (metis (hide_lams, no_types) OclSize_def)
    apply(subst (asm) cp_OclNot, subst (asm) cp_OclOr, subst (asm) cp_StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r, subst (asm) cp_OclAnd, subst (asm) cp_OclNot)
    apply(simp add: OclValid_def foundation20[simplified OclValid_def]
                    cp_OclNot[symmetric] cp_OclAnd[symmetric] cp_OclOr[symmetric])
  apply(simp add: OclNot_def
   StrongEq_def
   StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r valid_def bot_option_def bot_fun_def false_def true_def invalid_def)

  apply (metis OCL_core.bot_fun_def null_fun_def null_is_valid valid_def)

 by(drule defined_inject_true, simp add: false_def true_def OclIf_false[simplified false_def] invalid_def)
qed

subsection{* OclForall *}

lemma forall_set_null_exec[simp,code_unfold] :
"(null->forAll(z| P(z))) = invalid"
by(simp add: OclForall_def invalid_def false_def true_def)

lemma forall_set_mt_exec[simp,code_unfold] :
"((Set{})->forAll(z| P(z))) = true"
apply(simp add: OclForall_def)
apply(subst mtSet_def)+
apply(subst Abs_Set_0_inverse, simp_all add: true_def)+
done

lemma forall_set_including_exec[simp,code_unfold] :
 assumes cp0 : "cp P"
 shows "((S->including(x))->forAll(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                 then P x and (S->forAll(z | P(z)))
                                                 else invalid
                                                 endif)"
proof -
 have cp: "\<And>\<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
    by(insert cp0, auto simp: cp_def)

 have insert_in_Set_0 : "\<And>\<tau>. (\<tau> \<Turnstile>(\<delta> S)) \<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<Longrightarrow> \<lfloor>\<lfloor>insert (x \<tau>) \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          apply(frule Set_inv_lemma)
          apply(simp add: foundation18 invalid_def)
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
 have cp_OclNot_eq : "\<And>\<tau> v. (P x \<tau> \<noteq> v) = (P (\<lambda>_. x \<tau>) \<tau> \<noteq> v)" by(subst cp, simp)

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
  apply(simp add: OclIf_def)
  apply(simp add: cp_defined[of "\<delta> S and \<upsilon> x"])
  apply(simp add: cp_defined[THEN sym])
  apply(rule conjI, rule impI)

  apply(subgoal_tac "\<tau> \<Turnstile> \<delta> S")
    prefer 2
    apply(drule foundation5[simplified OclValid_def], erule conjE)+ apply(simp add: OclValid_def)

  apply(subst OclForall_def)
  apply(simp add: cp_OclAnd[THEN sym] OclValid_def
                  foundation10'[where x = "\<delta> S" and y = "\<upsilon> x", simplified OclValid_def])

  apply(subgoal_tac "\<tau> \<Turnstile> (\<delta> S and \<upsilon> x)")
    prefer 2
    apply(simp add: OclValid_def)

  (* false *)
    (* false YES *)
  apply(case_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau>", simp_all)
  apply(subst contradict_Rep_Set_0[where f = "\<lambda> x \<tau>. P x \<tau> = false \<tau>"], simp)+
  apply(simp add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = false \<tau>", OF cp_eq])

  apply(simp add: cp_OclAnd[of "P x"])
  apply(erule disjE)
  apply(simp only: cp_OclAnd[symmetric], simp)

  apply(subgoal_tac "OclForall S P \<tau> = false \<tau>")
  apply(simp only: cp_OclAnd[symmetric], simp)
  apply(simp add: OclForall_def)

    (* false NO *)
  apply(simp add: forall_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> \<noteq> false \<tau>", OF cp_OclNot_eq],
        erule conjE)

  (* bot *)
    (* bot YES *)
  apply(case_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = bot \<tau>", simp_all)
  apply(subst contradict_Rep_Set_0[where f = "\<lambda> x \<tau>. P x \<tau> = bot \<tau>"], simp)+
  apply(simp add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = bot \<tau>", OF cp_eq])

  apply(simp add: cp_OclAnd[of "P x"])
  apply(erule disjE)

  apply(subgoal_tac "OclForall S P \<tau> \<noteq> false \<tau>")
  apply(simp only: cp_OclAnd[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

  apply(subgoal_tac "OclForall S P \<tau> = bot \<tau>")
  apply(simp only: cp_OclAnd[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

    (* bot NO *)
  apply(simp add: forall_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> \<noteq> bot \<tau>", OF cp_OclNot_eq],
        erule conjE)

  (* null *)
    (* null YES *)
  apply(case_tac "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S->including(x) \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau>", simp_all)
  apply(subst contradict_Rep_Set_0[where f = "\<lambda> x \<tau>. P x \<tau> = null \<tau>"], simp)+
  apply(simp add: exists_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> = null \<tau>", OF cp_eq])

  apply(simp add: cp_OclAnd[of "P x"])
  apply(erule disjE)

  apply(subgoal_tac "OclForall S P \<tau> \<noteq> false \<tau> \<and> OclForall S P \<tau> \<noteq> bot \<tau>")
  apply(simp only: cp_OclAnd[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

  apply(subgoal_tac "OclForall S P \<tau> = null \<tau>")
  apply(simp only: cp_OclAnd[symmetric], simp)
  apply(simp add: OclForall_def null_fun_def null_option_def bot_fun_def bot_option_def true_def false_def)

    (* null NO *)
  apply(simp add: forall_including_invert[where f = "\<lambda> x \<tau>. P x \<tau> \<noteq> null \<tau>", OF cp_OclNot_eq],
        erule conjE)

  (* true *)
  apply(simp add: cp_OclAnd[of "P x"] OclForall_def)
  apply(subgoal_tac "P x \<tau> = true \<tau>", simp)
  apply(metis bot_fun_def bool_split foundation18' foundation2 valid1)

  (* invalid *)
  by(metis OclForall_def including_defined_args_valid' invalid_def)
qed




lemma forall_includes :
 assumes x_def : "\<tau> \<Turnstile> \<delta> x"
     and y_def : "\<tau> \<Turnstile> \<delta> y"
   shows "(\<tau> \<Turnstile> OclForall x (OclIncludes y)) = (\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>)"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis defined3 defined_def discr_eq_false_true)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False" by (metis bot_fun_def discr_eq_bot1_true)
 have discr_eq_null_true : "\<And>\<tau>. (null \<tau> = true \<tau>) = False" by (metis OclValid_def foundation4)
 show ?thesis
  apply(case_tac "\<tau> \<Turnstile> OclForall x (OclIncludes y)")
  (* *)
  apply(simp add: OclValid_def OclForall_def)
  apply(split split_if_asm, simp_all add: discr_eq_false_true discr_eq_bot1_true discr_eq_null_true discr_eq_bot2_true)+
  apply(subgoal_tac "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>. (\<tau> \<Turnstile> y->includes((\<lambda>_. x)))")
   prefer 2
   apply(simp add: OclValid_def)
   apply (metis (full_types) bot_fun_def bool_split invalid_def null_fun_def)
  apply(rule subsetI, rename_tac e)
  apply(drule_tac P = "\<lambda>x. \<tau> \<Turnstile> y->includes((\<lambda>_. x))" and x = e in ballE) prefer 3 apply assumption
  apply(simp add: OclIncludes_def OclValid_def)
  apply (metis discr_eq_bot2_true option.inject true_def)
  apply(simp)

  (* *)
  apply(simp add: OclValid_def OclForall_def x_def[simplified OclValid_def])
  apply(subgoal_tac "(\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>. (y->includes((\<lambda>_. x))) \<tau> = false \<tau>
                                           \<or> (y->includes((\<lambda>_. x))) \<tau> = \<bottom> \<tau>
                                           \<or> (y->includes((\<lambda>_. x))) \<tau> = null \<tau>)")
   prefer 2
   apply metis
  apply(erule bexE, rename_tac e)
  apply(simp add: OclIncludes_def y_def[simplified OclValid_def])

  apply(case_tac "\<tau> \<Turnstile> \<upsilon> (\<lambda>_. e)", simp add: OclValid_def)
  apply(erule disjE)
  apply(metis (mono_tags) discr_eq_false_true set_mp true_def)
  apply(simp add: bot_fun_def bot_option_def null_fun_def null_option_def)
  apply(erule contrapos_nn[OF _ Set_inv_lemma'[OF x_def]], simp)
 done
qed

lemma forall_not_includes :
 assumes x_def : "\<tau> \<Turnstile> \<delta> x"
     and y_def : "\<tau> \<Turnstile> \<delta> y"
   shows "(OclForall x (OclIncludes y) \<tau> = false \<tau>) = (\<not> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>)"
proof -
 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_eq_null_true : "\<And>\<tau>. (null \<tau> = true \<tau>) = False" by (metis OclValid_def foundation4)
 have discr_eq_null_false : "\<And>\<tau>. (null \<tau> = false \<tau>) = False" by (metis defined4 foundation1 foundation16 null_fun_def)
 have discr_neq_false_true : "\<And>\<tau>. (false \<tau> \<noteq> true \<tau>) = True" by (metis discr_eq_false_true)
 have discr_neq_true_false : "\<And>\<tau>. (true \<tau> \<noteq> false \<tau>) = True" by (metis discr_eq_false_true)
 have discr_eq_bot1_true : "\<And>\<tau>. (\<bottom> \<tau> = true \<tau>) = False" by (metis defined3 defined_def discr_eq_false_true)
 have discr_eq_bot2_true : "\<And>\<tau>. (\<bottom> = true \<tau>) = False" by (metis bot_fun_def discr_eq_bot1_true)
 have discr_eq_bot1_false : "\<And>\<tau>. (\<bottom> \<tau> = false \<tau>) = False" by (metis OCL_core.bot_fun_def defined4 foundation1 foundation16)
 have discr_eq_bot2_false : "\<And>\<tau>. (\<bottom> = false \<tau>) = False" by (metis foundation1 foundation18' valid4)
 show ?thesis
  apply(subgoal_tac "\<not> (OclForall x (OclIncludes y) \<tau> = false \<tau>) = (\<not> (\<not> \<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil> \<subseteq> \<lceil>\<lceil>Rep_Set_0 (y \<tau>)\<rceil>\<rceil>))", simp)
  apply(subst forall_includes[symmetric], simp add: x_def, simp add: y_def)
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
  apply(simp add: x_def[simplified OclValid_def])
  apply(subgoal_tac "(\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (x \<tau>)\<rceil>\<rceil>. ((y->includes((\<lambda>_. x))) \<tau> = true \<tau> \<or> (y->includes((\<lambda>_. x))) \<tau> = false \<tau>))")
  apply(metis bot_fun_def discr_eq_bot2_true discr_eq_null_true null_fun_def)
  apply(rule ballI, rename_tac e)
  apply(simp add: OclIncludes_def, rule conjI)
  apply (metis (full_types) false_def true_def)

  apply(simp add: y_def[simplified OclValid_def], rule impI)
  apply(drule contrapos_nn[OF _ Set_inv_lemma'[OF x_def], simplified OclValid_def], blast +)
 done
qed

lemma forall_iterate:
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
  apply(case_tac a) apply (metis null_Boolean_def)
  apply(case_tac aa) apply (metis (full_types) true_def)
 by (metis (full_types) false_def)

 have disjE4 : "\<And> P1 P2 P3 P4 R.
   (P1 \<or> P2 \<or> P3 \<or> P4) \<Longrightarrow> (P1 \<Longrightarrow> R) \<Longrightarrow> (P2 \<Longrightarrow> R) \<Longrightarrow> (P3 \<Longrightarrow> R) \<Longrightarrow> (P4 \<Longrightarrow> R) \<Longrightarrow> R"
 by metis

 show ?thesis
  apply(simp only: OclForall_def OclIterate\<^sub>S\<^sub>e\<^sub>t_def)
  apply(case_tac "\<tau> \<Turnstile> \<delta> S", simp only: OclValid_def)
  apply(subgoal_tac "(if \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau> then false \<tau>
               else if \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = \<bottom> \<tau> then \<bottom> \<tau>
                    else if \<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = null \<tau> then null \<tau>
                         else true \<tau>) = Finite_Set.fold (\<lambda>x acc. acc and P x) true ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>) \<tau>",
        simp add: S_finite)
  apply(case_tac "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> = {}", simp)
  apply(rule finite_ne_induct[where P = "\<lambda>set. (if \<exists>x\<in>set. P (\<lambda>_. x) \<tau> = false \<tau> then false \<tau>
      else if \<exists>x\<in>set. P (\<lambda>_. x) \<tau> = \<bottom> \<tau> then \<bottom> \<tau>
           else if \<exists>x\<in>set. P (\<lambda>_. x) \<tau> = null \<tau> then null \<tau> else true \<tau>) =
     Finite_Set.fold (\<lambda>x acc. acc and P x) true ((\<lambda>a \<tau>. a) ` set) \<tau>", OF S_finite])
  apply(simp)
  (* *)
  apply(simp only: image_insert)
  apply(subst comp_fun_commute.fold_insert[OF and_comm], simp)
  apply (metis empty_iff image_empty)
  apply(simp)
  apply (metis OCL_core.bot_fun_def destruct_ocl null_fun_def)
  (* *)
  apply(simp only: image_insert)
  apply(subst comp_fun_commute.fold_insert[OF and_comm], simp)
  apply (metis (mono_tags) imageE)

  (* *)
  apply(subst cp_OclAnd) apply(drule sym, drule sym, simp only:)
  apply(simp only: ex_insert)
  apply(subgoal_tac "\<exists>x. x\<in>F") prefer 2
  apply(metis all_not_in_conv)
  proof - fix x F show "(\<delta> S) \<tau> = true \<tau> \<Longrightarrow> \<exists>x. x \<in> F \<Longrightarrow>
           (if P (\<lambda>_. x) \<tau> = false \<tau> \<or> (\<exists>x\<in>F. P (\<lambda>_. x) \<tau> = false \<tau>) then false \<tau>
            else if P (\<lambda>_. x) \<tau> = \<bottom> \<tau> \<or> (\<exists>x\<in>F. P (\<lambda>_. x) \<tau> = \<bottom> \<tau>) then \<bottom> \<tau>
                 else if P (\<lambda>_. x) \<tau> = null \<tau> \<or> (\<exists>x\<in>F. P (\<lambda>_. x) \<tau> = null \<tau>) then null \<tau> else (\<delta> S) \<tau>) =
           ((\<lambda>_. if \<exists>x\<in>F. P (\<lambda>_. x) \<tau> = false \<tau> then false \<tau>
                 else if \<exists>x\<in>F. P (\<lambda>_. x) \<tau> = \<bottom> \<tau> then \<bottom> \<tau>
                      else if \<exists>x\<in>F. P (\<lambda>_. x) \<tau> = null \<tau> then null \<tau> else (\<delta> S) \<tau>) and
            (\<lambda>_. P (\<lambda>\<tau>. x) \<tau>))
            \<tau>"
   apply(cut_tac destruct_ocl[where x = "P (\<lambda>\<tau>. x) \<tau>" and \<tau> = \<tau>])
   apply(erule disjE4)
   apply(simp_all add: true_def false_def null_fun_def null_option_def bot_fun_def bot_option_def OclAnd_def)
  by (metis (lifting) option.distinct(1))+
  apply_end(simp add: OclValid_def)+
 qed
qed

subsection{* OclExists *}

lemma exists_set_null_exec[simp,code_unfold] :
"(null->exists(z | P(z))) = invalid"
by(simp add: OclExists_def)

lemma exists_set_mt_exec[simp,code_unfold] :
"((Set{})->exists(z | P(z))) = false"
by(simp add: OclExists_def)

lemma exists_set_including_exec[simp,code_unfold] :
 assumes cp: "cp P"
 shows "((S->including(x))->exists(z | P(z))) = (if \<delta> S and \<upsilon> x
                                                 then P x or (S->exists(z | P(z)))
                                                 else invalid
                                                 endif)"
 by(simp add: OclExists_def OclOr_def forall_set_including_exec cp OclNot_inject)


subsection{* OclIterate *}

lemma OclIterate\<^sub>S\<^sub>e\<^sub>t_infinite:
assumes non_finite: "\<tau> \<Turnstile> not(\<delta>(S->size()))"
shows "(OclIterate\<^sub>S\<^sub>e\<^sub>t S A F) \<tau> = invalid \<tau>"
apply(insert non_finite [THEN OclSize_infinite])
apply(erule disjE)
apply(simp_all add: OclIterate\<^sub>S\<^sub>e\<^sub>t_def invalid_def)
apply(erule contrapos_np)
apply(simp add: OclValid_def)
done

lemma OclIterate\<^sub>S\<^sub>e\<^sub>t_empty[simp,code_unfold]: "((Set{})->iterate(a; x = A | P a x)) = A"
proof -
 have A1 : "\<lfloor>\<lfloor>{}\<rfloor>\<rfloor> \<in> {X. X = bot \<or> X = null \<or> (\<forall>x\<in>\<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}" by(simp add: mtSet_def)
 have C : "\<And> \<tau>. (\<delta> (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor>{}\<rfloor>\<rfloor>)) \<tau> = true \<tau>"
 by (metis A1 Abs_Set_0_cases Abs_Set_0_inverse cp_defined defined_def false_def mtSet_def mtSet_defined null_fun_def null_option_def null_set_OclNot_defined true_def)
 show ?thesis
      apply(simp add: OclIterate\<^sub>S\<^sub>e\<^sub>t_def mtSet_def Abs_Set_0_inverse valid_def C)
      apply(rule ext)
      apply(case_tac "A \<tau> = \<bottom> \<tau>", simp_all, simp add:true_def false_def bot_fun_def)
      apply(simp add: A1 Abs_Set_0_inverse)
 done
qed

text{* In particular, this does hold for A = null. *}

lemma OclIterate\<^sub>S\<^sub>e\<^sub>t_including:
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
          apply(simp add: foundation18 invalid_def)
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
  apply(simp add: foundation18 invalid_def)
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
  apply(simp only: cp_OclIterate\<^sub>S\<^sub>e\<^sub>t[of "S->including(a)"] cp_OclIterate\<^sub>S\<^sub>e\<^sub>t[of "S->excluding(a)"])
  apply(subst OclIncluding_def, subst OclExcluding_def)
  apply(case_tac "\<not> ((\<delta> S) \<tau> = true \<tau> \<and> (\<upsilon> a) \<tau> = true \<tau>)", simp)

  apply(subgoal_tac "OclIterate\<^sub>S\<^sub>e\<^sub>t (\<lambda>_. \<bottom>) A F \<tau> = OclIterate\<^sub>S\<^sub>e\<^sub>t (\<lambda>_. \<bottom>) (F a A) F \<tau>", simp)
  apply(rule conjI)
  apply(blast)
  apply(blast)
  apply(auto)

  apply(simp add: OclIterate\<^sub>S\<^sub>e\<^sub>t_def) apply(auto)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)

  apply(simp add: OclIterate\<^sub>S\<^sub>e\<^sub>t_def) apply(auto)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)
  apply(simp add: defined_def bot_option_def bot_fun_def false_def true_def)

  apply(simp add: OclIterate\<^sub>S\<^sub>e\<^sub>t_def)

  apply(subst abs_rep[OF insert_in_Set_0[simplified OclValid_def], of \<tau>], simp_all)+
  apply(subst abs_rep[OF remove_in_Set_0[simplified OclValid_def], of \<tau>], simp_all)+
  apply(subst insert_defined, simp_all add: OclValid_def)+
  apply(subst remove_defined, simp_all add: OclValid_def)+

  apply(case_tac "\<not> ((\<upsilon> A) \<tau> = true \<tau>)", simp add: F_valid_arg)
  apply(simp add: valid_inject_true F_valid_arg)
  apply(rule impI)
  apply(subst Finite_Set.comp_fun_commute.fold_fun_left_comm[where f = F and z = A and x = a and A = "((\<lambda>a \<tau>. a) ` (\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> - {a \<tau>}))", symmetric, OF F_commute])
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

subsection{* OclSelect *}

lemma select_set_mt_exec[code_unfold, simp]: "OclSelect\<^sub>s\<^sub>e\<^sub>t mtSet P = mtSet"
 apply(rule ext, rename_tac \<tau>)
 apply(simp add: OclSelect\<^sub>s\<^sub>e\<^sub>t_def mtSet_def defined_def false_def true_def bot_Set_0_def null_Set_0_def null_fun_def bot_fun_def)
 apply(subst (1 2 3 4 5) Abs_Set_0_inverse)
 apply(simp add: null_option_def bot_option_def)+
 apply(subst Abs_Set_0_inject)
 apply(simp add: null_option_def bot_option_def)+
done

lemma select_set_including_exec[simp,code_unfold]:
"OclSelect\<^sub>s\<^sub>e\<^sub>t (X->including(y)) P =
 (if  \<delta> X  then
   if  \<upsilon> y  then
     if \<delta>(X->size()) then
        if P y  then (OclSelect\<^sub>s\<^sub>e\<^sub>t X P)->including(y)
        else (OclSelect\<^sub>s\<^sub>e\<^sub>t X P)
        endif
     else invalid
     endif
   else invalid
   endif
 else invalid
endif)"
sorry

subsection{* Strict Equality *}

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

 have defined_inject_true : "\<And>\<tau> P. \<not> (\<tau> \<Turnstile> \<delta> P) \<Longrightarrow> (\<delta> P) \<tau> = false \<tau>"
 by(metis bot_fun_def defined_def foundation16 null_fun_def)

 have valid_inject_true : "\<And>\<tau> P. \<not> (\<tau> \<Turnstile> \<upsilon> P) \<Longrightarrow> (\<upsilon> P) \<tau> = false \<tau>"
 by(metis bot_fun_def foundation18' valid_def)

 have valid_inject_defined : "\<And>\<tau> P. \<not> (\<tau> \<Turnstile> \<upsilon> P) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<delta> P)"
 by(metis foundation20)

 have null_simp : "\<And>\<tau> y. \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<delta> y) \<Longrightarrow> y \<tau> = null \<tau>"
 by (simp add: foundation16 foundation18' null_fun_def)

 have discr_eq_false_true : "\<And>\<tau>. (false \<tau> = true \<tau>) = False" by (metis OclValid_def foundation2)
 have discr_neq_true_false : "\<And>\<tau>. (true \<tau> \<noteq> false \<tau>) = True" by (metis discr_eq_false_true)

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
  apply(simp add: cp_OclIf[of "\<delta> x"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> x)")
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<delta> x)")
   prefer 2
   apply(metis foundation20)
  apply(simp add: defined_inject_true)
  apply(simp add: cp_OclIf[symmetric] OclValid_def StrictRefEq\<^sub>S\<^sub>e\<^sub>t)

  apply(simp)
  (* *)
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<upsilon> y)")
  apply(subgoal_tac "\<not> (\<tau> \<Turnstile> \<delta> y)")
   prefer 2
   apply(metis foundation20)
  apply(simp add: defined_inject_true)
  apply(simp add: cp_OclIf[symmetric] OclValid_def StrictRefEq\<^sub>S\<^sub>e\<^sub>t)

  apply(simp)
  (* *)
  apply(simp add: cp_OclIf[of "\<delta> y"])
  apply(simp add: cp_OclIf[symmetric])

  (* *)
  apply(simp add: cp_OclIf[of "\<delta> x"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> x)")
  apply(simp add: defined_inject_true)
  apply(simp add: cp_OclIf[symmetric])
  apply(simp add: cp_OclNot[of "\<delta> y"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> y)")
  apply(simp add: defined_inject_true)
  apply(simp add: cp_OclNot[symmetric])
  apply(metis (hide_lams, no_types) OclValid_def StrongEq_sym foundation22 null_fun_def null_simp StrictRefEq\<^sub>S\<^sub>e\<^sub>t_vs_StrongEq true_def)
  apply(simp add: OclValid_def cp_OclNot[symmetric])

  apply(simp add: null_simp[simplified OclValid_def, of x] StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def false_def)
  apply(simp add: defined_def[of y])
  apply(metis discr_neq_true_false)
  (* *)
  apply(simp)
  apply(simp add: OclValid_def)
  apply(simp add: cp_OclIf[of "\<delta> y"])
  apply(case_tac "\<not> (\<tau> \<Turnstile> \<delta> y)")
  apply(simp add: defined_inject_true)
  apply(simp add: cp_OclIf[symmetric])

  apply(drule null_simp[simplified OclValid_def, of y])
  apply(simp add: OclValid_def)
  apply(simp add: cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t[of x])
  apply(simp add: cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t[symmetric])
  apply(simp add: null_simp[simplified OclValid_def, of y] StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def false_def)
  apply(simp add: defined_def[of x])
  apply (metis discr_neq_true_false)

  (* *)
  apply(simp add: OclValid_def)


  apply(simp add: StrictRefEq\<^sub>S\<^sub>e\<^sub>t StrongEq_def)

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
  apply(simp add: cp_OclAnd[of "OclForall x (OclIncludes y)"] true_def OclValid_def)
  apply(simp add: OclValid_def)
  apply(simp add: forall_includes[simplified OclValid_def])

  (* *)
  apply(simp add: strongeq_false)

  apply(subgoal_tac "OclForall x (OclIncludes y) \<tau> = false \<tau> \<or> OclForall y (OclIncludes x) \<tau> = false \<tau>")
  apply(simp add: cp_OclAnd[of "OclForall x (OclIncludes y)"] false_def)
  apply(erule disjE)
   apply(simp)
   apply(subst cp_OclAnd[symmetric])
   apply(simp only: OclAnd_false1[simplified false_def])

   apply(simp)
   apply(subst cp_OclAnd[symmetric])
   apply(simp only: OclAnd_false2[simplified false_def])
  apply(simp add: forall_not_includes[simplified OclValid_def] rep_set_inj)
 done
qed



section{* Test Statements *}

lemma syntax_test: "Set{\<two>,\<one>} = (Set{}->including(\<one>)->including(\<two>))"
by (rule refl)

text{* Here is an example of a nested collection. Note that we have
to use the abstract null (since we did not (yet) define a concrete
constant @{term null} for the non-existing Sets) :*}
lemma semantic_test2:
assumes H:"(Set{\<two>} \<doteq> null) = (false::('\<AA>)Boolean)"
shows   "(\<tau>::('\<AA>)st) \<Turnstile> (Set{Set{\<two>},null}->includes(null))"
by(simp add: includes_execute_set H)

(* legacy --- still better names ?
lemmas defined_charn = foundation16
lemmas definedD = foundation17
lemmas valid_charn =
lemmas validD = foundation19
lemmas valid_implies_defined = foundation20
 end legacy *)

lemma short_cut'[simp,code_unfold]: "(\<eight> \<doteq> \<six>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt8_def OclInt6_def
                 true_def false_def invalid_def bot_option_def)
done

lemma short_cut''[simp,code_unfold]: "(\<two> \<doteq> \<one>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt2_def OclInt1_def
                 true_def false_def invalid_def bot_option_def)
done
lemma short_cut'''[simp,code_unfold]: "(\<one> \<doteq> \<two>) = false"
 apply(rule ext)
 apply(simp add: StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r StrongEq_def OclInt2_def OclInt1_def
                 true_def false_def invalid_def bot_option_def)
done

text{* Elementary computations on Sets.*}

value "\<not> (\<tau> \<Turnstile> \<upsilon>(invalid::('\<AA>,'\<alpha>::null) Set))"
value    "\<tau> \<Turnstile> \<upsilon>(null::('\<AA>,'\<alpha>::null) Set)"
value "\<not> (\<tau> \<Turnstile> \<delta>(null::('\<AA>,'\<alpha>::null) Set))"
value    "\<tau> \<Turnstile> \<upsilon>(Set{})"
value    "\<tau> \<Turnstile> \<upsilon>(Set{Set{\<two>},null})"
value    "\<tau> \<Turnstile> \<delta>(Set{Set{\<two>},null})"
value    "\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes(\<one>))"
value "\<not> (\<tau> \<Turnstile> (Set{\<two>}->includes(\<one>)))"
value "\<not> (\<tau> \<Turnstile> (Set{\<two>,\<one>}->includes(null)))"
value    "\<tau> \<Turnstile> (Set{\<two>,null}->includes(null))"
value    "\<tau> \<Turnstile> (Set{null,\<two>}->includes(null))"

value    "\<tau> \<Turnstile> ((Set{})->forAll(z | \<zero> <\<^sub>o\<^sub>c\<^sub>l z))"

value    "\<tau> \<Turnstile> ((Set{\<two>,\<one>})->forAll(z | \<zero> <\<^sub>o\<^sub>c\<^sub>l z))"
value "\<not> (\<tau> \<Turnstile> ((Set{\<two>,\<one>})->exists(z | z <\<^sub>o\<^sub>c\<^sub>l \<zero> )))"
value "\<not> (\<tau> \<Turnstile> \<delta>(Set{\<two>,null})->forAll(z | \<zero> <\<^sub>o\<^sub>c\<^sub>l z))"
value "\<not> (\<tau> \<Turnstile> ((Set{\<two>,null})->forAll(z | \<zero> <\<^sub>o\<^sub>c\<^sub>l z)))"
value    "\<tau> \<Turnstile> ((Set{\<two>,null})->exists(z | \<zero> <\<^sub>o\<^sub>c\<^sub>l z))"

value "\<not> (\<tau> \<Turnstile> (Set{null::'a Boolean} \<doteq> Set{}))"
value "\<not> (\<tau> \<Turnstile> (Set{null::'a Integer} \<doteq> Set{}))"

value   "(\<tau> \<Turnstile> (Set{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>} \<doteq> Set{\<lambda>_. \<lfloor>\<lfloor>x\<rfloor>\<rfloor>}))"
value   "(\<tau> \<Turnstile> (Set{\<lambda>_. \<lfloor>x\<rfloor>} \<doteq> Set{\<lambda>_. \<lfloor>x\<rfloor>}))"

(* TO BE DONE
   why does this not work ? ? ?
   une regle importante est dans simp, mais pas dans code_unfold ... *)

lemma "\<not> (\<tau> \<Turnstile> (Set{true} \<doteq> Set{false}))" by simp
lemma "\<not> (\<tau> \<Turnstile> (Set{true,true} \<doteq> Set{false}))" by simp
lemma "\<not> (\<tau> \<Turnstile> (Set{\<two>} \<doteq> Set{\<one>}))" by simp
lemma    "\<tau> \<Turnstile> (Set{\<two>,null,\<two>} \<doteq> Set{null,\<two>})" by simp
lemma    "\<tau> \<Turnstile> (Set{\<one>,null,\<two>} <> Set{null,\<two>})" by simp
lemma    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} \<doteq> Set{Set{null,\<two>}})" by simp
lemma    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} <> Set{Set{null,\<two>},null})" by simp
lemma "\<not> (\<tau> \<Turnstile> (Set{null}->select(x | not x) \<doteq> Set{null}))" by simp
(*
value "\<not> (\<tau> \<Turnstile> (Set{true} \<doteq> Set{false}))"
value "\<not> (\<tau> \<Turnstile> (Set{true,true} \<doteq> Set{false}))"
value "\<not> (\<tau> \<Turnstile> (Set{\<two>} \<doteq> Set{\<one>}))"
value    "\<tau> \<Turnstile> (Set{\<two>,null,\<two>} \<doteq> Set{null,\<two>})"
value    "\<tau> \<Turnstile> (Set{\<one>,null,\<two>} <> Set{null,\<two>})"
value    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} \<doteq> Set{Set{null,\<two>}})"
value    "\<tau> \<Turnstile> (Set{Set{\<two>,null}} <> Set{Set{null,\<two>},null})"
value "\<not> (\<tau> \<Turnstile> (Set{null}->select(x | not x) \<doteq> Set{null}))"
*)
end
