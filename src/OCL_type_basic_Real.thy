(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_type_basic_Real.thy --- Library definitions.
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

theory  OCL_type_basic_Real
imports OCL_core
        OCL_type_basic_Integer
        (* Real *) (* Transcendental *) (* For Real Numbers only ...
                                      Has unfortunate side-effects on syntax. *)
begin

section{* Basic Types: Real *}
subsection{* The Construction of the Real Type *}
text{* The following text can only be included if the two packages "Real" and "Transcendental"
were also included. *}
type_synonym real = int (* If package Real is not incl*)

text{* Since @{term "Real"} is again a basic type, we define its semantic domain
as the valuations over @{typ "real option option"} --- i.e. the mathematical type of real numbers.
The HOL-theory for @{typ real} ``Real'' transcendental numbers such as $\pi$ and $e$ as well as
infrastructure to reason over infinite convergent Cauchy-sequences (it is thus possible, in principle,
to reason that the sum of two-s exponentials is actually 2.

If needed, a code-generator to compile @{term "Real"} to floating-point
numbers can be added; this allows for mapping reals to an efficient machine representation;
of course, this feature would be logically unsafe.*}

type_synonym Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e = "real option option"
type_synonym ('\<AA>)Real = "('\<AA>,Real\<^sub>b\<^sub>a\<^sub>s\<^sub>e) val"

text{* Although the remaining part of this library reasons about
reals abstractly, we provide here as example some convenient shortcuts. *}

definition OclReal0 ::"('\<AA>)Real" ("\<zero>.\<zero>")
where      "\<zero>.\<zero> =  (\<lambda> _ . \<lfloor>\<lfloor>0::real\<rfloor>\<rfloor>)"

definition OclReal1 ::"('\<AA>)Real" ("\<one>.\<zero>")
where      "\<one>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>1::real\<rfloor>\<rfloor>)"

definition OclReal2 ::"('\<AA>)Real" ("\<two>.\<zero>")
where      "\<two>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>2::real\<rfloor>\<rfloor>)"

definition OclReal3 ::"('\<AA>)Real" ("\<three>.\<zero>")
where      "\<three>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>3::real\<rfloor>\<rfloor>)"

definition OclReal4 ::"('\<AA>)Real" ("\<four>.\<zero>")
where      "\<four>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>4::real\<rfloor>\<rfloor>)"

definition OclReal5 ::"('\<AA>)Real" ("\<five>.\<zero>")
where      "\<five>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>5::real\<rfloor>\<rfloor>)"

definition OclReal6 ::"('\<AA>)Real" ("\<six>.\<zero>")
where      "\<six>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>6::real\<rfloor>\<rfloor>)"

definition OclReal7 ::"('\<AA>)Real" ("\<seven>.\<zero>")
where      "\<seven>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>7::real\<rfloor>\<rfloor>)"

definition OclReal8 ::"('\<AA>)Real" ("\<eight>.\<zero>")
where      "\<eight>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>8::real\<rfloor>\<rfloor>)"

definition OclReal9 ::"('\<AA>)Real" ("\<nine>.\<zero>")
where      "\<nine>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>9::real\<rfloor>\<rfloor>)"

definition OclReal10 ::"('\<AA>)Real" ("\<one>\<zero>.\<zero>")
where      "\<one>\<zero>.\<zero> = (\<lambda> _ . \<lfloor>\<lfloor>10::real\<rfloor>\<rfloor>)"

term "pi"

(* TODO: Infrastructure for Reals; ... *)


subsection{* Validity and Definedness Properties on Real *}

lemma  "\<delta>(null::('\<AA>)Real) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)Real) = true"  by simp

(* ecclectic proofs to make examples executable *)
lemma [simp,code_unfold]: "\<delta> \<zero>.\<zero> = true" by(simp add:OclReal0_def)
lemma [simp,code_unfold]: "\<upsilon> \<zero>.\<zero> = true" by(simp add:OclReal0_def)
lemma [simp,code_unfold]: "\<delta> \<one>.\<zero> = true" by(simp add:OclReal1_def)
lemma [simp,code_unfold]: "\<upsilon> \<one>.\<zero> = true" by(simp add:OclReal1_def)


subsection{* Arithmetical Operations on Real *}

subsubsection{* Definition *}
text{* Here is a common case of a built-in operation on built-in types.
Note that the arguments must be both defined (non-null, non-bot). *}
text{* Note that we can not follow the lexis of the OCL Standard for Isabelle
technical reasons; these operators are heavily overloaded in the HOL library
that a further overloading would lead to heavy technical buzz in this
document.
*}
definition OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "+\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 40)
where "x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> + \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "

definition OclMinus\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "-\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 41)
where "x -\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> - \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "

definition OclMult\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "*\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 45)
where "x *\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> * \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "

definition OclDivision\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "div\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 45)
where "x div\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> div \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "


definition OclModulus\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Real" (infix "mod\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 45)
where "x mod\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> mod \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "


definition OclLess\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 35)
where "x <\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> < \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "

definition OclLe\<^sub>R\<^sub>e\<^sub>a\<^sub>l ::"('\<AA>)Real \<Rightarrow> ('\<AA>)Real \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l" 35)
where "x \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                       then \<lfloor>\<lfloor>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil> \<le> \<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rfloor>\<rfloor>
                       else invalid \<tau> "

subsubsection{* Basic Properties *}

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_commute: "(X +\<^sub>r\<^sub>e\<^sub>a\<^sub>l Y) = (Y +\<^sub>r\<^sub>e\<^sub>a\<^sub>l X)"
  by(rule ext,auto simp:true_def false_def OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def invalid_def
                   split: option.split option.split_asm
                          bool.split bool.split_asm)

subsubsection{* Execution with Invalid or Null or Zero as Argument *}

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_strict1[simp,code_unfold] : "(x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l invalid) = invalid"
by(rule ext, simp add: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def true_def false_def)

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_strict2[simp,code_unfold] : "(invalid +\<^sub>r\<^sub>e\<^sub>a\<^sub>l x) = invalid"
by(rule ext, simp add: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def true_def false_def)

lemma [simp,code_unfold] : "(x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l null) = invalid"
by(rule ext, simp add: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def true_def false_def)

lemma [simp,code_unfold] : "(null +\<^sub>r\<^sub>e\<^sub>a\<^sub>l x) = invalid"
by(rule ext, simp add: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def true_def false_def)

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_zero1[simp,code_unfold] :
"(x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
 proof (rule ext, rename_tac \<tau>, case_tac "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau>")
  fix \<tau> show "(\<upsilon> x and not (\<delta> x)) \<tau> = true \<tau> \<Longrightarrow>
              (x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_true', simp add: OclValid_def)
  by (metis OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def OclNot_defargs OclValid_def foundation5 foundation9)
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
              (x +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<zero>) \<tau> = (if \<upsilon> x and not (\<delta> x) then invalid else x endif) \<tau>"
   apply(subst OclIf_false', simp, simp add: A, auto simp: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def OclInt0_def)
     (* *)
     apply(simp add: foundation16'[simplified OclValid_def])
    apply(simp add: B)
  by(simp add: OclValid_def)
  apply_end(metis OclValid_def defined5 defined6 defined_and_I defined_not_I foundation9)
qed

lemma OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_zero2[simp,code_unfold] :
"(\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l x) = (if \<upsilon> x and not (\<delta> x) then invalid else x endif)"
by(subst OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_commute, simp)

(* TODO Basic proproperties for multiplication, division, modulus. *)


subsubsection{* Context Passing *}

lemma cp_OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l:"(X +\<^sub>r\<^sub>e\<^sub>a\<^sub>l Y) \<tau> = ((\<lambda> _. X \<tau>) +\<^sub>r\<^sub>e\<^sub>a\<^sub>l (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclAdd\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def cp_defined[symmetric])

lemma cp_OclLess\<^sub>R\<^sub>e\<^sub>a\<^sub>l:"(X <\<^sub>r\<^sub>e\<^sub>a\<^sub>l Y) \<tau> = ((\<lambda> _. X \<tau>) <\<^sub>r\<^sub>e\<^sub>a\<^sub>l (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclLess\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def cp_defined[symmetric])

lemma cp_OclLe\<^sub>R\<^sub>e\<^sub>a\<^sub>l:"(X \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l Y) \<tau> = ((\<lambda> _. X \<tau>) \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (\<lambda> _. Y \<tau>)) \<tau>"
by(simp add: OclLe\<^sub>R\<^sub>e\<^sub>a\<^sub>l_def cp_defined[symmetric])

(* TODO Basic proproperties for multiplication, division, modulus. *)


subsubsection{* Test Statements *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}

Assert "  \<tau> \<Turnstile> ( \<nine>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero> )"
Assert "  \<tau> \<Turnstile> (( \<four>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<four>.\<zero> ) \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero> )"
Assert "\<not>(\<tau> \<Turnstile> (( \<four>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l ( \<four>.\<zero> +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<four>.\<zero> )) <\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>\<zero>.\<zero> ))"
Assert "  \<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<one>.\<zero>)) "


end
