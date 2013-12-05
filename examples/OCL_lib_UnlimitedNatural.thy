(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib_UnlimitedNatural.thy --- Library definitions.
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

header{* Part II: Library Definitions *}

theory
  OCL_lib_UnlimitedNatural
imports
  "../src/OCL_lib"
begin

section{* Basic Types: UnlimitedNatural *}
subsection{* The construction of the UnlimitedNatural Type *}

text{* Unlike @{term "Integer"}, we should also include the infinity value besides @{term "undefined"} and @{term "null"}. *}


class      infinity = null +
   fixes   infinity :: "'a"
   assumes infinity_is_valid : "infinity \<noteq> bot"
   assumes infinity_is_defined : "infinity \<noteq> null"

instantiation   option  :: (null)infinity
begin
   definition infinity_option_def: "(infinity::'a\<Colon>null option) \<equiv>  \<lfloor> null \<rfloor>"
   instance proof  show "(infinity::'a\<Colon>null option) \<noteq> null"
                   by( simp add:infinity_option_def null_is_valid null_option_def bot_option_def)
                   show "(infinity::'a\<Colon>null option) \<noteq> bot"
                   by( simp add:infinity_option_def null_option_def bot_option_def)
            qed
end

instantiation "fun"  :: (type,infinity) infinity
begin
 definition infinity_fun_def: "(infinity::'a \<Rightarrow> 'b::infinity) \<equiv> (\<lambda> x. infinity)"

 instance proof
            show "(infinity::'a \<Rightarrow> 'b::infinity) \<noteq> bot"
              apply(auto simp: infinity_fun_def bot_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: infinity_is_valid)
            done
            show "(infinity::'a \<Rightarrow> 'b::infinity) \<noteq> null"
              apply(auto simp: infinity_fun_def null_fun_def)
              apply(drule_tac x=x in fun_cong)
              apply(erule contrapos_pp, simp add: infinity_is_defined)
            done
          qed
end

type_synonym ('\<AA>,'\<alpha>) val' = "'\<AA> st \<Rightarrow> '\<alpha>::infinity"

definition limitedNatural :: "('\<AA>,'a::infinity)val' \<Rightarrow> ('\<AA>)Boolean" ("\<mu> _" [100]100)
where   "\<mu> X \<equiv>  \<lambda> \<tau> . if X \<tau> = bot \<tau> \<or> X \<tau> = null \<tau> \<or> X \<tau> = infinity \<tau> then false \<tau> else true \<tau>"

lemma (*valid*)[simp]: "\<upsilon> infinity = true"
  by(rule ext, simp add: bot_fun_def infinity_fun_def infinity_is_valid valid_def)

lemma (*defined*)[simp]: "\<delta> infinity = true"
  by(rule ext, simp add: bot_fun_def defined_def infinity_fun_def infinity_is_defined infinity_is_valid null_fun_def)

lemma (*limitedNatural*)[simp]: "\<mu> invalid = false"
  by(rule ext, simp add: bot_fun_def invalid_def limitedNatural_def)

lemma (*limitedNatural*)[simp]: "\<mu> null = false"
  by(rule ext, simp add: limitedNatural_def)

lemma (*limitedNatural*)[simp]: "\<mu> infinity = false"
  by(rule ext, simp add: limitedNatural_def)

type_synonym ('\<AA>)UnlimitedNatural = "('\<AA>, nat option option option) val'"
locale OclUnlimitedNatural

definition OclNat0 ::"('\<AA>)UnlimitedNatural" (*"\<zero>"*)
where      "OclNat0(*\<zero>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>0::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat1 ::"('\<AA>)UnlimitedNatural" (*"\<one>"*)
where      "OclNat1(*\<one>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>1::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat2 ::"('\<AA>)UnlimitedNatural" (*"\<two>"*)
where      "OclNat2(*\<two>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>2::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat3 ::"('\<AA>)UnlimitedNatural" (*"\<three>"*)
where      "OclNat3(*\<three>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>3::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat4 ::"('\<AA>)UnlimitedNatural" (*"\<four>"*)
where      "OclNat4(*\<four>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>4::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat5 ::"('\<AA>)UnlimitedNatural" (*"\<five>"*)
where      "OclNat5(*\<five>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>5::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat6 ::"('\<AA>)UnlimitedNatural" (*"\<six>"*)
where      "OclNat6(*\<six>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>6::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat7 ::"('\<AA>)UnlimitedNatural" (*"\<seven>"*)
where      "OclNat7(*\<seven>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>7::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat8 ::"('\<AA>)UnlimitedNatural" (*"\<eight>"*)
where      "OclNat8(*\<eight>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>8::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat9 ::"('\<AA>)UnlimitedNatural" (*"\<nine>"*)
where      "OclNat9(*\<nine>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>9::nat\<rfloor>\<rfloor>\<rfloor>)"

definition OclNat10 ::"('\<AA>)UnlimitedNatural" (*"\<one>\<zero>"*)
where      "OclNat10(*\<one>\<zero>*) = (\<lambda> _ . \<lfloor>\<lfloor>\<lfloor>10::nat\<rfloor>\<rfloor>\<rfloor>)"

context OclUnlimitedNatural
begin

abbreviation OclNat_0 ("\<zero>") where "\<zero> \<equiv> OclNat0"
abbreviation OclNat_1 ("\<one>") where "\<one> \<equiv> OclNat1"
abbreviation OclNat_2 ("\<two>") where "\<two> \<equiv> OclNat2"
abbreviation OclNat_3 ("\<three>") where "\<three> \<equiv> OclNat3"
abbreviation OclNat_4 ("\<four>") where "\<four> \<equiv> OclNat4"
abbreviation OclNat_5 ("\<five>") where "\<five> \<equiv> OclNat5"
abbreviation OclNat_6 ("\<six>") where "\<six> \<equiv> OclNat6"
abbreviation OclNat_7 ("\<seven>") where "\<seven> \<equiv> OclNat7"
abbreviation OclNat_8 ("\<eight>") where "\<eight> \<equiv> OclNat8"
abbreviation OclNat_9 ("\<nine>") where "\<nine> \<equiv> OclNat9"
abbreviation OclNat_10 ("\<one>\<zero>") where "\<one>\<zero> \<equiv> OclNat10"

end

definition OclNat_infinity :: "('\<AA>)UnlimitedNatural" ("\<infinity>")
where "\<infinity> = (\<lambda>_. \<lfloor>\<lfloor>None\<rfloor>\<rfloor>)"

subsection{* Validity and Definedness Properties *}

lemma  "\<delta>(null::('\<AA>)UnlimitedNatural) = false" by simp
lemma  "\<upsilon>(null::('\<AA>)UnlimitedNatural) = true"  by simp

lemma [simp,code_unfold]: "\<delta> (\<lambda>_. \<lfloor>\<lfloor>\<lfloor>n\<rfloor>\<rfloor>\<rfloor>) = true"
by(simp)

lemma [simp,code_unfold]: "\<upsilon> (\<lambda>_. \<lfloor>\<lfloor>\<lfloor>n\<rfloor>\<rfloor>\<rfloor>) = true"
by(simp)

lemma [simp,code_unfold]: "\<mu> (\<lambda>_. \<lfloor>\<lfloor>\<lfloor>n\<rfloor>\<rfloor>\<rfloor>) = true"
by(simp add: limitedNatural_def true_def
               bot_fun_def bot_option_def null_fun_def null_option_def infinity_fun_def infinity_option_def)

subsection{* Arithmetical Operations on UnlimitedNatural *}

subsubsection{* Definition *}

definition OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural" (infix "+\<^sub>o\<^sub>c\<^sub>l" 40)
where "x +\<^sub>o\<^sub>c\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> + \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>\<rfloor>
                else invalid \<tau> "

definition OclLess\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)Boolean" (infix "<\<^sub>o\<^sub>c\<^sub>l" 40)
where "x <\<^sub>o\<^sub>c\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> < \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then (\<mu> x) \<tau>
                else invalid \<tau>"

definition OclLe\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l ::"('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)UnlimitedNatural \<Rightarrow> ('\<AA>)Boolean" (infix "\<le>\<^sub>o\<^sub>c\<^sub>l" 40)
where "x \<le>\<^sub>o\<^sub>c\<^sub>l y \<equiv> \<lambda> \<tau>. if (\<mu> x) \<tau> = true \<tau> \<and> (\<mu> y) \<tau> = true \<tau>
                then \<lfloor>\<lfloor>\<lceil>\<lceil>\<lceil>x \<tau>\<rceil>\<rceil>\<rceil> \<le> \<lceil>\<lceil>\<lceil>y \<tau>\<rceil>\<rceil>\<rceil>\<rfloor>\<rfloor>
                else if (\<delta> x) \<tau> = true \<tau> \<and> (\<delta> y) \<tau> = true \<tau>
                then not (\<mu> y) \<tau>
                else invalid \<tau>"

abbreviation OclAdd_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "+\<^sub>U\<^sub>N" 40) where "x +\<^sub>U\<^sub>N y \<equiv> OclAdd\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclLess_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "<\<^sub>U\<^sub>N" 40) where "x <\<^sub>U\<^sub>N y \<equiv> OclLess\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"
abbreviation OclLe_\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l (infix "\<le>\<^sub>U\<^sub>N" 40) where "x \<le>\<^sub>U\<^sub>N y \<equiv> OclLe\<^sub>U\<^sub>n\<^sub>l\<^sub>i\<^sub>m\<^sub>i\<^sub>t\<^sub>e\<^sub>d\<^sub>N\<^sub>a\<^sub>t\<^sub>u\<^sub>r\<^sub>a\<^sub>l x y"

subsubsection{* Test Statements *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}

context OclUnlimitedNatural
begin
value "  \<tau> \<Turnstile> ( \<nine> \<le>\<^sub>U\<^sub>N \<one>\<zero> )"
value "  \<tau> \<Turnstile> (( \<four> +\<^sub>U\<^sub>N \<four> ) \<le>\<^sub>U\<^sub>N \<one>\<zero> )"
value "\<not>(\<tau> \<Turnstile> (( \<four> +\<^sub>U\<^sub>N ( \<four> +\<^sub>U\<^sub>N \<four> )) <\<^sub>U\<^sub>N \<one>\<zero> ))"
value "  \<tau> \<Turnstile> (\<zero> \<le>\<^sub>o\<^sub>c\<^sub>l \<infinity>)"
value "  \<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>U\<^sub>N \<one>))"
value "  \<tau> \<Turnstile> not (\<upsilon> (\<infinity> +\<^sub>o\<^sub>c\<^sub>l \<zero>))"
value "  \<tau> \<Turnstile>      \<mu> \<one>"
end
value "  \<tau> \<Turnstile> not (\<upsilon> (null +\<^sub>o\<^sub>c\<^sub>l \<infinity>))"
value "  \<tau> \<Turnstile> not (\<infinity> <\<^sub>o\<^sub>c\<^sub>l \<infinity>)"
value "  \<tau> \<Turnstile> not (\<upsilon> (invalid \<le>\<^sub>o\<^sub>c\<^sub>l \<infinity>))"
value "  \<tau> \<Turnstile> not (\<upsilon> (null \<le>\<^sub>o\<^sub>c\<^sub>l \<infinity>))"
value "  \<tau> \<Turnstile>      \<upsilon> \<infinity>"
value "  \<tau> \<Turnstile>      \<delta> \<infinity>"
value "  \<tau> \<Turnstile> not (\<mu> \<infinity>)"

end
