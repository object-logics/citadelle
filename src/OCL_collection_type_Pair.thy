(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_collection_type_Pair.thy --- Library definitions.
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

theory  OCL_collection_type_Pair
imports OCL_lib_common
begin

section{* Collection Type Pairs: Operations *}

text{* The OCL standard provides the concept of \emph{Tuples}, \ie{} a family of record-types
with projection functions. In FeatherWeight OCL,  only the theory of a special case is
developped, namely the type of Pairs, which is, however, sufficient for all applications
since it can be used to mimick all tuples. In particular, it can be used to express operations
with multiple arguments, roles of n-ary associations, ... *}

subsection{* Semantic Properties of the Type Constructor *}

lemma A[simp]:"Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> None \<Longrightarrow> Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> null \<Longrightarrow> (fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
by(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x],auto simp:null_option_def bot_option_def)

lemma A'[simp]:" x \<noteq> bot \<Longrightarrow>  x \<noteq> null \<Longrightarrow> (fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
apply(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x], simp add: bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
apply(auto simp:null_option_def bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: null_option_def bot_option_def)
done

lemma B[simp]:"Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> None \<Longrightarrow> Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x \<noteq> null \<Longrightarrow> (snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
by(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x],auto simp:null_option_def bot_option_def)

lemma B'[simp]:"x \<noteq> bot \<Longrightarrow> x \<noteq> null \<Longrightarrow> (snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e x\<rceil>\<rceil>) \<noteq> bot" 
apply(insert Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e[of x], simp add: bot_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
apply(auto simp:null_option_def bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e None"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: bot_option_def)
apply(erule contrapos_np[of "x = Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>None\<rfloor>"])
apply(subst Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject[symmetric], simp)
apply(subst Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp_all,simp add: null_option_def bot_option_def)
done

subsection{* Strict Equality *}

subsubsection{* Definition *}

text{* After the part of foundational operations on sets, we detail here equality on sets.
Strong equality is inherited from the OCL core, but we have to consider
the case of the strict equality. We decide to overload strict equality in the
same way we do for other value's in OCL:*}

defs  StrictRefEq\<^sub>P\<^sub>a\<^sub>i\<^sub>r :
      "((x::('\<AA>,'\<alpha>::null,'\<beta>::null)Pair) \<doteq> y) \<equiv> (\<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                                       then (x \<triangleq> y)\<tau>
                                                       else invalid \<tau>)"


text{* Property proof in terms of @{term "binop_property_profile3"}*}
interpretation  StrictRefEq\<^sub>P\<^sub>a\<^sub>i\<^sub>r : binop_property_profile3 "\<lambda> x y. (x::('\<AA>,'\<alpha>::null,'\<beta>::null)Pair) \<doteq> y" 
                by unfold_locales (auto simp:  StrictRefEq\<^sub>P\<^sub>a\<^sub>i\<^sub>r)
 
subsection{* Standard Operations *}

text{* This part provides a collection of operators for the Pair type. *}

subsubsection{* Definition: OclPair Constructor *}

definition OclPair::"('\<AA>, '\<alpha>) val \<Rightarrow>
                     ('\<AA>, '\<beta>) val \<Rightarrow>
                     ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair"  ("Pair{(_),(_)}")
where     "Pair{X,Y} \<equiv> (\<lambda> \<tau>. if (\<upsilon> X) \<tau> = true \<tau> \<and> (\<upsilon> Y) \<tau> = true \<tau>
                              then Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>(X \<tau>, Y \<tau>)\<rfloor>\<rfloor>
                              else invalid \<tau>)"

subsubsection{* Definition: OclFst *}

definition OclFirst::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<alpha>) val"  (" _ .First'(')")
where     "X .First() \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                              then fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>
                              else invalid \<tau>)"


interpretation OclFirst : monop_property_profile2 OclFirst "\<lambda>x.  fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x)\<rceil>\<rceil>"
                         by unfold_locales (auto simp:  OclFirst_def)

subsubsection{* Definition: OclSnd *}
                              
definition OclSecond::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<beta>) val"  ("_ .Second'(')")
where     "X .Second() \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                               then snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>
                               else invalid \<tau>)"

interpretation OclSecond : monop_property_profile2 OclSecond "\<lambda>x.  snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (x)\<rceil>\<rceil>"
                           by unfold_locales  (auto simp:  OclSecond_def)
                               
subsection{* Execution Properties *}


subsection{*Test Statements*}

Assert "\<tau> \<Turnstile> invalid .First() \<triangleq> invalid "
Assert "\<tau> \<Turnstile> null .First() \<triangleq> invalid "
Assert "\<tau> \<Turnstile> null .Second() \<triangleq> invalid .Second() "
(*
Assert "\<tau> \<Turnstile> Pair{invalid, true} \<triangleq> invalid "
text{*\fixme{TODO}*}
*)
end
