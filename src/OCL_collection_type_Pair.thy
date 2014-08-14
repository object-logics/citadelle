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
imports OCL_Types OCL_core OCL_lib_common OCL_basic_type_Boolean OCL_basic_type_Integer
begin

section{* Collection Type Pairs: Operations *}

subsection{* Operations *}

text{* This part provides a collection of operators for the Pair type. *}

subsubsection{* Definition: OclPair *}

definition OclPair::"('\<AA>, '\<alpha>) val \<Rightarrow>
                     ('\<AA>, '\<beta>) val \<Rightarrow>
                     ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair"  ("Pair{(_),(_)}")
where     "Pair{X,Y} \<equiv> (\<lambda> \<tau>. if (\<upsilon> X) \<tau> = true \<tau> \<and> (\<upsilon> Y) \<tau> = true \<tau>
                              then Abs_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>(X \<tau>, Y \<tau>)\<rfloor>\<rfloor>
                              else invalid \<tau>)"

subsubsection{* Definition: OclFst *}

definition OclFst::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<alpha>) val"  ("Fst'(_')")
where     "Fst(X) \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                           then fst \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>
                           else invalid \<tau>)"

subsubsection{* Definition: OclSnd *}

definition OclSnd::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<beta>) val"  ("Snd'(_')")
where     "Snd(X) \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                           then snd \<lceil>\<lceil>Rep_Pair\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>
                           else invalid \<tau>)"

(* TODO : cp_lemmas, strictness rules, definedness - inference ...
          fst_conv, snd_conv, Product_Type.pair_collapse *)
subsubsection{* Validity and Definedness Properties *}
subsubsection{* Execution with Invalid or Null as Argument *}
subsubsection{* Context Passing *}

lemmas cp_intro''\<^sub>P\<^sub>a\<^sub>i\<^sub>r[intro!,simp,code_unfold] = cp_intro'

subsubsection{* Const *}

subsection{*Test Statements*}

text{*\fixme{TODO}*}

end
