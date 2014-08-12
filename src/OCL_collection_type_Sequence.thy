(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_collection_type_Sequence.thy --- Library definitions.
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

theory  OCL_collection_type_Sequence
imports OCL_basic_type OCL_Types
begin

section{* The Collection Sequence Type Operations *}

subsection{* Constants on Sequences: mtSequence *}
definition mtSequence::"('\<AA>,'\<alpha>::null) Sequence"  ("Seq{}")
where     "Seq{} \<equiv> (\<lambda> \<tau>.  Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>[]::'\<alpha> list\<rfloor>\<rfloor> )"


lemma mtSequence_defined[simp,code_unfold]:"\<delta>(Seq{}) = true"
apply(rule ext, auto simp: mtSequence_def defined_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                           bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtSequence_valid[simp,code_unfold]:"\<upsilon>(Seq{}) = true"
apply(rule ext,auto simp: mtSequence_def valid_def null_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
                          bot_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def bot_fun_def null_fun_def)
by(simp_all add: Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject bot_option_def null_option_def)

lemma mtSequence_rep_set: "\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Seq{} \<tau>)\<rceil>\<rceil> = []"
 apply(simp add: mtSequence_def, subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
by(simp add: bot_option_def)+

lemma [simp,code_unfold]: "const Seq{}"
by(simp add: const_def mtSequence_def)


text{* Note that the collection types in OCL allow for null to be included;
  however, there is the null-collection into which inclusion yields invalid. *}


lemmas cp_intro''\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e[intro!,simp,code_unfold] = cp_intro'

end
