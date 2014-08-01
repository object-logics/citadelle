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

header{* ... *}

theory  OCL_collection_type_Pair
imports OCL_core
begin

section{* Complex Types: The Pair-Collection Type (I) Core *}

subsection{* The Construction of the Pair Type (Tuples) *}

text{* The core of an own type construction is done via a type
  definition which provides the raw-type @{text "('\<alpha>, '\<beta>) Pair_0"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. *}

typedef ('\<alpha>, '\<beta>) Pair_0 = "{X::('\<alpha>\<Colon>null \<times> '\<beta>\<Colon>null) option option.
                                       X = bot \<or> X = null \<or> (fst\<lceil>\<lceil>X\<rceil>\<rceil> \<noteq> bot \<and> snd\<lceil>\<lceil>X\<rceil>\<rceil> \<noteq> bot)}"
                          by (rule_tac x="bot" in exI, simp)


instantiation   Pair_0  :: (null,null)bot
begin
   definition bot_Pair_0_def: "(bot_class.bot :: ('a\<Colon>null,'b\<Colon>null) Pair_0) \<equiv> Abs_Pair_0 None"

   instance proof show "\<exists>x\<Colon>('a,'b) Pair_0. x \<noteq> bot"
                  apply(rule_tac x="Abs_Pair_0 \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Pair_0_def)
                  apply(subst Abs_Pair_0_inject)
                  apply(simp_all add: bot_Pair_0_def
                                      null_option_def bot_option_def)
                  done
            qed
end

instantiation   Pair_0  :: (null,null)null
begin
   definition null_Pair_0_def: "(null::('a::null,'b::null) Pair_0) \<equiv> Abs_Pair_0 \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null,'b::null) Pair_0) \<noteq> bot"
                  apply(simp add:null_Pair_0_def bot_Pair_0_def)
                  apply(subst Abs_Pair_0_inject)
                  apply(simp_all add: bot_Pair_0_def null_option_def bot_option_def)
                  done
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>,'\<beta>) Pair  = "('\<AA>, ('\<alpha>,'\<beta>) Pair_0) val"

section{* Complex Types: The Pair-Collection Type (II) Library *}

text{* This part provides a collection of operators for the Pair type. *}

subsection{* Computational Operations on Pair *}

subsubsection{* Definition *}

definition OclPair::"('\<AA>, '\<alpha>) val \<Rightarrow>
                     ('\<AA>, '\<beta>) val \<Rightarrow>
                     ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair"  ("Pair{(_),(_)}")
where     "Pair{X,Y} \<equiv> (\<lambda> \<tau>. if (\<upsilon> X) \<tau> = true \<tau> \<and> (\<upsilon> Y) \<tau> = true \<tau>
                              then Abs_Pair_0 \<lfloor>\<lfloor>(X \<tau>, Y \<tau>)\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclFst::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<alpha>) val"  ("Fst'(_')")
where     "Fst(X) \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                           then fst \<lceil>\<lceil>Rep_Pair_0 (X \<tau>)\<rceil>\<rceil>
                           else invalid \<tau>)"


definition OclSnd::" ('\<AA>,'\<alpha>::null,'\<beta>::null) Pair \<Rightarrow> ('\<AA>, '\<beta>) val"  ("Snd'(_')")
where     "Snd(X) \<equiv> (\<lambda> \<tau>. if (\<delta> X) \<tau> = true \<tau>
                           then snd \<lceil>\<lceil>Rep_Pair_0 (X \<tau>)\<rceil>\<rceil>
                           else invalid \<tau>)"

(* TODO : cp_lemmas, strictness rules, definedness - inference ...
          fst_conv, snd_conv, Product_Type.pair_collapse *)

end
