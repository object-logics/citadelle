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
imports OCL_basic_type
begin

section{* Complex Types: The Sequence-Collection Type (I) Core *}

subsection{* The Construction of the Sequence Type *}

text{* The core of an own type construction is done via a type
  definition which provides the raw-type @{text "'\<alpha> Sequence_0"}. It
  is shown that this type ``fits'' indeed into the abstract type
  interface discussed in the previous section. *}

typedef '\<alpha> Sequence_0 ="{X::('\<alpha>\<Colon>null) list option option.
                              X = bot \<or> X = null \<or> (\<forall>x\<in>set \<lceil>\<lceil>X\<rceil>\<rceil>. x \<noteq> bot)}"
          by (rule_tac x="bot" in exI, simp)

instantiation   Sequence_0  :: (null)bot
begin

   definition bot_Sequence_0_def: "(bot::('a::null) Sequence_0) \<equiv> Abs_Sequence_0 None"

   instance proof show "\<exists>x\<Colon>'a Sequence_0. x \<noteq> bot"
                  apply(rule_tac x="Abs_Sequence_0 \<lfloor>None\<rfloor>" in exI)
                  apply(simp add:bot_Sequence_0_def)
                  apply(subst Abs_Sequence_0_inject)
                    apply(simp_all add: bot_Sequence_0_def
                                        null_option_def bot_option_def)
                  done
            qed
end


instantiation   Sequence_0  :: (null)null
begin

   definition null_Sequence_0_def: "(null::('a::null) Sequence_0) \<equiv> Abs_Sequence_0 \<lfloor> None \<rfloor>"

   instance proof show "(null::('a::null) Sequence_0) \<noteq> bot"
                  apply(simp add:null_Sequence_0_def bot_Sequence_0_def)
                  apply(subst Abs_Sequence_0_inject)
                    apply(simp_all add: bot_Sequence_0_def
                                        null_option_def bot_option_def)
                  done
            qed
end


text{* ...  and lifting this type to the format of a valuation gives us:*}
type_synonym    ('\<AA>,'\<alpha>) Sequence  = "('\<AA>, '\<alpha> Sequence_0) val"

lemmas cp_intro''\<^sub>S\<^sub>e\<^sub>q\<^sub>u\<^sub>e\<^sub>n\<^sub>c\<^sub>e[intro!,simp,code_unfold] = cp_intro'

end
