(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_core_experiments.thy --- 
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012      Université Paris-Saclay, Univ Paris Sud, France
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

theory 
  OCL_core_experiments
imports
  OCL_core (* Testing *)
begin

section{* OCL Core Definitions *}

nitpick_params
 [timeout = 30, tac_timeout = 0.5, show_datatypes,assms=true]
lemma ocl_and_defargs: 
"\<tau> \<Turnstile> (P and Q) \<Longrightarrow> (\<tau> \<Turnstile> \<delta> P) \<and> (\<tau> \<Turnstile> \<delta> Q)"
by(auto dest: foundation5 foundation6)

(*
nitpick_params
nitpick_params
 [timeout = 30, tac_timeout = 0.5, show_datatypes]
lemma ocl_and_defargs: 
"\<tau> \<Turnstile> ((P and Q)  \<triangleq>  (P or Q))"
nitpick[show_all]

oops
lemma "P & Q = Q"
nitpick
*)


end