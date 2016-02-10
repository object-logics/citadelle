(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_OCL.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2016 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2016 IRT SystemX, France
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

theory   UML_OCL
imports  "UML_Main" 
         "../examples/archive/Monads" (* NOTE: perform lazily the extraction of generation_syntax 
                                         so that dependencies can alternate among theories *)
         "compiler/Static"
         "compiler/Generator_dynamic"
begin

no_notation valid_SE (infix "\<Turnstile>" 15)
notation valid_SE (infix "\<Turnstile>\<^sub>M\<^sub>o\<^sub>n" 15)

definition "k x _ = \<lfloor>\<lfloor> x \<rfloor>\<rfloor>"
notation "k" ("\<guillemotleft>_\<guillemotright>")
lemma "K \<lfloor>\<lfloor>x\<rfloor>\<rfloor> = \<guillemotleft>x\<guillemotright>"
by(rule ext, simp add: K_def k_def)

declare [[quick_and_dirty = true]]

generation_syntax [ (*deep
                      (*(generation_semantics [ analysis (*, oid_start 10*) ])*)
                      (THEORY Model_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/Static"]
                               "../src/compiler/Generator_dynamic")
                      SECTION
                      (*SORRY*)
                      [ in SML module_name M ]
                      (output_directory "../doc")
                  ,*) shallow (*SORRY*) ]

end