(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Flight_AnalysisModel.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2014 Universite Paris-Sud, France
 *               2014 IRT SystemX, France
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

header{* Part ... *}

theory
  Flight_AnalysisModel
imports
  "../src/UML_Main"
  "../src/compiler/OCL_compiler_static"
  "../src/compiler/OCL_compiler_generator_dynamic"
begin

generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      (THEORY Flight_AnalysisModel_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/OCL_compiler_static"]
                               "../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "../doc")
                  , shallow (generation_semantics [ analysis ]) ]

Class Flight
  Attributes
    seats : Integer
    destifrom : String
    destito : String
End

Class Reservation
  Attributes
    ident : Integer
End

Class Person
  Attributes
    name : String
End

Class Client < Person
  Attributes
    address : String
End

Class Staff < Person
End

Association passengers
  Between Person      [0 \<bullet>\<bullet> *]
            Role passengers
          Flight      [0 \<bullet>\<bullet> *]
            Role flights
End

Association flights
  Between Flight      [1]
            Role flight
          Reservation [0 \<bullet>\<bullet> *]
            Role flightreserv
End

Association reservations
  Between Client      [1]
            Role client
          Reservation [0 \<bullet>\<bullet> *]
            Role clientreserv
End

Association connection
  Between Reservation [0 \<bullet>\<bullet> 1]
            Role reservnext
          Reservation [0 \<bullet>\<bullet> 1]
            Role reservprev
End

(*
Define_state \<sigma>\<^sub>1' =
  [ ]

Define_state ss = [] 

Define_pre_post ss \<sigma>\<^sub>1' 

Define_base [ 25, 250.0 ]
*)
(*generation_syntax deep flush_all*)

end
