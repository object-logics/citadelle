(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Flight_AnalysisModel.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2015 Université Paris-Sud, France
 *               2015 IRT SystemX, France
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

generation_syntax [ (*deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      (THEORY Flight_AnalysisModel_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/OCL_compiler_static"]
                               "../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "../doc")
                  ,*) shallow (generation_semantics [ analysis ]) ]

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
            Role flightreserv Sequence_
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

(* (* Example of type errors *)
Instance R00 :: Reservation = [ ident = 00, flight = [ F1 ], reservnext = R11 ]
     and R11 :: Reservation = [ ident = 11, flight = [ F1, F2 ], reservnext = R00 ]
     and R22 :: Reservation = [ ident = 22, reservnext = [ R00, R11, R22 ] ]
     and F1 :: Flight = [ seats = 120, destifrom = "Paris", destito = "London" ]
     and F2 :: Flight = [ seats = 370, destifrom = "London", destito = "New-York" ]
*)

Instance S1 :: Staff = [ name = "James" , (**) flights = F1 ]
     and C1 :: Client = [ name = "Peter" , address = "London" , (**) flights = F1 , (**) clientreserv = R11 ]
     and C2 :: Client = [ name = "Marie" , address = "Paris" , (**) flights = F1 , (**) clientreserv = R21 ]
     and R11 :: Reservation = [ ident = 12345 , (**) flight = F1 ]
     and R21 :: Reservation = [ ident = 98796 , (**) flight = F1 ]
     and F1 :: Flight = [ seats = 120 , destifrom = "Paris" , destito = "London" ]
     and F2 :: Flight = [ seats = 370 , destifrom = "London" , destito = "New-York" ]

Define_state \<sigma>\<^sub>1 =
  [ defines [ S1
            , C1
            , C2 
            , R11
            , R21
            , F1
            , F2 ] ]

Define_state \<sigma>\<^sub>2 =
  [ defines [ S1
            , ([ name = "Peter" , address = "Dublin" , (**) flights = F1 , (**) clientreserv = R11 ] :: Client)
            , ([ name = "Marie" , address = "Paris" , (**) flights = [ F1 , F2 ] , (**) clientreserv = [ self 4, self 7 ] ] :: Client)
            , R11
            , ([ ident = 98796 , (**) flight = F1 , (**) reservnext = self 7 ] :: Reservation)
            , F1
            , F2
            , ([ ident = 98798 , (**) flight = F2 ] :: Reservation) ] ]

Define_pre_post \<sigma>\<^sub>1 \<sigma>\<^sub>2

Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .flightreserv ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .flightreserv)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"

Context r: Reservation
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (r .ident)"
  Inv B : "r .reservnext <> null implies (r .flight .destito \<doteq> r .reservnext .flight .destifrom)"
  Inv C : "r .reservnext <> null implies (r .client \<doteq> r .reservnext .client)"

(*generation_syntax deep flush_all*)

lemmas [simp,code_unfold] = dot_accessor

end
