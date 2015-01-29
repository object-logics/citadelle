(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Flight_Model.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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
  Flight_Model

imports
  "../src/UML_OCL"
  (* separate compilation : UML_OCL *)
begin


Class Flight
  Attributes
    seats : Integer
    "from" : String
    to : String
End

term id (* REMARK "id" already exists *)
Class Reservation
  Attributes
    id : Integer
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
  Between Person      [*]
            Role passengers
          Flight      [*]
            Role flights
End

Aggregation flights
  Between Flight      [1]
            Role flight
          Reservation [*]
            Role fl_res Sequence_
End

Association reservations
  Between Client      [1]
            Role client
          Reservation [*]
            Role cl_res
End

Association connection
  Between Reservation [0 \<bullet>\<bullet> 1]
            Role "next"
          Reservation [0 \<bullet>\<bullet> 1]
            Role prev
End

(*
(* Illustration of a wrong model transition: *)
Instance R00 :: Reservation = [ id = 00, flight = [ F1 ], "next" = R11 ]
     and R11 :: Reservation = [ id = 11, flight = [ F1, F2 ], "next" = R00 ]
     and R22 :: Reservation = [ id = 22, "next" = [ R00, R11, R22 ] ]
     and F1 :: Flight = [ seats = 120, "from" = "Ostrava", to = "Plzen" ]
     and F2 :: Flight = [ seats = 370, "from" = "Plzen", to = "Brno" ]
(*
R00 .flight = Set{ F1 } 
R00 .client = Set{} // minimum constraint [1] not satisfied 
R00 .prev = Set{ R11 , R22 } // maximum constraint [0 .. 1] not satisfied 
R00 .next = Set{ R11 } 
R11 .flight = Set{ F1 , F2 } // maximum constraint [1] not satisfied 
R11 .client = Set{} // minimum constraint [1] not satisfied 
R11 .prev = Set{ R00 , R22 } // maximum constraint [0 .. 1] not satisfied 
R11 .next = Set{ R00 } 
R22 .flight = Set{} // minimum constraint [1] not satisfied 
R22 .client = Set{} // minimum constraint [1] not satisfied 
R22 .prev = Set{ R22 } 
R22 .next = Set{ R00 , R11 , R22 } // maximum constraint [0 .. 1] not satisfied 
F1 .passengers = Set{} 
F1 .fl_res = Set{ R00 , R11 } 
F2 .passengers = Set{} 
F2 .fl_res = Set{ R11 } 
8 error(s) in multiplicity constraints
*)
*)

Instance S1 :: Staff = [ name = "Mallory" , (**) flights = F1 ]
     and C1 :: Client = [ name = "Bob" , address = "Plzen" , (**) flights = F1 , (**) cl_res = R11 ]
     and C2 :: Client = [ name = "Alice" , address = "Ostrava" , (**) flights = F1 , (**) cl_res = R21 ]
     and R11 :: Reservation = [ id = 12345 , (**) flight = F1 ]
     and R21 :: Reservation = [ id = 98765 , (**) flight = F1 ]
     and F1 :: Flight = [ seats = 120 , "from" = "Ostrava" , to = "Plzen" ]
     and F2 :: Flight = [ seats = 370 , "from" = "Plzen" , to = "Brno" ]

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
            , ([ name = "Bob" , address = "Praha" , (**) flights = F1 , (**) cl_res = R11 ] :: Client)
            , ([ name = "Alice" , address = "Ostrava" , (**) flights = [ F1 , F2 ] , (**) cl_res = [ self 4, self 7 ] ] :: Client)
            , R11
            , ([ id = 98765 , (**) flight = F1 , (**) "next" = self 7 ] :: Reservation)
            , F1
            , F2
            , ([ id = 19283 , (**) flight = F2 ] :: Reservation) ] ]

Define_pre_post \<sigma>\<^sub>1 \<sigma>\<^sub>2

Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .fl_res)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"

Context r: Reservation
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (r .id)"
  Inv B : "r .next <> null implies (r .flight .to \<doteq> r .next .flight .from)"
  Inv C : "r .next <> null implies (r .client \<doteq> r .next .client)"

(* example for a recursive query *)
Context Reservation :: connections () : Set(Integer)
  Post : "result \<triangleq> if (self .next \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .id))
                   else (self .next .connections()->including\<^sub>S\<^sub>e\<^sub>t(self .id))
                   endif"
  Pre  : "true"    

(*generation_syntax deep flush_all*)

lemmas [simp,code_unfold] = dot_accessor

end
