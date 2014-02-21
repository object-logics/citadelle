(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_DesignModel_UMLPart_generator_shallow.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2014      Universite Paris-Sud, France
 *               2014      IRT SystemX, France
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
  Employee_DesignModel_UMLPart_generator_shallow
imports
  "../src/OCL_main"
  "../src/OCL_class_diagram_generator"
begin

generation_mode [ shallow ]

Class Person =
  attr_base salary :: int
  attr_object boss

Class Planet =
  attr_base weight :: nat
  child Person

Class Galaxy =
  attr_base sound :: unit
  attr_base moving :: bool
  child Planet

Class OclAny =
  child Galaxy

Class.end OclAny

Define_int [ 1000, 1200, 1300, 1800, 2600, 2900, 3200, 3500 ]

Instance_tmp
         X1 :: Person = ([ _, _, _ ], [ salary = 1300 , boss = self 1 ])
     and X2 :: Person = ([ _, _, _ ], [ salary = 1800 , boss = self 1 ])
     and X3 :: Person = ([ _, _, _ ], [ _, _ ])
     and X4 :: Person = ([ _, _, _ ], [ salary = 2900 , _ ])
     and X5 :: Person = ([ _, _, _ ], [ salary = 3500 , _ ])
     and X6 :: Person = ([ _, _, _ ], [ salary = 2500 , boss = self 6 ])
     and X7 :: OclAny = ((([ _, _, _ ], [ salary = 3200 , boss = self 6 ]) :: Person) , [])
     and X8 :: OclAny = ([], [])
     and X9 :: Person = ([ _, _, _ ], [ salary = 0 , _ ])

Define_state_tmp s1 =
  [ defines [ (([ _, _, _ ], [ salary = 1000 , boss = self 1 ]) :: Person)
            , (([ _, _, _ ], [ salary = 1200 , _]) :: Person) ]
  , skip 
  , defines [ (([ _, _, _ ], [ salary = 2600 , boss = self 4 ]) :: Person)
            , (X5 :: Person)
            , (([ _, _, _ ], [ salary = 2300 , boss = self 3 ]) :: Person) ]
  , skip 
  , skip 
  , defines [ (X9 :: Person) ] ]

Define_state_tmp s2 =
  [ defines [ (X1 :: Person)
            , (X2 :: Person)
            , (X3 :: Person)
            , (X4 :: Person) ]
  , skip
  , defines [ (X6 :: Person)
            , (X7 :: OclAny)
            , (X8 :: OclAny)
            , (X9 :: Person) ] ]

Define_state_tmp s0 = []

end
