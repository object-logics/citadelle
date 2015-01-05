(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_AnalysisModel_UMLPart_generator_deep.thy --- OCL Contracts and an Example.
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
  Employee_AnalysisModel_UMLPart_generator_deep
imports
  "../src/compiler/OCL_compiler_generator_dynamic"
begin

generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      (THEORY Employee_AnalysisModel_UMLPart_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/OCL_compiler_static"]
                               "../src/compiler/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "../doc")
                  (*, syntax_print*) ]

Class Person < Planet
  Attributes salary : Integer (*\<acute>int\<acute>*)
End

Association boss
  Between Person [*]
          Person [0 \<bullet>\<bullet> 1] Role boss
End

Class Planet < Galaxy
  Attributes wormhole : UnlimitedNatural
             weight : Integer
End

Class Galaxy
  Attributes sound : Void
             moving : Boolean
End

(* wishlist:
Class Galaxy
  Attributes sound : Set(Set(Integer))
             outerworld : Galaxy
End
*)

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = []
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 :: Person = [ salary = 2900 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 :: Person = [ salary = 3500 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 :: Person = [ salary = 2500 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 :: OclAny = ([ salary = 3200 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ] :: Person)
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 :: OclAny = []
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 :: Person = [ salary = 0 ]

Define_state \<sigma>\<^sub>1 =
  [ defines [ ([ salary = 1000 , boss = self 1 ] :: Person)
            , ([ salary = 1200 ] :: Person) ]
  , skip
  , defines [ ([ salary = 2600 , boss = self 4 ] :: Person)
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5
            , ([ salary = 2300 , boss = self 3 ] :: Person) ]
  , skip
  , skip
  , defines [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ] ]

Define_state \<sigma>\<^sub>1' =
  [ defines [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 ]
  , skip
  , defines [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ] ]

(*Define_state \<sigma>\<^sub>0 = []*)

Define_pre_post \<sigma>\<^sub>1 \<sigma>\<^sub>1'

Context Person :: contents () : Set(Integer)
  Post : "result \<triangleq> if (self .boss \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   else (self .boss .contents()->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   endif"
  Post : "true"
  Pre : "false"

Context Person
  Inv a: "self .boss <> null implies (self .salary  \<triangleq>  ((self .boss) .salary))"

Context Planet
  Inv A : "true and (self .weight \<le>\<^sub>i\<^sub>n\<^sub>t \<zero>)"

(*Define_base [ 1000, 1200, 1300, 1800, 2600, 2900, 3200, 3500
            , 3.14159265
            , "abc", "\<AA>\<BB>\<CC>\<DD>\<EE>\<FF>" ]*)

(*generation_syntax deep flush_all*)

end
