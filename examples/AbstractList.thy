(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * LinkedList.thy --- OCL Contracts and Example drawn from
 *                     "A Specification-Based Test Case Generation Method for UML/OCL"
 *                     (Brucker, Krieger, Longuet, and  Wolff)
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
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

header{* Example: Linked List *}

theory
  AbstractList
imports
  "../src/UML_OCL"
  (* separate compilation : UML_OCL *)
begin

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

section{* The Class Model *}


Class List
  Attributes content : Sequence(Integer)
End!

section{* ... and its Annotation by OCL Constraints  *}

Context List
  Inv asc : "Integer ->forAll\<^sub>S\<^sub>e\<^sub>t(i | (\<zero><\<^sub>i\<^sub>n\<^sub>t i and i <\<^sub>i\<^sub>n\<^sub>t  (self .content ->size\<^sub>S\<^sub>e\<^sub>q())) implies 
                                     (self .content ->at\<^sub>S\<^sub>e\<^sub>q(i) <\<^sub>i\<^sub>n\<^sub>t self .content ->at\<^sub>S\<^sub>e\<^sub>q(i +\<^sub>i\<^sub>n\<^sub>t \<one>)))"


Context List :: insert(x:Integer) : Void
  Post : "if (self .content \<doteq> null)
          then (self .content) \<triangleq> Sequence{x}
          else (self .content) \<triangleq> (self .content@pre)
          endif"

section{* Instances and States of the Class Model  *}

Instance l1  :: List = [ content = [1,3] ]
         l2  :: List = [ content = [1,2,3] ]


State \<sigma>\<^sub>1  = [ l1 ]
State \<sigma>\<^sub>1' = [ l1, l2 ]

Transition  \<sigma>\<^sub>1 \<sigma>\<^sub>1'

section{* Proof of State-Consistency and Implementability of ``insert'' *}

lemmas [simp,code_unfold] = dot_accessor

end
