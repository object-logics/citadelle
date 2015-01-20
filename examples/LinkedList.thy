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
  LinkedList
imports
  "../src/UML_Main"
  "../src/compiler/OCL_compiler_static"
  "../src/compiler/OCL_compiler_generator_dynamic"
begin

generation_syntax [ shallow (*SORRY*) ]

Class Node
  Attributes i       : Integer
             "next"  : Node
End

Class List
  Attributes content : Node
End

(* TODO : Work out simple instance
Instance Node1 :: Node = ([ i = 2 ] :: Savings)
     and Node2 :: Client = [ clientaccounts = [ Saving1 ] , banks = Bank1 ]
     and Account1 :: Account = [ ident = 666 , owner = Client1 ]
     and Bank1 :: Bank = [ bankaccounts = [ Saving1 , Account1 ], name = "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>" (* (* TODO latex *) \<euro> *) ]

Define_state \<sigma>\<^sub>1' =
  [ defines [ Account1
            , Client1 ]
  , skip , skip , skip
  , defines [ Bank1
            , Saving1 ] ]

Define_state ss = [] 

Define_pre_post ss \<sigma>\<^sub>1' 

Define_base [ 25, 250.0 ]
*)

Context Node :: contents() : Set(Integer)
  Post : "result \<triangleq> if (self .next \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .i))
                   else (self .next .contents() ->including\<^sub>S\<^sub>e\<^sub>t(self .i))
                   endif"

Context List :: insert(x:Integer) : Void
  Post : "if (self .content \<doteq> null) 
          then self .content .contents() \<triangleq> Set{x}
          else self .content .contents() \<triangleq> (self .content@pre .contents@pre())
          endif"

lemmas [simp,code_unfold] = dot_accessor

end
