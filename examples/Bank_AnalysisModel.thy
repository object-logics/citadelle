(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Bank_AnalysisModel.thy --- OCL Contracts and an Example.
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
  Bank_AnalysisModel
imports
  "../src/OCL_main"
  "../src/OCL_compiler_generator_dynamic"
begin

definition ocl_eq (infixl "equiv" 30)
where "ocl_eq a b = ((a implies b) and (b implies a))"

consts OclMinus\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r :: "('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer \<Rightarrow> ('\<AA>)Integer" (infix "-\<^sub>o\<^sub>c\<^sub>l" 40)

type_synonym Real = int
type_synonym String = int
type_synonym Integer' = int

(* *)

generation_syntax [ deep
                      (generation_semantics [ analysis (*, oid_start 10*) ])
                      (THEORY Bank_AnalysisModel_generated)
                      (IMPORTS ["../src/OCL_main"]
                               "../src/OCL_compiler_generator_dynamic")
                      SECTION
                      [ in SML module_name M (no_signatures) ]
                      (output_directory "../doc")
                  , shallow (generation_semantics [ analysis ]) ]

Class Bank
  Attributes name : String
End

Class Client
  Attributes clientname : String
             address : String
             age : Integer'
End

Class Account
  Attributes ident : Integer'
             moneybalance : Real
End

Association clients
  Between Bank [1 `..` `*`] Role banks
          Client [1 `..` `*`] Role clients
End

Association accounts
  Between Account [1 `..` `*`] Role clientaccounts
          Client [1] Role owner
End

Association bankaccounts
  Between Account [1 `..` `*`] Role bankaccounts
          Bank [1] Role bank
End

Class Savings < Account
  Attributes maximum : Real
End

Class Checks < Account
  Attributes overdraft: Real
End

Define_int [ 25, 250, 2000 ]

Instance Saving1 :: Account = ([ maximum = 2000 ] :: Savings)
     and Client1 :: Client = [ clientaccounts = [ Saving1 ] , banks = Bank1 ]
     and Account1 :: Account = [ ident = 250 , owner = Client1 ]
     and Bank1 :: Bank = [ bankaccounts = [ Saving1 , Account1 ] ]

Define_state \<sigma>\<^sub>1' =
  [ defines [ Account1
            , Client1 ]
  , skip , skip , skip
  , defines [ Bank1
            , Saving1 ] ]

Define_state ss = []

Define_pre_post ss \<sigma>\<^sub>1'

Context c: Savings
  Inv A : `\<zero> <\<^sub>o\<^sub>c\<^sub>l (c .maximum)`
  Inv B : `c .moneybalance \<le>\<^sub>o\<^sub>c\<^sub>l (c .maximum) and \<zero> \<le>\<^sub>o\<^sub>c\<^sub>l (c .moneybalance)`

Context c: Checks
  Inv A : `\<two>\<five> <\<^sub>o\<^sub>c\<^sub>l (c .owner .age) implies (c .overdraft \<doteq> \<zero>)`
  Inv B : `c .owner .age \<le>\<^sub>o\<^sub>c\<^sub>l \<two>\<five> implies (c .overdraft \<doteq> \<zero> -\<^sub>o\<^sub>c\<^sub>l \<two>\<five>\<zero>)`

(*generation_syntax deep flush_all*)

end
