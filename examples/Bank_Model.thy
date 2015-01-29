(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Bank_Model.thy --- OCL Contracts and an Example.
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
  Bank_Model
imports
  "../src/UML_OCL"
  (* separate compilation : UML_OCL *)
begin

Class Bank
  Attributes name : String
End

Class Client
  Attributes clientname : String
             address : String
             age : Integer
             (*id  : Integer*)
End

Class Account
  Attributes ident : Integer
             moneybalance : Real
End

Association clients
  Between Bank [1 \<bullet>\<bullet> *] Role banks
          Client [1 \<bullet>\<bullet> *] Role clients
End

Association accounts
  Between Account [1 \<bullet>\<bullet> *] Role clientaccounts
          Client [1] Role owner
End

Association bankaccounts
  Between Account [1 \<bullet>\<bullet> *] Role bankaccounts
          Bank [1] Role bank
End

Class Savings < Account
  Attributes maximum : Real
End

Class Current < Account
  Attributes overdraft : Real
End

Instance Saving1 :: Account = ([ maximum = 2000 ] :: Savings)
     and Client1 :: Client = [ clientaccounts = [ Saving1 ] , banks = Bank1 ]
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

Context c: Savings
  Inv A : "\<zero>.\<zero> <\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .maximum)"
  Inv B : "c .moneybalance \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .maximum) and \<zero>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .moneybalance)"

Context c: Current
  Inv A : "\<two>\<five> <\<^sub>i\<^sub>n\<^sub>t (c .owner .age) implies (c .overdraft \<doteq> \<zero>.\<zero>)"
  Inv B : "c .owner .age \<le>\<^sub>i\<^sub>n\<^sub>t \<two>\<five> implies   (c .overdraft \<doteq> \<zero>.\<zero> -\<^sub>r\<^sub>e\<^sub>a\<^sub>l \<two>\<five>\<zero>.\<zero>)"

Context c: Client
  Inv A : "c .banks ->forAll\<^sub>S\<^sub>e\<^sub>t(b | b .bankaccounts ->select\<^sub>S\<^sub>e\<^sub>t(a | (a .owner \<doteq> c) and 
                                                                  (a .oclIsTypeOf(Current)))
                        ->size\<^sub>S\<^sub>e\<^sub>t() \<le>\<^sub>i\<^sub>n\<^sub>t \<one>)"

Context Bank :: create_client(name:String, address:String, age:Integer, b:Bank) : Integer
  Pre : "b .clients ->forAll\<^sub>S\<^sub>e\<^sub>t(c | c .clientname <> name or c .address <> address)" 
  Post: "b .clients ->exists\<^sub>S\<^sub>e\<^sub>t(c | c .clientname <> name or c .address <> address or c .age <> age)"
  Post : "true"

(*generation_syntax deep flush_all*)

lemmas [simp,code_unfold] = dot_accessor

end
