(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Bank_Test_Model.thy --- OCL Contracts and an Example.
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

theory   Bank_Test_Model
imports
  "../src/UML_OCL" (*"../../../src/Monads" (*To be uncommented as soon as we have no errors with Isabelle 2014 *)*)
begin

Class Account 
Attributes account_id : Integer
           balance    : Integer

Context c: Account
  Inv "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t (c .balance)"


Class Client 
Attributes client_id : Integer
           name      : String
           
Association owner
  Between Account [1 \<bullet>\<bullet> *] Role accounts
          Client [1] Role       owner 

Association manages
  Between Account [1 \<bullet>\<bullet> *] Role managed_accounts
          Bank [1]         Role bank

Class Bank 
Attributes bank_name : String

End! (* forces generation of the oo - datatype theory *)

Context Bank :: deposit (c : Client, account_id : Integer, amount:Integer)
  Pre  "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t amount"
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))"
  Post "let A' = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                                        ->any\<^sub>S\<^sub>e\<^sub>t();
            A = self .managed_accounts@pre ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                                           ->any\<^sub>S\<^sub>e\<^sub>t()
        in  (A' .balance) \<doteq> (A .balance +\<^sub>i\<^sub>n\<^sub>t  amount)"

Context Bank :: withdraw (c : Client, account_id : Integer, amount:Integer)
  Pre  "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t amount"
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and 
                                                ((X .account_id) \<doteq> account_id) and
                                                (amount \<le>\<^sub>i\<^sub>n\<^sub>t (X .balance)) )"
  Post "let A' = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                                        ->any\<^sub>S\<^sub>e\<^sub>t();
            A = self .managed_accounts@pre ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                                           ->any\<^sub>S\<^sub>e\<^sub>t()
        in  (A' .balance) \<doteq> (A .balance -\<^sub>i\<^sub>n\<^sub>t  amount)"


Context Bank :: get_balance (c : Client, account_id : Integer) : Integer
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and 
                                                ((X .account_id) \<doteq> account_id))"
  Post "let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                                        ->any\<^sub>S\<^sub>e\<^sub>t()
        in  result \<doteq> (A .balance)"

lemmas [simp,code_unfold] = dot_accessor

end
