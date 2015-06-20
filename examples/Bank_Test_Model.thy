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
  "../src/UML_OCL" 
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

End! (* Bang forces generation of the oo - datatype theory *)

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

lemma XXX: "\<tau> \<Turnstile>  (X \<triangleq> null) \<Longrightarrow>  \<tau> \<Turnstile>  \<upsilon>(X)" 
by (metis foundation18 foundation22 valid2 valid_bool_split)

lemma YYY: "\<tau> \<Turnstile> \<upsilon> bank .withdraw(c,a1,b) \<Longrightarrow> (\<tau> \<Turnstile> \<delta> bank) \<and> (\<tau> \<Turnstile> \<upsilon> c) \<and> (\<tau> \<Turnstile> \<upsilon> a1) \<and> (\<tau> \<Turnstile> \<upsilon> b)"
oops

lemma 
assumes  *:   "(\<sigma>,\<sigma>')       \<Turnstile> ((bank :: \<cdot>Bank) .get_balance(c , a1) \<triangleq> d)"
and      **:  "(\<sigma>',\<sigma>'')     \<Turnstile>  (bank .deposit(c, a1, a)    \<triangleq> null)"
and      ***: "(\<sigma>'',\<sigma>''')   \<Turnstile>  (bank .withdraw(c, a1, b)   \<triangleq> null)"
shows         "(\<sigma>''',\<sigma>'''') \<Turnstile> ((bank .get_balance(c , a1)) \<triangleq> (d +\<^sub>i\<^sub>n\<^sub>t a -\<^sub>i\<^sub>n\<^sub>t b))"
apply(insert * ** ***) 
apply(frule XXX) back
(*apply(frule YYY) 
apply(subst UML_OCL.dot\<g>\<e>\<t>095\<b>\<a>\<l>\<a>\<n>\<c>\<e>_def)*)

oops

(* TODO : Use Locales. *)
(* Definition (and this MUST be a definition, since it is not a recursive query) must be:

UML_OCL.dot\<d>\<e>\<p>\<o>\<s>\<i>\<t>_def:
    (?\<tau> \<Turnstile> \<delta> ?self \<and> ?\<tau> \<Turnstile> \<upsilon> ?c \<and> ?\<tau> \<Turnstile> \<upsilon> ?account_id \<and> ?\<tau> \<Turnstile> \<upsilon> ?amount \<Longrightarrow>
     ?\<tau> \<Turnstile> \<delta> (\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t ?amount and
              ?self .managed_accounts@pre->exists\<^sub>S\<^sub>e\<^sub>t(X|X .owner@pre \<doteq> ?c and
     (X .account_id@pre \<doteq> ?account_id)) implies
              (let A' = ?self .managed_accounts->select\<^sub>S\<^sub>e\<^sub>t(X|X .owner \<doteq> ?c and
           (X .account_id \<doteq> ?account_id))->any\<^sub>S\<^sub>e\<^sub>t();
                   A = ?self .managed_accounts->select\<^sub>S\<^sub>e\<^sub>t(X|X .owner \<doteq> ?c and
          (X .account_id \<doteq> ?account_id))->any\<^sub>S\<^sub>e\<^sub>t()
               in A' .balance \<doteq> A .balance +\<^sub>i\<^sub>n\<^sub>t ?amount))) \<Longrightarrow>
    (?\<tau> \<Turnstile> ?self .deposit(?c,?account_id,?amount) \<triangleq> ?result) =
    (if ?\<tau> \<Turnstile> \<delta> ?self \<and> ?\<tau> \<Turnstile> \<upsilon> ?c \<and> ?\<tau> \<Turnstile> \<upsilon> ?account_id \<and> ?\<tau> \<Turnstile> \<upsilon> ?amount
     then ?\<tau> \<Turnstile> \<zero> \<le>\<^sub>i\<^sub>n\<^sub>t ?amount and
                ?self .managed_accounts@pre->exists\<^sub>S\<^sub>e\<^sub>t(X|X .owner@pre \<doteq> ?c and
       (X .account_id@pre \<doteq> ?account_id)) implies
                (let A' = ?self .managed_accounts->select\<^sub>S\<^sub>e\<^sub>t(X|X .owner \<doteq> ?c and
             (X .account_id \<doteq> ?account_id))->any\<^sub>S\<^sub>e\<^sub>t();
                     A = ?self .managed_accounts->select\<^sub>S\<^sub>e\<^sub>t(X|X .owner \<doteq> ?c and
            (X .account_id \<doteq> ?account_id))->any\<^sub>S\<^sub>e\<^sub>t()
                 in A' .balance \<doteq> A .balance +\<^sub>i\<^sub>n\<^sub>t ?amount)
     else ?\<tau> \<Turnstile> ?result \<triangleq> invalid)

   *)


find_theorems (100) "dot\<g>\<e>\<t>095\<b>\<a>\<l>\<a>\<n>\<c>\<e>"
find_theorems (100) name:"\<d>\<e>\<p>\<o>\<s>\<i>\<t>"

definition val2Mon :: "('\<sigma>, '\<alpha>::null)val \<Rightarrow>  ('\<alpha>,'\<sigma> state)MON\<^sub>S\<^sub>E"
where     "val2Mon f \<equiv> (\<lambda>\<sigma>. if \<exists>\<sigma>'. \<exists>d.  ((\<sigma>,\<sigma>') \<Turnstile> (f \<triangleq> d)) 
                             then Some(SOME(d,\<sigma>'). ((\<sigma>,\<sigma>') \<Turnstile> (f \<triangleq> (\<lambda>_. d)))) 
                             else None)"

term "\<sigma> \<Turnstile> (( r \<leftarrow> (val2Mon ((bank :: \<cdot>Bank) .get_balance(c , a1))) ;
              _ \<leftarrow> (val2Mon ((bank :: \<cdot>Bank) .deposit(c, a1, a))) ;
              _ \<leftarrow> (val2Mon ((bank .withdraw(c , a1, b)))) ;
              r' \<leftarrow> (val2Mon ((bank :: \<cdot>Bank) .get_balance(c , a1))) ; 
             return (r = r')))"

end
