(******************************************************************************
 * HOL-OCL
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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

chapter\<open> Part ...  \<close>

theory   Bank_Test_Model
imports
  FOCL.UML_OCL
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
          Client  [1]      Role owner

Association manages
  Between Account [1 \<bullet>\<bullet> *] Role managed_accounts
          Bank [1]         Role bank

Class Bank
Attributes bank_name : String

(*
Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = []
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 :: Person = [ salary = 2900 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 :: Person = [ salary = 3500 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 :: Person = [ salary = 2500 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7           = ([ salary = 3200 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ] :: Person) \<rightarrow>oclAsType( OclAny )
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 :: OclAny = []
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 :: Person = [ salary = 0 ]
     and X0 :: Person = [ outer_world = [ [ P1 ] ] ]
     and P1 :: Planet = [ outer_world = [ [ P1 ] , [ self 10 ] ] ]

State \<sigma>\<^sub>1 =
  [ ([ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 with_only salary = 1000 , boss = self 1 ] :: Person)
  , ([ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 with_only salary = 1200 ] :: Person)
*)

End! (* Bang forces generation of the oo - datatype theory *)


Context Bank :: deposit (c : Client, account_id : Integer, amount:Integer)
  Pre  "def": "(\<delta> c) and (\<delta> account_id) and (\<delta> amount)" (* this mimics the syntax : c : Client[1], account_id : Integer[1] *)
  Pre  "pos": "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t amount"
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))"
  Post "let A' = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                        ->any\<^sub>S\<^sub>e\<^sub>t();
            A  = self .managed_accounts@pre ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                            ->any\<^sub>S\<^sub>e\<^sub>t()
        in  (A' .balance) \<doteq> (A .balance +\<^sub>i\<^sub>n\<^sub>t  amount)"
  Post frame: "let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and 
                          ((X .account_id) \<doteq> account_id)) ->any\<^sub>S\<^sub>e\<^sub>t()                   
               in  ((Set{A} :: \<cdot>Set( \<langle>\<langle>ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>)) ->oclIsModifiedOnly())"

Context Bank :: withdraw (c : Client, account_id : Integer, amount:Integer)
  Pre  "def": "(\<delta> c) and (\<delta> account_id) and (\<delta> amount)" (* this mimics the syntax : c : Client[1], account_id : Integer[1] *)
  Pre  "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t amount"
  Pre  "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and
                                                ((X .account_id) \<doteq> account_id) and
                                                (amount \<le>\<^sub>i\<^sub>n\<^sub>t (X .balance)) )"
  Post "let A' = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                        ->any\<^sub>S\<^sub>e\<^sub>t();
            A  = self .managed_accounts@pre ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                                            ->any\<^sub>S\<^sub>e\<^sub>t()
        in  (A' .balance) \<doteq> (A .balance -\<^sub>i\<^sub>n\<^sub>t  amount)"
  Post frame: "let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and 
                          ((X .account_id) \<doteq> account_id)) ->any\<^sub>S\<^sub>e\<^sub>t()                   
               in  ((Set{A} :: \<cdot>Set( \<langle>\<langle>ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>)) ->oclIsModifiedOnly())"


Context Bank :: get_balance (c : Client, account_id : Integer) : Integer
  Pre  "(\<delta> c) and (\<delta> account_id)" (* this mimics the syntax : c : Client[1], account_id : Integer[1] *)
  Pre  client_exists: "(self .managed_accounts) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and
                                                              ((X .account_id) \<doteq> account_id))"
  Post spec: "let A = self .managed_accounts 
                           ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id))
                           ->any\<^sub>S\<^sub>e\<^sub>t()
              in  result \<triangleq> (A .balance)"
  Post frame: "(Set{} :: \<cdot>Set(\<langle>\<langle>ty\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y\<rangle>\<^sub>\<bottom>\<rangle>\<^sub>\<bottom>)) ->oclIsModifiedOnly()"



section\<open>A Rudimentary Embedding of val's into the State-Exception Monad\<close>

definition val2Mon :: "('\<sigma>, '\<alpha>::null)val \<Rightarrow>  ('\<alpha>,'\<sigma> state)MON\<^sub>S\<^sub>E"
where     "val2Mon f \<equiv> (\<lambda>\<sigma>. if \<exists>\<sigma>'. \<exists>d.  ((\<sigma>,\<sigma>') \<Turnstile> (f \<triangleq> d))
                             then Some(SOME(d,\<sigma>'). ((\<sigma>,\<sigma>') \<Turnstile> (f \<triangleq> (\<lambda>_. d))))
                             else None)"

definition "bind_SE' f1 f2 = bind_SE f1 (f2 o K)"

syntax    (xsymbols)
          "_bind_SE'" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E"
          ("(2 _ ::= _; _)" [5,8,8]8)
translations
          "x ::= f; g" == "CONST bind_SE' (CONST val2Mon (f)) (% x . g)"




section\<open>Basic State-Management which is Missing\<close>
text\<open>The data-type package constructs a global, non-extensible type @{typ "\<AA>"} for all objects
living in the current 00 data universe. In constructs injections and constructors such as 
@{term "mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t \<Rightarrow> \<langle>int\<rangle>\<^sub>\<bottom> \<Rightarrow> \<langle>int\<rangle>\<^sub>\<bottom> \<Rightarrow> ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t"} and
@{term "in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t:: ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t \<Rightarrow> \<AA>"} as well as the universal oid-destructor
@{term "oid_of:: \<AA>\<Rightarrow>nat"}, and a kind of dereferantiator
@{term "deref_oid\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t"} but overall, the generated infrastructure for
what is called \<^emph>\<open>level 1 - model\<close> in Brucker and Wolff's 
\<^emph>\<open>An Extensible Encoding of Object-oriented Data Models in HOL\<close> is rudimentary.

The universe construction is the essential building block for the state construction
@{typ "\<AA> state"} and the resulting notion of state relations @{typ "(\<AA> state \<times> \<AA> state) set"}.
\<close>

text\<open>We construct what is missing by hand for the special case \<^verbatim>\<open>Account\<close>. 
Note that the entire interface is intended for "non-null objects"\<close>

definition is\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "\<AA> \<Rightarrow> bool" 
  where   "is\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x = (case x of in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x \<Rightarrow> True 
                                | in\<^sub>B\<^sub>a\<^sub>n\<^sub>k x  \<Rightarrow> False
                                | in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t x \<Rightarrow> False 
                                | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y x \<Rightarrow> False)"
(* etc. for Bank, Client, OclAny. *)

definition from\<AA>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "\<AA> \<Rightarrow> ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t" 
  where   "from\<AA>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x = (case x of in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x \<Rightarrow> x 
                                | in\<^sub>B\<^sub>a\<^sub>n\<^sub>k x  \<Rightarrow> undefined
                                | in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t x \<Rightarrow> undefined 
                                | in\<^sub>O\<^sub>c\<^sub>l\<^sub>A\<^sub>n\<^sub>y x \<Rightarrow> undefined)"
(* etc. for Bank, Client, OclAny. It should be very easy to generate these
by just changing the generated datatype definition for @{type "\<AA>"} ... *)

definition dest\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t \<Rightarrow> ty\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t \<times> \<langle>int\<rangle>\<^sub>\<bottom> \<times> \<langle>int\<rangle>\<^sub>\<bottom>" 
  where   "dest\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x = (case x of mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x xa xb \<Rightarrow> (x, xa, xb))"
(* other instances  for Bank, Client, OclAny analogously;
   this shortcut is pbly not the most necessary. *)

find_theorems "map_option"
definition  upd_obj\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t :: "(\<langle>int\<rangle>\<^sub>\<bottom> \<Rightarrow> \<langle>int\<rangle>\<^sub>\<bottom>) \<Rightarrow> (\<langle>int\<rangle>\<^sub>\<bottom> \<Rightarrow> \<langle>int\<rangle>\<^sub>\<bottom>) \<Rightarrow> ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t \<Rightarrow> ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t"
  where    "upd_obj\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t upd\<^sub>1 upd\<^sub>2 x = 
                  (case ((x::ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t)) of 
                     mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t oid aid bal \<Rightarrow> ((mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t oid (upd\<^sub>1 aid) (upd\<^sub>2 bal))))"



text\<open>Here is a bit more infrastructure on the object state:\<close>
consts is_defined_in_state :: "'a:: object \<Rightarrow> ('\<AA> :: object) state \<Rightarrow> bool" (infix "\<triangleleft>" 80)

overloading is_defined_in_state \<equiv> "is_defined_in_state :: (ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) \<Rightarrow> \<AA> state \<Rightarrow> bool"
begin
definition  is_defined_in_state\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t : "(x::ty\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t) \<triangleleft> (\<sigma>::\<AA> state) = (oid_of x \<in> dom (heap \<sigma>))"
end
(* other instances  for Bank, Client, OclAny analogously. *)

definition heap_upd\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t 
  where   "heap_upd\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t x upd\<^sub>1 upd\<^sub>2 = 
                heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of x) \<mapsto> in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t(upd_obj\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t upd\<^sub>1 upd\<^sub>2 x))))"

(* generic heap - theory *)
lemma heap_upd_commute : 
     "oid_of x \<noteq> oid_of y \<Longrightarrow> 
          (heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of x) \<mapsto> E))) o
          (heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of y) \<mapsto> E'))))) =
          (heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of y) \<mapsto> E'))) o
          (heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of x) \<mapsto> E)))))" 
  apply(rule ext)
  by (simp add: fun_upd_twist)

lemma heap_upd_idem : 
     "    (heap_update(\<lambda>\<sigma>.(\<sigma>(x \<mapsto> E))) o
          (heap_update(\<lambda>\<sigma>.(\<sigma>(x \<mapsto> E'))))) =
          (heap_update(\<lambda>\<sigma>.(\<sigma>(x \<mapsto> E))))" 
  by(rule ext, simp add: o_def)

lemma heap_upd_acces1 : 
     "   heap (heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of x) \<mapsto> E))) \<sigma>) (oid_of x)  =
         (Some E)" 
  by auto

lemma heap_upd_acces2 :
     "oid_of x \<noteq> oid_of y \<Longrightarrow> 
         heap (heap_update(\<lambda>\<sigma>.(\<sigma>((oid_of x) \<mapsto> E))) \<sigma>) (oid_of y)  =
         heap \<sigma> (oid_of y)" 
  by auto


text\<open>The @{term "heap_create\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t"}-operation creates within the heap of a state a new 
     @{term "Account"}-object with a fresh @{term "new_id"}. Arguments of the constructor maybe 
     @{term "null"}, but not @{term "invalid"} by construction (constructors are assumed to be
     strict).\<close>
definition heap_create\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t
  where   "heap_create\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t acc_id bal \<equiv>
               heap_update(\<lambda>\<sigma>. let new_oid = Max(dom \<sigma>) + 1 
                               in \<sigma>(new_oid \<mapsto> in\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t(mk\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t (mk\<E>\<X>\<T>\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t new_oid) acc_id bal)))"


(* We will also need an add_association and a delete_association. TODO. *)

section\<open>Derived Symbolic Execution Rules\<close>

lemma get_balanceE :
assumes 1: "\<sigma> \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r ::= (self :: \<cdot>Bank) .get_balance(c , a1) ; M r)"
and     2: "(\<sigma>,\<sigma>')\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> a1))"
and     3: "\<sigma>' = \<sigma>"
and     4: "(\<sigma>,\<sigma>')\<Turnstile> (let A = self .managed_accounts 
                               ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> a1))
                               ->any\<^sub>S\<^sub>e\<^sub>t()
                     in  result  \<triangleq> (A .balance))"
shows      "\<sigma>' \<Turnstile>\<^sub>M\<^sub>o\<^sub>n  (M (\<lambda>_. (result (\<sigma>,\<sigma>')))) "
oops



(* should be generated automatically from modifiesOnly({}) and the result = ... format
   of the body *)
lemma get_balance_detNquery:
  assumes 1 : "(\<sigma>,\<sigma>')\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> a1))"
  and     2 : "(\<sigma>,\<sigma>)\<Turnstile>(let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner)
                             \<doteq> c and ((X .account_id) \<doteq> a1))->any\<^sub>S\<^sub>e\<^sub>t()
                    in  result  \<triangleq> (A .balance)) "
shows   "(SOME (d, \<sigma>'). (\<sigma>, \<sigma>') \<Turnstile> self .get_balance(c,a1) \<triangleq> (\<lambda>_. d)) = (result (\<sigma>, \<sigma>), \<sigma>)"
  sorry

lemma get_balance_Symbex :
assumes 1: "(\<sigma>,\<sigma>')\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> a1))"
and     2: "(\<sigma>,\<sigma>)\<Turnstile>(let A = self .managed_accounts ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner)
                             \<doteq> c and ((X .account_id) \<doteq> a1))->any\<^sub>S\<^sub>e\<^sub>t()
                    in  result  \<triangleq> (A .balance)) "
shows      "(\<sigma>  \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r ::= (self :: \<cdot>Bank) .get_balance(c , a1) ; M r)) =
            (\<sigma>  \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( M (K(result (\<sigma>,\<sigma>)))))"
proof -
  have 3: "\<exists>\<sigma>' d. ((\<sigma>, \<sigma>') \<Turnstile> (self .get_balance(c,a1) \<triangleq> d))" sorry (* rephrases 2 on HOL level *)
  show ?thesis
      apply(rule trans)
      unfolding bind_SE'_def
       apply(rule exec_bind_SE_success)
      unfolding val2Mon_def
       apply(simp add: val2Mon_def 3)
       prefer 2
      apply(simp add: valid_SE_def unit_SE_def bind_SE_def )
      using "3" "local.1" "local.2" get_balance_detNquery by blast 
qed


lemma K_lemma : "K x = (\<lambda>_ . x)"
  apply(rule ext)
  by (simp add: K_def)


(* update on simply lifted base types; undefinedness is treated elsewhere *)
lemma deposit_Symbex :
assumes 1: "(\<sigma>,X)\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> account))"
and     2: "A  = self .managed_accounts@pre 
                      ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                      ->any\<^sub>S\<^sub>e\<^sub>t()"
and     3: "bal = (A .balance)"
and     4: "\<sigma>' = (heap_upd\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t((the o the)(A(\<sigma>,\<sigma>))) id ((K o the)((bal +\<^sub>i\<^sub>n\<^sub>t amount)(\<sigma>,\<sigma>))))\<sigma>"
shows      "(\<sigma>   \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r ::= (self :: \<cdot>Bank) .deposit(c, account, amount) ; M r)) =
            (\<sigma>'  \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( M (null)))"
proof -
  have 5: "\<exists>\<sigma>'. (\<sigma>, \<sigma>') \<Turnstile> self .deposit(c, account, amount) \<triangleq> null" sorry (* rephrases 2 on HOL level *)
  have 6: "\<exists>\<sigma>' d. (\<sigma>, \<sigma>') \<Turnstile> self .deposit(c, account, amount) \<triangleq> d"  using "5" by blast 
  show ?thesis
      apply(rule trans)
      unfolding bind_SE'_def            
       apply(rule exec_bind_SE_success)
      unfolding val2Mon_def
       apply(simp add: 6)
       prefer 2
      apply(simp add: null_option_def)
       apply(simp add: valid_SE_def unit_SE_def bind_SE_def null_fun_def K_lemma)
      sorry (* doable but quite a lot of work *) 
qed


lemma withdraw_Symbex :
assumes 1: "(\<sigma>,X)\<Turnstile>(self .managed_accounts@pre) ->exists\<^sub>S\<^sub>e\<^sub>t(X | (X .owner@pre) \<doteq> c and
                                                ((X .account_id@pre) \<doteq> account))"
and     2: "A  = self .managed_accounts@pre 
                      ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account)) 
                      ->any\<^sub>S\<^sub>e\<^sub>t()"
and     3: "bal = (A .balance)"
and     4: "\<sigma>' = (heap_upd\<^sub>A\<^sub>c\<^sub>c\<^sub>o\<^sub>u\<^sub>n\<^sub>t((the o the)(A(\<sigma>,\<sigma>))) id ((K o the)((bal -\<^sub>i\<^sub>n\<^sub>t amount)(\<sigma>,\<sigma>))))\<sigma>"
shows      "(\<sigma>   \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r ::= (self :: \<cdot>Bank) .withdraw(c, account, amount) ; M r)) =
            (\<sigma>'  \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( M (null)))"
proof -
  have 5: "\<exists>\<sigma>'. (\<sigma>, \<sigma>') \<Turnstile> self .withdraw(c, account, amount) \<triangleq> null" sorry (* rephrases 2 on HOL level *)
  have 6: "\<exists>\<sigma>' d. (\<sigma>, \<sigma>') \<Turnstile> self .withdraw(c, account, amount) \<triangleq> d"  using "5" by blast 
  show ?thesis
      apply(rule trans)
      unfolding bind_SE'_def            
       apply(rule exec_bind_SE_success)
      unfolding val2Mon_def
       apply(simp add: 6)
       prefer 2
      apply(simp add: null_option_def)
       apply(simp add: valid_SE_def unit_SE_def bind_SE_def null_fun_def K_lemma)
      sorry (* doable but quite a lot of work *) 
qed


lemma valid_sequence:
  assumes client_account_defined : 
        "\<forall> \<sigma> . (\<sigma>\<^sub>0, \<sigma>) \<Turnstile> bank .managed_accounts@pre
                         ->exists\<^sub>S\<^sub>e\<^sub>t(X|X .owner@pre \<doteq> c and (X .account_id@pre \<doteq> account_id))"
  and     2: "A  = bank .managed_accounts@pre 
                      ->select\<^sub>S\<^sub>e\<^sub>t(X | (X .owner) \<doteq> c and ((X .account_id) \<doteq> account_id)) 
                      ->any\<^sub>S\<^sub>e\<^sub>t()"
  and     3 : "(\<sigma>\<^sub>0, \<sigma>) \<Turnstile> null \<le>\<^sub>i\<^sub>n\<^sub>t A .balance" 
  shows
        "\<sigma>\<^sub>0 \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r ::= (bank :: \<cdot>Bank) .get_balance(c , account_id) ;
                  _  ::=  bank .deposit(c, account_id, a) ;
                  _  ::=  bank .withdraw(c, account_id, b) ;
                  r' ::=  bank .get_balance(c , account_id) ;
                  assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  ((\<sigma>,\<sigma>) \<Turnstile> (r +\<^sub>i\<^sub>n\<^sub>t a -\<^sub>i\<^sub>n\<^sub>t b \<doteq> r'))))"  
  apply(subst get_balance_Symbex)
      apply(rule client_account_defined[THEN spec],simp only:Let_def,rule UML_Logic.StrongEq_L_refl)
  apply(subst deposit_Symbex)
      apply(rule client_account_defined[THEN spec], rule 2,rule refl, rule refl)
  apply(subst withdraw_Symbex)
      defer 1
      apply(rule 2, rule refl)
  sorry


lemma valid_sequence2:
  assumes client_account_defined : 
        "\<forall> \<sigma> . (\<sigma>\<^sub>0, \<sigma>) \<Turnstile> bank .managed_accounts@pre
                         ->exists\<^sub>S\<^sub>e\<^sub>t(X|X .owner@pre \<doteq> c1 and (X .account_id@pre \<doteq> a))"
  and   "\<forall> \<sigma> . (\<sigma>\<^sub>0, \<sigma>) \<Turnstile> bank .managed_accounts@pre
                         ->exists\<^sub>S\<^sub>e\<^sub>t(X|X .owner@pre \<doteq> c3 and (X .account_id@pre \<doteq> b))"
  shows
        "\<sigma>\<^sub>0 \<Turnstile>\<^sub>M\<^sub>o\<^sub>n ( r    ::= (bank :: \<cdot>Bank) .get_balance(c1 , a1) ;
                  r'   ::=  bank .get_balance(c2 , a3) ;
                  _    ::=  bank .withdraw(c1 , a1, a) ;
                  _    ::=  bank .deposit(c2, a3, a) ;
                  r''  ::=  bank .get_balance(c1 , a1) ;
                  r''' ::=  bank .get_balance(c2 , a3) ;
                  assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  ((\<sigma>,\<sigma>) \<Turnstile> (r +\<^sub>i\<^sub>n\<^sub>t r' \<doteq> r'' +\<^sub>i\<^sub>n\<^sub>t r'''))))"
  oops




end
