(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_linked_list_ops.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012      Université Paris-Sud, France
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

header{* Part III: OCL Contracts and an Example *}

(* This example is not yet balanced. Some parts of should go to 
   Part II : State and Objects. *)

theory 
  OCL_linked_list_ops
imports
  OCL_linked_list_data (* Testing *)
begin

section{* Standard State Infrastructure *}
text{* These definitions should be generated --- again --- from the class diagram. *}

section{* Invariant *}
text{* These recursive predicates can be defined conservatively 
by greatest fix-point constructions - automatically. See HOL-OCL Book
for details. For the purpose of this example, we state them as axioms
here.*}
axiomatization inv_Node :: "Node \<Rightarrow> Boolean"
where A : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node(self)) =
                   ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node(self .next))))) "


axiomatization inv_Node_at_pre :: "Node \<Rightarrow> Boolean"
where B : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node_at_pre(self)) =
                   ((\<tau> \<Turnstile> (self .next@pre \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next@pre <> null) \<and> (\<tau> \<Turnstile> (self .next@pre .i@pre \<prec> self .i@pre))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node_at_pre(self .next@pre))))) "

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: "Node \<Rightarrow> (\<AA>)st \<Rightarrow> bool" where 
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                      (\<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     ( (inv(self .next))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"


section{* The contract of a recursive query : *}
text{* The original specification of a recursive query :
\begin{verbatim}
context Node::contents():Set(Integer)
post:  result = if self.next = null 
                then Set{i}
                else self.next.contents()->including(i)
                endif
\end{verbatim} *}


consts dot_contents :: "Node \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
 
axiomatization dot_contents_def where
"(\<tau> \<Turnstile> ((self).contents() \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then ((\<tau> \<Turnstile> true) \<and>  
        (\<tau> \<Turnstile> (result \<triangleq> if (self .next \<doteq> null) 
                        then (Set{self .i}) 
                        else (self .next .contents()->including(self .i))
                        endif)))
  else \<tau> \<Turnstile> result \<triangleq> invalid)"


consts dot_contents_AT_pre :: "Node \<Rightarrow> Set_Integer"  ("(1(_).contents@pre'('))" 50)
 
axiomatization where dot_contents_AT_pre_def:
"(\<tau> \<Turnstile> (self).contents@pre() \<triangleq> result) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then \<tau> \<Turnstile> true \<and>                                (* pre *)
        \<tau> \<Turnstile> (result \<triangleq> if (self).next@pre \<doteq> null  (* post *)
                        then Set{(self).i@pre}
                        else (self).next@pre .contents@pre()->including(self .i@pre)
                        endif)
  else \<tau> \<Turnstile> result \<triangleq> invalid)"

text{* Note that these @pre variants on methods are only available on queries, i.e.
operations without side-effect. *}
(* TODO: Should be rephased by conservative means... *)

(* Missing: Properties on Casts, type-tests, and equality vs. projections. *)

section{* The contract of a method. *}
text{*
The specification in high-level OCL input syntax reads as follows:
\begin{verbatim}
context Node::insert(x:Integer) 
post: contents():Set(Integer)
contents() = contents@pre()->including(x)
\end{verbatim}
*}

consts dot_insert :: "Node \<Rightarrow> Integer \<Rightarrow> Void"  ("(1(_).insert'(_'))" 50)

axiomatization where dot_insert_def:
"(\<tau> \<Turnstile> ((self).insert(x) \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>  
  then \<tau> \<Turnstile> true \<and>  
       \<tau> \<Turnstile> ((self).contents() \<triangleq> (self).contents@pre()->including(x))
  else \<tau> \<Turnstile> ((self).insert(x) \<triangleq> invalid))"

(*
lemma H : "(\<tau> \<Turnstile> (self).insert(x) \<triangleq> result)"
 nitpick
thm dot_insert_def
oops
takes too long...
*) 
(* Old stuff by Matthias Diss - will not really work any longer in this context: 

declare OO_List.inv.simps [testgen_OO_eqs]
declare contents_def [testgen_OO_eqs]

test_spec "inv pre_state s \<longrightarrow> contents (post_state pre_state x) (Some s) = contents_at_pre pre_state (Some s) \<union> {x}"
apply(gen_test_cases "post_state" simp del: contents_post contents_post2)
store_test_thm "oo_test"

gen_test_data "oo_test"

thm oo_test.test_data

ML {*

val test_tac = alias_closure_tac @{context} @{typ "'a option"}

*}

lemma "(at_next st y) = (at_next st (at_next st y))" 
apply(tactic "test_tac 1")
apply(simp_all)
oops

lemma rewr: "id (x::int) = id x + id x - id x"
apply(simp)
done

lemma "(x::int) = id x"
(* apply(tactic "EqSubst.eqsubst_tac @{context} [1] [@{thm rewr}] 1") *)
apply(tactic "bounded_unfold_tac @{context} 3 @{thm rewr} 1")
oops
*)

end
