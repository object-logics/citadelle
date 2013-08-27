(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_DesignModel_OCLPart.thy --- OCL Contracts and an Example.
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
  Employee_AnalysisModel_OCLPart
imports
  Employee_AnalysisModel_UMLPart (* Testing *)
begin

section{* Standard State Infrastructure *}
text{* These definitions should be generated --- again --- from the class diagram. *}

section{* Invariant *}
text{* These recursive predicates can be defined conservatively 
by greatest fix-point constructions - automatically. See HOL-OCL Book
for details. For the purpose of this example, we state them as axioms
here.*}
axiomatization inv_Person :: "Person \<Rightarrow> Boolean"
where A : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Person(self)) =
                   ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .boss <> null) \<and> (\<tau> \<Turnstile> ((self .salary)  \<le>\<^isub>o\<^isub>c\<^isub>l  (self .boss .salary)))  \<and> 
                     (\<tau> \<Turnstile> (inv_Person(self .boss))))) "


axiomatization inv_Person_at_pre :: "Person \<Rightarrow> Boolean"
where B : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Person_at_pre(self)) =
                   ((\<tau> \<Turnstile> (self .boss@pre \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .boss@pre <> null) \<and> 
                     (\<tau> \<Turnstile> (self .boss@pre .salary@pre \<le>\<^isub>o\<^isub>c\<^isub>l self .salary@pre))  \<and> 
                     (\<tau> \<Turnstile> (inv_Person_at_pre(self .boss@pre))))) "

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: "Person \<Rightarrow> (\<AA>)st \<Rightarrow> bool" where 
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or> 
                      (\<tau> \<Turnstile> (self .boss <> null) \<and> (\<tau> \<Turnstile> (self .boss .salary \<le>\<^isub>o\<^isub>c\<^isub>l self .salary))  \<and> 
                     ( (inv(self .boss))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"

section{* The contract of a recursive query : *}
text{* The original specification of a recursive query :
\begin{verbatim}
context Person::contents():Set(Integer)
post:  result = if self.boss = null 
                then Set{i}
                else self.boss.contents()->including(i)
                endif
\end{verbatim} *}


consts dot_contents :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
 
axiomatization dot_contents_def where
"(\<tau> \<Turnstile> ((self).contents() \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then ((\<tau> \<Turnstile> true) \<and>  
        (\<tau> \<Turnstile> (result \<triangleq> if (self .boss \<doteq> null) 
                        then (Set{self .salary}) 
                        else (self .boss .contents()->including(self .salary))
                        endif)))
  else \<tau> \<Turnstile> result \<triangleq> invalid)"


consts dot_contents_AT_pre :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents@pre'('))" 50)
 
axiomatization where dot_contents_AT_pre_def:
"(\<tau> \<Turnstile> (self).contents@pre() \<triangleq> result) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then \<tau> \<Turnstile> true \<and>                                (* pre *)
        \<tau> \<Turnstile> (result \<triangleq> if (self).boss@pre \<doteq> null  (* post *)
                        then Set{(self).salary@pre}
                        else (self).boss@pre .contents@pre()->including(self .salary@pre)
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
context Person::insert(x:Integer) 
post: contents():Set(Integer)
contents() = contents@pre()->including(x)
\end{verbatim}
*}

consts dot_insert :: "Person \<Rightarrow> Integer \<Rightarrow> Void"  ("(1(_).insert'(_'))" 50)

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


end
