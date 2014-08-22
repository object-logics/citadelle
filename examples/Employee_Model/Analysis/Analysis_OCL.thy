(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Analysis_OCL.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2014 Université Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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

theory
  Analysis_OCL
imports
  Analysis_UML (* Testing *)
begin
text {* \label{ex:employee-analysis:ocl} *}
section{* OCL Part: Standard State Infrastructure *}
text{* Ideally, these definitions are automatically generated from the class model. *}

section{* Invariant *}
text{* These recursive predicates can be defined conservatively
by greatest fix-point
constructions---automatically. See~\cite{brucker.ea:hol-ocl-book:2006,brucker:interactive:2007}
for details. For the purpose of this example, we state them as axioms
here.

\begin{ocl}
context Person
  inv label : self .boss <> null implies (self .salary  \<le>  ((self .boss) .salary))
\end{ocl}
*}

definition Person_label\<^sub>i\<^sub>n\<^sub>v :: "Person \<Rightarrow> Boolean" 
where     "Person_label\<^sub>i\<^sub>n\<^sub>v (self) \<equiv>  
                 (self .boss <> null implies (self .salary  \<le>\<^sub>i\<^sub>n\<^sub>t  ((self .boss) .salary)))"
                                       

definition Person_label\<^sub>i\<^sub>n\<^sub>v\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e :: "Person \<Rightarrow> Boolean" 
where     "Person_label\<^sub>i\<^sub>n\<^sub>v\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e (self) \<equiv>  
                 (self .boss@pre <> null implies (self .salary@pre \<le>\<^sub>i\<^sub>n\<^sub>t ((self .boss@pre) .salary@pre)))"

definition Person_label\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>i\<^sub>n\<^sub>v :: "Boolean"
where     "Person_label\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>i\<^sub>n\<^sub>v \<equiv> (Person .allInstances()->forAll(x | Person_label\<^sub>i\<^sub>n\<^sub>v (x)) and 
                                  (Person .allInstances@pre()->forAll(x | Person_label\<^sub>i\<^sub>n\<^sub>v\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e (x))))"
                                  
                                  
lemma "\<tau> \<Turnstile> \<delta> (X .boss) \<Longrightarrow> \<tau> \<Turnstile> Person .allInstances()->includes(X .boss) \<and>
                            \<tau> \<Turnstile> Person .allInstances()->includes(X) "
sorry 
(* To be generated generically ... hard, but crucial lemma that should hold. 
   It means that X and it successor are object representation that actually
   occur in the state. *)

lemma REC_pre : "\<tau> \<Turnstile> Person_label\<^sub>g\<^sub>l\<^sub>o\<^sub>b\<^sub>a\<^sub>l\<^sub>i\<^sub>n\<^sub>v 
       \<Longrightarrow> \<tau> \<Turnstile> Person .allInstances()->includes(X) (* X represented object in state *)
       \<Longrightarrow> \<exists> REC.  \<tau> \<Turnstile> REC(X)  \<triangleq> (Person_label\<^sub>i\<^sub>n\<^sub>v (X) and (X .boss <> null implies REC(X .boss)))"
sorry (* Attempt to allegiate the burden of he following axiomatizations: could be
         a witness for a constant specification ...*)       

text{* This allows to state a predicate: *}
                                       
axiomatization inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l :: "Person \<Rightarrow> Boolean"
where inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l_def:
"(\<tau> \<Turnstile> Person .allInstances()->includes(self)) \<Longrightarrow> 
 (\<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self) \<triangleq>  (self .boss <> null implies  
                                  (self .salary  \<le>\<^sub>i\<^sub>n\<^sub>t  ((self .boss) .salary)) and
                                   inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self .boss))))"

axiomatization inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e :: "Person \<Rightarrow> Boolean"
where inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e_def: 
"(\<tau> \<Turnstile> Person .allInstances@pre()->includes(self)) \<Longrightarrow>
 (\<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self) \<triangleq> (self .boss@pre <> null implies 
                                   (self .salary@pre  \<le>\<^sub>i\<^sub>n\<^sub>t  ((self .boss@pre) .salary@pre)) and
                                    inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self .boss@pre))))"


lemma inv_1 : 
"(\<tau> \<Turnstile> Person .allInstances()->includes(self)) \<Longrightarrow>
    (\<tau> \<Turnstile> inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self) = ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or>
                               ( \<tau> \<Turnstile> (self .boss <> null) \<and> 
                                 \<tau> \<Turnstile> ((self .salary)  \<le>\<^sub>i\<^sub>n\<^sub>t  (self .boss .salary))  \<and>
                                 \<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l(self .boss))))) "
sorry (* Let's hope that this holds ... *)


lemma inv_2 : 
"(\<tau> \<Turnstile> Person .allInstances@pre()->includes(self)) \<Longrightarrow>
    (\<tau> \<Turnstile> inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self)) =  ((\<tau> \<Turnstile> (self .boss@pre \<doteq> null)) \<or>
                                     (\<tau> \<Turnstile> (self .boss@pre <> null) \<and>
                                     (\<tau> \<Turnstile> (self .boss@pre .salary@pre \<le>\<^sub>i\<^sub>n\<^sub>t self .salary@pre))  \<and>
                                     (\<tau> \<Turnstile> (inv\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<^sub>_\<^sub>l\<^sub>a\<^sub>b\<^sub>e\<^sub>l\<^sub>A\<^sub>T\<^sub>p\<^sub>r\<^sub>e(self .boss@pre)))))"
sorry (* Let's hope that this holds ... *)

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: "Person \<Rightarrow> (\<AA>)st \<Rightarrow> bool" where
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or>
                      (\<tau> \<Turnstile> (self .boss <> null) \<and> (\<tau> \<Turnstile> (self .boss .salary \<le>\<^sub>i\<^sub>n\<^sub>t self .salary))  \<and>
                     ( (inv(self .boss))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"


section{* The Contract of a Recursive Query *}
text{* The original specification of a recursive query :
\begin{ocl}
context Person::contents():Set(Integer)
pre:   true
post:  result = if self.boss = null
                then Set{i}
                else self.boss.contents()->including(i)
                endif
\end{ocl} *}

(*
consts dot_contents :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
*)

                  
text{* For the case of recursive queries, we use at present just axiomatizations: *}               
                  
axiomatization contents :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
where contents_def:
"(self .contents()) = (\<lambda> \<tau>. (if \<tau> \<Turnstile> (\<delta> self)
                             then SOME res.((\<tau> \<Turnstile> true) \<and>
                                            (\<tau> \<Turnstile> (\<lambda>_ . res) \<triangleq> if (self .boss \<doteq> null)
                                                               then (Set{self .salary})
                                                               else (self .boss .contents()
                                                                        ->including(self .salary))
                                                               endif))
                             else invalid \<tau>))"
                             
declare dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_def [simp del]
declare dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_def  [simp del]

interpretation contents : contract0 "contents" "\<lambda> self. true"  
                          "\<lambda> self res.  res \<triangleq> if (self .boss \<doteq> null)
                                                               then (Set{self .salary})
                                                               else (self .boss .contents()
                                                                        ->including(self .salary))
                                                               endif"  
         proof (unfold_locales)
            show "\<And>self \<tau>. true \<tau> = true \<tau>" by auto
         next
            show "\<And>self. \<forall>\<sigma> \<sigma>' \<sigma>''. ((\<sigma>, \<sigma>') \<Turnstile> true) = ((\<sigma>, \<sigma>'') \<Turnstile> true)" by auto
         next
            show "\<And>self. self .contents() \<equiv>
                         \<lambda>\<tau>. if \<tau> \<Turnstile> \<delta> self
                             then SOME res. 
                                      \<tau> \<Turnstile> true \<and>
                                      \<tau> \<Turnstile> (\<lambda>_. res) \<triangleq> (if self .boss \<doteq> null then Set{self .salary} 
                                              else self .boss .contents()->including(self .salary) 
                                              endif)
                             else invalid \<tau>"
                  by(auto simp: contents_def )
         next
            have A:"\<And>self \<tau>. ((\<lambda>_. self \<tau>) .boss \<doteq> null) \<tau> = (\<lambda>_. (self .boss \<doteq> null) \<tau>) \<tau>"  sorry
            have B:"\<And>self \<tau>. (\<lambda>_. Set{(\<lambda>_. self \<tau>) .salary} \<tau>) = (\<lambda>_. Set{self .salary} \<tau>)" sorry
            have C:"\<And>self \<tau>. ((\<lambda>_. self \<tau>).boss .contents()->including((\<lambda>_. self \<tau>).salary) \<tau>) = 
                              (self .boss .contents() ->including(self .salary) \<tau>)" sorry
            show "\<And>self res \<tau>.
                   (res \<triangleq> if (self .boss) \<doteq> null then Set{self .salary} 
                           else self .boss .contents()->including(self .salary) endif) \<tau> =
                   ((\<lambda>_. res \<tau>) \<triangleq> if (\<lambda>_. self \<tau>) .boss \<doteq> null then Set{(\<lambda>_. self \<tau>) .salary} 
                                   else(\<lambda>_. self \<tau>) .boss .contents()->including((\<lambda>_. self \<tau>) .salary) endif) \<tau>"
           apply(subst cp_StrongEq)
           apply(subst (2) cp_StrongEq)
           apply(subst cp_OclIf)
           apply(subst (2)cp_OclIf)
           by(simp add: A B C)
         qed

         
text{* Specializing @{thm contents.unfold2}, one gets the following more practical rewrite
rule that is amenable to symbolic evaluation: *}
theorem unfold_contents :
   assumes "cp E"
   and     "\<tau> \<Turnstile> \<delta> self"
   shows   "(\<tau> \<Turnstile> E (self .contents())) = 
            (\<tau> \<Turnstile> E (if self .boss \<doteq> null 
                    then Set{self .salary} 
                    else self .boss .contents()->including(self .salary) endif))"
by(rule contents.unfold2[of _ _ _ "\<lambda> X. true"], simp_all add: assms)


text{* Since we have only one interpretation function, we need the corresponding
operation on the pre-state: *}               

consts contentsATpre :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents@pre'('))" 50)

axiomatization where contentsATpre_def:
" (self).contents@pre() = (\<lambda> \<tau>.
      (if \<tau> \<Turnstile> (\<delta> self)
       then SOME res.((\<tau> \<Turnstile> true) \<and>                                  (* pre *)
                      (\<tau> \<Turnstile> ((\<lambda>_. res) \<triangleq> if (self).boss@pre \<doteq> null  (* post *)
                                         then Set{(self).salary@pre}
                                         else (self).boss@pre .contents@pre()
                                                    ->including(self .salary@pre)
                                         endif)))
        else invalid \<tau>))"

declare dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<S>\<A>\<L>\<A>\<R>\<Y>_at_pre_def [simp del]
declare dot\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n\<B>\<O>\<S>\<S>_at_pre_def  [simp del]

interpretation contentsATpre : contract0 "contentsATpre" "\<lambda> self. true"  
                          "\<lambda> self res.  res \<triangleq> if (self .boss@pre \<doteq> null)
                                                               then (Set{self .salary@pre})
                                                               else (self .boss@pre .contents@pre()
                                                                        ->including(self .salary@pre))
                                                               endif"     
         proof (unfold_locales)
            show "\<And>self \<tau>. true \<tau> = true \<tau>" by auto
         next
            show "\<And>self. \<forall>\<sigma> \<sigma>' \<sigma>''. ((\<sigma>, \<sigma>') \<Turnstile> true) = ((\<sigma>, \<sigma>'') \<Turnstile> true)" by auto
         next
            show "\<And>self. self .contents@pre() \<equiv>
                         \<lambda>\<tau>. if \<tau> \<Turnstile> \<delta> self
                             then SOME res. 
                                      \<tau> \<Turnstile> true \<and>
                                      \<tau> \<Turnstile> (\<lambda>_. res) \<triangleq> (if self .boss@pre \<doteq> null then Set{self .salary@pre} 
                                              else self .boss@pre .contents@pre()->including(self .salary@pre) 
                                              endif)
                             else invalid \<tau>"
                  by(auto simp: contentsATpre_def)
         next
            have A:"\<And>self \<tau>. ((\<lambda>_. self \<tau>) .boss@pre \<doteq> null) \<tau> = (\<lambda>_. (self .boss@pre \<doteq> null) \<tau>) \<tau>" sorry
            have B:"\<And>self \<tau>. (\<lambda>_. Set{(\<lambda>_. self \<tau>) .salary@pre} \<tau>) = (\<lambda>_. Set{self .salary@pre} \<tau>)" sorry
            have C:"\<And>self \<tau>. ((\<lambda>_. self \<tau>).boss@pre .contents@pre()->including((\<lambda>_. self \<tau>).salary@pre) \<tau>) = 
                              (self .boss@pre .contents@pre() ->including(self .salary@pre) \<tau>)" sorry
            show "\<And>self res \<tau>.
                   (res \<triangleq> if (self .boss@pre) \<doteq> null then Set{self .salary@pre} 
                           else self .boss@pre .contents@pre()->including(self .salary@pre) endif) \<tau> =
                   ((\<lambda>_. res \<tau>) \<triangleq> if (\<lambda>_. self \<tau>) .boss@pre \<doteq> null then Set{(\<lambda>_. self \<tau>) .salary@pre} 
                                   else(\<lambda>_. self \<tau>) .boss@pre .contents@pre()->including((\<lambda>_. self \<tau>) .salary@pre) endif) \<tau>"
           apply(subst cp_StrongEq)
           apply(subst (2) cp_StrongEq)
           apply(subst cp_OclIf)
           apply(subst (2)cp_OclIf)
           by(simp add: A B C)
         qed
  
text{* Again, we derive via @{thm [source] contents.unfold2} a Knaster-Tarski like Fixpoint rule
that is amenable to symbolic evaluation: *}
theorem unfold_contentsATpre :
   assumes "cp E"
   and     "\<tau> \<Turnstile> \<delta> self"
   shows   "(\<tau> \<Turnstile> E (self .contents@pre())) = 
            (\<tau> \<Turnstile> E (if self .boss@pre \<doteq> null 
                    then Set{self .salary@pre} 
                    else self .boss@pre .contents@pre()->including(self .salary@pre) endif))"
by(rule contentsATpre.unfold2[of _ _ _ "\<lambda> X. true"], simp_all add: assms)

         
text{* Note that these \inlineocl{@pre} variants on methods are only available on queries, \ie,
operations without side-effect. *}

(* Missing: Properties on Casts, type-tests, and equality vs. projections. *)

section{* The Contract of a User-defined Method *}
text{*
The example specification in high-level OCL input syntax reads as follows:
\begin{ocl}
context Person::insert(x:Integer)
pre: true
post: contents():Set(Integer)
contents() = contents@pre()->including(x)
\end{ocl}

This boils down to:
*}

definition insert :: "Person \<Rightarrow>Integer \<Rightarrow> Void"  ("(1(_).insert'(_'))" 50)
where "self .insert(x) \<equiv> 
            (\<lambda> \<tau>. if (\<tau> \<Turnstile> (\<delta> self)) \<and>  (\<tau> \<Turnstile> \<upsilon> x)
                  then SOME res. (\<tau> \<Turnstile> true \<and>  
                                 (\<tau> \<Turnstile> ((self).contents() \<triangleq> (self).contents@pre()->including(x))))
                  else invalid \<tau>)"  

text{* The semantic consequences of this definition were computed inside this locale interpretation:*}
interpretation insert : contract1 "insert" "\<lambda> self x. true" 
                                  "\<lambda> self x res. ((self .contents()) \<triangleq> 
                                                       (self .contents@pre()->including(x)))" 
         apply unfold_locales  apply(auto simp:insert_def)
         apply(subst cp_StrongEq) apply(subst (2) cp_StrongEq)
         apply(subst contents.cp0)
         apply(subst UML_Set.OclIncluding.cp0)
         apply(subst (2) UML_Set.OclIncluding.cp0)
         apply(subst contentsATpre.cp0)
         by(simp)  (* an extremely hacky proof that cries for reformulation and automation - bu *)

         
text{* The result of this locale interpretation for our @{term insert}  contract is the following 
set of properties, which serves as basis for automated deduction on them: 

\begin{table}[htbp]
   \centering
   \begin{tabu}{lX[,c,]}
      \toprule
      Name & Theorem \\
      \midrule
      @{thm [source] insert.strict0}  & @{thm  [display=false] insert.strict0} \\
      @{thm [source] insert.nullstrict0}  & @{thm  [display=false] insert.nullstrict0} \\
      @{thm [source] insert.strict1}  & @{thm  [display=false] insert.strict1} \\
      @{thm [source] insert.cp\<^sub>P\<^sub>R\<^sub>E}  & @{thm  [display=false] insert.cp\<^sub>P\<^sub>R\<^sub>E} \\
      @{thm [source] insert.cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T}  & @{thm  [display=false] insert.cp\<^sub>P\<^sub>O\<^sub>S\<^sub>T} \\
      @{thm [source] insert.cp_pre}  & @{thm  [display=false] insert.cp_pre} \\
      @{thm [source] insert.cp_post}  & @{thm [display=false] insert.cp_post} \\
      @{thm [source] insert.cp}   & @{thm  [display=false] insert.cp} \\
      @{thm [source] insert.cp0}   & @{thm  [display=false] insert.cp0} \\   
      @{thm [source] insert.def_scheme}   & @{thm  [display=false] insert.def_scheme} \\
      @{thm [source] insert.unfold} & @{thm [display=false] insert.unfold} \\
      @{thm [source] insert.unfold2} & @{thm [display=false] insert.unfold2} \\
      \bottomrule
   \end{tabu}
   \caption{Basic semantic constant definitions of the logic (except @{term null})}
   \label{tab:sem_basic_constants}
\end{table}

*}
         
end
