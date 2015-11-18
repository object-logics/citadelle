(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Flight_Model_compact.thy --- OCL Contracts and an Example.
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

header{* Part ... *}

theory
  Flight_Model_compact
imports
  "../../src/UML_OCL"
  (* separate compilation : UML_OCL *)
begin

section{* Class Model *}

Class Flight
  Attributes
    seats : Integer
    "from" : String
    to : String
End

term id (* REMARK "id" already exists *)
Class Reservation
  Attributes
    id : Integer
    date : Week
End

Class Person
  Attributes
    name : String
End

Class Client < Person
  Attributes
    address : String
End

Class Staff < Person
End

Association passengers
  Between Person      [*]
            Role passengers
          Flight      [*]
            Role flights
End

Aggregation flights
  Between Flight      [1]
            Role flight
          Reservation [*]
            Role fl_res Sequence_
End

Association reservations
  Between Client      [1]
            Role client
          Reservation [*]
            Role cl_res
End

Association connection
  Between Reservation [0 \<bullet>\<bullet> 1]
            Role "next"
          Reservation [0 \<bullet>\<bullet> 1]
            Role prev
End

Enum Week 
  [ Mon, Tue, Wed, Thu, Fri, Sat, Sun ]
End!

(*
(* Illustration of a wrong model transition: *)
Instance R00 :: Reservation = [ id = 00, flight = [ F1 ], "next" = R11 ]
     and R11 :: Reservation = [ id = 11, flight = [ F1, F2 ], "next" = R00 ]
     and R22 :: Reservation = [ id = 22, "next" = [ R00, R11, R22 ] ]
     and F1 :: Flight = [ seats = 120, "from" = "Ostrava", to = "Plzen" ]
     and F2 :: Flight = [ seats = 370, "from" = "Plzen", to = "Brno" ]
(*
R00 .flight = Set{ F1 }
R00 .client = Set{} // minimum constraint [1] not satisfied
R00 .prev = Set{ R11 , R22 } // maximum constraint [0 .. 1] not satisfied
R00 .next = Set{ R11 }
R11 .flight = Set{ F1 , F2 } // maximum constraint [1] not satisfied
R11 .client = Set{} // minimum constraint [1] not satisfied
R11 .prev = Set{ R00 , R22 } // maximum constraint [0 .. 1] not satisfied
R11 .next = Set{ R00 }
R22 .flight = Set{} // minimum constraint [1] not satisfied
R22 .client = Set{} // minimum constraint [1] not satisfied
R22 .prev = Set{ R22 }
R22 .next = Set{ R00 , R11 , R22 } // maximum constraint [0 .. 1] not satisfied
F1 .passengers = Set{}
F1 .fl_res = Set{ R00 , R11 }
F2 .passengers = Set{}
F2 .fl_res = Set{ R11 }
8 error(s) in multiplicity constraints
*)
*)

section{* Two State Instances of the Class Model *}

text{* The following Featherweight OCL statement creates  the (typed) object instances \verb$S1$,
\verb$C1$, \verb$R11$, \verb$R21$, \verb$F1$ and \verb$F2$ and verifies the 
corresponding multiplicities.
\begin{verbatim}
S1 .flights \<cong> Set{ F1 } 
C1 .flights \<cong> Set{ F1 } 
C1 .cl_res \<cong> Set{ R11 } 
C2 .flights \<cong> Set{ F1 } 
C2 .cl_res \<cong> Set{ R21 } 
R11 .flight \<cong> Set{ F1 } 
R11 .client \<cong> Set{ C1 } 
R11 .prev \<cong> Set{} 
R11 .next \<cong> Set{} 
R21 .flight \<cong> Set{ F1 } 
R21 .client \<cong> Set{ C2 } 
R21 .prev \<cong> Set{} 
R21 .next \<cong> Set{} 
F1 .passengers \<cong> Set{ S1 , C1 , C2 } 
F1 .fl_res \<cong> Set{ R11 , R21 } 
F2 .passengers \<cong> Set{} 
F2 .fl_res \<cong> Set{}
\end{verbatim}
*}
Instance S1  :: Staff  = [ name = "Mallory" , flights = F1 ]
     and C1  :: Client = [ name = "Bob" , address = "Plzen" , flights = F1 , cl_res = R11 ]
     and C2  :: Client = [ name = "Alice" , address = "Ostrava" , flights = F1 , cl_res = R21 ]
     and R11 :: Reservation = [ id = 12345 , flight = F1 , date = Mon ]
     and R21 :: Reservation = [ id = 98765 , flight = F1 ]
     and F1  :: Flight = [ seats = 120 , "from" = "Ostrava" , to = "Plzen" ]
     and F2  :: Flight = [ seats = 370 , "from" = "Plzen" , to = "Brno" ]

text{* We check that, for example, the constant @{term S1} is now declared with the right OCL type. *}
term "S1 ::\<cdot> Staff"

text{* In the following command, we place the object instances into a state @{text "\<sigma>\<^sub>1"}. This generates a definition
for the latter as well as a number of theorems resulting from it, for example:
\begin{isar}
(\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Staff .allInstancesOf@pre() \<triangleq> Set{S1}
(\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Client .allInstancesOf@pre() \<triangleq> Set{C1,C2}
(\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Reservation .allInstancesOf@pre() \<triangleq> Set{R11,R12}
(\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Flight .allInstancesOf@pre() \<triangleq> Set{F1,F2}
\end{isar}
as well as:
\begin{isar}
(\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Staff .allInstancesOf() \<triangleq> Set{S1}
(\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Client .allInstancesOf() \<triangleq> Set{C1,C2}
(\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Reservation .allInstancesOf() \<triangleq> Set{R11,R12}
(\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Flight .allInstancesOf() \<triangleq> Set{F1,F2}
\end{isar}
All these lemmas were stated under the precondition that the object instances are actually 
defined entities.

To simplify matters, we group all these definedness assumptions in a locale.

*}


State \<sigma>\<^sub>1 =  [ S1, C1, C2, R11, R21, F1, F2 ]

text{* The following statement shows that object instances can also be generated
inside the \verb$State$-command on the fly. The latter were bound to generated
constant names like $\sigma_1\_object1$, etc.

Thus, the resulting object instances look like:
\begin{isar}
\<sigma>\<^sub>2_object1 .flights \<cong> Set{ /*8*/ } 
\<sigma>\<^sub>2_object1 .cl_res \<cong> Set{ /*6*/ } 
\<sigma>\<^sub>2_object2 .flights \<cong> Set{ /*8*/ , /*9*/ } 
\<sigma>\<^sub>2_object2 .cl_res \<cong> Set{ \<sigma>\<^sub>2_object4 , \<sigma>\<^sub>2_object7 } 
\<sigma>\<^sub>2_object4 .flight \<cong> Set{ /*8*/ } 
\<sigma>\<^sub>2_object4 .client \<cong> Set{ \<sigma>\<^sub>2_object2 } 
\<sigma>\<^sub>2_object4 .prev \<cong> Set{} 
\<sigma>\<^sub>2_object4 .next \<cong> Set{ \<sigma>\<^sub>2_object7 } 
\<sigma>\<^sub>2_object7 .flight \<cong> Set{ /*9*/ } 
\<sigma>\<^sub>2_object7 .client \<cong> Set{ \<sigma>\<^sub>2_object2 } 
\<sigma>\<^sub>2_object7 .prev \<cong> Set{ \<sigma>\<^sub>2_object4 } 
\<sigma>\<^sub>2_object7 .next \<cong> Set{} 
\end{isar}

Note that there is a mechanism to reference objects via the key-word \verb$self$
with its number in the list of declarations; this indexing starts with 0 for the first position.
*}
State \<sigma>\<^sub>2 =
  [ S1
  , ([ name = "Bob", address = "Praha" , flights = F1 , cl_res = R11 ] :: Client)
  , ([ name = "Alice",address = "Ostrava",flights=[F1,F2],cl_res=[self 4,self 7]]::Client)
  , R11
  , ([ id = 98765 , flight = F1 , "next" = self 7] :: Reservation)
  , F1
  , F2
  , ([ id = 19283 , flight = F2 ] :: Reservation) ]

text{* The subsequent command establishes for a pair of a pre- and a post state,
so : a state-transition, that a number of 
crucial properties are satisfied. 
For instance, the well-formedness of the two states is proven:
\begin{isar}
   WFF(\<sigma>_1, \<sigma>_2)
\end{isar}
Furthermore, for each object $X$ either a lemma of the form:
\begin{isar}
  (\<sigma>\<^sub>1,\<sigma>\<^sub>2) \<Turnstile> X .oclIsNew() 
\end{isar}
or 
\begin{isar}
  (\<sigma>\<^sub>1,\<sigma>\<^sub>2) \<Turnstile> X .oclIsDeleted() 
\end{isar}
or 
\begin{isar}
  (\<sigma>\<^sub>1,\<sigma>\<^sub>2) \<Turnstile> X .oclIsMaintained() 
\end{isar}
where the latter only means that $X$'s object id exists both in $\sigma_1$ and
$\sigma_2$, not that its content has not been changed.
*}

(* TODO : Rename PrePost into : Transition *)
PrePost \<sigma>\<^sub>1 \<sigma>\<^sub>2


locale TRANS_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin
lemma \<sigma>\<^sub>1: "state_interpretation_\<sigma>\<^sub>1 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>1_def,
   default,
   simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

lemma \<sigma>\<^sub>2: "state_interpretation_\<sigma>\<^sub>2 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>2_def,
   default,
   simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

lemma \<sigma>\<^sub>1_\<sigma>\<^sub>2: "pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2 \<tau>"
by(simp add: pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def,
   default,
   simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+,
   (simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

definition \<sigma>\<^sub>0 :: "\<AA> state" where "\<sigma>\<^sub>0 = state.make Map.empty Map.empty"

definition "\<sigma>\<^sub>1 = pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>2 = pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid6 oid8 oid9 oid10 oid11 oid12 oid13
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "s1 = state_\<sigma>\<^sub>1.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "s2 = state_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid10 oid11 oid6 oid12 oid8 oid9 oid13
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

text{* Both formats are equivalent: *}

lemma \<sigma>\<^sub>1_s1: "\<sigma>\<^sub>1 = s1"
unfolding \<sigma>\<^sub>1_def s1_def 
 apply(subst pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def)
by(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def], simp)


lemma \<sigma>\<^sub>2_s2: "\<sigma>\<^sub>2 = s2"
unfolding \<sigma>\<^sub>2_def s2_def 
 apply(subst pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def)
by(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def], simp)

lemma WFF_\<sigma>\<^sub>1_\<sigma>\<^sub>2: "WFF (\<sigma>\<^sub>1, \<sigma>\<^sub>2)"
unfolding \<sigma>\<^sub>1_s1 \<sigma>\<^sub>2_s2 s1_def s2_def
 apply(rule pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.basic_\<sigma>\<^sub>1_\<sigma>\<^sub>2_wff)
 apply(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def])
by(simp_all add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2 pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2 
      (* *)
      oid_of_\<AA>_def oid_of_ty\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_def oid_of_ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
      (* *)
      S1\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_def C1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def C2\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def R21\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
      \<sigma>\<^sub>2_object1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def \<sigma>\<^sub>2_object2\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def \<sigma>\<^sub>2_object4\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def \<sigma>\<^sub>2_object7\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def)

end


section{* Annotations of the Class Model in OCL *}

text{* Subsequently, we state a desired class invariant for \verb$Flight$'s in the usual
OCL syntax: *}
Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .fl_res)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .client .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"



section{* Model Analysis I: A satisfiability proof of the invariants. *}

text{* We wish to analyse our class model and show that the entire set of invariants can
be satisfied, \ie{} there exists legal states that satisfy all constraints imposed
by the class invariants. *}

(* TODO : rename: pre_post into transition *)

context pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin

lemma Flight_at_pre_sat: "let \<tau> = (\<sigma>\<^sub>1,\<sigma>\<^sub>2) in
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))) \<longrightarrow>
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))) \<longrightarrow>
                           Flight_Aat_pre \<tau>"
proof - 
 have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre() in
                       (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
 by(simp add: Let_def, rule OclForall_body_trivial, rule OclAllInstances_at_pre_defined)
 show ?thesis
  apply(simp add: Let_def, intro impI)
  apply(simp add: Flight_Aat_pre_def StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def], where P = "\<lambda>x. x"])
  apply(subst StrongEq_L_subst3[where x = "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre()"], simp, simp add: \<sigma>\<^sub>1_def)
   apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'[THEN iffD1, OF _ _ state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Flight[OF \<sigma>\<^sub>1, simplified Flight_def]])
            apply(rule OclAllInstances_at_pre_valid)
           apply(simp add: F1_def F2_def)
  apply(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
  apply(simp add: OclValid_def, subst cp_OclOr, subst cp_OclIf, subst (1 2) cp_OclAnd, subst cp_OclIf)
 by(simp add: F1_def F2_def OclIf_def, fold true_def, simp add: OclOr_true2)
qed

lemma Flight_at_pre_sat': "\<exists> \<tau>.
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))) \<longrightarrow>
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))) \<longrightarrow>
                        Flight_Aat_pre \<tau>"
by(rule exI[where x = "(\<sigma>\<^sub>1,\<sigma>\<^sub>2)"], rule Flight_at_pre_sat[simplified Let_def])

lemma Flight_at_post_sat: "let \<tau> = (\<sigma>\<^sub>1,\<sigma>\<^sub>2) in
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats))) \<longrightarrow>
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats))) \<longrightarrow>
                           Flight_A \<tau>"
proof - 
 have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances() in
                       (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
 by(simp add: Let_def, rule OclForall_body_trivial, rule OclAllInstances_at_post_defined)
 show ?thesis
  apply(simp add: Let_def, intro impI)
  apply(simp add: Flight_A_def StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def], where P = "\<lambda>x. x"])
  apply(subst StrongEq_L_subst3[where x = "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances()"], simp, simp add: \<sigma>\<^sub>2_def)
   apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'[THEN iffD1, OF _ _ state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_OclAllInstances_at_post_exec_Flight[OF \<sigma>\<^sub>2, simplified Flight_def]])
            apply(rule OclAllInstances_at_post_valid)
           apply(simp add: F1_def F2_def)
  apply(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
  apply(simp add: OclValid_def, subst cp_OclOr, subst cp_OclIf, subst (1 2) cp_OclAnd, subst cp_OclIf)
 by(simp add: F1_def F2_def OclIf_def, fold true_def, simp add: OclOr_true2)
qed

lemma Flight_at_post_sat': "\<exists> \<tau>.
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats))) \<longrightarrow>
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats))) \<longrightarrow>
                        Flight_A \<tau>"
by(rule exI[where x = "(\<sigma>\<^sub>1,\<sigma>\<^sub>2)"], rule Flight_at_post_sat[simplified Let_def])

end

context TRANS_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin
lemma Flight_at_pre_sat: "\<exists> \<tau>. Flight_Aat_pre \<tau>"
proof - 
 note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
 note PP = \<sigma>\<^sub>1_\<sigma>\<^sub>2[of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)", simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def]

 have F1_val: "F1 .seats@pre (s1, s2) = (\<lambda>_. \<lfloor>\<lfloor>120\<rfloor>\<rfloor>) (s1, s2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
  apply(subst (8) s1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 have F2_val: "F2 .seats@pre (s1, s2) = (\<lambda>_. \<lfloor>\<lfloor>370\<rfloor>\<rfloor>) (s1, s2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid9_def)
  apply(subst (8) s1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 show ?thesis
  apply(rule exI[where x = "(\<sigma>\<^sub>1,\<sigma>\<^sub>2)"], simp add: \<sigma>\<^sub>1_def \<sigma>\<^sub>2_def)
  apply(rule pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_pre_sat[OF PP, simplified Let_def, THEN mp, THEN mp])
   apply(simp add: pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold s1_def, fold s2_def)
   apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F1_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)

  apply(simp add: pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold s1_def, fold s2_def)
  apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F2_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)
 done
qed

lemma Flight_at_post_sat: "\<exists> \<tau>. Flight_A \<tau>"
proof - 
 note S2 = \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
 note PP = \<sigma>\<^sub>1_\<sigma>\<^sub>2[of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)", simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def]

 have F1_val: "F1 .seats (s1, s2) = (\<lambda>_. \<lfloor>\<lfloor>120\<rfloor>\<rfloor>) (s1, s2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
  apply(subst (8) s2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 have F2_val: "F2 .seats (s1, s2) = (\<lambda>_. \<lfloor>\<lfloor>370\<rfloor>\<rfloor>) (s1, s2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
  apply(subst (8) s2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 show ?thesis
  apply(rule exI[where x = "(\<sigma>\<^sub>1,\<sigma>\<^sub>2)"], simp add: \<sigma>\<^sub>1_def \<sigma>\<^sub>2_def)
  apply(rule pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_post_sat[OF PP, simplified Let_def, THEN mp, THEN mp])
   apply(simp add: pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold s1_def, fold s2_def)
   apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F1_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)

  apply(simp add: pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold s1_def, fold s2_def)
  apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F2_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)
 done
qed
end

thm TRANS_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_pre_sat[simplified Flight_Aat_pre_def]
thm TRANS_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_post_sat[simplified Flight_A_def]

Context r: Reservation
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (r .id)"
  Inv B : "r .next <> null implies (r .flight .to \<doteq> r .next .flight .from)"
  Inv C : "r .next <> null implies (r .client \<doteq> r .next .client)"

Context Client :: book (f : Flight)
  Pre : "f .passengers ->excludes\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person))
         and (f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() <\<^sub>i\<^sub>n\<^sub>t (f .seats))"
  Post: "f .passengers \<doteq> (f .passengers@pre ->including\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person)))
         and (let r = self .cl_res ->select\<^sub>S\<^sub>e\<^sub>t(r | r .flight \<doteq> f)->any\<^sub>S\<^sub>e\<^sub>t() in
              (r .oclIsNew())
              and (r .prev \<doteq> null)
              and (r .next \<doteq> null))"

Context Client :: booknext (f : Flight, r : Reservation)
  Pre : "f .passengers ->excludes\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person))
         and (f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() <\<^sub>i\<^sub>n\<^sub>t (f .seats))
         and (r .client \<doteq> self)
         and (f .from \<doteq> (r .flight .to))"
  Post: "f .passengers \<doteq> (f .passengers@pre ->including\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person)))
         and (let r = self .cl_res ->select\<^sub>S\<^sub>e\<^sub>t(r | r .flight \<doteq> f)->any\<^sub>S\<^sub>e\<^sub>t() in
              (r .oclIsNew())
              and (r .prev \<doteq> r)
              and (r .next \<doteq> null))"


Context Client :: cancel (r : Reservation)
  Pre : "r .client \<doteq> self"
  Post: "self .cl_res ->select\<^sub>S\<^sub>e\<^sub>t(res | res .flight \<doteq> r .flight@pre)
                      ->isEmpty\<^sub>S\<^sub>e\<^sub>t()"

(* example for a recursive query *)
Context Reservation :: connections () : Set(Integer)
  Post : "result \<triangleq> if (self .next \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .id))
                   else (self .next .connections()->including\<^sub>S\<^sub>e\<^sub>t(self .id))
                   endif"
  Pre  : "true"

find_theorems (350) name:"Client"
lemmas [simp,code_unfold] = dot_accessor

end
