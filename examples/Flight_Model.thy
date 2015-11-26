(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Flight_Model.thy --- OCL Contracts and an Example.
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
  Flight_Model
imports
  "../src/UML_OCL"
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

To simplify matters, we group all these definedness assumptions in a locale called
@{text "state_\<sigma>\<^sub>1"}.

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
with its number in the list of declarations; this indexing starts with 0 for the 
first position.

All these facts were grouped together in an implicitly generated locale called
@{text "state_\<sigma>\<^sub>2"}. 
*}

State \<sigma>\<^sub>2 =
  [ S1
  , ([ C1 with_only name = "Bob", address = "Praha" , flights = F1 , cl_res = R11 ] :: Client)
  , ([ C2 with_only name = "Alice",address = "Ostrava",flights=[F1,F2],cl_res=[self 4,self 7]]::Client)
  , R11
  , ([ R21 with_only id = 98765 , flight = F1 , "next" = self 7] :: Reservation)
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

All these facts were grouped together in an implicitly generated locale called
@{text "transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2"}. 

*}

Transition \<sigma>\<^sub>1 \<sigma>\<^sub>2


text{* The following lemma establishes that the generated object presentations
       like @{thm "S1_def"}, @{thm "C1_def"}, etc. satisfy indeed the requirements
       of the locale @{text "state_\<sigma>\<^sub>1"}. In particular, it has to be shown that the
       chosen object representations are defined and have distinct object id's.
       Proving this lemma gives access to the already defined properties in this 
       locale.  *}

lemma \<sigma>\<^sub>1: "state_interpretation_\<sigma>\<^sub>1 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>1_def,
   default, simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

text{* This instance proof goes analogously. *}

lemma \<sigma>\<^sub>2: "state_interpretation_\<sigma>\<^sub>2 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>2_def,
   default, simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

text{* The latter proof gives access to the locale @{text "transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2"}. *}

lemma \<sigma>\<^sub>1_\<sigma>\<^sub>2: "pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2 \<tau>"
by(simp add: pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def,
   default, simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+,
   (simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)


text{* For convenience, we (re)-define the entirely empty state. *}
definition \<sigma>\<^sub>0 :: "\<AA> state" where "\<sigma>\<^sub>0 = state.make Map.empty Map.empty"

text{* Moreover, we introduce the following abbreviations: *}
definition "\<sigma>\<^sub>t\<^sub>1 = transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>t\<^sub>2 = transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid4 oid5 oid6 oid7 oid8 oid9 oid10
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>s\<^sub>1 = state_\<sigma>\<^sub>1.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>s\<^sub>2 = state_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid4 oid5 oid6 oid7 oid8 oid9 oid10
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

text{* Both formats are, fortunately, equivalent; this means that for these states we
can access properties from both state and transition locales, in which the
object representation were "wired in" the same way. *}

lemma \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1: "\<sigma>\<^sub>t\<^sub>1 = \<sigma>\<^sub>s\<^sub>1"
unfolding \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>s\<^sub>1_def 
 apply(subst transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def)
by(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def], simp)


lemma \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2: "\<sigma>\<^sub>t\<^sub>2 = \<sigma>\<^sub>s\<^sub>2"
unfolding \<sigma>\<^sub>t\<^sub>2_def \<sigma>\<^sub>s\<^sub>2_def 
 apply(subst transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def)
by(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def], simp)


text{* In the following, we prove that the constructed states are in fact well-formed. *}

(* TODO : this should be done at the level of states, not transitions... *)
lemma "WFF (\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)"
unfolding \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1 \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2 \<sigma>\<^sub>s\<^sub>1_def \<sigma>\<^sub>s\<^sub>2_def
 apply(rule transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.basic_\<sigma>\<^sub>1_\<sigma>\<^sub>2_wff)
 apply(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def])
by(simp_all add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2 pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2 
      (* *)
      oid_of_\<AA>_def oid_of_ty\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_def oid_of_ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
      (* *)
      S1\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_def C1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def C2\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def R21\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
      \<sigma>\<^sub>2_object1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def \<sigma>\<^sub>2_object2\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def \<sigma>\<^sub>2_object4\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def \<sigma>\<^sub>2_object7\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def)

 

(* TODO : the following low-level properties on the states @{term \<sigma>\<^sub>s\<^sub>1} ... should also 
          be proven automatically. This is stuff from the object and state presentation that
          should be hidden away from the user. *)

lemma F1_val_seatsATpre: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>) \<Turnstile> F1 .seats@pre \<triangleq> \<guillemotleft>120\<guillemotright>"
      proof(simp add: UML_Logic.foundation22 k_def )
         show "F1 .seats@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>) = \<lfloor>\<lfloor>120\<rfloor>\<rfloor>"
            proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
            show ?thesis
                apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def 
                                F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
                apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
                apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
                by(simp add: reconst_basetype_def)
            qed
       qed

lemma F2_val_seatsATpre: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>) \<Turnstile> F2 .seats@pre \<triangleq> \<guillemotleft>370\<guillemotright>"
      proof(simp add: UML_Logic.foundation22 k_def )
         show "F2 .seats@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>) = \<lfloor>\<lfloor>370\<rfloor>\<rfloor>"
            proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
            show ?thesis
                apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def 
                                F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid9_def)
                apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
                apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
                by(simp add: reconst_basetype_def)
            qed
       qed


lemma F1_val_seats: "(\<sigma>, \<sigma>\<^sub>s\<^sub>2) \<Turnstile> F1 .seats \<triangleq> \<guillemotleft>120\<guillemotright>"
proof(simp add: UML_Logic.foundation22 k_def )
   show "F1 .seats (\<sigma>, \<sigma>\<^sub>s\<^sub>2) = \<lfloor>\<lfloor>120\<rfloor>\<rfloor>"
        proof - note  S2 = \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
              show ?thesis
              apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def 
                              oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
              apply(subst (8) \<sigma>\<^sub>s\<^sub>2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
              apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
              by(simp add: reconst_basetype_def)
        qed
qed

lemma F2_val_seats: "(\<sigma>, \<sigma>\<^sub>s\<^sub>2) \<Turnstile> F2 .seats \<triangleq> \<guillemotleft>370\<guillemotright>"
proof(simp add: UML_Logic.foundation22 k_def )
   show   "F2 .seats (\<sigma>, \<sigma>\<^sub>s\<^sub>2) =  \<lfloor>\<lfloor>370\<rfloor>\<rfloor>"
        proof - note  S2 = \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
              show ?thesis
              apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def 
                              oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid9_def)
              apply(subst (8) \<sigma>\<^sub>s\<^sub>2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
              apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
              by(simp add: reconst_basetype_def)
        qed
qed

lemma C1_valid: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> (\<upsilon> C1)"
by(simp add: OclValid_def C1_def)

lemma R11_val_clientATpre: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> R11 .client@pre \<triangleq> C1"
  proof(simp add: foundation22)

  have C1_deref_val: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4 \<triangleq> C1"
    proof(simp add: foundation22)
    show "deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4 (\<sigma>\<^sub>s\<^sub>1, \<sigma>') = C1 (\<sigma>\<^sub>s\<^sub>1, \<sigma>')"
      proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
      show ?thesis
          apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
          apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
          by(simp add: reconst_basetype_def C1_def)
      qed
    qed
  
  show "R11 .client@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>') = C1 (\<sigma>\<^sub>s\<^sub>1, \<sigma>')"
  proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
  show ?thesis
    apply(simp add: dot\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_1___clientat_pre R11_def deref_oid\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def in_pre_state_def
                    R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid6_def)
    apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
    apply(simp add: deref_assocs\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_1___client_def deref_assocs_def oid\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_1___client_def)
    apply(subst (3) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1] map_of_list_def
          oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___flights_def oid\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_0___flights_def oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___cl_res_def)
    apply(simp add: switch\<^sub>2_01_def switch\<^sub>2_10_def choose_0_def choose_1_def deref_assocs_list_def
                    pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2 R11_def R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def List.member_def)
    apply(simp add: select\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n__client_def select_object_any\<^sub>S\<^sub>e\<^sub>t_def select_object\<^sub>S\<^sub>e\<^sub>t_def)
    apply(subgoal_tac "(let s = Set{deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4} in
                        if s->size\<^sub>S\<^sub>e\<^sub>t() \<triangleq> \<one> then s->any\<^sub>S\<^sub>e\<^sub>t() else \<bottom> endif) (\<sigma>\<^sub>s\<^sub>1, \<sigma>') = C1 (\<sigma>\<^sub>s\<^sub>1, \<sigma>')")
     apply(subgoal_tac "Set{deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4} =
             select_object Set{} UML_Set.OclIncluding id (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype) [4]")
      apply(simp only: Let_def)
     apply(simp add: select_object_def)
    apply(simp only: Let_def)
    apply(subst cp_OclIf, subst OclSize_singleton[simplified OclValid_def])
     apply(subst cp_valid)
     using C1_deref_val[simplified OclValid_def StrongEq_def true_def]
     apply(simp, subst cp_valid[symmetric], simp add: C1_valid[simplified OclValid_def])
    using C1_deref_val[simplified OclValid_def StrongEq_def true_def]
    by(subst cp_OclIf[symmetric], simp)
  qed
qed

section{* Annotations of the Class Model in OCL *}

text{* Subsequently, we state a desired class invariant for \verb$Flight$'s in the 
       usual OCL syntax: *}
Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .fl_res)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .client .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"



section{* Model Analysis I: A satisfiability proof of the invariants. *}

(* Junk : TO BE DONE IN LIBRARY *)

lemma [simp]: "(\<guillemotleft>x\<guillemotright> <\<^sub>i\<^sub>n\<^sub>t \<guillemotleft>y\<guillemotright>) = \<guillemotleft>x < y\<guillemotright>"
by(rule ext, simp add: OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def k_def defined_def UML_Types.bot_fun_def 
                       bot_option_def null_fun_def null_option_def)

lemma [simp]: "(\<guillemotleft>x\<guillemotright> \<le>\<^sub>i\<^sub>n\<^sub>t \<guillemotleft>y\<guillemotright>) = \<guillemotleft>x \<le> y\<guillemotright>"
by(rule ext, simp add: OclLe\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def k_def defined_def UML_Types.bot_fun_def 
                       bot_option_def null_fun_def null_option_def)


lemma OclInt0' : "\<zero> = \<guillemotleft>0\<guillemotright>" by(rule ext, simp add: OclInt0_def k_def)
lemma OclInt1' : "\<one> = \<guillemotleft>1\<guillemotright>" by(rule ext, simp add: OclInt1_def k_def)
lemma OclInt2' : "\<two> = \<guillemotleft>2\<guillemotright>" by(rule ext, simp add: OclInt2_def k_def)
lemma OclInt3' : "\<three> = \<guillemotleft>3\<guillemotright>" by(rule ext, simp add: OclInt3_def k_def)
lemma OclInt4' : "\<four> = \<guillemotleft>4\<guillemotright>" by(rule ext, simp add: OclInt4_def k_def)
lemma OclInt5' : "\<five> = \<guillemotleft>5\<guillemotright>" by(rule ext, simp add: OclInt5_def k_def)
lemma OclInt6' : "\<six> = \<guillemotleft>6\<guillemotright>" by(rule ext, simp add: OclInt6_def k_def)
lemma OclInt7' : "\<seven> = \<guillemotleft>7\<guillemotright>" by(rule ext, simp add: OclInt7_def k_def)
lemma OclInt8' : "\<eight> = \<guillemotleft>8\<guillemotright>" by(rule ext, simp add: OclInt8_def k_def)
lemma OclInt9' : "\<nine> = \<guillemotleft>9\<guillemotright>" by(rule ext, simp add: OclInt9_def k_def)
lemma OclInt10': "\<one>\<zero>= \<guillemotleft>10\<guillemotright>"by(rule ext, simp add: OclInt10_def k_def) 

lemma [simp]: "\<tau> \<Turnstile> \<guillemotleft>True\<guillemotright>"
              "\<tau> |\<noteq> \<guillemotleft>False\<guillemotright>"
by(simp add: OclValid_def true_def k_def)+


text{* We wish to analyse our class model and show that the entire set of invariants can
be satisfied, \ie{} there exists legal states that satisfy all constraints imposed
by the class invariants. *}

lemma Flight_consistent: "\<exists> \<tau>. Flight_Aat_pre \<tau> \<and>  Flight_A \<tau>"
proof (rule_tac x="(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)" in exI, rule conjI)
       txt{* The following auxiliary fact establishes that @{thm OclForall_body_trivial} from the
             library is applicable since @{term "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre()"}
             is indeed defined. *}
       have  forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre() in
                            (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
             unfolding Let_def by(rule OclForall_body_trivial, rule OclAllInstances_at_pre_defined)
       show  "Flight_Aat_pre (\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)" 
       proof -
             have *: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F1_val_seatsATpre, 
                                                                  simplified \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]],simp)
                      by(simp add: OclInt0')
             have **: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F2_val_seatsATpre, 
                                                                  simplified \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]],simp)
                      by(simp add: OclInt0')

             txt{* Now we calculate: *}

             have    "((\<sigma>\<^sub>t\<^sub>1,\<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(self|
                                         Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(f|\<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats@pre))) =
                      ((\<sigma>\<^sub>t\<^sub>1,\<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances@pre() \<triangleq> Set{} or 
                                         Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats@pre))"
                     by(simp add: StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def], 
                                                     where P = "\<lambda>x. x"])
             also
             have    "... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> ((Set{F1, F2} \<triangleq> Set{}) or 
                                           (Set{F1, F2}->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t  f .seats@pre))))"
                     unfolding Flight_def
                     apply(subst StrongEq_L_subst3[where x="OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre()"], 
                           simp, simp add: \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[simplified \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>s\<^sub>1_def])
                     apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'
                                 [THEN iffD1, OF _ _ state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Flight
                                                     [OF \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def], 
                                  simplified Flight_def]])
                     apply(rule OclAllInstances_at_pre_valid)
                     apply(simp add: F1_def F2_def)
                     by(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
             also
             have    "... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Set{F1, F2} \<triangleq> Set{} or 
                                         (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F2 .seats@pre)) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F1 .seats@pre)))"
                     apply(simp, simp add: OclValid_def, subst (1 2) cp_OclOr, 
                           subst cp_OclIf, subst (1 2 3) cp_OclAnd, subst cp_OclIf)
                     by(simp add: F1_def F2_def OclIf_def)
             also
             have    "... = True" 
                     by(simp,rule foundation25', simp add: foundation10' * **)
             finally show ?thesis 
                     unfolding Flight_Aat_pre_def  by simp
          qed
next
       txt{* Analogously for the first part, the following auxiliary fact establishes 
             that @{thm OclForall_body_trivial} from the  library is applicable since 
             @{term "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances()"}  is indeed defined. *}
       have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances() in
                         (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
            by(simp add: Let_def, rule OclForall_body_trivial, rule OclAllInstances_at_post_defined)
       show "Flight_A (\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)" 
       proof -
             have *: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> \<zero> <\<^sub>i\<^sub>n\<^sub>t F1 .seats"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F1_val_seats, 
                                                                  simplified \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2[symmetric]],simp)
                      by(simp add: OclInt0')
             have**: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> \<zero> <\<^sub>i\<^sub>n\<^sub>t F2 .seats"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F2_val_seats, 
                                                                  simplified \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2[symmetric]],simp)
                      by(simp add: OclInt0')
             have    "((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(self|
                                         Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(f|\<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats))) =
                      ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances() \<triangleq> Set{} or 
                                         Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats))"
                     by(simp add: StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def], 
                                                    where P = "\<lambda>x. x"])
             also   
             have    " ... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Set{F1,F2} \<triangleq> Set{} or 
                                          Set{F1,F2}->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t  f .seats))"
                     unfolding Flight_def
                     apply(subst StrongEq_L_subst3[where x = "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances()"], 
                           simp, simp add: \<sigma>\<^sub>t\<^sub>2_def \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2[simplified \<sigma>\<^sub>t\<^sub>2_def \<sigma>\<^sub>s\<^sub>2_def])            
                     apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'
                                    [THEN iffD1, OF _ _ state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_OclAllInstances_at_post_exec_Flight
                                                [OF \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def], 
                                    simplified Flight_def]])
                     apply(rule OclAllInstances_at_post_valid)
                     apply(simp add: F1_def F2_def)
                     by(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
             also   
             have    "... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Set{F1, F2} \<triangleq> Set{} or 
                                          (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F2 .seats)) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F1 .seats)))"
                     apply(simp, simp add: OclValid_def, subst (1 2) cp_OclOr, 
                           subst cp_OclIf, subst (1 2 3) cp_OclAnd, subst cp_OclIf)
                     by(simp add: F1_def F2_def OclIf_def)
             also   
             have   "... = True"
                       by(simp,rule foundation25', simp add: foundation10' * **)
             finally show ?thesis 
                     unfolding Flight_A_def  by simp
       qed
qed

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

section{* Proving the implementability of operations. *}
text{* An operation contract is said to be non-blocking, iff there exists input and input
       states where the pre-condition is satisfied. 
       Moreover, a contract is said to be implementable, iff for all inputs satisfying the
       pre-condition output data exists that satisfies the post-condition.
*}


definition cancel\<^sub>p\<^sub>r\<^sub>e :: "(\<cdot>Client) \<Rightarrow> (\<cdot>Reservation) \<Rightarrow> \<cdot>Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e" 
where     "cancel\<^sub>p\<^sub>r\<^sub>e  self r \<equiv> (r .client@pre) \<doteq> self" 

definition cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t :: "(\<cdot>Client) \<Rightarrow> (\<cdot>Reservation) \<Rightarrow> (\<cdot>Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<Rightarrow> \<cdot>Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e" 
where     "cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t  self r result \<equiv> self .cl_res->select\<^sub>S\<^sub>e\<^sub>t(res|res .flight \<doteq> r .flight@pre)->isEmpty\<^sub>S\<^sub>e\<^sub>t()" 

lemma cancel\<^sub>n\<^sub>o\<^sub>n\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>i\<^sub>n\<^sub>g : "\<exists> self r \<sigma>.  (\<sigma>,\<sigma>') \<Turnstile> (cancel\<^sub>p\<^sub>r\<^sub>e  self r)"
 apply(rule exI[where x = "C1"], rule exI[where x = "R11"], rule exI[where x = "\<sigma>\<^sub>t\<^sub>1"])
 using R11_val_clientATpre[simplified OclValid_def StrongEq_def true_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric], of \<sigma>']
 apply(simp add: cancel\<^sub>p\<^sub>r\<^sub>e_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def)
by(subst cp_valid, simp, subst cp_valid[symmetric],
   simp add: C1_valid[simplified OclValid_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]])

lemma cancel\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>a\<^sub>b\<^sub>l\<^sub>e : " (\<sigma>,\<sigma>') \<Turnstile> (cancel\<^sub>p\<^sub>r\<^sub>e  self r) \<Longrightarrow> 
                           \<exists> \<sigma>' result.  ((\<sigma>,\<sigma>') \<Turnstile> (cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t  self r result))"
oops(* TODO *)

find_theorems (350) name:"Client"
lemmas [simp,code_unfold] = dot_accessor

end
