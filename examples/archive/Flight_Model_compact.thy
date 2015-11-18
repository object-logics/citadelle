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

Instance S1  :: Staff  = [ name = "Mallory" , flights = F1 ]
     and C1  :: Client = [ name = "Bob" , address = "Plzen" , flights = F1 , cl_res = R11 ]
     and C2  :: Client = [ name = "Alice" , address = "Ostrava" , flights = F1 , cl_res = R21 ]
     and R11 :: Reservation = [ id = 12345 , flight = F1 , date = Mon ]
     and R21 :: Reservation = [ id = 98765 , flight = F1 ]
     and F1  :: Flight = [ seats = 120 , "from" = "Ostrava" , to = "Plzen" ]
     and F2  :: Flight = [ seats = 370 , "from" = "Plzen" , to = "Brno" ]

State \<sigma>\<^sub>1 =
  [ S1, C1, C2, R11, R21, F1, F2 ]

State \<sigma>\<^sub>2 =
  [ S1
  , ([ name = "Bob", address = "Praha" , flights = F1 , cl_res = R11 ] :: Client)
  , ([ name = "Alice",address = "Ostrava",flights=[F1,F2],cl_res=[self 4,self 7]]::Client)
  , R11
  , ([ id = 98765 , flight = F1 , "next" = self 7] :: Reservation)
  , F1
  , F2
  , ([ id = 19283 , flight = F2 ] :: Reservation) ]

PrePost \<sigma>\<^sub>1 \<sigma>\<^sub>2

section{* Annotations of the Class Model in OCL *}

Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .fl_res)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .client .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"

section{* Model Analysis: A satisfiable *}

locale PRE_POST_\<sigma>\<^sub>1_\<sigma>\<^sub>2
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

definition "\<sigma>1 = pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>2 = pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid6 oid8 oid9 oid10 oid11 oid12 oid13
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "s1 = state_\<sigma>\<^sub>1.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "s2 = state_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid10 oid11 oid6 oid12 oid8 oid9 oid13
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"
end

lemma forall_trivial0:
      assumes S_defined: "\<tau> \<Turnstile> \<delta> S"
      assumes S_not_emp: "\<tau> |\<noteq> (S \<triangleq> Set{})"
      shows "(if \<exists>xa\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (S \<tau>)\<rceil>\<rceil>. P then A else B) = (if P then A else B)"
 apply (simp add: OclValid_def StrongEq_def true_def mtSet_def, intro impI)
 apply(case_tac "S \<tau>", simp, subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp)
 apply(insert S_not_emp, simp add: OclValid_def StrongEq_def mtSet_def true_def)
 proof - fix y show "\<lceil>\<lceil>y\<rceil>\<rceil> = {} \<Longrightarrow> S \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e y \<Longrightarrow> B = A"
  apply(case_tac y, simp)
   apply(insert S_defined, simp add: defined_def OclValid_def false_def true_def bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def split: split_if_asm)
  apply(simp)
  proof - fix a show "\<lceil>a\<rceil> = {} \<Longrightarrow> S \<tau> = Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>a\<rfloor> \<Longrightarrow> y = \<lfloor>a\<rfloor> \<Longrightarrow> B = A"
   apply(case_tac a, simp)
    apply(insert S_defined, simp add: defined_def OclValid_def false_def true_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def split: split_if_asm)
   apply(simp)
  by(insert S_not_emp, simp add: OclValid_def StrongEq_def mtSet_def true_def)
 qed
qed

lemma forall_trivial:
  assumes S_defined: "\<tau> \<Turnstile> \<delta> S"
  shows "(\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
proof - 
 have A: "\<And>A B C. \<tau> \<Turnstile> (B \<triangleq> false) \<Longrightarrow> (\<tau> \<Turnstile> (A \<triangleq> (B or C))) = (\<tau> \<Turnstile> (A \<triangleq> C))"
  apply(simp add: OclValid_def StrongEq_def true_def)
 by(subst cp_OclOr, simp add: cp_OclOr[symmetric])

 show ?thesis
  apply(case_tac "\<tau> \<Turnstile> (S \<triangleq> Set{})")
   apply(simp add: OclValid_def StrongEq_def Let_def true_def)
   apply(subst cp_OclOr, subst cp_OclForall, simp, fold true_def, subst cp_OclForall[symmetric], simp)

  apply(subst A)
   apply(simp add: OclValid_def StrongEq_def false_def true_def)
  apply(simp add: OclValid_def, simp only: UML_Set.OclForall_def)
  apply(subst cp_StrongEq, subst (1 2 3) forall_trivial0,
        rule S_defined, simp add: OclValid_def, simp only: S_defined[simplified OclValid_def])
 by(simp add: StrongEq_def true_def, insert bool_split_0[of P \<tau>], auto simp add: true_def)
qed

context pre_post_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin

lemma Flight_at_pre_sat: "let \<tau> = (\<sigma>\<^sub>1,\<sigma>\<^sub>2) in
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))) \<longrightarrow>
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))) \<longrightarrow>
                           Flight_Aat_pre \<tau>"
proof - 
 have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre() in
                       (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
 by(simp add: Let_def, rule forall_trivial, rule OclAllInstances_at_pre_defined)
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
 by(simp add: Let_def, rule forall_trivial, rule OclAllInstances_at_post_defined)
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

context PRE_POST_\<sigma>\<^sub>1_\<sigma>\<^sub>2
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
  apply(rule exI[where x = "(\<sigma>1,\<sigma>2)"], simp add: \<sigma>1_def \<sigma>2_def)
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
  apply(rule exI[where x = "(\<sigma>1,\<sigma>2)"], simp add: \<sigma>1_def \<sigma>2_def)
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

thm PRE_POST_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_pre_sat[simplified Flight_Aat_pre_def]
thm PRE_POST_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_post_sat[simplified Flight_A_def]

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
