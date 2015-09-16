(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Aux_proof.thy ---
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

header\<open>Part ...\<close>

theory Aux_proof
imports Main
begin

section\<open>On the Semantics of Object-oriented Data Structures and Path Expressions\<close>

subsection\<open>Basic modelization of attributes\<close>

datatype oid = Oid
datatype attr_own = Attr_own
datatype attr_inh = Attr_inh
datatype '\<alpha> recurse = R nat '\<alpha>

subsection\<open>Datatype definition of the class type and class type extension (version 1)\<close>

datatype t1_ext = T1_ext attr_own "(t1_ext recurse) option"
datatype t1 = T1 oid attr_own attr_inh "(t1_ext recurse) option"

subsection\<open>Datatype definition of the class type and class type extension (version 2)\<close>

datatype t2_ext = T2_ext_oid oid attr_inh
                | T2_ext_rec "t2 recurse"
     and t2 = T2 t2_ext attr_own

fun get2_oid where
   "get2_oid v = (\<lambda> T2 (T2_ext_oid oid _) _ \<Rightarrow> oid
                  | T2 (T2_ext_rec (R _ t)) _ \<Rightarrow> get2_oid t) v"

fun get2_inh where
   "get2_inh v = (\<lambda> T2 (T2_ext_oid _ inh) _ \<Rightarrow> inh
                  | T2 (T2_ext_rec (R _ t)) _ \<Rightarrow> get2_inh t) v"

subsection\<open>Datatype definition of the class type and class type extension (version 3)\<close>

datatype t3_ext = T3_ext_oid oid attr_inh attr_own
                | T3_ext_rec "t3 recurse"
     and t3 = T3 t3_ext

fun get3_oid where
   "get3_oid v = (\<lambda> T3 (T3_ext_oid oid _ _) \<Rightarrow> oid
                  | T3 (T3_ext_rec (R _ t)) \<Rightarrow> get3_oid t) v"

fun get3_inh where
   "get3_inh v = (\<lambda> T3 (T3_ext_oid _ inh _) \<Rightarrow> inh
                  | T3 (T3_ext_rec (R _ t)) \<Rightarrow> get3_inh t) v"

fun get3_own where
   "get3_own v = (\<lambda> T3 (T3_ext_oid _ _ own) \<Rightarrow> own
                  | T3 (T3_ext_rec (R _ t)) \<Rightarrow> get3_own t) v"

subsection\<open>Conversion t2 of t1\<close>

fun m2_of_m1_ext where
   "m2_of_m1_ext oid attr_inh m1 = (\<lambda> T1_ext attr_own opt \<Rightarrow> T2 (case opt
      of None \<Rightarrow> T2_ext_oid oid attr_inh
       | Some (R ide m1) \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext oid attr_inh m1))) attr_own) m1"

definition "m2_of_m1 = (\<lambda> T1 oid attr_own attr_inh opt \<Rightarrow> T2 (case opt
   of None \<Rightarrow> T2_ext_oid oid attr_inh
    | Some (R ide m1) \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext oid attr_inh m1))) attr_own)"

subsection\<open>Conversion t1 of t2\<close>

fun m1_ext_of_m2 where
   "m1_ext_of_m2 m2 =
  (\<lambda> T2 (T2_ext_oid _ _) attr_own \<Rightarrow> T1_ext attr_own None
   | T2 (T2_ext_rec (R ide m2)) attr_own \<Rightarrow> T1_ext attr_own (Some (R ide (m1_ext_of_m2 m2)))) m2"

definition "m1_of_m2 =
  (\<lambda> T2 (T2_ext_oid oid attr_inh) attr_own \<Rightarrow> T1 oid attr_own attr_inh None
   | T2 (T2_ext_rec (R ide m2)) attr_own \<Rightarrow> T1 (get2_oid m2) attr_own (get2_inh m2) (Some (R ide (m1_ext_of_m2 m2))))"

subsection\<open>Bijectivity proofs\<close>

lemma "m1_of_m2 (m2_of_m1 X) = X"
 apply(case_tac X, simp)
 proof -

 have id_get_oid : "\<And>oid inh m1. get2_oid (m2_of_m1_ext oid inh m1) = oid"
 by (metis (full_types) oid.exhaust)

 have id_get_inh : "\<And>oid inh m1. get2_inh (m2_of_m1_ext oid inh m1) = inh"
 by (metis (full_types) attr_inh.exhaust)

 have t1_ext_induct : "\<And> P1 P2 P3 t1_ext option recurse. ((\<And>attr_own option. P2 option \<Longrightarrow> P1 (T1_ext attr_own option)) \<Longrightarrow>
  P2 None \<Longrightarrow>
  (\<And>recurse. P3 recurse \<Longrightarrow> P2 (Some recurse)) \<Longrightarrow>
  (\<And>nat t1_ext. P1 t1_ext \<Longrightarrow> P3 (R nat t1_ext)) \<Longrightarrow> P1 t1_ext \<and> P2 option \<and> P3 recurse)"
 sorry

 have id_rec : "\<And>oid inh m1. m1_ext_of_m2 (m2_of_m1_ext oid inh m1) = m1"
  apply(case_tac m1, simp only:)
  proof -
  fix oid inh attr_own option
  def P \<equiv> "\<lambda>m1. m1_ext_of_m2 (m2_of_m1_ext oid inh m1) = m1"
  show "m1_ext_of_m2 (m2_of_m1_ext oid inh (T1_ext attr_own option)) = T1_ext attr_own option"
   apply(rule t1_ext_induct[ of "\<lambda>option. \<forall>oid attr_own attr_inh. P (T1_ext attr_own option)"
                                "\<lambda>t1_ext. \<forall>nat oid attr_own attr_inh. P (T1_ext attr_own (Some (R nat t1_ext)))"
                                "\<lambda>recurse. \<forall>oid attr_own attr_inh. P (T1_ext attr_own (Some recurse))"
                           , THEN conjunct2, THEN conjunct1, THEN spec, THEN spec, THEN spec, simplified Let_def P_def])
  by auto
 qed

 fix oid attr_own attr_inh option
 def P \<equiv> "\<lambda>X. m1_of_m2 (m2_of_m1 X) = X"
 show "m1_of_m2 (m2_of_m1 (T1 oid attr_own attr_inh option)) = T1 oid attr_own attr_inh option"
  apply(rule t1_ext_induct[ of "\<lambda>option. \<forall>oid attr_own attr_inh. P (T1 oid attr_own attr_inh option)"
                               "\<lambda>t1_ext. \<forall>nat oid attr_own attr_inh. P (T1 oid attr_own attr_inh (Some (R nat t1_ext)))"
                               "\<lambda>recurse. \<forall>oid attr_own attr_inh. P (T1 oid attr_own attr_inh (Some recurse))"
                          , THEN conjunct2, THEN conjunct1, THEN spec, THEN spec, THEN spec, simplified Let_def P_def])
  apply(auto)
  apply(subst m2_of_m1_def, subst m1_of_m2_def, auto)
  apply (metis (no_types) get2_oid.simps id_get_oid m2_of_m1_ext.simps t1_ext.case t2.case)
  apply (metis (no_types) get2_inh.simps id_get_inh m2_of_m1_ext.simps t1_ext.case t2.case)
  apply (metis (mono_tags) id_rec m1_ext_of_m2.simps m2_of_m1_ext.simps t1_ext.case t2.case)

  apply(simp add: m2_of_m1_def m1_of_m2_def)
 done
qed

lemma "m2_of_m1 (m1_of_m2 X) = X"
 apply(case_tac X, simp)
 proof -
  have t2_ext_t2_induct : "(\<And>P1 P2 P3 t2_ext t2_0 recurse. (\<And>oid attr_inh. P1 (T2_ext_oid oid attr_inh)) \<Longrightarrow>
    (\<And>recurse. P3 recurse \<Longrightarrow> P1 (T2_ext_rec recurse)) \<Longrightarrow>
    (\<And>t2_ext attr_own. P1 t2_ext \<Longrightarrow> P2 (T2 t2_ext attr_own)) \<Longrightarrow>
    (\<And>nat t2. P2 t2 \<Longrightarrow> P3 (R nat t2)) \<Longrightarrow> P1 t2_ext \<and> P2 t2_0 \<and> P3 recurse)"
  sorry

  fix t2_ext attr_own
  def P \<equiv> "\<lambda>X. m2_of_m1 (m1_of_m2 X) = X"
  show "m2_of_m1 (m1_of_m2 (T2 t2_ext attr_own)) = T2 t2_ext attr_own"
   apply(rule t2_ext_t2_induct[ of "\<lambda>t2_ext. \<forall>attr_own. P (T2 t2_ext attr_own)"
                                   "\<lambda>recurse. \<forall>attr_own. P (T2 (T2_ext_rec recurse) attr_own)"
                                   "\<lambda>option. \<forall>nat attr_own. P (T2 (T2_ext_rec (R nat option)) attr_own)"
                              , THEN conjunct1, THEN spec, simplified Let_def P_def])
   apply(auto)
   apply(subst m1_of_m2_def, subst m2_of_m1_def, auto)+

   apply(subgoal_tac "(
    let oid = case t2_ext of T2_ext_oid oid _ \<Rightarrow> oid | T2_ext_rec (R _ xb) \<Rightarrow> get2_oid xb
      ; inh = case t2_ext of T2_ext_oid _ inh \<Rightarrow> inh | T2_ext_rec (R _ xb) \<Rightarrow> get2_inh xb in

    T2 (case t2_ext of T2_ext_oid _ _ \<Rightarrow> T2_ext_oid oid inh | T2_ext_rec (R ide m2) \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext oid inh (m1_ext_of_m2 m2))) ) x) =
           T2 t2_ext x")
   apply(simp add: Let_def) apply(case_tac t2_ext, simp, simp) apply(case_tac x2, simp)

   apply(case_tac t2_ext, simp, simp)
   apply(subst (asm) m2_of_m1_def, subst (asm) m1_of_m2_def, simp)
   proof -
   def P \<equiv> "\<lambda>recurse. (case recurse of R ide m2 \<Rightarrow> T2_ext_rec (R ide (m2_of_m1_ext (case recurse of R xa x \<Rightarrow> get2_oid x) (case recurse of R xa x \<Rightarrow> get2_inh x) (m1_ext_of_m2 m2)))) =
          T2_ext_rec recurse"
   fix recurse
   show "P recurse"
   apply(rule t2_ext_t2_induct[ of "\<lambda>t2_ext. \<forall>nat attr_own. P (R nat (T2 t2_ext attr_own))"
                                   "\<lambda>recurse. P recurse"
                                   "\<lambda>t2. \<forall>nat attr_own. P (R nat t2)"
                              , THEN conjunct2, THEN conjunct2], simp_all add: P_def)
   apply(case_tac recurse, simp)
  done
 qed
qed

end
