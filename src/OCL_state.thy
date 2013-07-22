(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_state.thy --- State Operations and Objects.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2013 Université Paris-Sud, France
 *               2013      IRT SystemX, France
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

header{* Part III: State Operations and Objects *}

theory OCL_state
imports OCL_lib
begin

subsection{* Recall: The generic structure of States*}

text{* Next we will introduce the foundational concept of an object id (oid), 
which is just some infinite set.  *}

type_synonym oid = nat

text{* States are pair of a partial map from oid's to elements of an object universe @{text "'\<AA>"}
--- the heap --- and a map to relations of objects. The relations were encoded as lists of
pairs in order to leave the possibility to have Bags, OrderedSets or Sequences as association
ends.  *}
text{* Recall:
\begin{isar}
record ('\<AA>)state = 
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs :: "oid  \<rightharpoonup> (oid \<times> oid) list"
\end{isar}
*}

type_synonym ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"


text{* Now we refine our state-interface.
In certain contexts, we will require that the elements of the object universe have 
a particular structure; more precisely, we will require that there is a function that
reconstructs the oid of an object in the state (we will settle the question how to define
this function later). *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"


subsection{* Referential Object Equality in States*}

text{* Generic referential equality - to be used for instantiations
 with concrete object types ... *}
definition  gen_ref_eq :: "('\<AA>,'a::{object,null})val \<Rightarrow> ('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean" 
where      "gen_ref_eq x y
            \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                    then if x \<tau> = null \<or> y \<tau> = null
                         then \<lfloor>\<lfloor>x \<tau> = null \<and> y \<tau> = null\<rfloor>\<rfloor>
                         else \<lfloor>\<lfloor>(oid_of (x \<tau>)) = (oid_of (y \<tau>)) \<rfloor>\<rfloor>
                    else invalid \<tau>"

lemma gen_ref_eq_sym : assumes x_val : "\<tau> \<Turnstile> \<upsilon> x" shows "\<tau> \<Turnstile> gen_ref_eq x x"
by(simp add: gen_ref_eq_def true_def OclValid_def x_val[simplified OclValid_def])

lemma gen_ref_eq_object_strict1[simp] : 
"(gen_ref_eq x invalid) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma gen_ref_eq_object_strict2[simp] : 
"(gen_ref_eq invalid x) = invalid"
by(rule ext, simp add: gen_ref_eq_def true_def false_def)

lemma cp_gen_ref_eq_object: 
"(gen_ref_eq x y \<tau>) = (gen_ref_eq (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: gen_ref_eq_def cp_valid[symmetric])

lemmas cp_intro''[simp,intro!] = 
       cp_intro''
       cp_gen_ref_eq_object[THEN allI[THEN allI[THEN allI[THEN cpI2]], 
             of "gen_ref_eq"]]

text{* Finally, we derive the usual laws on definedness for (generic) object equality:*}
lemma gen_ref_eq_defargs: 
"\<tau> \<Turnstile> (gen_ref_eq x (y::('\<AA>,'a::{null,object})val))\<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: gen_ref_eq_def OclValid_def true_def invalid_def bot_option_def
        split: bool.split_asm HOL.split_if_asm)


subsection{* Further requirements on States*}
text{* A key-concept for linking strict referential equality to
       logical equality: in well-formed states (i.e. those
       states where the self (oid-of) field contains the pointer
       to which the object is associated to in the state), 
       referential equality coincides with logical equality. *}

definition WFF :: "('\<AA>::object)st \<Rightarrow> bool"
where "WFF \<tau> = ((\<forall> x \<in> ran(heap(fst \<tau>)). \<lceil>heap(fst \<tau>) (oid_of x)\<rceil> = x) \<and>
                (\<forall> x \<in> ran(heap(snd \<tau>)). \<lceil>heap(snd \<tau>) (oid_of x)\<rceil> = x))"

text{* This is a generic definition of referential equality:
Equality on objects in a state is reduced to equality on the
references to these objects. As in HOL-OCL, we will store
the reference of an object inside the object in a (ghost) field.
By establishing certain invariants ("consistent state"), it can
be assured that there is a "one-to-one-correspondance" of objects
to their references --- and therefore the definition below
behaves as we expect. *}
text{* Generic Referential Equality enjoys the usual properties:
(quasi) reflexivity, symmetry, transitivity, substitutivity for
defined values. For type-technical reasons, for each concrete
object type, the equality @{text "\<doteq>"} is defined by generic referential
equality. *}

theorem strictEqGen_vs_strongEq: 
"WFF \<tau> \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> x) \<Longrightarrow> \<tau> \<Turnstile>(\<upsilon> y) \<Longrightarrow> 
(x \<tau> \<in> ran (heap(fst \<tau>)) \<and> y \<tau> \<in> ran (heap(fst \<tau>))) \<and>
(x \<tau> \<in> ran (heap(snd \<tau>)) \<and> y \<tau> \<in> ran (heap(snd \<tau>))) \<Longrightarrow> (* x and y must be object representations
                                                          that exist in either the pre or post state *) 
           (\<tau> \<Turnstile> (gen_ref_eq x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(auto simp: gen_ref_eq_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
apply(erule_tac x="x \<tau>" in allE', simp_all)
done

text{* So, if two object descriptions live in the same state (both pre or post), the referential
equality on objects implies in a WFF state the logical equality. Uffz. *}

section{* Miscellaneous: Initial States (for Testing and Code Generation) *}

definition \<tau>\<^isub>0 :: "('\<AA>)st"
where     "\<tau>\<^isub>0 \<equiv> (\<lparr>heap=Map.empty, assocs= Map.empty\<rparr>,
                 \<lparr>heap=Map.empty, assocs= Map.empty\<rparr>)"


subsection{* Generic Operations on States *}

text{* In order to denote OCL-types occuring in OCL expressions syntactically --- as, for example, 
as "argument" of allInstances --- we use the inverses of the injection functions into the object
universes; we show that this is sufficient "characterization". *}

definition allinstances :: "('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<AA>::object,'\<alpha> option option) Set" 
                           ("_ .oclAllInstances'(')")
where  "((H).oclAllInstances()) \<tau> = 
                 Abs_Set_0 \<lfloor>\<lfloor>(Some o Some o H) ` (ran(heap(snd \<tau>)) \<inter> {x. \<exists> y. y=H x}) \<rfloor>\<rfloor> "

definition allinstancesATpre :: "('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow> ('\<AA>::object,'\<alpha> option option) Set" 
                           ("_ .oclAllInstances@pre'(')")
where  "((H).oclAllInstances@pre()) \<tau> = 
                 Abs_Set_0 \<lfloor>\<lfloor>(Some o Some o H) ` (ran(heap(fst \<tau>)) \<inter> {x. \<exists> y. y=H x}) \<rfloor>\<rfloor> "

lemma "\<tau>\<^isub>0 \<Turnstile> H .oclAllInstances() \<triangleq> Set{}"
by(simp add: StrongEq_def allinstances_def OclValid_def \<tau>\<^isub>0_def mtSet_def)


lemma "\<tau>\<^isub>0 \<Turnstile> H .oclAllInstances@pre() \<triangleq> Set{}"
by(simp add: StrongEq_def allinstancesATpre_def OclValid_def \<tau>\<^isub>0_def mtSet_def)

lemma state_update_vs_allInstances_rec0:
shows   "(Type .oclAllInstances())
         (\<sigma>, \<lparr>heap=empty, assocs=A\<rparr>)
         =
         Set{}
         (\<sigma>, \<lparr>heap=empty, assocs=A\<rparr>)"
by(simp add: allinstances_def[simplified] mtSet_def)

lemma state_update_vs_allInstances_rec':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
shows   "(Type .oclAllInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         (Type .oclAllInstances()->including(\<lambda> _. \<lfloor>\<lfloor>Type Object\<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>)"
proof -
 have allinst_def : "(\<sigma>, \<lparr>heap = \<sigma>', assocs = A\<rparr>) \<Turnstile> (\<delta> (Type .oclAllInstances()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def allinstances_def[simplified])
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 show ?thesis
  apply(simp add: OclIncluding_def allinst_def[simplified OclValid_def] allinstances_def[simplified])
  apply(subst Abs_Set_0_inverse, simp add: bot_option_def, simp add: comp_def)
  apply(subst image_insert[symmetric])
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
  apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
  apply(rule ranI, simp)
  apply(subst insert_absorb, simp)
 by (metis fun_upd_apply)
qed


lemma state_update_vs_allInstances_rec:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
shows   "(Type .oclAllInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         ((\<lambda>_. (Type .oclAllInstances()) (\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>))->including(\<lambda> _. \<lfloor>\<lfloor>Type Object\<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)"
proof -
 have allinst_def : "(\<sigma>, \<lparr>heap = \<sigma>', assocs = A\<rparr>) \<Turnstile> (\<delta> (Type .oclAllInstances()))"
  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def allinstances_def[simplified])
  apply(subst (1 2) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+

 show ?thesis

  apply(subst state_update_vs_allInstances_rec', simp add: assms)
  apply(subst cp_OclIncluding)
  apply(simp add: OclIncluding_def)
  apply(subst (1 3) cp_defined[symmetric], simp add: allinst_def[simplified OclValid_def])

  apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def allinstances_def[simplified])
  apply(subst (1 3) Abs_Set_0_inject)
 by(simp add: bot_option_def null_option_def)+
qed

theorem state_update_vs_allInstances: 
assumes "oid\<notin>dom \<sigma>'"
and     "cp P" 
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>) \<Turnstile> (P(Type .oclAllInstances()))) =  
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>) \<Turnstile> (P((Type .oclAllInstances())->including(\<lambda> _. \<lfloor>\<lfloor>Type Object\<rfloor>\<rfloor>)))) "
proof -
 have P_cp : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
 by (metis (full_types) assms(2) cp_def)
oops

theorem state_update_vs_allInstancesATpre: 
assumes "oid\<notin>dom \<sigma>"
and     "cp P" 
shows   "((\<lparr>heap=\<sigma>(oid\<mapsto>Object), assocs=A\<rparr>, \<sigma>') \<Turnstile> (P(Type .oclAllInstances@pre()))) =  
          ((\<lparr>heap=\<sigma>, assocs=A\<rparr>, \<sigma>') \<Turnstile> (P((Type .oclAllInstances@pre())->including(\<lambda> _. Some(Some((the_inv Type) Object)))))) "
oops


definition oclisnew:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsNew'(')")
where "X .oclIsNew() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau> 
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and> 
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)" 

text{* The following predicates --- which are not part of the OCL standard descriptions ---
complete the goal of oclIsNew() by describing where an object belongs.
*}

definition oclisold:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsOld'(')")
where "X .oclIsOld() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau> 
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and> 
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)" 

definition ocliseverywhere:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsEverywhere'(')")
where "X .oclIsEverywhere() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau> 
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)" 

definition oclisabsent:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsAbsent'(')")
where "X .oclIsAbsent() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau> 
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)" 

lemma state_split : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> \<tau> \<Turnstile> (X .oclIsNew()) \<or> \<tau> \<Turnstile> (X .oclIsOld()) \<or> \<tau> \<Turnstile> (X .oclIsEverywhere()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent())"
by(simp add: oclisold_def oclisnew_def ocliseverywhere_def oclisabsent_def
             OclValid_def true_def, blast)

lemma notNew_vs_others : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow> (\<not> \<tau> \<Turnstile> (X .oclIsNew())) = (\<tau> \<Turnstile> (X .oclIsOld()) \<or> \<tau> \<Turnstile> (X .oclIsEverywhere()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent()))"
by(simp add: oclisold_def oclisnew_def ocliseverywhere_def oclisabsent_def
                not_def OclValid_def true_def, blast)

text{* The following predicate --- which is not part of the OCL standard descriptions ---
provides a simple, but powerful means to describe framing conditions. For any formal
approach, be it animation of OCL contracts, test-case generation or die-hard theorem
proving, the specification of the part of a system transistion that DOES NOT CHANGE
is of premordial importance. The following operator establishes the equality between
old and new objects in the state (provided that they exist in both states), with the 
exception of those objects 
*}

definition oclismodified ::"('\<AA>::object,'\<alpha>::{null,object})Set \<Rightarrow> '\<AA> Boolean" 
                        ("_->oclIsModifiedOnly'(')")
where "X->oclIsModifiedOnly() \<equiv> (\<lambda>(\<sigma>,\<sigma>').  let  X' = (oid_of ` \<lceil>\<lceil>Rep_Set_0(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>);
                                                 S = ((dom (heap \<sigma>) \<inter> dom (heap \<sigma>')) - X')
                                            in if (\<delta> X) (\<sigma>,\<sigma>') = true (\<sigma>,\<sigma>') 
                                               then \<lfloor>\<lfloor>\<forall> x \<in> S. (heap \<sigma>) x = (heap \<sigma>') x\<rfloor>\<rfloor>
                                               else invalid (\<sigma>,\<sigma>'))"


definition atSelf :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@pre(_)")
where "x @pre H = (\<lambda>\<tau> . if (\<delta> x) \<tau> = true \<tau> 
                        then if oid_of (x \<tau>) \<in> dom(heap(fst \<tau>)) \<and> oid_of (x \<tau>) \<in> dom(heap (snd \<tau>))
                             then  H \<lceil>(heap(fst \<tau>))(oid_of (x \<tau>))\<rceil>
                             else invalid \<tau>
                        else invalid \<tau>)"


theorem framing:
      assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding(x))->oclIsModifiedOnly()"
      and    represented_x: "\<tau> \<Turnstile> \<delta>(x @pre H)"
      and    H_is_typerepr: "inj H"
      shows "\<tau> \<Turnstile> (x  \<triangleq>  (x @pre H))"
sorry


end
