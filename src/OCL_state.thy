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

header{* Formalization III:  State Operations and Objects *}

theory OCL_state
imports OCL_lib
begin

section{* Introduction: States over Typed Object Universes *}

text{*
  In the following, we will refine the concepts of a user-defined
  data-model (implied by a class-diagram) as well as the notion of
  $\state{}$ used in the previous section to much more detail.
  Surprisingly, even without a concrete notion of an objects and a
  universe of object representation, the generic infrastructure of
  state-related operations is fairly rich.
*}



subsection{* Recall: The generic structure of States *}
text{* Recall the foundational concept of an object id (oid),
which is just some infinite set.*}

text{*
\begin{isar}[mathescape]
$\text{\textbf{type-synonym}}$ $\mathit{oid = nat}$
\end{isar}
*}

text{* Further, recall that states are pair of a partial map from oid's to elements of an
object universe @{text "'\<AA>"}---the heap---and a map to relations of objects.
The relations were encoded as lists of pairs  to leave the possibility to have Bags,
OrderedSets or Sequences as association ends.  *}
text{* This leads to the definitions:
\begin{isar}[mathescape]
record ('\<AA>)state =
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs\<^sub>2 :: "oid  \<rightharpoonup> (oid \<times> oid) list"
             assocs\<^sub>3 :: "oid  \<rightharpoonup> (oid \<times> oid \<times> oid) list"

$\text{\textbf{type-synonym}}$ ('\<AA>)st = "'\<AA> state \<times> '\<AA> state"
\end{isar}
*}

text{* Now we refine our state-interface.
In certain contexts, we will require that the elements of the object universe have
a particular structure; more precisely, we will require that there is a function that
reconstructs the oid of an object in the state (we will settle the question how to define
this function later). *}

class object =  fixes oid_of :: "'a \<Rightarrow> oid"

text{* Thus, if needed, we can constrain the object universe to objects by adding
the following type class constraint:*}
typ "'\<AA> :: object"

text{* The major instance needed are instances constructed over options: once an object,
options of objects are also objects. *}
instantiation   option  :: (object)object
begin
   definition oid_of_option_def: "oid_of x = oid_of (the x)"
   instance ..
end

section{* Fundamental Predicates on Object: Strict Equality *}
subsubsection{* Definition *}

text{* Generic referential equality - to be used for instantiations
 with concrete object types ... *}
definition  StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "('\<AA>,'a::{object,null})val \<Rightarrow> ('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean"
where      "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y
            \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                    then if x \<tau> = null \<or> y \<tau> = null
                         then \<lfloor>\<lfloor>x \<tau> = null \<and> y \<tau> = null\<rfloor>\<rfloor>
                         else \<lfloor>\<lfloor>(oid_of (x \<tau>)) = (oid_of (y \<tau>)) \<rfloor>\<rfloor>
                    else invalid \<tau>"

subsection{* Logic and Algebraic Layer on Object *}
subsubsection{* Validity and Definedness Properties *}

text{* We derive the usual laws on definedness for (generic) object equality:*}
lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_defargs:
"\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x (y::('\<AA>,'a::{null,object})val))\<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def true_def invalid_def bot_option_def
        split: bool.split_asm HOL.split_if_asm)


subsubsection{* Symmetry *}

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym :
assumes x_val : "\<tau> \<Turnstile> \<upsilon> x"
shows "\<tau> \<Turnstile> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x x"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def OclValid_def
             x_val[simplified OclValid_def])

subsubsection{* Execution with invalid or null as argument *}

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict1[simp,code_unfold] :
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x invalid) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def false_def)

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict2[simp,code_unfold] :
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t invalid x) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def false_def)

subsubsection{* Context Passing *}

lemma cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t:
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y \<tau>) = (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def cp_valid[symmetric])

lemmas cp_intro''[intro!,simp,code_unfold] =
       cp_intro''
       cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t[THEN allI[THEN allI[THEN allI[THEN cpI2]],
             of "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t"]]

subsubsection{* Behavior vs StrongEq *}

text{* It remains to clarify the role of the state invariant
$\inv_\sigma(\sigma)$ mentioned above that states the condition that
there is a ``one-to-one'' correspondence between object
representations and $\oid$'s: $\forall \mathit{oid} \in \dom\ap
\sigma\spot oid = \HolOclOidOf\ap \drop{\sigma(\mathit{oid})}$.  This
condition is also mentioned in~\cite[Annex A]{omg:ocl:2012} and goes
back to \citet{richters:precise:2002}; however, we state this
condition as an invariant on states rather than a global axiom. It
can, therefore, not be taken for granted that an $\oid$ makes sense
both in pre- and post-states of OCL expressions.
*}

text{* We capture this invariant in the predicate WFF :*}

definition WFF :: "('\<AA>::object)st \<Rightarrow> bool"
where "WFF \<tau> = ((\<forall> x \<in> ran(heap(fst \<tau>)). \<lceil>heap(fst \<tau>) (oid_of x)\<rceil> = x) \<and>
                (\<forall> x \<in> ran(heap(snd \<tau>)). \<lceil>heap(snd \<tau>) (oid_of x)\<rceil> = x))"

text{* It turns out that WFF is a key-concept for linking strict referential equality to
logical equality: in well-formed states (i.e. those states where the self (oid-of) field contains
the pointer to which the object is associated to in the state), referential equality coincides
with logical equality. *}


text{* We turn now to the generic definition of referential equality on objects:
Equality on objects in a state is reduced to equality on the
references to these objects. As in HOL-OCL~\cite{brucker.ea:hol-ocl:2008,brucker.ea:hol-ocl-book:2006},
we will store the reference of an object inside the object in a (ghost) field.
By establishing certain invariants (``consistent state''), it can
be assured that there is a ``one-to-one-correspondence'' of objects
to their references---and therefore the definition below
behaves as we expect. *}
text{* Generic Referential Equality enjoys the usual properties:
(quasi) reflexivity, symmetry, transitivity, substitutivity for
defined values. For type-technical reasons, for each concrete
object type, the equality @{text "\<doteq>"} is defined by generic referential
equality. *}

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq:
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> x)"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and x_present_pre: "x \<tau> \<in> ran (heap(fst \<tau>))"
and y_present_pre: "y \<tau> \<in> ran (heap(fst \<tau>))"
and x_present_post:"x \<tau> \<in> ran (heap(snd \<tau>))"
and y_present_post:"y \<tau> \<in> ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(insert WFF valid_x valid_y x_present_pre y_present_pre x_present_post y_present_post)
apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
apply(erule_tac x="x \<tau>" in allE', simp_all)
done

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq':
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> (x :: ('\<AA>::object,'\<alpha>::{null,object})val))"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and oid_preserve: "\<And>x. H x \<noteq> \<bottom> \<Longrightarrow> oid_of (H x) = oid_of x"
and xy_together: "x \<tau> \<in> H ` ran (heap(fst \<tau>)) \<and> y \<tau> \<in> H ` ran (heap(fst \<tau>)) \<or>
                  x \<tau> \<in> H ` ran (heap(snd \<tau>)) \<and> y \<tau> \<in> H ` ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
 apply(insert WFF valid_x valid_y xy_together)
 apply(simp add: WFF_def)
 apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
by (metis foundation18' oid_preserve valid_x valid_y)+

text{* So, if two object descriptions live in the same state (both pre or post), the referential
equality on objects implies in a WFF state the logical equality.  *}

section{* Operations on Object *}
subsection{* Initial States (for Testing and Code Generation) *}

definition \<tau>\<^sub>0 :: "('\<AA>)st"
where     "\<tau>\<^sub>0 \<equiv> (\<lparr>heap=Map.empty, assocs\<^sub>2= Map.empty, assocs\<^sub>3= Map.empty\<rparr>,
                 \<lparr>heap=Map.empty, assocs\<^sub>2= Map.empty, assocs\<^sub>3= Map.empty\<rparr>)"

subsection{* OclAllInstances *}

text{* To denote OCL types occurring in OCL expressions syntactically---as, for example,
as ``argument'' of \inlineocl{oclAllInstances()}---we use the inverses of the injection functions into the object
universes; we show that this is a sufficient ``characterization.'' *}

definition OclAllInstances_generic :: "(('\<AA>::object) st \<Rightarrow> '\<AA> state) \<Rightarrow> ('\<AA>::object \<rightharpoonup> '\<alpha>) \<Rightarrow>
                                       ('\<AA>, '\<alpha> option option) Set"
where "OclAllInstances_generic fst_snd H =
                    (\<lambda>\<tau>. Abs_Set_0 \<lfloor>\<lfloor> Some ` ((H ` ran (heap (fst_snd \<tau>))) - { None }) \<rfloor>\<rfloor>)"

lemma OclAllInstances_generic_defined: "\<tau> \<Turnstile> \<delta> (OclAllInstances_generic pre_post H)"
 apply(simp add: defined_def OclValid_def OclAllInstances_generic_def bot_fun_def bot_Set_0_def null_fun_def null_Set_0_def false_def true_def)
 apply(rule conjI)
 apply(rule notI, subst (asm) Abs_Set_0_inject, simp,
       (rule disjI2)+,
       metis bot_option_def option.distinct(1),
       (simp add: bot_option_def null_option_def)+)+
done

lemma OclAllInstances_generic_init_empty:
 assumes [simp]: "\<And>x. pre_post (x, x) = x"
 shows "\<tau>\<^sub>0 \<Turnstile> OclAllInstances_generic pre_post H \<triangleq> Set{}"
by(simp add: StrongEq_def OclAllInstances_generic_def OclValid_def \<tau>\<^sub>0_def mtSet_def)

lemma represented_generic_objects_nonnull:
assumes A: "\<tau> \<Turnstile> ((OclAllInstances_generic pre_post (H::('\<AA>::object \<rightharpoonup> '\<alpha>))) ->includes(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
proof -
    have B: "\<tau> \<Turnstile> \<delta> (OclAllInstances_generic pre_post H)"
         by(insert  A[THEN OCL_core.foundation6,
                      simplified OCL_lib.OclIncludes_defined_args_valid], auto)
    have C: "\<tau> \<Turnstile> \<upsilon> x"
         by(insert  A[THEN OCL_core.foundation6,
                      simplified OCL_lib.OclIncludes_defined_args_valid], auto)
    show ?thesis
    apply(insert A)
    apply(simp add: StrongEq_def  OclValid_def
                    OclNot_def null_def true_def OclIncludes_def B[simplified OclValid_def]
                                                                 C[simplified OclValid_def])
    apply(simp add:OclAllInstances_generic_def)
    apply(erule contrapos_pn)
    apply(subst OCL_lib.Set_0.Abs_Set_0_inverse,
          auto simp: null_fun_def null_option_def bot_option_def)
    done
qed


lemma represented_generic_objects_defined:
assumes A: "\<tau> \<Turnstile> ((OclAllInstances_generic pre_post (H::('\<AA>::object \<rightharpoonup> '\<alpha>))) ->includes(x))"
shows      "\<tau> \<Turnstile> \<delta> (OclAllInstances_generic pre_post H) \<and> \<tau> \<Turnstile> \<delta> x"
apply(insert  A[THEN OCL_core.foundation6,
                simplified OCL_lib.OclIncludes_defined_args_valid])
apply(simp add: OCL_core.foundation16 OCL_core.foundation18 invalid_def, erule conjE)
apply(insert A[THEN represented_generic_objects_nonnull])
by(simp add: foundation24 null_fun_def)


text{* One way to establish the actual presence of an object representation in a state is:*}

lemma represented_generic_objects_in_state:
assumes A: "\<tau> \<Turnstile> (OclAllInstances_generic pre_post H)->includes(x)"
shows      "x \<tau> \<in> (Some o H) ` ran (heap(pre_post \<tau>))"
proof -
   have B: "(\<delta> (OclAllInstances_generic pre_post H)) \<tau> = true \<tau>"
           by(simp add: OCL_core.OclValid_def[symmetric] OclAllInstances_generic_defined)
   have C: "(\<upsilon> x) \<tau> = true \<tau>"
           by(insert  A[THEN OCL_core.foundation6,
                           simplified OCL_lib.OclIncludes_defined_args_valid],
                 auto simp: OclValid_def)
   have F: "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (pre_post \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (pre_post \<tau>)) - {None})\<rfloor>\<rfloor>"
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def)
   show ?thesis
    apply(insert A)
    apply(simp add: OclIncludes_def OclValid_def ran_def B C image_def true_def)
    apply(simp add: OclAllInstances_generic_def)
    apply(simp add: F)
    apply(simp add: ran_def)
   by(fastforce)
qed


lemma state_update_vs_allInstances_generic_empty:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
shows   "(mk \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> OclAllInstances_generic pre_post Type \<doteq> Set{}"
proof -
 have state_update_vs_allInstances_empty: "(OclAllInstances_generic pre_post Type) (mk \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) =
                                           Set{} (mk \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
 by(simp add: OclAllInstances_generic_def mtSet_def)
 show ?thesis
  apply(simp only: OclValid_def, subst cp_StrictRefEq\<^sub>S\<^sub>e\<^sub>t, simp add: state_update_vs_allInstances_empty)
  apply(simp add: OclIf_def valid_def mtSet_def defined_def bot_fun_def bot_option_def null_fun_def null_option_def invalid_def bot_Set_0_def)
 by(subst Abs_Set_0_inject, (simp add: bot_option_def true_def)+)
qed

text{* Here comes a couple of operational rules that allow to infer the value
of \inlineisar+oclAllInstances+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like ``constant contexts P'' are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand). *}


lemma state_update_vs_allInstances_generic_including':
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         ((OclAllInstances_generic pre_post Type)->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (mk \<lparr>heap=\<sigma>',assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
proof -
 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def OclAllInstances_generic_defined[simplified OclValid_def],
        simp add: OclAllInstances_generic_def)
  apply(subst Abs_Set_0_inverse, simp add: bot_option_def, simp add: comp_def,
        subst image_insert[symmetric],
        subst drop_none, simp add: assms)
  apply(case_tac "Type Object", simp add: assms, simp only:,
        subst insert_diff, drule sym, simp)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
  apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
  apply(rule ranI, simp)
  by(subst insert_absorb, simp, metis fun_upd_apply)
qed


lemma state_update_vs_allInstances_generic_including:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         ((\<lambda>_. (OclAllInstances_generic pre_post Type) (mk \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>))->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
 apply(subst state_update_vs_allInstances_generic_including', (simp add: assms)+,
       subst cp_OclIncluding,
       simp add: OclIncluding_def)
 apply(subst (1 3) cp_defined[symmetric], simp add: OclAllInstances_generic_defined[simplified OclValid_def])

 apply(simp add: defined_def OclValid_def bot_fun_def null_fun_def bot_Set_0_def null_Set_0_def OclAllInstances_generic_def)
 apply(subst (1 3) Abs_Set_0_inject)
by(simp add: bot_option_def null_option_def)+



lemma state_update_vs_allInstances_generic_noincluding':
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         (OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
proof -
 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def OclAllInstances_generic_defined[simplified OclValid_def] OclAllInstances_generic_def)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp add: assms)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
  apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
  apply(rule ranI, simp)
  apply(subst insert_absorb, simp)
 by (metis fun_upd_apply)
qed

theorem state_update_vs_allInstances_generic_ntc:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(OclAllInstances_generic pre_post Type))) =
         ((mk \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)            \<Turnstile> (P(OclAllInstances_generic pre_post Type)))"
         (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>)")
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
             by (metis (full_types) cp_ctxt cp_def)
 have includes_const_inv: "\<And>x S \<tau> \<tau>'. (\<lambda>_. S)->including(\<lambda>_. x) \<tau> = ((\<lambda>_. S)->including(\<lambda>_. x) \<tau>')"
             by(simp add: OclIncluding_def defined_def valid_def
                          bot_fun_def null_fun_def true_def false_def)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst OCL_core.cp_validity, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             apply(subst const_ctxt[THEN spec,of"(\<lambda>_. ?\<phi> ?\<tau>)",THEN spec,of"?\<tau>",THEN spec,of"?\<tau>'"])
             by (simp add: true_def)+
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp
 show ?thesis
 apply(subst X) apply(subst OCL_core.cp_validity[symmetric])
 apply(rule StrongEq_L_subst3[OF cp_ctxt])
 apply(simp add: OclValid_def StrongEq_def true_def)
 apply(rule state_update_vs_allInstances_generic_noincluding')
 by(insert oid_def, auto simp: non_type_conform)
qed

theorem state_update_vs_allInstances_generic_tc:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(OclAllInstances_generic pre_post Type))) =
         ((mk \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)            \<Turnstile> (P((OclAllInstances_generic pre_post Type)
                                                               ->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
         (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>')")

proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
             by (metis (full_types) cp_ctxt cp_def)
 have includes_const_inv: "\<And>x S \<tau> \<tau>'. (\<lambda>_. S)->including(\<lambda>_. x) \<tau> = ((\<lambda>_. S)->including(\<lambda>_. x) \<tau>')"
             by(simp add: OclIncluding_def defined_def valid_def
                          bot_fun_def null_fun_def true_def false_def)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst OCL_core.cp_validity, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             apply(subst const_ctxt[THEN spec,of"(\<lambda>_. ?\<phi> ?\<tau>)",THEN spec,of"?\<tau>",THEN spec,of"?\<tau>'"])
             by (simp add: true_def)+
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp
 have        "OclAllInstances_generic pre_post Type ?\<tau> =
              \<lambda>_. OclAllInstances_generic pre_post Type ?\<tau>'->including(\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>"
             apply(rule state_update_vs_allInstances_generic_including)
             by(insert oid_def, auto simp: type_conform)
 also have   "... = ((\<lambda>_. OclAllInstances_generic pre_post Type ?\<tau>')->including(\<lambda>_. (\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>') ?\<tau>')"
             by(rule includes_const_inv)
 also have   "... = ((OclAllInstances_generic pre_post Type)->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>)?\<tau>')"
             apply(subst OCL_lib.cp_OclIncluding[symmetric])
             by(insert type_conform, auto)
 finally have Y : "OclAllInstances_generic pre_post Type ?\<tau> =
                   ((OclAllInstances_generic pre_post Type)->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>) ?\<tau>')"
             by auto
 show ?thesis
      apply(subst X) apply(subst OCL_core.cp_validity[symmetric])
      apply(rule StrongEq_L_subst3[OF cp_ctxt])
      apply(simp add: OclValid_def StrongEq_def Y true_def)
 done
qed

declare OclAllInstances_generic_def [simp]

subsubsection{* OclAllInstances (@post) *}

definition OclAllInstances_at_post :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances'(')")
where  "OclAllInstances_at_post =  OclAllInstances_generic snd"

lemma OclAllInstances_at_post_defined: "\<tau> \<Turnstile> \<delta> (H .allInstances())"
unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic_defined)

lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances() \<triangleq> Set{}"
unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic_init_empty, simp)


lemma represented_at_post_objects_nonnull:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances()) ->includes(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
by(rule represented_generic_objects_nonnull[OF A[simplified OclAllInstances_at_post_def]])


lemma represented_at_post_objects_defined:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances()) ->includes(x))"
shows      "\<tau> \<Turnstile> \<delta> (H .allInstances()) \<and> \<tau> \<Turnstile> \<delta> x"
unfolding OclAllInstances_at_post_def 
by(rule represented_generic_objects_defined[OF A[simplified OclAllInstances_at_post_def]])


text{* One way to establish the actual presence of an object representation in a state is:*}

lemma
assumes A: "\<tau> \<Turnstile> H .allInstances()->includes(x)"
shows      "x \<tau> \<in> (Some o H) ` ran (heap(snd \<tau>))"
by(rule represented_generic_objects_in_state[OF A[simplified OclAllInstances_at_post_def]])

lemma state_update_vs_allInstances_at_post_empty:
shows   "(\<sigma>, \<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>) \<Turnstile> Type .allInstances() \<doteq> Set{}"
unfolding OclAllInstances_at_post_def 
by(rule state_update_vs_allInstances_generic_empty[OF snd_conv])

text{* Here comes a couple of operational rules that allow to infer the value
of \inlineisar+oclAllInstances+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like ``constant contexts P'' are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand). *}


lemma state_update_vs_allInstances_at_post_including':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         ((Type .allInstances())->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>',assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
unfolding OclAllInstances_at_post_def 
by(rule state_update_vs_allInstances_generic_including'[OF snd_conv], insert assms)


lemma state_update_vs_allInstances_at_post_including:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         ((\<lambda>_. (Type .allInstances()) (\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>))->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
unfolding OclAllInstances_at_post_def 
by(rule state_update_vs_allInstances_generic_including[OF snd_conv], insert assms)



lemma state_update_vs_allInstances_at_post_noincluding':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)
         =
         (Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)"
unfolding OclAllInstances_at_post_def 
by(rule state_update_vs_allInstances_generic_noincluding'[OF snd_conv], insert assms)

theorem state_update_vs_allInstances_at_post_ntc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)            \<Turnstile> (P(Type .allInstances())))"
unfolding OclAllInstances_at_post_def 
by(rule state_update_vs_allInstances_generic_ntc[OF snd_conv], insert assms)

theorem state_update_vs_allInstances_at_post_tc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>)            \<Turnstile> (P((Type .allInstances())
                                                               ->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
unfolding OclAllInstances_at_post_def 
by(rule state_update_vs_allInstances_generic_tc[OF snd_conv], insert assms)

subsubsection{* OclAllInstances (@pre) *}

definition OclAllInstances_at_pre :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances@pre'(')")
where  "OclAllInstances_at_pre = OclAllInstances_generic fst"

lemma OclAllInstances_at_pre_defined: "\<tau> \<Turnstile> \<delta> (H .allInstances@pre())"
unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic_defined)

lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances@pre() \<triangleq> Set{}"
unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic_init_empty, simp)


lemma represented_at_pre_objects_nonnull:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances@pre()) ->includes(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
by(rule represented_generic_objects_nonnull[OF A[simplified OclAllInstances_at_pre_def]])

lemma represented_at_pre_objects_defined:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances@pre()) ->includes(x))"
shows      "\<tau> \<Turnstile> \<delta> (H .allInstances@pre()) \<and> \<tau> \<Turnstile> \<delta> x"
unfolding OclAllInstances_at_pre_def 
by(rule represented_generic_objects_defined[OF A[simplified OclAllInstances_at_pre_def]])


text{* One way to establish the actual presence of an object representation in a state is:*}

lemma
assumes A: "\<tau> \<Turnstile> H .allInstances@pre()->includes(x)"
shows      "x \<tau> \<in> (Some o H) ` ran (heap(fst \<tau>))"
by(rule represented_generic_objects_in_state[OF A[simplified OclAllInstances_at_pre_def]])


lemma state_update_vs_allInstances_at_pre_empty:
shows   "(\<lparr>heap=empty, assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> Type .allInstances@pre() \<doteq> Set{}"
unfolding OclAllInstances_at_pre_def 
by(rule state_update_vs_allInstances_generic_empty[OF fst_conv])

text{* Here comes a couple of operational rules that allow to infer the value
of \inlineisar+oclAllInstances@pre+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like ``constant contexts P'' are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand). *}


lemma state_update_vs_allInstances_at_pre_including':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)
         =
         ((Type .allInstances@pre())->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<lparr>heap=\<sigma>',assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
unfolding OclAllInstances_at_pre_def 
by(rule state_update_vs_allInstances_generic_including'[OF fst_conv], insert assms)


lemma state_update_vs_allInstances_at_pre_including:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)
         =
         ((\<lambda>_. (Type .allInstances@pre()) (\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>))->including(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
unfolding OclAllInstances_at_pre_def 
by(rule state_update_vs_allInstances_generic_including[OF fst_conv], insert assms)



lemma state_update_vs_allInstances_at_pre_noincluding':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)
         =
         (Type .allInstances@pre())
         (\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)"
unfolding OclAllInstances_at_pre_def 
by(rule state_update_vs_allInstances_generic_noincluding'[OF fst_conv], insert assms)

theorem state_update_vs_allInstances_at_pre_ntc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (P(Type .allInstances@pre()))) =
         ((\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)            \<Turnstile> (P(Type .allInstances@pre())))"
unfolding OclAllInstances_at_pre_def 
by(rule state_update_vs_allInstances_generic_ntc[OF fst_conv], insert assms)

theorem state_update_vs_allInstances_at_pre_tc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<forall> X. \<forall>\<tau> \<tau>'. X \<tau> = X \<tau>' \<longrightarrow> P X \<tau> =  P X \<tau>' "
shows   "((\<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs\<^sub>2=A,assocs\<^sub>3=B\<rparr>, \<sigma>) \<Turnstile> (P(Type .allInstances@pre()))) =
         ((\<lparr>heap=\<sigma>', assocs\<^sub>2=A, assocs\<^sub>3=B\<rparr>, \<sigma>)            \<Turnstile> (P((Type .allInstances@pre())
                                                               ->including(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
unfolding OclAllInstances_at_pre_def 
by(rule state_update_vs_allInstances_generic_tc[OF fst_conv], insert assms)

subsubsection{* @post or @pre *}

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq'':
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> (x :: ('\<AA>::object,'\<alpha>::object option option)val))"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and oid_preserve: "\<And>x. oid_of (H x) = oid_of x"
and xy_together: "\<tau> \<Turnstile> ((H .allInstances()->includes(x) and (H .allInstances()->includes(y))) or
                       (H .allInstances@pre()->includes(x) and (H .allInstances@pre()->includes(y))))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
proof -
   have at_post_def : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> (H .allInstances()->includes(x))"
    apply(simp add: OclIncludes_def OclValid_def OclAllInstances_at_post_defined[simplified OclValid_def])
   by(subst cp_defined, simp)
   have at_pre_def : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> (H .allInstances@pre()->includes(x))"
    apply(simp add: OclIncludes_def OclValid_def OclAllInstances_at_pre_defined[simplified OclValid_def])
   by(subst cp_defined, simp)
   have F: "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>"
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def)
   have F': "Rep_Set_0 (Abs_Set_0 \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>"
           by(subst OCL_lib.Set_0.Abs_Set_0_inverse,simp_all add: bot_option_def)
 show ?thesis
  apply(rule StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq'[OF WFF valid_x valid_y, where H = "Some o H"])
  apply(subst oid_preserve[symmetric], simp, simp add: oid_of_option_def)
  apply(insert xy_together,
        subst (asm) foundation11,
        metis at_post_def defined_and_I valid_x valid_y,
        metis at_pre_def defined_and_I valid_x valid_y)
  apply(erule disjE)
 by(drule foundation5,
    simp add: OclAllInstances_at_pre_def OclAllInstances_at_post_def OclValid_def OclIncludes_def true_def F F'
              valid_x[simplified OclValid_def] valid_y[simplified OclValid_def] bot_option_def
         split: split_if_asm,
    simp add: comp_def image_def, fastforce)+
qed

subsection{* OclIsNew, OclIsDeleted, OclIsMaintained, OclIsAbsent *}

definition OclIsNew:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsNew'(')")
where "X .oclIsNew() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

text{* The following predicates --- which are not part of the OCL standard descriptions ---
complete the goal of \inlineisar+oclIsNew+ by describing where an object belongs.
*}

definition OclIsDeleted:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsDeleted'(')")
where "X .oclIsDeleted() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclIsMaintained:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsMaintained'(')")
where "X .oclIsMaintained() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclIsAbsent:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsAbsent'(')")
where "X .oclIsAbsent() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

lemma state_split : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                     \<tau> \<Turnstile> (X .oclIsNew()) \<or> \<tau> \<Turnstile> (X .oclIsDeleted()) \<or>
                     \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent())"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
             OclValid_def true_def, blast)

lemma notNew_vs_others : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                         (\<not> \<tau> \<Turnstile> (X .oclIsNew())) = (\<tau> \<Turnstile> (X .oclIsDeleted()) \<or>
                          \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent()))"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
                OclNot_def OclValid_def true_def, blast)

subsection{* OclIsModifiedOnly *}
subsubsection{* Definition *}

text{* The following predicate---which is not part of the OCL
standard---provides a simple, but powerful means to describe framing
conditions. For any formal approach, be it animation of OCL contracts,
test-case generation or die-hard theorem proving, the specification of
the part of a system transition that \emph{does not change} is of
primordial importance. The following operator establishes the equality
between old and new objects in the state (provided that they exist in
both states), with the exception of those objects. *}

definition OclIsModifiedOnly ::"('\<AA>::object,'\<alpha>::{null,object})Set \<Rightarrow> '\<AA> Boolean"
                        ("_->oclIsModifiedOnly'(')")
where "X->oclIsModifiedOnly() \<equiv> (\<lambda>(\<sigma>,\<sigma>').  let  X' = (oid_of ` \<lceil>\<lceil>Rep_Set_0(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>);
                                                 S = ((dom (heap \<sigma>) \<inter> dom (heap \<sigma>')) - X')
                                            in if (\<delta> X) (\<sigma>,\<sigma>') = true (\<sigma>,\<sigma>') \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>. x \<noteq> null)
                                               then \<lfloor>\<lfloor>\<forall> x \<in> S. (heap \<sigma>) x = (heap \<sigma>') x\<rfloor>\<rfloor>
                                               else invalid (\<sigma>,\<sigma>'))"

subsubsection{* Execution with invalid or null or null element as argument *}

lemma "invalid->oclIsModifiedOnly() = invalid"
by(simp add: OclIsModifiedOnly_def)

lemma "null->oclIsModifiedOnly() = invalid"
by(simp add: OclIsModifiedOnly_def)

lemma
 assumes X_null : "\<tau> \<Turnstile> X->includes(null)"
 shows "\<tau> \<Turnstile> X->oclIsModifiedOnly() \<triangleq> invalid"
 apply(insert X_null, simp add : OclIncludes_def OclIsModifiedOnly_def StrongEq_def OclValid_def true_def)
 apply(case_tac \<tau>, simp)
 apply(simp split: split_if_asm)
by(simp add: null_fun_def, blast)

subsubsection{* Context Passing *}

lemma cp_OclIsModifiedOnly : "X->oclIsModifiedOnly() \<tau> = (\<lambda>_. X \<tau>)->oclIsModifiedOnly() \<tau>"
by(simp only: OclIsModifiedOnly_def, case_tac \<tau>, simp only:, subst cp_defined, simp)

subsection{* OclSelf *}

definition [simp]: "OclSelf x H fst_snd = (\<lambda>\<tau> . if (\<delta> x) \<tau> = true \<tau>
                        then if oid_of (x \<tau>) \<in> dom(heap(fst \<tau>)) \<and> oid_of (x \<tau>) \<in> dom(heap (snd \<tau>))
                             then  H \<lceil>(heap(fst_snd \<tau>))(oid_of (x \<tau>))\<rceil>
                             else invalid \<tau>
                        else invalid \<tau>)"

definition OclSelf_at_pre :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@pre(_)")
where "x @pre H = OclSelf x H fst"

definition OclSelf_at_post :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@post(_)")
where "x @post H = OclSelf x H snd"

subsection{* Framing Theorem *}

lemma all_oid_diff:
 assumes def_x : "\<tau> \<Turnstile> \<delta> x"
 assumes def_X : "\<tau> \<Turnstile> \<delta> X"
 assumes def_X' : "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> x \<noteq> null"

 defines "P \<equiv> (\<lambda>a. not (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x a))"
 shows "(\<tau> \<Turnstile> X->forAll(a| P a)) = (oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>)"
proof -
 have P_null_bot: "\<And>b. b = null \<or> b = \<bottom> \<Longrightarrow> 
                        \<not> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>(_:: 'a state \<times> 'a state). x) \<tau> = b \<tau>)"
  apply(erule disjE)
  apply(simp, rule ballI,
        simp add: P_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def, rename_tac x',
        subst cp_OclNot, simp,
        subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp,
        simp add: OclNot_def null_fun_def null_option_def bot_option_def bot_fun_def invalid_def,
        ( metis def_X' def_x foundation17
        | (metis OCL_core.bot_fun_def OclValid_def Set_inv_lemma def_X def_x defined_def valid_def,
           metis def_X' def_x foundation17)))+
 done

 have not_inj : "\<And>x y. ((not x) \<tau> = (not y) \<tau>) = (x \<tau> = y \<tau>)"
 by (metis foundation21 foundation22)

 have P_false : "\<exists>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau> \<Longrightarrow> oid_of (x \<tau>) \<in> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(erule bexE, rename_tac x')
  apply(simp add: P_def)
  apply(simp only: OclNot3[symmetric], simp only: not_inj)
  apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: split_if_asm)
  apply(subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp)
  apply (metis (mono_tags) OCL_core.drop.simps def_x foundation17 true_def)
 by(simp add: invalid_def bot_option_def true_def)+

 have P_true : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = true \<tau> \<Longrightarrow> oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
  apply(subgoal_tac "\<forall>x'\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. oid_of x' \<noteq> oid_of (x \<tau>)")
  apply (metis imageE)
  apply(rule ballI, drule_tac x = "x'" in ballE) prefer 3 apply assumption
  apply(simp add: P_def)
  apply(simp only: OclNot4[symmetric], simp only: not_inj)
  apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def false_def split: split_if_asm)
  apply(subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp)
  apply (metis def_X' def_x foundation17)
 by(simp add: invalid_def bot_option_def false_def)+

 have bool_split : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> null \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<bottom> \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = true \<tau>"
  apply(rule ballI)
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
  apply (metis (full_types) OCL_core.bot_fun_def OclNot4 OclValid_def foundation16 foundation18'
                            foundation9 not_inj null_fun_def)
 by(fast+)

 show ?thesis
  apply(subst OclForall_rep_set_true[OF def_X], simp add: OclValid_def)
  apply(rule iffI, simp add: P_true)
 by (metis P_false P_null_bot bool_split)
qed

theorem framing:
      assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding(x :: ('\<AA>::object,'\<alpha>::{null,object})val))->oclIsModifiedOnly()"
      and oid_is_typerepr : "\<tau> \<Turnstile> X->forAll(a| not (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x a))"
      shows "\<tau> \<Turnstile> (x @pre H  \<triangleq>  (x @post H))"
 apply(case_tac "\<tau> \<Turnstile> \<delta> x")
 proof - show "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> ?thesis" proof - assume def_x : "\<tau> \<Turnstile> \<delta> x" show ?thesis proof -

 have def_X : "\<tau> \<Turnstile> \<delta> X"
  apply(insert oid_is_typerepr, simp add: OclForall_def OclValid_def split: split_if_asm)
 by(simp add: bot_option_def true_def)

 have def_X' : "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> x \<noteq> null"
  apply(insert modifiesclause, simp add: OclIsModifiedOnly_def OclValid_def split: split_if_asm)
  apply(case_tac \<tau>, simp split: split_if_asm)
  apply(simp add: OclExcluding_def split: split_if_asm)
  apply(subst (asm) (2) Abs_Set_0_inverse)
  apply(simp, (rule disjI2)+)
  apply (metis (hide_lams, mono_tags) Diff_iff Set_inv_lemma def_X)
  apply(simp)
  apply(erule ballE[where P = "\<lambda>x. x \<noteq> null"]) apply(assumption)
  apply(simp)
  apply (metis (hide_lams, no_types) def_x foundation17)
  apply (metis (hide_lams, no_types) OclValid_def def_X def_x OclExcluding_valid_args_valid OclExcluding_valid_args_valid'' foundation20)
 by(simp add: invalid_def bot_option_def)

 have oid_is_typerepr : "oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set_0 (X \<tau>)\<rceil>\<rceil>"
 by(rule all_oid_diff[THEN iffD1, OF def_x def_X def_X' oid_is_typerepr])

 show ?thesis
  apply(simp add:StrongEq_def OclValid_def true_def OclSelf_at_pre_def OclSelf_at_post_def def_x[simplified OclValid_def])
  apply(rule conjI, rule impI)
  apply(rule_tac f = "\<lambda>x. H \<lceil>x\<rceil>" in arg_cong)
  apply(insert modifiesclause[simplified OclIsModifiedOnly_def OclValid_def])
  apply(case_tac \<tau>, rename_tac \<sigma> \<sigma>', simp split: split_if_asm)
  apply(subst (asm) (2) OclExcluding_def)
  apply(drule foundation5[simplified OclValid_def true_def], simp)
  apply(subst (asm) Abs_Set_0_inverse, simp)
  apply(rule disjI2)+
  apply (metis (hide_lams, no_types) DiffD1 OclValid_def Set_inv_lemma def_x foundation16 foundation18')
  apply(simp)
  apply(erule_tac x = "oid_of (x (\<sigma>, \<sigma>'))" in ballE) apply simp+
  apply (metis (hide_lams, no_types) DiffD1 image_iff image_insert insert_Diff_single insert_absorb oid_is_typerepr)
  apply(simp add: invalid_def bot_option_def)+
 by blast
 qed qed
 apply_end(simp add: OclSelf_at_post_def OclSelf_at_pre_def OclValid_def StrongEq_def true_def)+
qed


theorem framing':
      assumes wff : "WFF \<tau>"
      assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding(x :: ('\<AA>::object,'\<alpha>::object option option)val))->oclIsModifiedOnly()"
      and oid_is_typerepr : "\<tau> \<Turnstile> X->forAll(a| not (x \<triangleq> a))"
      and oid_preserve: "\<And>x. oid_of (Hh x) = oid_of x"
      and xy_together: "\<tau> \<Turnstile> X->forAll(y | ((Hh .allInstances()->includes(x) and (Hh .allInstances()->includes(y))) or
                             (Hh .allInstances@pre()->includes(x) and (Hh .allInstances@pre()->includes(y)))) )"
      shows "\<tau> \<Turnstile> (x @pre H  \<triangleq>  (x @post H))"
proof -
 have def_X : "\<tau> \<Turnstile> \<delta> X"
  apply(insert oid_is_typerepr, simp add: OclForall_def OclValid_def split: split_if_asm)
 by(simp add: bot_option_def true_def)
 show ?thesis
 apply(case_tac "\<tau> \<Turnstile> \<delta> x")
 proof - show "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> ?thesis" proof - assume def_x : "\<tau> \<Turnstile> \<delta> x" show ?thesis proof -

 have change_not : "\<And>a b. (not a \<tau> = b \<tau>) = (a \<tau> = not b \<tau>)"
 by (metis OclNot_not cp_OclNot)

 have contrapos_not: "\<And>A B. \<tau> \<Turnstile> \<delta> A \<Longrightarrow> (\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> B) \<Longrightarrow> \<tau> \<Turnstile> not B \<Longrightarrow> \<tau> \<Turnstile> not A"
  apply(simp add: OclValid_def, subst change_not, subst (asm) change_not)
  apply(simp add: OclNot_def true_def)
 by (metis OCL_core.bot_fun_def OclValid_def bool_split defined_def false_def foundation2 invalid_def true_def)

 have val_x: "\<tau> \<Turnstile> \<upsilon> x"
 by(rule foundation20[OF def_x])

 show ?thesis
  apply(rule framing[OF modifiesclause])
  apply(rule OclForall_cong'[OF _ oid_is_typerepr xy_together], rename_tac y)
  apply(cut_tac Set_inv_lemma'[OF def_X]) prefer 2 apply assumption
  apply(rule contrapos_not, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
  apply(simp add: OclValid_def, subst cp_defined, simp add: val_x[simplified OclValid_def])
 by(rule StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq''[THEN iffD1, OF wff val_x _ oid_preserve])
 qed qed
 apply_end(simp add: OclSelf_at_post_def OclSelf_at_pre_def OclValid_def StrongEq_def true_def)+
 qed
qed

subsection{* Miscellaneous *}

lemma pre_post_new: "\<tau> \<Turnstile> (x .oclIsNew()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsNew_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_old: "\<tau> \<Turnstile> (x .oclIsDeleted()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsDeleted_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_absent: "\<tau> \<Turnstile> (x .oclIsAbsent()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsAbsent_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_maintained: "(\<tau> \<Turnstile> \<upsilon>(x @pre H1) \<or> \<tau> \<Turnstile> \<upsilon>(x @post H2)) \<Longrightarrow> \<tau> \<Turnstile> (x .oclIsMaintained())"
by(simp add: OclIsMaintained_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma pre_post_maintained':
"\<tau> \<Turnstile> (x .oclIsMaintained()) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(x @pre (Some o H1)) \<and> \<tau> \<Turnstile> \<upsilon>(x @post (Some o H2)))"
by(simp add: OclIsMaintained_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: split_if_asm)

lemma framing_same_state: "(\<sigma>, \<sigma>) \<Turnstile> (x @pre H  \<triangleq>  (x @post H))"
by(simp add: OclSelf_at_pre_def OclSelf_at_post_def OclValid_def StrongEq_def)

section{* Miscellaneous : Propagation of "constant contexts P" *}
subsection{* *}

lemma true_cp_all : "true \<tau>1 = true \<tau>2"
by(simp add: true_def)
(*
lemma false_cp_all : "false \<tau>1 = false \<tau>2"
by(simp add: false_def)

lemma null_cp_all : "null \<tau>1 = null \<tau>2"
by(simp add: null_fun_def)
*)
lemma invalid_cp_all : "invalid \<tau>1 = invalid \<tau>2"
by(simp add: invalid_def)
(*
lemma bot_cp_all : "\<bottom> \<tau>1 = \<bottom> \<tau>2"
by(simp add: bot_fun_def)
*)
lemma defined_cp_all :
 assumes "X \<tau>1 = X \<tau>2"
 shows "(\<delta> X) \<tau>1 = (\<delta> X) \<tau>2"
by(simp add: defined_def false_def true_def bot_fun_def null_fun_def assms)

lemma valid_cp_all :
 assumes "X \<tau>1 = X \<tau>2"
 shows "(\<upsilon> X) \<tau>1 = (\<upsilon> X) \<tau>2"
by(simp add: valid_def false_def true_def bot_fun_def null_fun_def assms)
(*
lemma OclAnd_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "(X and X') \<tau>1 = (X and X') \<tau>2"
by(subst (1 2) cp_OclAnd, simp add: assms OclAnd_def)

lemma OclIf_cp_all :
  assumes "B \<tau>1 = B \<tau>2"
  assumes "C1 \<tau>1 = C1 \<tau>2"
  assumes "C2 \<tau>1 = C2 \<tau>2"
  shows "(if B then C1 else C2 endif) \<tau>1 = (if B then C1 else C2 endif) \<tau>2"
 apply(subst (1 2) cp_OclIf, simp only: OclIf_def cp_defined[symmetric])
by(simp add: defined_cp_all[OF assms(1)] true_cp_all assms invalid_cp_all)
*)
lemma OclIncluding_cp_all :
 assumes x_int : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
     and x_incl : "x \<tau>1 = x \<tau>2"
     and S_def : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> S"
     and S_incl : "S \<tau>1 = S \<tau>2"
   shows  "S->including(x) \<tau>1 = S->including(x) \<tau>2"
 apply(unfold OclIncluding_def)
 apply(simp add: S_def[simplified OclValid_def] x_int[simplified OclValid_def] S_incl)
 apply(simp add: x_incl)
done
(*
lemma OclForall_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "\<And>x. x \<tau>1 = x \<tau>2 \<Longrightarrow> X' x \<tau>1 = X' x \<tau>2"
  shows "OclForall X X' \<tau>1 = OclForall X X' \<tau>2"
 apply(subst (1 2) cp_OclForall, simp only: OclForall_def cp_defined[symmetric])
by(simp only: defined_cp_all[OF assms(1)] true_cp_all[of \<tau>1 \<tau>2] false_cp_all[of \<tau>1 \<tau>2] null_cp_all[of \<tau>1 \<tau>2] bot_cp_all[of \<tau>1 \<tau>2] assms)

lemma OclIncludes_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "OclIncludes X X' \<tau>1 = OclIncludes X X' \<tau>2"
 apply(subst (1 2) cp_OclIncludes, simp only: OclIncludes_def cp_defined[symmetric] cp_valid[symmetric])
by(simp add: defined_cp_all[OF assms(1)] valid_cp_all[OF assms(2)] true_cp_all assms)

lemma OclNot_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  shows "not X \<tau>1 = not X \<tau>2"
by(simp add: OclNot_def assms)
*)
lemma StrongEq_cp_all :
  assumes "X \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "(X \<triangleq> X') \<tau>1 = (X \<triangleq> X') \<tau>2"
by(simp add: StrongEq_def assms)

lemma StrictEq_cp_all :
  assumes "(X :: (_,_::null) Set) \<tau>1 = X \<tau>2"
  assumes "X' \<tau>1 = X' \<tau>2"
  shows "(X \<doteq> X') \<tau>1 = (X \<doteq> X') \<tau>2"
 apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t)
by(subst valid_cp_all[OF assms(1)],
   subst valid_cp_all[OF assms(2)],
   subst (1 2) true_cp_all[of \<tau>1 \<tau>2],
   subst invalid_cp_all[of \<tau>1 \<tau>2],
   subst StrongEq_cp_all[OF assms],
   simp)

lemma mtSet_cp_all : "Set{} \<tau>1 = Set{} \<tau>2"
by(simp add: mtSet_def)

subsection{* *}

definition "const X \<equiv> \<forall> \<tau> \<tau>'. X \<tau> = X \<tau>'"

lemma const_imply2 :
 assumes "\<And>\<tau>1 \<tau>2. P \<tau>1 = P \<tau>2 \<Longrightarrow> Q \<tau>1 = Q \<tau>2"
 shows "const P \<Longrightarrow> const Q"
by(simp add: const_def, insert assms, blast)

lemma const_imply3 :
 assumes "\<And>\<tau>1 \<tau>2. P \<tau>1 = P \<tau>2 \<Longrightarrow> Q \<tau>1 = Q \<tau>2 \<Longrightarrow> R \<tau>1 = R \<tau>2"
 shows "const P \<Longrightarrow> const Q \<Longrightarrow> const R"
by(simp add: const_def, insert assms, blast)

lemma const_imply4 :
 assumes "\<And>\<tau>1 \<tau>2. P \<tau>1 = P \<tau>2 \<Longrightarrow> Q \<tau>1 = Q \<tau>2 \<Longrightarrow> R \<tau>1 = R \<tau>2 \<Longrightarrow> S \<tau>1 = S \<tau>2"
 shows "const P \<Longrightarrow> const Q \<Longrightarrow> const R \<Longrightarrow> const S"
by(simp add: const_def, insert assms, blast)

lemma const_lam : "const (\<lambda>_. e)"
by(simp add: const_def)

(* *)

lemma const_true : "const true"
by(simp add: const_def true_def)
(*
lemma const_false : "const false"
by(simp add: const_def false_def)

lemma const_null : "const null"
by(simp add: const_def null_fun_def)
*)
lemma const_invalid : "const invalid"
by(simp add: const_def invalid_def)
(*
lemma const_bot : "const \<bottom>"
by(simp add: const_def bot_fun_def)
*)

lemma const_defined :
 assumes "const X"
 shows "const (\<delta> X)"
by(rule const_imply2[OF _ assms], simp add: defined_def false_def true_def bot_fun_def bot_option_def null_fun_def null_option_def)

lemma const_valid :
 assumes "const X"
 shows "const (\<upsilon> X)"
by(rule const_imply2[OF _ assms], simp add: valid_def false_def true_def bot_fun_def null_fun_def assms)
(*
lemma const_OclAnd :
  assumes "const X"
  assumes "const X'"
  shows "const (X and X')"
by(rule const_imply3[OF _ assms], subst (1 2) cp_OclAnd, simp add: assms OclAnd_def)

lemma const_OclIf :
  assumes "const B"
  assumes "const C1"
  assumes "const C2"
  shows "const (if B then C1 else C2 endif)"
 apply(rule const_imply4[OF _ assms], subst (1 2) cp_OclIf, simp only: OclIf_def cp_defined[symmetric])
 apply(simp add: const_defined[OF assms(1), simplified const_def, THEN spec, THEN spec]
                 const_true[simplified const_def, THEN spec, THEN spec]
                 assms[simplified const_def, THEN spec, THEN spec]
                 const_invalid[simplified const_def, THEN spec, THEN spec])
by (metis (no_types) OCL_core.bot_fun_def OclValid_def const_def const_true defined_def foundation17 null_fun_def)
*)
lemma const_OclIncluding :
 assumes x_int : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> x"
     and x_incl : "const x"
     and S_def : "\<And>\<tau>. \<tau> \<Turnstile> \<delta> S"
     and S_incl : "const S"
   shows  "const (S->including(x))"
 apply(rule const_imply3[OF _ assms(2) assms(4)], unfold OclIncluding_def)
by(simp add: S_def[simplified OclValid_def] x_int[simplified OclValid_def] S_incl)
(*
lemma const_OclForall :
  assumes "const X"
  assumes "\<And>x \<tau>1 \<tau>2. x \<tau>1 = x \<tau>2 \<Longrightarrow> X' x \<tau>1 = X' x \<tau>2"
  shows "const (OclForall X X')"
 apply(simp only: const_def, intro allI)
 proof - fix \<tau>1 \<tau>2 show "OclForall X X' \<tau>1 = OclForall X X' \<tau>2"
  apply(subst (1 2) cp_OclForall, simp only: OclForall_def cp_defined[symmetric])
 by(simp only: const_defined[OF assms(1), simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_true[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_false[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_null[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  const_bot[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  assms(1)[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
                  assms(2)[of _ \<tau>1 \<tau>2])
qed

lemma const_OclIncludes :
  assumes "const X"
  assumes "const X'"
  shows "const (OclIncludes X X')"
 apply(rule const_imply3[OF _ assms], subst (1 2) cp_OclIncludes, simp only: OclIncludes_def cp_defined[symmetric] cp_valid[symmetric])
 apply(simp add:
  const_defined[OF assms(1), simplified const_def, THEN spec, THEN spec]
  const_valid[OF assms(2), simplified const_def, THEN spec, THEN spec]
  const_true[simplified const_def, THEN spec, THEN spec] assms[simplified const_def]
  bot_option_def)
by (metis (no_types) const_def const_defined const_true const_valid cp_defined cp_valid)

lemma const_OclNot :
  assumes "const X"
  shows "const (not X)"
by(rule const_imply2[OF _ assms], simp add: OclNot_def)
*)
lemma const_StrongEq :
  assumes "const (X :: (_,_::null) Set)"
  assumes "const X'"
  shows "const (X \<triangleq> X')"
 apply(rule const_imply3[OF _ assms])
by(simp add: StrongEq_def assms)

lemma const_StrictEq :
  assumes "const (X :: (_,_::null) Set)"
  assumes "const X'"
  shows "const (X \<doteq> X')"
 apply(simp only: const_def, intro allI)
 proof -
 fix \<tau>1 \<tau>2 show "(X \<doteq> X') \<tau>1 = (X \<doteq> X') \<tau>2"
  apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t)
 by(simp add: const_valid[OF assms(1), simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_valid[OF assms(2), simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_true[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_invalid[simplified const_def, THEN spec, THEN spec, of \<tau>1 \<tau>2]
              const_StrongEq[OF assms, simplified const_def, THEN spec, THEN spec])
qed


lemma const_mtSet : "const Set{}"
by(simp add: const_def mtSet_def)

subsection{* *}

lemma StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1 : "cp P \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> y \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P x \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> P y \<Longrightarrow> \<tau> \<Turnstile> (x::('\<AA>,'\<alpha>::null)Set) \<doteq> y \<Longrightarrow> \<tau> \<Turnstile> (P x ::('\<AA>,'\<alpha>::null)Set) \<doteq> P y"
 apply(simp only: StrictRefEq\<^sub>S\<^sub>e\<^sub>t OclValid_def)
 apply(split split_if_asm)
 apply(simp add: StrongEq_L_subst1[simplified OclValid_def])
by (simp add: invalid_def bot_option_def true_def)

lemma including_subst_set' :
shows "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> ((s::('\<AA>,'a::null)Set) \<doteq> t) \<Longrightarrow> \<tau> \<Turnstile> (s->including(x) \<doteq> (t->including(x)))"
proof -
 have cp: "cp (\<lambda>s. (s->including(x)))"
  apply(simp add: cp_def, subst cp_OclIncluding)
 by (rule_tac x = "(\<lambda>xab ab. ((\<lambda>_. xab)->including(\<lambda>_. x ab)) ab)" in exI, simp)

 show "\<tau> \<Turnstile> \<delta> s \<Longrightarrow> \<tau> \<Turnstile> \<delta> t \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> (s \<doteq> t) \<Longrightarrow> ?thesis"
  apply(rule_tac P = "\<lambda>s. (s->including(x))" in StrictRefEq\<^sub>S\<^sub>e\<^sub>t_L_subst1)
  apply(rule cp)
  apply(simp add: foundation20) apply(simp add: foundation20)
  apply (simp add: foundation10 foundation6)+
 done
qed

end
