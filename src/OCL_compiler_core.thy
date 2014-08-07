(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_core.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Universite Paris-Sud, France
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

header{* Part ... *}

theory  OCL_compiler_core
imports OCL_compiler_core_infra
        OCL_compiler_core_astype
        OCL_compiler_core_istypeof
        OCL_compiler_core_iskindof
        OCL_compiler_core_allinst
        OCL_compiler_core_access
        OCL_compiler_core_examp
        OCL_compiler_core_ctxt
begin

section{* Translation of AST *}

subsection{* Conclusion *}

definition "section_aux n s = start_map' (\<lambda>_. [ Thy_section_title (Section_title n s) ])"
definition "section = section_aux 0"
definition "subsection = section_aux 1"
definition "subsubsection = section_aux 2"
definition "txt f = start_map'''' Thy_text o (\<lambda>_ design_analysis. [Text (f design_analysis)])"
definition "txt' s = txt (\<lambda>_. s)"
definition "txt'' = txt' o flatten"
definition "txt''d s = txt (\<lambda> Gen_design \<Rightarrow> flatten s | _ \<Rightarrow> [])"
definition "txt''a s = txt (\<lambda> Gen_analysis \<Rightarrow> flatten s | _ \<Rightarrow> [])"

definition thy_class ::
  (* polymorphism weakening needed by code_reflect *)
  "(_ \<Rightarrow> ocl_compiler_config \<Rightarrow> _) list" where "thy_class =
  (let subsection_def = subsection ''Definition''
     ; subsection_cp = subsection ''Context Passing''
     ; subsection_exec = subsection ''Execution with Invalid or Null as Argument''
     ; subsection_up = subsection ''Up Down Casting''
     ; subsection_defined = subsection ''Validity and Definedness Properties''
     ; e = [Char Nibble5 NibbleC]
     ; n = [Char Nibble2 Nibble7]
     ; a = [Char Nibble2 Nibble2] in
  flatten
          [ [ txt''d [ ''
   '', e, ''label{ex:employee-design:uml} '' ]
            , txt''a [ ''
   '', e, ''label{ex:employee-analysis:uml} '' ]
            , section ''Introduction''
            , txt'' [ ''

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'', n, '''', n, '' a concrete,
  closed-world class diagram into a ``theory'', n, '''', n, '' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. '' ]
            , txt'' [ ''
   Such generic function or ``compiler'', n, '''', n, '' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~'', e, ''cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL. '' ]
            , subsection ''Outlining the Example''
            , txt''d [ ''
   We are presenting here a ``design-model'', n, '''', n, '' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~'', e, ''cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the UML class model (see '', e, ''autoref{fig:person}):'' ]
            , txt''a [ ''
   We are presenting here an ``analysis-model'', n, '''', n, '' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~'', e, ''cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model'', n, '''', n, '' (see '', e, ''autoref{ex:employee-design:uml}).
To be precise, this theory contains the formalization of the data-part
covered by the UML class model (see '', e, ''autoref{fig:person-ana}):'' ]
            , txt''d [ ''

'', e, ''begin{figure}
  '', e, ''centering'', e, ''scalebox{.3}{'', e, ''includegraphics{figures/person.png}}%
  '', e, ''caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~'', e, ''cite{omg:ocl:2012}. '', e, ''label{fig:person}}
'', e, ''end{figure}
'' ]
            , txt''a [ ''

'', e, ''begin{figure}
  '', e, ''centering'', e, ''scalebox{.3}{'', e, ''includegraphics{figures/person.png}}%
  '', e, ''caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~'', e, ''cite{omg:ocl:2012}. '', e, ''label{fig:person-ana}}
'', e, ''end{figure}
'' ]
            , txt'' [ ''
   This means that the association (attached to the association class
'', e, ''inlineocl{EmployeeRanking}) with the association ends '', e, ''inlineocl+boss+ and '', e, ''inlineocl+employees+ is implemented
by the attribute  '', e, ''inlineocl+boss+ and the operation '', e, ''inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
'' ]
            , section ''Example Data-Universe and its Infrastructure''
            (*, txt'' [ ''
   Ideally, the following is generated automatically from a UML class model.  '' ]
            *), txt'' [ ''
   Our data universe  consists in the concrete class diagram just of node'', n, ''s,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: '' ]
            , print_infra_datatype_class
            , txt'' [ ''
   Now, we construct a concrete ``universe of OclAny types'', n, '''', n, '' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables. '' ]
            , print_infra_datatype_universe
            , txt'' [ ''
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'', n, '''', n, '' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL. '' ]
            , print_infra_type_synonym_class
            , print_infra_type_synonym_class_set
            (*, txt'' [ ''
   Just a little check: '' ]
            *), txt'' [ ''
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'', n, '''', n, '' '', e, ''ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object. '' ]
            , print_infra_instantiation_class
            , print_infra_instantiation_universe

            , section ''Instantiation of the Generic Strict Equality''
            , txt'' [ ''
   We instantiate the referential equality
on @{text '', a, ''Person'', a, ''} and @{text '', a, ''OclAny'', a, ''} '' ]
            , print_instantia_def_strictrefeq
            , print_instantia_lemmas_strictrefeq
            , txt'' [ ''
   For each Class '', e, ''emph{C}, we will have a casting operation '', e, ''inlineocl{.oclAsType($C$)},
   a test on the actual type '', e, ''inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   '', e, ''inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java'', n, ''s '', e, ''verb+instanceof+-operator.
'' ]
            , txt'' [ ''
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
'' ] ]

          , flatten (List_map (\<lambda>(title, body_def, body_cp, body_exec, body_defined, body_up).
              section title # flatten [ subsection_def # body_def
                                      , subsection_cp # body_cp
                                      , subsection_exec # body_exec
                                      , subsection_defined # body_defined
                                      , subsection_up # body_up ])
          [ (''OclAsType'',
            [ print_astype_consts
            , print_astype_class
            , print_astype_from_universe
            , print_astype_lemmas_id ]
            , [ print_astype_lemma_cp
            , print_astype_lemmas_cp ]
            , [ print_astype_lemma_strict
            , print_astype_lemmas_strict ]
            , [ print_astype_defined ]
            , [ print_astype_up_d_cast0
            , print_astype_up_d_cast ])

          , (''OclIsTypeOf'',
            [ print_istypeof_consts
            , print_istypeof_class
            , print_istypeof_from_universe
            , print_istypeof_lemmas_id ]
            , [ print_istypeof_lemma_cp
            , print_istypeof_lemmas_cp ]
            , [ print_istypeof_lemma_strict
            , print_istypeof_lemmas_strict ]
            , [ print_istypeof_defined
            , print_istypeof_defined' ]
            , [ print_istypeof_up_larger
            , print_istypeof_up_d_cast ])

          , (''OclIsKindOf'',
            [ print_iskindof_consts
            , print_iskindof_class
            , print_iskindof_from_universe
            , print_iskindof_lemmas_id ]
            , [ print_iskindof_lemma_cp
            , print_iskindof_lemmas_cp ]
            , [ print_iskindof_lemma_strict
            , print_iskindof_lemmas_strict ]
            , [ print_iskindof_defined
            , print_iskindof_defined' ]
            , [ print_iskindof_up_eq_asty
            , print_iskindof_up_larger
            , print_iskindof_up_istypeof_unfold
            , print_iskindof_up_istypeof
            , print_iskindof_up_d_cast ]) ])

          , [ section ''OclAllInstances''
            , txt'' [ ''
   To denote OCL-types occuring in OCL expressions syntactically---as, for example,  as
``argument'', n, '''', n, '' of '', e, ''inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.'', n, '''', n, '' '' ]
            , print_allinst_def_id
            , print_allinst_lemmas_id
            , print_allinst_astype
            , print_allinst_exec
            , subsection ''OclIsTypeOf''
            , print_allinst_istypeof_pre
            , print_allinst_istypeof
            , subsection ''OclIsKindOf''
            , print_allinst_iskindof_eq
            , print_allinst_iskindof_larger

            , section ''The Accessors''
            , txt''d [ ''
  '', e, ''label{sec:edm-accessors}'' ]
            , txt''a [ ''
  '', e, ''label{sec:eam-accessors}'' ]
            (*, txt'' [ ''
   Should be generated entirely from a class-diagram. '' ]
            *), subsection_def
            , txt''a [ ''
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the '', e, ''inlineisar+Employee_DesignModel_UMLPart+, where we stored
an '', e, ''verb+oid+ inside the class as ``pointer.'', n, '''', n, '' '' ]
            , print_access_oid_uniq_ml
            , print_access_oid_uniq
            , txt''a [ ''
   From there on, we can already define an empty state which must contain
for $'', e, ''mathit{oid}_{Person}'', e, ''mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure).'' ]
            , print_access_eval_extract
            , txt''a [ ''
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}: '' ]
            , print_access_choose_ml
            , print_access_choose
            , print_access_deref_oid
            , print_access_deref_assocs
            , txt''a [ ''
   The continuation @{text f} is usually instantiated with a smashing
function which is either the identity @{term id} or, for '', e, ''inlineocl{0..1} cardinalities
of associations, the @{term OclANY}-selector which also handles the
@{term null}-cases appropriately. A standard use-case for this combinator
is for example: '' ]
            , print_access_select_object
            , txt'' [ ''
   pointer undefined in state or not referencing a type conform object representation '' ]
            , print_access_select
            , print_access_select_obj
            , print_access_dot_consts
            , print_access_dot
            , print_access_dot_lemmas_id
            , subsection_cp
            , print_access_dot_cp_lemmas
            , print_access_dot_lemma_cp
            , print_access_dot_lemmas_cp
            , subsection_exec
            , print_access_lemma_strict

            , section ''A Little Infra-structure on Example States''
            , txt''d [ ''

The example we are defining in this section comes from the figure~'', e, ''ref{fig:edm1_system-states}.
'', e, ''begin{figure}
'', e, ''includegraphics[width='', e, ''textwidth]{figures/pre-post.pdf}
'', e, ''caption{(a) pre-state $'', e, ''sigma_1$ and
  (b) post-state $'', e, ''sigma_1'', n, ''$.}
'', e, ''label{fig:edm1_system-states}
'', e, ''end{figure}
'' ]
            , txt''a [ ''

The example we are defining in this section comes from the figure~'', e, ''ref{fig:eam1_system-states}.
'', e, ''begin{figure}
'', e, ''includegraphics[width='', e, ''textwidth]{figures/pre-post.pdf}
'', e, ''caption{(a) pre-state $'', e, ''sigma_1$ and
  (b) post-state $'', e, ''sigma_1'', n, ''$.}
'', e, ''label{fig:eam1_system-states}
'', e, ''end{figure}
'' ]
            , print_examp_def_st_defs
            , print_astype_lemmas_id2 ] ])"

definition "thy_class_flat = []"
definition "thy_association = []"
definition "thy_instance = [ print_examp_instance_defassoc
                           , print_examp_instance
                           , print_examp_instance_defassoc_typecheck ]"
definition "thy_def_int = [ print_examp_oclint ]"
definition "thy_def_state = [ print_examp_def_st_defassoc
                            , print_examp_def_st
                            , print_examp_def_st_inst_var
                            , print_examp_def_st_dom
                            , print_examp_def_st_dom_lemmas
                            , print_examp_def_st_perm
                            , print_examp_def_st_allinst ]"
definition "thy_def_pre_post = [ print_pre_post_wff
                               , print_pre_post_where ]"
definition "thy_ctxt_pre_post = [ print_ctxt_pre_post ]"
definition "thy_ctxt2_pre_post = [ print_ctxt2_pre_post ]"
definition "thy_ctxt_inv = [ print_ctxt_inv ]"
definition "thy_ctxt2_inv = [ print_ctxt2_inv ]"
definition "thy_flush_all = []"

definition "ocl_compiler_config_empty disable_thy_output file_out_path_dep oid_start design_analysis =
  ocl_compiler_config.make
    disable_thy_output
    file_out_path_dep
    oid_start
    (0, 0)
    design_analysis
    None [] [] [] False False ([], [])"

definition "ocl_compiler_config_reset_no_env ocl =
  ocl_compiler_config_empty
    (D_disable_thy_output ocl)
    (D_file_out_path_dep ocl)
    (oidReinitAll (D_oid_start ocl))
    (D_design_analysis ocl)
    \<lparr> D_ocl_env := D_ocl_env ocl \<rparr>"

definition "ocl_compiler_config_reset_all ocl =
  (let ocl = ocl_compiler_config_reset_no_env ocl in
   ( ocl \<lparr> D_ocl_env := [] \<rparr>
   , let (l_class, l_ocl) = List.partition (\<lambda> OclAstClassRaw _ \<Rightarrow> True
                                            | OclAstAssociation _ \<Rightarrow> True
                                            | OclAstAssClass _ \<Rightarrow> True
                                            | _ \<Rightarrow> False) (rev (D_ocl_env ocl)) in
     flatten
       [ l_class
       , List.filter (\<lambda> OclAstFlushAll _ \<Rightarrow> False | _ \<Rightarrow> True) l_ocl
       , [OclAstFlushAll OclFlushAll] ] ))"

definition "fold_thy0 univ thy_object0 f =
  List.fold (\<lambda>x (acc1, acc2).
    let (l, acc1) = x univ acc1 in
    (f l acc1 acc2)) thy_object0"

definition "ocl_env_class_spec_rm f_fold f ocl_accu =
  (let (ocl, accu) = f_fold f ocl_accu in
   (ocl \<lparr> D_class_spec := None \<rparr>, accu))"

definition "ocl_env_class_spec_mk f_try f_accu_reset f_fold f =
  (\<lambda> (ocl, accu).
    f_fold f
      (case D_class_spec ocl of Some _ \<Rightarrow> (ocl, accu) | None \<Rightarrow>
       let (l_class, l_ocl) = find_class_ass ocl in
       (f_try (\<lambda> () \<Rightarrow> List.fold
           (\<lambda>ast. (case ast of
               OclAstInstance univ \<Rightarrow> fold_thy0 univ thy_instance
             | OclAstDefInt univ \<Rightarrow> fold_thy0 univ thy_def_int
             | OclAstDefState univ \<Rightarrow> fold_thy0 univ thy_def_state
             | OclAstDefPrePost univ \<Rightarrow> fold_thy0 univ thy_def_pre_post
             | OclAstCtxtPrePost univ \<Rightarrow> fold_thy0 univ thy_ctxt_pre_post
             | OclAstCtxt2PrePost univ \<Rightarrow> fold_thy0 univ thy_ctxt2_pre_post
             | OclAstCtxtInv univ \<Rightarrow> fold_thy0 univ thy_ctxt_inv
             | OclAstCtxt2Inv univ \<Rightarrow> fold_thy0 univ thy_ctxt2_inv
             | OclAstFlushAll univ \<Rightarrow> fold_thy0 univ thy_flush_all)
                  f)
           l_ocl
           (let univ = class_unflat
                         (List.map_filter (\<lambda> OclAstClassRaw cflat \<Rightarrow> Some cflat
                                           | OclAstAssClass (OclAssClass _ cflat) \<Rightarrow> Some cflat
                                           | _ \<Rightarrow> None) l_class)
                         (filter_ass l_class)
              ; (ocl, accu) = fold_thy0 univ thy_class f (let ocl = ocl_compiler_config_reset_no_env ocl in
                                                          (ocl, f_accu_reset ocl accu)) in
            (ocl \<lparr> D_class_spec := Some univ \<rparr>, accu))))))"

definition "ocl_env_save ast f_fold f ocl_accu =
  (let (ocl, accu) = f_fold f ocl_accu in
   (ocl \<lparr> D_ocl_env := ast # D_ocl_env ocl \<rparr>, accu))"

definition "ocl_env_class_spec_bind l f =
  List.fold (\<lambda>x. x f) l"

definition "fold_thy' f_try f_accu_reset f =
 (let ocl_env_class_spec_mk = ocl_env_class_spec_mk f_try f_accu_reset in
  List.fold (\<lambda> ast.
    ocl_env_save ast (case ast of
     OclAstClassRaw univ \<Rightarrow> ocl_env_class_spec_rm (fold_thy0 univ thy_class_flat)
   | OclAstAssociation univ \<Rightarrow> ocl_env_class_spec_rm (fold_thy0 univ thy_association)
   | OclAstAssClass (OclAssClass univ_ass univ_class) \<Rightarrow>
       ocl_env_class_spec_rm (ocl_env_class_spec_bind [ fold_thy0 univ_ass thy_association
                                                      , fold_thy0 univ_class thy_class_flat ])
   | OclAstInstance univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_instance)
   | OclAstDefInt univ \<Rightarrow> fold_thy0 univ thy_def_int
   | OclAstDefState univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_def_state)
   | OclAstDefPrePost univ \<Rightarrow> fold_thy0 univ thy_def_pre_post
   | OclAstCtxtPrePost univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_ctxt_pre_post)
   | OclAstCtxt2PrePost univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_ctxt2_pre_post)
   | OclAstCtxtInv univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_ctxt_inv)
   | OclAstCtxt2Inv univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_ctxt2_inv)
   | OclAstFlushAll univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_flush_all)) f))"

definition "fold_thy_shallow f_try f_accu_reset x = fold_thy' f_try f_accu_reset (\<lambda>l acc1. List.fold x l o Pair acc1)"
definition "fold_thy_deep obj ocl =
  (case fold_thy'
          (\<lambda>f. f ())
          (\<lambda>ocl _. D_output_position ocl)
          (\<lambda>l acc1 (i, cpt). (acc1, (Succ i, natural_of_nat (List.length l) + cpt)))
          obj
          (ocl, D_output_position ocl) of
    (ocl, output_position) \<Rightarrow> ocl \<lparr> D_output_position := output_position \<rparr>)"

end
