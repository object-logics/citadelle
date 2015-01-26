(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_core.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
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

theory  OCL_compiler_core
imports "core/OCL_compiler_floor1_infra"
        "core/OCL_compiler_floor1_astype"
        "core/OCL_compiler_floor1_istypeof"
        "core/OCL_compiler_floor1_iskindof"
        "core/OCL_compiler_floor1_allinst"
        "core/OCL_compiler_floor1_access"
        "core/OCL_compiler_floor1_examp"
        "core/OCL_compiler_floor1_ctxt"
        "core/OCL_compiler_floor2_ctxt"
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
definition "txt''d s = txt (\<lambda> Gen_only_design \<Rightarrow> flatten s | _ \<Rightarrow> \<langle>''''\<rangle>)"
definition "txt''a s = txt (\<lambda> Gen_only_design \<Rightarrow> \<langle>''''\<rangle> | _ \<Rightarrow> flatten s)"

definition thy_class ::
  (* polymorphism weakening needed by code_reflect *)
  "(_ \<Rightarrow> ocl_compiler_config \<Rightarrow> _) list" where "thy_class =
  (let subsection_def = subsection \<langle>''Definition''\<rangle>
     ; subsection_cp = subsection \<langle>''Context Passing''\<rangle>
     ; subsection_exec = subsection \<langle>''Execution with Invalid or Null as Argument''\<rangle>
     ; subsection_up = subsection \<langle>''Up Down Casting''\<rangle>
     ; subsection_defined = subsection \<langle>''Validity and Definedness Properties''\<rangle>
     ; e = \<langle>[Char Nibble5 NibbleC]\<rangle>
     ; n = \<langle>[Char Nibble2 Nibble7]\<rangle>
     ; a = \<langle>[Char Nibble2 Nibble2]\<rangle> in
  List_flatten
          [ [ txt''d [ \<langle>''
   ''\<rangle>, e, \<langle>''label{ex:employee-design:uml} ''\<rangle> ]
            , txt''a [ \<langle>''
   ''\<rangle>, e, \<langle>''label{ex:employee-analysis:uml} ''\<rangle> ]
            , section \<langle>''Introduction''\<rangle>
            , txt'' [ \<langle>''

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' a concrete,
  closed-world class diagram into a ``theory''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. ''\<rangle> ]
            , txt'' [ \<langle>''
   Such generic function or ``compiler''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~''\<rangle>, e, \<langle>''cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL. ''\<rangle> ]
            , subsection \<langle>''Outlining the Example''\<rangle>
            , txt''d [ \<langle>''
   We are presenting here a ``design-model''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~''\<rangle>, e, \<langle>''cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the UML class model (see ''\<rangle>, e, \<langle>''autoref{fig:person}):''\<rangle> ]
            , txt''a [ \<langle>''
   We are presenting here an ``analysis-model''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~''\<rangle>, e, \<langle>''cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' (see ''\<rangle>, e, \<langle>''autoref{ex:employee-design:uml}).
To be precise, this theory contains the formalization of the data-part
covered by the UML class model (see ''\<rangle>, e, \<langle>''autoref{fig:person-ana}):''\<rangle> ]
            , txt''d [ \<langle>''

''\<rangle>, e, \<langle>''begin{figure}
  ''\<rangle>, e, \<langle>''centering''\<rangle>, e, \<langle>''scalebox{.3}{''\<rangle>, e, \<langle>''includegraphics{figures/person.png}}%
  ''\<rangle>, e, \<langle>''caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~''\<rangle>, e, \<langle>''cite{omg:ocl:2012}. ''\<rangle>, e, \<langle>''label{fig:person}}
''\<rangle>, e, \<langle>''end{figure}
''\<rangle> ]
            , txt''a [ \<langle>''

''\<rangle>, e, \<langle>''begin{figure}
  ''\<rangle>, e, \<langle>''centering''\<rangle>, e, \<langle>''scalebox{.3}{''\<rangle>, e, \<langle>''includegraphics{figures/person.png}}%
  ''\<rangle>, e, \<langle>''caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~''\<rangle>, e, \<langle>''cite{omg:ocl:2012}. ''\<rangle>, e, \<langle>''label{fig:person-ana}}
''\<rangle>, e, \<langle>''end{figure}
''\<rangle> ]
            , txt'' [ \<langle>''
   This means that the association (attached to the association class
''\<rangle>, e, \<langle>''inlineocl{EmployeeRanking}) with the association ends ''\<rangle>, e, \<langle>''inlineocl+boss+ and ''\<rangle>, e, \<langle>''inlineocl+employees+ is implemented
by the attribute  ''\<rangle>, e, \<langle>''inlineocl+boss+ and the operation ''\<rangle>, e, \<langle>''inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
''\<rangle> ]
            , section \<langle>''Example Data-Universe and its Infrastructure''\<rangle>
            (*, txt'' [ \<langle>''
   Ideally, the following is generated automatically from a UML class model.  ''\<rangle> ]
            *), txt'' [ \<langle>''
   Our data universe  consists in the concrete class diagram just of node''\<rangle>, n, \<langle>''s,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: ''\<rangle> ]
            (*, print_latex_infra_datatype_class*)
            , print_infra_datatype_class
            , txt'' [ \<langle>''
   Now, we construct a concrete ``universe of OclAny types''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables. ''\<rangle> ]
            , print_infra_datatype_universe
            , txt'' [ \<langle>''
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL. ''\<rangle> ]
            , print_infra_type_synonym_class
            , print_infra_type_synonym_class_rec
            (*, txt'' [ \<langle>''
   Just a little check: ''\<rangle> ]
            *), txt'' [ \<langle>''
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' ''\<rangle>, e, \<langle>''ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object. ''\<rangle> ]
            , print_infra_instantiation_class
            , print_infra_instantiation_universe

            , section \<langle>''Instantiation of the Generic Strict Equality''\<rangle>
            , txt'' [ \<langle>''
   We instantiate the referential equality
on @{text ''\<rangle>, a, \<langle>''Person''\<rangle>, a, \<langle>''} and @{text ''\<rangle>, a, \<langle>''OclAny''\<rangle>, a, \<langle>''} ''\<rangle> ]
            , print_instantia_def_strictrefeq
            , print_instantia_lemmas_strictrefeq
            , txt'' [ \<langle>''
   For each Class ''\<rangle>, e, \<langle>''emph{C}, we will have a casting operation ''\<rangle>, e, \<langle>''inlineocl{.oclAsType($C$)},
   a test on the actual type ''\<rangle>, e, \<langle>''inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   ''\<rangle>, e, \<langle>''inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java''\<rangle>, n, \<langle>''s ''\<rangle>, e, \<langle>''verb+instanceof+-operator.
''\<rangle> ]
            , txt'' [ \<langle>''
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
''\<rangle> ] ]

          , List_flatten (List_map (\<lambda>(title, body_def, body_cp, body_exec, body_defined, body_up).
              section title # List_flatten [ subsection_def # body_def
                                      , subsection_cp # body_cp
                                      , subsection_exec # body_exec
                                      , subsection_defined # body_defined
                                      , subsection_up # body_up ])
          [ (\<langle>''OclAsType''\<rangle>,
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
            , print_astype_up_d_cast
            , print_astype_d_up_cast ])

          , (\<langle>''OclIsTypeOf''\<rangle>,
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

          , (\<langle>''OclIsKindOf''\<rangle>,
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

          , [ section \<langle>''OclAllInstances''\<rangle>
            , txt'' [ \<langle>''
   To denote OCL-types occuring in OCL expressions syntactically---as, for example,  as
``argument''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' of ''\<rangle>, e, \<langle>''inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' ''\<rangle> ]
            , print_allinst_def_id
            , print_allinst_lemmas_id
            , print_allinst_astype
            , print_allinst_exec
            , subsection \<langle>''OclIsTypeOf''\<rangle>
            , print_allinst_istypeof_pre
            , print_allinst_istypeof
            , subsection \<langle>''OclIsKindOf''\<rangle>
            , print_allinst_iskindof_eq
            , print_allinst_iskindof_larger

            , section \<langle>''The Accessors''\<rangle>
            , txt''d [ \<langle>''
  ''\<rangle>, e, \<langle>''label{sec:edm-accessors}''\<rangle> ]
            , txt''a [ \<langle>''
  ''\<rangle>, e, \<langle>''label{sec:eam-accessors}''\<rangle> ]
            (*, txt'' [ \<langle>''
   Should be generated entirely from a class-diagram. ''\<rangle> ]
            *), subsection_def
            , txt''a [ \<langle>''
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the ''\<rangle>, e, \<langle>''inlineisar+Employee_DesignModel_UMLPart+, where we stored
an ''\<rangle>, e, \<langle>''verb+oid+ inside the class as ``pointer.''\<rangle>, n, \<langle>''''\<rangle>, n, \<langle>'' ''\<rangle> ]
            , print_access_oid_uniq_ml
            , print_access_oid_uniq
            , txt''a [ \<langle>''
   From there on, we can already define an empty state which must contain
for $''\<rangle>, e, \<langle>''mathit{oid}_{Person}''\<rangle>, e, \<langle>''mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure).''\<rangle> ]
            , print_access_eval_extract
            , txt''a [ \<langle>''
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}: ''\<rangle> ]
            , print_access_choose_ml
            , print_access_choose
            , print_access_deref_oid
            , print_access_deref_assocs
            , txt'' [ \<langle>''
   pointer undefined in state or not referencing a type conform object representation ''\<rangle> ]
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
            , subsection \<langle>''Representation in States''\<rangle>
            , print_access_def_mono
            , print_access_is_repr

            , section \<langle>''A Little Infra-structure on Example States''\<rangle>
            , txt''d [ \<langle>''

The example we are defining in this section comes from the figure~''\<rangle>, e, \<langle>''ref{fig:edm1_system-states}.
''\<rangle>, e, \<langle>''begin{figure}
''\<rangle>, e, \<langle>''includegraphics[width=''\<rangle>, e, \<langle>''textwidth]{figures/pre-post.pdf}
''\<rangle>, e, \<langle>''caption{(a) pre-state $''\<rangle>, e, \<langle>''sigma_1$ and
  (b) post-state $''\<rangle>, e, \<langle>''sigma_1''\<rangle>, n, \<langle>''$.}
''\<rangle>, e, \<langle>''label{fig:edm1_system-states}
''\<rangle>, e, \<langle>''end{figure}
''\<rangle> ]
            , txt''a [ \<langle>''

The example we are defining in this section comes from the figure~''\<rangle>, e, \<langle>''ref{fig:eam1_system-states}.
''\<rangle>, e, \<langle>''begin{figure}
''\<rangle>, e, \<langle>''includegraphics[width=''\<rangle>, e, \<langle>''textwidth]{figures/pre-post.pdf}
''\<rangle>, e, \<langle>''caption{(a) pre-state $''\<rangle>, e, \<langle>''sigma_1$ and
  (b) post-state $''\<rangle>, e, \<langle>''sigma_1''\<rangle>, n, \<langle>''$.}
''\<rangle>, e, \<langle>''label{fig:eam1_system-states}
''\<rangle>, e, \<langle>''end{figure}
''\<rangle> ]
            , print_examp_def_st_defs
            , print_astype_lemmas_id2 ] ])"

definition "thy_class_flat = []"
definition "thy_association = []"
definition "thy_instance = [ print_examp_instance_defassoc
                           , print_examp_instance
                           , print_examp_instance_defassoc_typecheck ]"
definition "thy_def_base_l = [ print_examp_oclbase ]"
definition "thy_def_state = [ print_examp_def_st_defassoc
                            , print_examp_def_st
                            , print_examp_def_st_inst_var
                            , print_examp_def_st_dom
                            , print_examp_def_st_dom_lemmas
                            , print_examp_def_st_perm
                            , print_examp_def_st_allinst ]"
definition "thy_def_pre_post = [ print_pre_post_wff
                               , print_pre_post_where ]"
definition "thy_ctxt_pre_post n = [ case n of Floor1 \<Rightarrow> OCL_compiler_floor1_ctxt.print_ctxt_pre_post
                                            | Floor2 \<Rightarrow> OCL_compiler_floor2_ctxt.print_ctxt_pre_post ]"
definition "thy_ctxt_inv n = [ case n of Floor1 \<Rightarrow> OCL_compiler_floor1_ctxt.print_ctxt_inv
                                       | Floor2 \<Rightarrow> OCL_compiler_floor2_ctxt.print_ctxt_inv ]"
definition "thy_flush_all = []"

definition "ocl_compiler_config_empty disable_thy_output file_out_path_dep oid_start design_analysis sorry_dirty =
  ocl_compiler_config.make
    disable_thy_output
    file_out_path_dep
    oid_start
    (0, 0)
    design_analysis
    None [] [] [] False False ([], []) []
    sorry_dirty"

definition "ocl_compiler_config_reset_no_env ocl =
  ocl_compiler_config_empty
    (D_disable_thy_output ocl)
    (D_file_out_path_dep ocl)
    (oidReinitAll (D_oid_start ocl))
    (D_design_analysis ocl)
    (D_sorry_dirty ocl)
    \<lparr> D_ocl_env := D_ocl_env ocl \<rparr>"

definition "ocl_compiler_config_reset_all ocl =
  (let ocl = ocl_compiler_config_reset_no_env ocl in
   ( ocl \<lparr> D_ocl_env := [] \<rparr>
   , let (l_class, l_ocl) = find_class_ass ocl in
     List_flatten
       [ l_class
       , List.filter (\<lambda> OclAstFlushAll _ \<Rightarrow> False | _ \<Rightarrow> True) l_ocl
       , [OclAstFlushAll OclFlushAll] ] ))"

definition "fold_thy0 univ thy_object0 f =
  List.fold (\<lambda>x (acc1, acc2).
    let (sorry, dirty) = D_sorry_dirty acc1
      ; (l, acc1) = x univ acc1 in
    (f (if sorry = Some Gen_sorry | sorry = None & dirty then
          List_map (hol_map_thy (hol_map_lemma (\<lambda> Lemma_by n spec _ _ \<Rightarrow> Lemma_by n spec [] Tacl_sorry
                                                | Lemma_by_assum n spec1 spec2 _ _ \<Rightarrow> Lemma_by_assum n spec1 spec2 [] Tacl_sorry))) l
        else
          l) acc1 acc2)) thy_object0"

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
             | OclAstDefBaseL univ \<Rightarrow> fold_thy0 univ thy_def_base_l
             | OclAstDefState univ \<Rightarrow> fold_thy0 univ thy_def_state
             | OclAstDefPrePost univ \<Rightarrow> fold_thy0 univ thy_def_pre_post
             | OclAstCtxtPrePost floor univ \<Rightarrow> fold_thy0 univ (thy_ctxt_pre_post floor)
             | OclAstCtxtInv floor univ \<Rightarrow> fold_thy0 univ (thy_ctxt_inv floor)
             | OclAstFlushAll univ \<Rightarrow> fold_thy0 univ thy_flush_all)
                  f)
           l_ocl
           (let univ = class_unflat (arrange_ass l_class)
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
     OclAstClassRaw Floor1 univ \<Rightarrow> ocl_env_class_spec_rm (fold_thy0 univ thy_class_flat)
   | OclAstAssociation univ \<Rightarrow> ocl_env_class_spec_rm (fold_thy0 univ thy_association)
   | OclAstAssClass Floor1 (OclAssClass univ_ass univ_class) \<Rightarrow>
       ocl_env_class_spec_rm (ocl_env_class_spec_bind [ fold_thy0 univ_ass thy_association
                                                      , fold_thy0 univ_class thy_class_flat ])
   | OclAstInstance univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_instance)
   | OclAstDefBaseL univ \<Rightarrow> fold_thy0 univ thy_def_base_l
   | OclAstDefState univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_def_state)
   | OclAstDefPrePost univ \<Rightarrow> fold_thy0 univ thy_def_pre_post
   | OclAstCtxtPrePost floor univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ (thy_ctxt_pre_post floor))
   | OclAstCtxtInv floor univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ (thy_ctxt_inv floor))
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
