(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_DesignModel_UMLPart_generator.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013      Universite Paris-Sud, France
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

header{* Part ... *}

theory
  Employee_DesignModel_UMLPart_generator
imports
  "../src/OCL_class_diagram_generator"
begin
section{* Code generation *}
subsection{* Instance *}

definition "Employee_DesignModel_UMLPart =
         Mk_univ ''OclAny'' []
  (Some (Mk_univ ''Galaxy'' [(''sound'', OclTy_base ''unit''), (''moving'', OclTy_base ''bool'')]
  (Some (Mk_univ ''Planet'' [(''weight'', OclTy_base ''nat'')]
  (Some (Mk_univ ''Person'' [(''salary'', OclTy_base ''int''), (''boss'', object)]
   None )) )) ))"

definition "Employee_DesignModel_UMLPart' =
         Mk_univ ''OclAny'' []
  (Some (Mk_univ ''Person'' [(''salary'', OclTy_base ''int''), (''boss'', object)]
   None ))"

subsection{* Raw *}

definition "thy_object =
            [ print_datatype_class
            , print_datatype_universe
            , print_type_synonym_class
            , print_instantiation_class
            , print_instantiation_universe
            , print_def_strictrefeq

            , print_astype_consts
            , print_astype_class
            (*, print_astype_from_universe*), print_astype_from_universe'
            , print_astype_lemmas_id
            , print_astype_lemma_cp
            , print_astype_lemmas_cp
            , print_astype_lemma_strict
            , print_astype_lemmas_strict

            , print_istypeof_consts
            , print_istypeof_class
            , print_istypeof_from_universe(*, print_istypeof_from_universe'*)
            , print_istypeof_lemmas_id
            , print_istypeof_lemma_cp
            , print_istypeof_lemmas_cp
            , print_istypeof_lemma_strict
            , print_istypeof_lemmas_strict

            , print_iskindof_consts
            , print_iskindof_class
            , print_iskindof_from_universe(*, print_iskindof_from_universe'*)
            , print_iskindof_lemmas_id
            , print_iskindof_lemma_cp
            , print_iskindof_lemmas_cp
            , print_iskindof_lemma_strict
            , print_iskindof_lemmas_strict

            , print_eval_extract
            , print_deref_oid
            , print_select
            , print_select_inherited
            , print_dot
            , print_dot_inherited ]"

definition "main = (let file_out = STR ''Employee_DesignModel_UMLPart_generated''
                      ; exemple = (case True of True \<Rightarrow> Employee_DesignModel_UMLPart
                                  | False \<Rightarrow> Employee_DesignModel_UMLPart') in
  case filter Sys_is_directory Sys_argv
  of dir # _ \<Rightarrow>
    out_file1
      (\<lambda>fprintf1.
        List_iter (fprintf1 (STR ''%s
''))
                  (s_of_thy_list
                     file_out
                     (STR ''../src/OCL_main'')
                     (map (\<lambda>f. f exemple) thy_object)))
      (sprintf2 (STR ''%s/%s.thy'') dir file_out)
   | _ \<Rightarrow> eprintf0 (STR ''No directory in argument''))"

export_code main
  in OCaml module_name M file "Employee_DesignModel_UMLPart_generator.ml"

end
