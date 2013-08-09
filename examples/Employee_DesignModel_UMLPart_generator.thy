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
  Mk_univ ''OclAny'' [] (Some (
  Mk_univ ''Person'' [ (''salary'', OclTy_base ''int''), (''boss'', object) ] (Some (
  Mk_univ ''Void'' [] (Some (
  Mk_univ ''Invalid'' [] None
  ))
  ))
  ))"

definition "Employee_DesignModel_UMLPart' =
  Mk_univ ''OclAny'' [] (Some (
  Mk_univ ''Person'' [ (''salary'', OclTy_base ''int''), (''boss'', object) ] None
  ))"

subsection{* Raw *}

definition "exemple = (case True of True \<Rightarrow> Employee_DesignModel_UMLPart
                                  | False \<Rightarrow> Employee_DesignModel_UMLPart')"
definition "datatype_class = snd (print_datatype_class exemple)"
definition "datatype_universe = [ Datatype unicode_AA (print_datatype_universe exemple) ]"
definition "type_synonym_class = Type_synonym ty_boolean (Ty_apply (Ty_base ty_boolean) [Ty_base unicode_AA]) # print_type_synonym_class exemple"
definition "instantiation_class = print_instantiation_class exemple"
definition "instantiation_universe = [ let oid_of = ''oid_of'' in Instantiation unicode_AA oid_of
  (let var_x = ''x'' in
       Expr_rewrite
        (Expr_basic [oid_of, var_x])
        ''=''
        (Expr_case (Expr_basic [var_x]) (print_instantiation_universe oid_of exemple))) ]"
definition "def_strictrefeq = print_def_strictrefeq exemple"

definition "astype_consts = print_astype_consts exemple"
definition "astype_from_universe = print_astype_from_universe exemple"
definition "astype_class = print_astype_class exemple"
definition "astype_lemmas_id = [ Lemmas_simp (print_astype_lemmas_id exemple) ]"
definition "astype_lemma_cp = print_astype_lemma_cp exemple"
definition "astype_lemmas_cp = print_astype_lemmas_cp exemple"
definition "astype_lemma_strict = print_astype_lemma_strict exemple"
definition "astype_lemmas_strict = print_astype_lemmas_strict exemple"

definition "istypeof_consts = print_istypeof_consts exemple"
definition "istypeof_from_universe = print_istypeof_from_universe exemple"
definition "istypeof_class = print_istypeof_class exemple"
definition "istypeof_lemmas_id = [ Lemmas_simp (print_istypeof_lemmas_id exemple) ]"
definition "istypeof_lemma_cp = print_istypeof_lemma_cp exemple"
definition "istypeof_lemmas_cp = print_istypeof_lemmas_cp exemple"
definition "istypeof_lemma_strict = print_istypeof_lemma_strict exemple"
definition "istypeof_lemmas_strict = print_istypeof_lemmas_strict exemple"

definition "iskindof_consts = print_iskindof_consts exemple"
definition "iskindof_from_universe = print_iskindof_from_universe exemple"
definition "iskindof_class = print_iskindof_class exemple"
definition "iskindof_lemmas_id = [ Lemmas_simp (print_iskindof_lemmas_id exemple) ]"
definition "iskindof_lemma_cp = print_iskindof_lemma_cp exemple"
definition "iskindof_lemmas_cp = print_iskindof_lemmas_cp exemple"
definition "iskindof_lemma_strict = print_iskindof_lemma_strict exemple"
definition "iskindof_lemmas_strict = print_iskindof_lemmas_strict exemple"

definition "eval_extract = print_eval_extract"
definition "deref_oid = print_deref_oid exemple"
definition "select = print_select exemple"
definition "dot = print_dot exemple"

export_code datatype_class
            datatype_universe
            type_synonym_class
            instantiation_class
            instantiation_universe
            def_strictrefeq

            astype_consts
            astype_from_universe
            astype_class
            astype_lemmas_id
            astype_lemma_cp
            astype_lemmas_cp
            astype_lemma_strict
            astype_lemmas_strict

            istypeof_consts
            istypeof_from_universe
            istypeof_class
            istypeof_lemmas_id
            istypeof_lemma_cp
            istypeof_lemmas_cp
            istypeof_lemma_strict
            istypeof_lemmas_strict

            iskindof_consts
            iskindof_from_universe
            iskindof_class
            iskindof_lemmas_id
            iskindof_lemma_cp
            iskindof_lemmas_cp
            iskindof_lemma_strict
            iskindof_lemmas_strict

            eval_extract
            deref_oid
            select
            dot

  in OCaml module_name M file "Employee_DesignModel_UMLPart_generator.ml" (no_signatures)

end
