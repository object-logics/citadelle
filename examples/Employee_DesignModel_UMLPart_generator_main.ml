(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Employee_DesignModel_UMLPart_generator_main.ml --- OCL Contracts and an Example.
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

open Employee_DesignModel_UMLPart_generator.M
open OCL_class_diagram_generator
open Printf

let fic = "Employee_DesignModel_UMLPart_generated"
let () =
  match List.filter Sys.is_directory (Array.to_list Sys.argv) with
  | dir :: _ ->
    let file = sprintf "%s/%s.thy" dir fic in
    let () = if Sys.file_exists file then eprintf "File exists %s\n" file else () in
    let oc = open_out file in
    begin
      List.iter
        (fprintf oc "%s\n")
        (List.flatten
       [ [ sprintf "theory %s imports \"../src/OCL_main\" begin" fic ]

       ; List.flatten (List.mapi
            (fun i s -> [ "" ; sprintf "(* %d *********************************** *)" (succ i) ; s ])
            [ concat s_of_datatype datatype_class
            ; concat s_of_datatype datatype_universe
            ; concat s_of_tsynonym type_synonym_class
            ; concat s_of_instantiation instantiation_class
            ; concat s_of_instantiation instantiation_universe
            ; concat s_of_defs_overloaded def_strictrefeq

            ; concat s_of_consts_class astype_consts
            ; concat s_of_definition_hol astype_from_universe
            ; concat s_of_defs_overloaded astype_class
            ; concat s_of_lemmas_simp astype_lemmas_id
            ; concat s_of_lemma_by astype_lemma_cp
            ; concat s_of_lemmas_simp astype_lemmas_cp
            ; concat s_of_lemma_by astype_lemma_strict
            ; concat s_of_lemmas_simp astype_lemmas_strict

            ; concat s_of_consts_class istypeof_consts
            (*; concat s_of_definition_hol istypeof_from_universe*)
            ; concat s_of_defs_overloaded istypeof_class
            ; concat s_of_lemmas_simp istypeof_lemmas_id
            ; concat s_of_lemma_by istypeof_lemma_cp
            ; concat s_of_lemmas_simp istypeof_lemmas_cp
            ; concat s_of_lemma_by istypeof_lemma_strict
            ; concat s_of_lemmas_simp istypeof_lemmas_strict

            ; concat s_of_consts_class iskindof_consts
            (*; concat s_of_definition_hol iskindof_from_universe*)
            ; concat s_of_defs_overloaded iskindof_class
            ; concat s_of_lemmas_simp iskindof_lemmas_id
            (*; concat s_of_lemma_by iskindof_lemma_cp
            ; concat s_of_lemmas_simp iskindof_lemmas_cp
            ; concat s_of_lemma_by iskindof_lemma_strict
            ; concat s_of_lemmas_simp iskindof_lemmas_strict
            *)

            ; concat s_of_definition_hol eval_extract
            ; concat s_of_definition_hol deref_oid
            ; concat s_of_definition_hol select
            ; concat s_of_definition_hol dot
            ])

       ; [ "" ; "end" ]
       ]);
      close_out oc;
    end
  | _ -> eprintf "No directory in argument"
