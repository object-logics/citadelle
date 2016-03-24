(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Class_model.thy --- Generation of class model represented as tree
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2016 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2016 IRT SystemX, France
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

theory  Class_model
imports "../../src/compiler/core/Core_init"
begin

definition "print_class =
 (\<lambda> (C_out_OclAny, s) \<Rightarrow> S.flatten [\<open>Class \<close>, s, \<open> End\<close>]
  | (C_out_simple s1, s2) \<Rightarrow> S.flatten [\<open>Class \<close>, s2, \<open> < \<close>, s1, \<open> End\<close>])"

definition' \<open>print_abr sprintf_int write_file =
  (let sprintf_int = sprintf_int o natural_of_nat
     ; S_flatten_n = S.flatten o L.map (\<lambda>s. S.flatten [s, \<lless>[Char Nibble0 NibbleA]\<ggreater>]) in
  L.flatten o L.flatten o L.map (\<lambda> (nb_child, deep).
    let body = L.map print_class (fst (mk_tree nb_child deep 0))
      ; tree_name = S.flatten [\<open>Tree_\<close>, sprintf_int nb_child, \<open>_\<close>, sprintf_int deep] in

    L.map
      (\<lambda> ((gen_mode, gen_comp), gen_import, gen_init, gen_flush).
        L.map
          (\<lambda>(comp, comp2).
            let filename = S.flatten [tree_name, \<open>_\<close>, gen_mode, if String.to_list comp = [] then \<open>\<close> else S.flatten [\<open>_\<close>, comp]] in
            write_file
              (S.flatten [filename, \<open>.thy\<close>])
              (L.flatten
                [ [ S.flatten [\<open>theory \<close>, filename, \<open> imports \<close>, gen_import, \<open> \<close>, 
                               \<open>"../../src/compiler/Generator_dynamic"\<close>,
                               \<open> begin\<close>]
                  , gen_init comp comp2]
                , body
                , [ \<open>\<close>
                  , S.flatten [\<open>(* \<close>, String.of_nat (length body), \<open> *)\<close> ]
                  , \<open>\<close>
                  , gen_flush
                  , \<open>\<close>
                  , \<open>end\<close> ] ])) gen_comp)
      [ ( (\<open>deep\<close>, [ (\<open>Haskell\<close>, \<open>\<close>)
                   , (\<open>OCaml\<close>, \<open>module_name M\<close>)
                   , (\<open>Scala\<close>, \<open>module_name M\<close>)
                   , (\<open>SML\<close>, \<open>module_name M\<close>)])
        , \<open>\<close>
        , \<lambda> comp comp2.
            S_flatten_n [            \<open>generation_syntax [ deep\<close>
                        ,            \<open>                      (generation_semantics [ analysis (*, oid_start 10*) ])\<close>
                        ,            \<open>                      skip_export\<close>
                        , S.flatten [\<open>                      (THEORY \<close>, tree_name, \<open>_generated\<close>, \<open>_\<close>, comp, \<open>)\<close>]
                        , S.flatten [\<open>                      (IMPORTS ["../../../src/UML_Main", "../../../src/compiler/Static"]\<close>]
                        , S.flatten [\<open>                               "../../../src/compiler/Generator_dynamic")\<close>]
                        ,            \<open>                      SECTION\<close>
                        , S.flatten [\<open>                      [ in \<close>, comp, \<open> \<close>, comp2, \<open> ]\<close>]
                        , S.flatten [\<open>                      (output_directory "./doc") ]\<close>] ]
        , S_flatten_n [ \<open>generation_syntax deep flush_all\<close> ])
      , ( (\<open>shallow\<close>, [(\<open>\<close>, \<open>\<close>)])
        , S.flatten [ \<open>"../../src/UML_Main"\<close>, \<open> \<close>
                    , \<open>"../../src/compiler/Static"\<close>  ]
        , \<lambda>_ _. S_flatten_n [ \<open>generation_syntax [ shallow (generation_semantics [ analysis ]) ]\<close> ]
        , \<open>End!\<close>) ]))\<close>

definition "main sprintf_int write_file = print_abr (\<lambda>n. \<lless>sprintf_int n\<ggreater>) (\<lambda>f l. write_file (String.to_list f) (L.map String.to_list l))
  [ (1, 0)
  , (1, 1)
  , (1, 2)
  , (1, 3)
  , (1, 4)
  , (1, 5)
  , (1, 6)
  , (1, 12)
  , (1, 14)
  , (1, 20)
  , (1, 30)
  , (1, 39)
  , (1, 42)
  , (1, 56)

  (* *)

  , (2, 1)
  , (2, 2)
  , (2, 3)
  , (2, 4)

  , (3, 1)
  , (3, 2)
  , (3, 3)

  , (4, 1)
  , (4, 2)

  , (5, 1)
  , (5, 2)

  , (6, 1)
  , (6, 2)

  , (7, 1)
  , (7, 2)

  (* *)

  , (12, 1)
  , (14, 1)
  , (20, 1)
  , (30, 1)
  , (39, 1)
  , (42, 1)
  , (56, 1) ]"
(*
export_code open main
  in OCaml module_name M file "class_model_isabelle.ml"
*)
end
