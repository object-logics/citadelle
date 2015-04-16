(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Class_model.thy --- Generation of class model represented as tree
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

theory  Class_model
imports "../../src/compiler/OCL_compiler_init_rbt"
begin

datatype 'a tree = T 'a "'a tree list"

fun make_tree
and make_tree' where
   "make_tree l_pos nb_child deep =
      T l_pos (case deep of 0 \<Rightarrow> []
               | Suc deep \<Rightarrow> make_tree' l_pos nb_child nb_child deep [])"

 | "make_tree' l_pos nb_child i deep l =
     (case i of 0 \<Rightarrow> l
      | Suc i \<Rightarrow> make_tree' l_pos nb_child i deep (make_tree (i # l_pos) nb_child deep # l))"

definition "mk_tree = make_tree []"

definition "ident_fresh = (\<lambda>l (map, ident).
  case RBT.lookup map l of None \<Rightarrow> (ident, (RBT.insert l ident map, Suc ident))
  | Some i \<Rightarrow> (i, (map, ident)))"

definition "ident_empty = (RBT.empty, 0)"

fun fold_tree where
   "fold_tree f t accu =
     (case t of T _ [] \<Rightarrow> accu
      | T x l \<Rightarrow>
          List.fold
            (fold_tree f)
            l
            (List.fold
              (\<lambda>t accu. case t of T x' _ \<Rightarrow> f x x' accu)
              l
              accu))"

datatype 'a class_output = OclAny | Class 'a

definition "nat_raw_of_str26 = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble6 Nibble1) + i))"
definition "nat_raw_of_str10 = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"

fun str_of_nat26_aux where (* FIXME merge polymorphically *)
   "str_of_nat26_aux l (n :: Nat.nat) =
     (if n < 26 then
        n # l
      else
        str_of_nat26_aux (n mod 26 # l) (n div 26))"
fun str_of_nat10_aux where (* FIXME merge polymorphically *)
   "str_of_nat10_aux l (n :: Nat.nat) =
     (if n < 10 then
        n # l
      else
        str_of_nat10_aux (n mod 10 # l) (n div 10))"

definition "str26_of_nat n = \<lless>nat_raw_of_str26 (str_of_nat26_aux [] n)\<ggreater>"
definition "str10_of_nat n = \<lless>nat_raw_of_str10 (str_of_nat10_aux [] n)\<ggreater>"

definition "string26_of_nat n =
 (let n = n - 1
    ; s1 = str26_of_nat n in
  case String_to_list
         (if n < 26 then
            let s2 = str26_of_nat (26 - n - 1) in
            flatten [s1, s1, s2, s2]
          else
            flatten [s1, s1])
  of
  x # xs \<Rightarrow> flatten [uppercase_of_str \<lless>[x]\<ggreater>, \<lless>xs\<ggreater>])"

definition "print_class =
 (\<lambda> (OclAny, s) \<Rightarrow> flatten [\<langle>''Class ''\<rangle>, s, \<langle>'' End''\<rangle>]
  | (Class s1, s2) \<Rightarrow> flatten [\<langle>''Class ''\<rangle>, s2, \<langle>'' < ''\<rangle>, s1, \<langle>'' End''\<rangle>]  )"

definition "print_abr sprintf_int write_file =
  (let sprintf_int = sprintf_int o natural_of_nat
     ; flatten_n = flatten o List_map (\<lambda>s. flatten [s, \<lless>[Char Nibble0 NibbleA]\<ggreater>]) in
  List_flatten o List_flatten o List_map (\<lambda> (nb_child, deep).
    let body = (rev o fst)
      (fold_tree
        (\<lambda> l1 l2 (l, map).
          let (n1, map) = ident_fresh l1 map
          ; (n2, map) = ident_fresh l2 map in
          (print_class (case n1 of 0 \<Rightarrow> OclAny | n \<Rightarrow> Class (string26_of_nat n), string26_of_nat n2) # l, map))
        (mk_tree nb_child deep)
        ([], ident_empty))
      ; tree_name = flatten [\<langle>''Tree_''\<rangle>, sprintf_int nb_child, \<langle>''_''\<rangle>, sprintf_int deep]
      ; g = \<lless>[Char Nibble2 Nibble2]\<ggreater> in

    List_map
      (\<lambda> ((gen_mode, gen_comp), gen_import, gen_init, gen_flush).
        List_map
          (\<lambda>(comp, comp2).
            let filename = flatten [tree_name, \<langle>''_''\<rangle>, gen_mode, if String_to_list comp = [] then \<langle>''''\<rangle> else flatten [\<langle>''_''\<rangle>, comp]] in
            write_file
              (flatten [filename, \<langle>''.thy''\<rangle>])
              (List_flatten
                [ [ flatten [\<langle>''theory ''\<rangle>, filename, \<langle>'' imports ''\<rangle>, gen_import, \<langle>'' ''\<rangle>, 
                             g,\<langle>''../../src/compiler/OCL_compiler_generator_dynamic''\<rangle>,g,
                             \<langle>'' begin''\<rangle>]
                  , gen_init comp comp2]
                , body
                , [ \<langle>''''\<rangle>
                  , flatten [\<langle>''(* ''\<rangle>, str10_of_nat (length body), \<langle>'' *)''\<rangle> ]
                  , \<langle>''''\<rangle>
                  , gen_flush
                  , \<langle>''''\<rangle>
                  , \<langle>''end''\<rangle> ] ])) gen_comp)
      [ ( (\<langle>''deep''\<rangle>, [ (\<langle>''Haskell''\<rangle>, \<langle>''''\<rangle>)
                     , (\<langle>''OCaml''\<rangle>, \<langle>''module_name M''\<rangle>)
                     , (\<langle>''Scala''\<rangle>, \<langle>''module_name M''\<rangle>)
                     , (\<langle>''SML''\<rangle>, \<langle>''module_name M''\<rangle>)])
        , \<langle>''''\<rangle>
        , \<lambda> comp comp2.
            flatten_n [          \<langle>''generation_syntax [ deep''\<rangle>
                      ,          \<langle>''                      (generation_semantics [ analysis (*, oid_start 10*) ])''\<rangle>
                      ,          \<langle>''                      skip_export''\<rangle>
                      , flatten [\<langle>''                      (THEORY ''\<rangle>, tree_name, \<langle>''_generated''\<rangle>, \<langle>''_''\<rangle>, comp, \<langle>'')''\<rangle>]
                      , flatten [\<langle>''                      (IMPORTS [''\<rangle>,g,\<langle>''../../../src/UML_Main''\<rangle>,g,\<langle>'', ''\<rangle>,g,\<langle>''../../../src/compiler/OCL_compiler_static''\<rangle>,g,\<langle>'']''\<rangle>]
                      , flatten [\<langle>''                               ''\<rangle>,g,\<langle>''../../../src/compiler/OCL_compiler_generator_dynamic''\<rangle>,g,\<langle>'')''\<rangle>]
                      ,          \<langle>''                      SECTION''\<rangle>
                      , flatten [\<langle>''                      [ in ''\<rangle>, comp, \<langle>'' ''\<rangle>, comp2, \<langle>'' ]''\<rangle>]
                      , flatten [\<langle>''                      (output_directory ''\<rangle>,g,\<langle>''./doc''\<rangle>,g,\<langle>'') ]''\<rangle>] ]
        , flatten_n [ \<langle>''generation_syntax deep flush_all''\<rangle> ])
      , ( (\<langle>''shallow''\<rangle>, [(\<langle>''''\<rangle>, \<langle>''''\<rangle>)])
        , flatten [ g,\<langle>''../../src/UML_Main''\<rangle>,g, \<langle>'' ''\<rangle>
                  , g,\<langle>''../../src/compiler/OCL_compiler_static''\<rangle>,g  ]
        , \<lambda>_ _. flatten_n [ \<langle>''generation_syntax [ shallow (generation_semantics [ analysis ]) ]''\<rangle> ]
        , \<langle>''END''\<rangle>) ]))"

definition "main sprintf_int write_file = print_abr (\<lambda>n. \<lless>sprintf_int n\<ggreater>) (\<lambda>f l. write_file (String_to_list f) (List_map String_to_list l))
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
