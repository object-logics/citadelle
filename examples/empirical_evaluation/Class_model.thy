(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Class_model.thy --- Generation of class model represented as tree
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2014      Universite Paris-Sud, France
 *               2014      IRT SystemX, France
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
        "~~/src/HOL/Library/Code_Char"
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
  case lookup map l of None \<Rightarrow> (ident, (insert l ident map, Suc ident))
  | Some i \<Rightarrow> (i, (map, ident)))"

definition "ident_empty = (empty, 0)"

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

definition "str26_of_nat n = nat_raw_of_str26 (str_of_nat26_aux [] n)"
definition "str10_of_nat n = nat_raw_of_str10 (str_of_nat10_aux [] n)"

definition "string26_of_nat n =
 (let n = n - 1
    ; s1 = str26_of_nat n in
  case
  if n < 26 then
    let s2 = str26_of_nat (26 - n - 1) in
    flatten [s1, s1, s2, s2]
  else
    flatten [s1, s1]
  of
  x # xs \<Rightarrow> flatten [uppercase_of_str [x], xs])"

definition "print_class =
 (\<lambda> (OclAny, s) \<Rightarrow> flatten [''Class '', s, '' End'']
  | (Class s1, s2) \<Rightarrow> flatten [''Class '', s2, '' < '', s1, '' End'']  )"

definition "print_abr sprintf_int write_file =
  (let sprintf_int = sprintf_int o natural_of_nat
     ; flatten_n = flatten o List_map (\<lambda>s. flatten [s, [Char Nibble0 NibbleA]]) in
  flatten o flatten o List_map (\<lambda> (nb_child, deep).
    let body = (rev o fst)
      (fold_tree
        (\<lambda> l1 l2 (l, map).
          let (n1, map) = ident_fresh l1 map
          ; (n2, map) = ident_fresh l2 map in
          (print_class (case n1 of 0 \<Rightarrow> OclAny | n \<Rightarrow> Class (string26_of_nat n), string26_of_nat n2) # l, map))
        (mk_tree nb_child deep)
        ([], ident_empty))
      ; tree_name = flatten [''Tree_'', sprintf_int nb_child, ''_'', sprintf_int deep]
      ; g = [Char Nibble2 Nibble2] in

    List_map
      (\<lambda> ((gen_mode, gen_comp), gen_import, gen_init, gen_flush).
        List_map
          (\<lambda>(comp, comp2).
            let filename = flatten [tree_name, ''_'', gen_mode, if comp = [] then [] else flatten [''_'', comp]] in
            write_file
              (flatten [filename, ''.thy''])
              (flatten
                [ [ flatten [''theory '', filename, '' imports '', gen_import,'' begin'']
                  , gen_init comp comp2]
                , body
                , [ ''''
                  , flatten [''(* '', str10_of_nat (length body), '' *)'' ]
                  , ''''
                  , gen_flush
                  , ''''
                  , ''end'' ] ])) gen_comp)
      [ ( (''deep'', [ (''Haskell'', '''')
                     , (''OCaml'', ''module_name M (no_signatures)'')
                     , (''Scala'', ''module_name M'')
                     , (''SML'', ''module_name M (no_signatures)'')])
        , flatten [ g,''../../src/compiler/OCL_compiler_generator_dynamic'',g ]
        , \<lambda> comp comp2.
            flatten_n [          ''generation_syntax [ deep''
                      ,          ''                      (generation_semantics [ analysis (*, oid_start 10*) ])''
                      ,          ''                      skip_export''
                      , flatten [''                      (THEORY '', tree_name, ''_generated'', ''_'', comp, '')'']
                      , flatten [''                      (IMPORTS ['',g,''../../../src/OCL_main'',g,'', '',g,''../../../src/compiler/OCL_compiler_static'',g,'']'']
                      , flatten [''                               '',g,''../../../src/compiler/OCL_compiler_generator_dynamic'',g,'')'']
                      ,          ''                      SECTION''
                      , flatten [''                      [ in '', comp, '' '', comp2, '' ]'']
                      , flatten [''                      (output_directory '',g,''./doc'',g,'') ]''] ]
        , flatten_n [ ''generation_syntax deep flush_all'' ])
      , ( (''shallow'', [('''', '''')])
        , flatten [ g,''../../src/OCL_main'',g, '' ''
                  , g,''../../src/compiler/OCL_compiler_static'',g  ]
        , \<lambda>_ _. flatten_n [ ''generation_syntax [ shallow (generation_semantics [ analysis ]) ]'' ]
        , ''Class.end'') ]))"

definition "main sprintf_int write_file = print_abr sprintf_int write_file
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
export_code main
  in OCaml module_name M file "class_model_isabelle.ml"
  (no_signatures)
*)
end
