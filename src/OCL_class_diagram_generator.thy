(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator.thy ---
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

theory OCL_class_diagram_generator
imports Main
  keywords "attr_base" "attr_object" "child"
       and "Class" :: thy_decl
       and "Class.end_deep" :: thy_decl
       and "Class.end_shallow" :: thy_decl
begin

definition "bug_ocaml_extraction = id"
  (* In this theory, this identifier can be removed everywhere it is used.
     However without this, there is a syntax error when the code is extracted to OCaml. *)

section{* ... *}

type_synonym str = "char list"

datatype oclTy = OclTy_base str | OclTy_object str
definition "str_of_ty = (\<lambda> OclTy_base x \<Rightarrow> x | OclTy_object x \<Rightarrow> x)"

datatype univ =
 Mk_univ
   str (* name of the class *)
   "(str (* name *) \<times> oclTy) list" (* attribute *)
   "univ option" (* link to subclasses *)

fun get_class_hierarchy_aux where
   "get_class_hierarchy_aux l_res (Mk_univ name l_attr dataty) =
   (let l_res = (name, l_attr) # l_res in
    case dataty of None \<Rightarrow> rev l_res
                 | Some dataty \<Rightarrow> get_class_hierarchy_aux l_res dataty)"
definition "get_class_hierarchy = get_class_hierarchy_aux []"

datatype position = EQ | LT | GT

fun less_than_hierarchy where
  "less_than_hierarchy l item1 item2 =
    (case l of x # xs \<Rightarrow>
               if x = item1 then GT
               else if x = item2 then LT
               else less_than_hierarchy xs item1 item2)"
definition "compare_hierarchy = (\<lambda>l x1 x2. if x1 = x2 then EQ else less_than_hierarchy l x1 x2)"


fun flip where "flip (a,b) = (b,a)"
definition "List_map f l = rev (foldl (\<lambda>l x. f x # l) [] l)"
definition "flatten l = foldl (\<lambda>acc l. foldl (\<lambda>acc x. x # acc) acc (rev l)) [] (rev l)"
definition List_append (infixr "@@" 65) where "List_append a b = flatten [a, b]"
definition "List_filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"

section{* HOL deep embedding *}
subsection{* type definition *}

datatype simplety = Opt str | Raw str

datatype dataty = Datatype str (* name *)
                           "(str (* name *) \<times> simplety list (* arguments *)) list" (* constructors *)

datatype raw_ty =
   Ty_apply raw_ty "raw_ty list"
 | Ty_base str

datatype ty_synonym = Type_synonym str (* name *)
                                   raw_ty (* content *)

datatype expr = Expr_case expr (* value *)
                          "(expr (* pattern *) \<times> expr (* to return *)) list"
              | Expr_rewrite expr (* left *) str (* symb rewriting *) expr (* right *)
              | Expr_basic "str list"
              | Expr_binop expr str expr
              | Expr_annot expr str (* type *)
              | Expr_lambda str (* lambda var *) expr
              | Expr_lambdas "str list" expr
              | Expr_function "(expr (* pattern *) \<times> expr (* to return *)) list"
              | Expr_apply str "expr list"
              | Expr_applys expr "expr list"
              | Expr_some expr (* with annotation \<lfloor> ... \<rfloor> *)
              | Expr_preunary expr expr (* no parenthesis and separated with one space *)
              | Expr_postunary expr expr (* no parenthesis and separated with one space *)
              | Expr_warning_parenthesis expr (* optional parenthesis that can be removed but a warning will be raised *)
              | Expr_parenthesis expr (* mandatory parenthesis *)

datatype instantiation_class = Instantiation str (* name *)
                                             str (* name in definition *)
                                             expr

datatype defs_overloaded = Defs_overloaded str (* name *) expr (* content *)

datatype consts_class = Consts str (* name *) str (* type output *) str (* ocl symbol1 *) str (* ocl symbol2 *)

datatype definition_hol = Definition expr
                        | Definition_abbrev str (* name *) "expr (* syntax extension *) \<times> nat (* priority *)" expr

datatype lemmas_simp = Lemmas_simp "str list"

datatype tactic = Tac_rule str
                | Tac_rule_where str "(str \<times> expr) list (* where clause *)"
                | Tac_plus tactic
                | Tac_simp | Tac_simp_add "str list" | Tac_simp_only "str list"
                | Tac_simp_all | Tac_simp_all_add str

datatype lemma_by = Lemma_by str (* name *) "expr list" (* specification to prove *)
                      "tactic list list" (* tactics : apply (... ',' ...) '\n' apply ... *)
                      "tactic list option" (* Some tactic : ending the proof with 'by ...' *)

datatype thy = Thy_dataty dataty
             | Thy_ty_synonym ty_synonym
             | Thy_instantiation_class instantiation_class
             | Thy_defs_overloaded defs_overloaded
             | Thy_consts_class consts_class
             | Thy_definition_hol definition_hol
             | Thy_lemmas_simp lemmas_simp
             | Thy_lemma_by lemma_by

subsection{* ... *}

definition "wildcard = ''_''"

definition "escape_unicode c = flatten [[Char Nibble5 NibbleC], ''<'', c, ''>'']"

definition "isub_of_str str = flatten (List_map (\<lambda>c. escape_unicode ''^sub'' @@ [c]) str)"
definition "isup_of_str str = flatten (List_map (\<lambda>c. escape_unicode [char_of_nat (nat_of_char c - 32)]) str)"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, ''_'', isub_of_str x])"
definition "mk_dot = (\<lambda>s1 s2. flatten [''.'', s1, s2])"
definition "mk_dot_par = (\<lambda>dot s. flatten [dot, ''('', s, '')''])"

subsection{* ... *}

definition "object = OclTy_object ''oid''"

definition "ty_boolean = ''Boolean''"

definition "unicode_equiv = escape_unicode ''equiv''"
definition "unicode_doteq = escape_unicode ''doteq''"
definition "unicode_tau = escape_unicode ''tau''"
definition "unicode_bottom = escape_unicode ''bottom''"
definition "unicode_AA = escape_unicode ''AA''"

definition "datatype_ext_name = ''type''"
definition "datatype_name = datatype_ext_name @@ str_of_ty object"
definition "datatype_ext_constr_name = ''mk''"
definition "datatype_constr_name = datatype_ext_constr_name @@ str_of_ty object"
definition "datatype_in = ''in''"

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "dot_oclastype = ''.oclAsType''"
definition "dot_oclistypeof = ''.oclIsTypeOf''"
definition "dot_ocliskindof = ''.oclIsKindOf''"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_in_pre_state = ''in_pre_state''"
definition "var_in_post_state = ''in_post_state''"
definition "var_reconst_basetype = ''reconst_basetype''"
definition "var_eval_extract = ''eval_extract''"
definition "var_deref_oid = ''deref_oid''"
definition "var_select = ''select''"

section{* Model of OCL classes *}

fun map_class_gen_aux where
   "map_class_gen_aux l_inherited l_res l_cons f (Mk_univ name l_attr dataty) = (
      let l_cons = tl l_cons
        ; l_res = f (\<lambda>s. s @@ isub_of_str name) name l_attr l_inherited l_cons (dataty = None) # l_res in
      case dataty
      of None \<Rightarrow> flatten l_res
       | Some dataty \<Rightarrow> map_class_gen_aux (l_attr # l_inherited) l_res l_cons f dataty)"
definition "map_class_gen f expr = map_class_gen_aux [] [] (List_map fst (get_class_hierarchy expr)) f expr"

definition "add_hierarchy f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (List_map fst (get_class_hierarchy x)))"
definition "add_hierarchy' f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (get_class_hierarchy x))"
definition "add_hierarchy'' f x = (\<lambda>isub_name name l_attr _ _ _. f isub_name name (get_class_hierarchy x) l_attr)"
definition "add_hierarchy''' f x = (\<lambda>isub_name name l_attr l_hierarchy _ last_dataty. f isub_name name (get_class_hierarchy x) l_attr l_hierarchy last_dataty)"
definition "add_hierarchy'''' f x = (\<lambda>isub_name name l_attr l_inherited l_cons _. f isub_name name (get_class_hierarchy x) l_attr l_inherited l_cons)"
definition "map_class f = map_class_gen (\<lambda>isub_name name l_attr l_inherited l_cons last_dataty. [f isub_name name l_attr l_inherited l_cons last_dataty])"
definition "map_class_gen_h f x = map_class_gen (add_hierarchy f x) x"
definition "map_class_gen_h' f x = map_class_gen (add_hierarchy' f x) x"
definition "map_class_gen_h'' f x = map_class_gen (add_hierarchy'' f x) x"
definition "map_class_gen_h''' f x = map_class_gen (add_hierarchy''' f x) x"
definition "map_class_gen_h'''' f x = map_class_gen (add_hierarchy'''' f x) x"
definition "map_class_h f x = map_class (add_hierarchy f x) x"
definition "map_class_h' f x = map_class (add_hierarchy' f x) x"
definition "map_class_h'' f x = map_class (add_hierarchy'' f x) x"
definition "map_class_arg_only f = map_class_gen (\<lambda> isub_name name l_attr _ _ _. case l_attr of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name l)"
definition "map_class_arg_only' f = map_class_gen (\<lambda> isub_name name l_attr l_inherited l_cons _. case flatten l_inherited of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name l_attr l l_cons)"
definition "get_hierarchy_fold f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  let (_, l) = foldl (\<lambda> (name1_last, l1) name1. (Some name1, List_map (\<lambda>name2. List_map (\<lambda>name3.
  f (name1_last, name1) name2 name3) l3) l2 # l1)) (None, []) l1 in rev l))"
definition "get_hierarchy_map f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  List_map (\<lambda>name1. List_map (\<lambda>name2. List_map (\<lambda>name3. f name1 name2 name3) l3) l2) l1))"

subsection{* ... *}

definition "activate_simp_optimization = True"

definition "print_datatype_class = List_map Thy_dataty o map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    [ Datatype
        (isub_name datatype_ext_name)
        (  (rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ isub_of_str x)])) l_cons)
        @@ [(isub_name datatype_ext_constr_name, Raw (str_of_ty object) # flatten ( List_map (List_map (\<lambda>(_, x). Opt (str_of_ty x))) l_inherited))])
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, [ Raw (isub_name datatype_ext_name) ] @@ List_map (\<lambda>(_, x). Opt (str_of_ty x)) l_attr ) ] ])"

definition "print_datatype_universe expr = List_map Thy_dataty
  [ Datatype unicode_AA
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_type_synonym_class expr = List_map Thy_ty_synonym
  (Type_synonym ty_boolean (Ty_apply (Ty_base ty_boolean) [Ty_base unicode_AA]) #
   (map_class (\<lambda>isub_name name _ _ _ _.
     Type_synonym name (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
     let option = (\<lambda>x. Ty_apply (Ty_base ''option'') [x]) in
     option (option (Ty_base (isub_name datatype_name))) ])) expr))"

definition "print_instantiation_class = List_map Thy_instantiation_class o map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let oid_of = ''oid_of'' in
    [Instantiation
      (isub_name datatype_name)
      oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        ''=''
        (Expr_function
                   [ let var_oid = ''t'' in
                     ( Expr_basic (isub_name datatype_constr_name # var_oid # List_map (\<lambda>_. wildcard) l_attr)
                     , Expr_case
                         (Expr_basic [var_oid])
                         ( (Expr_apply (isub_name datatype_ext_constr_name) (Expr_basic [var_oid] # flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inherited)), Expr_basic [var_oid])
                         # List_map (\<lambda>x. ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x) [Expr_basic [var_oid]]
                                    , Expr_apply oid_of [Expr_basic [var_oid]])) l_cons))]))
    ])"

definition "print_instantiation_universe expr = List_map Thy_instantiation_class
  [ let oid_of = ''oid_of'' in
    Instantiation unicode_AA oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        ''=''
        (Expr_function (map_class (\<lambda>isub_name name _ _ _ _.
    let esc = (\<lambda>h. Expr_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of)) expr))) ]"


definition "print_def_strictrefeq = List_map Thy_defs_overloaded o
  map_class (\<lambda>isub_name name _ _ _ _.
    let mk_strict = (\<lambda>l. flatten (''StrictRefEq'' # isub_of_str ''Object'' # l))
      ; s_strict = mk_strict [''_'', isub_of_str name]
      ; var_x = ''x''
      ; var_y = ''y'' in
    Defs_overloaded s_strict (Expr_rewrite (Expr_binop (Expr_annot (Expr_basic [var_x]) name)
                                                       unicode_doteq
                                                       (Expr_basic [var_y]))
                                           unicode_equiv
                                           (Expr_basic [mk_strict [], var_x, var_y])) )"

subsection{* AsType *}

definition "print_astype_consts = List_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclastype) name dot_oclastype name)"

definition "print_astype_class = List_map Thy_defs_overloaded o
  map_class_gen_h'' (\<lambda>isub_name name l_hierarchy nl_attr.
    List_map
      (let l_hierarchy = List_map fst l_hierarchy in (\<lambda> (h_name, hl_attr).
        Defs_overloaded
          (flatten [isub_name const_oclastype, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_astype name]))
             unicode_equiv
             (case compare_hierarchy l_hierarchy h_name name
              of EQ \<Rightarrow>
                Expr_basic [var_x]
              | x \<Rightarrow>
                let var_tau = unicode_tau
                  ; val_invalid = Expr_apply ''invalid'' [Expr_basic [var_tau]] in
                Expr_lambda var_tau
                  (Expr_case
                    (Expr_apply var_x [Expr_basic [var_tau]])
                    ( (Expr_basic [unicode_bottom], val_invalid)
                    # (Expr_some (Expr_basic [unicode_bottom]), Expr_apply ''null'' [Expr_basic [var_tau]])
                    # (let pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ ''_''))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name)
                                        ( Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]
                                        # l_extra) )
                         ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; var_name = name in
                             Expr_basic [var_name])
                         ; some_some = (\<lambda>x. Expr_some (Expr_some x)) in
                       if x = LT then
                         [ (some_some (pattern_simple h_name), some_some (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [''None'']) nl_attr))) ]
                       else
                         [ (some_some (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)), some_some (pattern_simple name))
                         , (Expr_basic [wildcard], val_invalid) ]) ) ))) ))
      l_hierarchy)"

definition "print_astype_from_universe = List_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_astype]) ''=''
   (
   (Expr_function (List_map (\<lambda>h_name.
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
     , Expr_warning_parenthesis
       (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                   h_name)
                       (Expr_basic [dot_astype name])))) l_hierarchy)))))"

definition "print_astype_from_universe' = List_map Thy_definition_hol o
  map_class_h'' (\<lambda>isub_name name l_hierarchy nl_attr.
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_astype]) ''=''
   (let ((finish_with_some1, finish_with_some2), last_case_none) =
     let (f, r) = (if (fst o hd) l_hierarchy = name then (id, []) else (flip, [(Expr_basic [wildcard], Expr_basic [''None''])])) in
     (f (id, Expr_some), r) in
   finish_with_some2
   (Expr_function (flatten (List_map
   (let l_hierarchy = List_map fst l_hierarchy in (\<lambda>(h_name, hl_attr).
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
       ; pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ ''_''))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name)
                                        ( Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]
                                        # l_extra ))
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; var_name = name in
                             Expr_basic [var_name])
       ; case_branch = (\<lambda>pat res. (Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)) in
             case compare_hierarchy l_hierarchy h_name name
             of GT \<Rightarrow> case_branch (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)) (pattern_simple name)
              | EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [''None'']) nl_attr)))) l_hierarchy
   # [last_case_none]))))))"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id expr =
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp (List_map (\<lambda>((isub_name, _), name).
    flatten [isub_name const_oclastype, ''_'', name] ) name_set) ])"

definition "print_astype_lemma_cp expr = (List_map Thy_lemma_by o get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [''cp_'', const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      (bug_ocaml_extraction (let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_astype name1])))]))
      []
      (Some [Tac_rule ''cpI1'', if check_opt name1 name2 then Tac_simp
                                else Tac_simp_add [flatten [const_oclastype, isub_of_str name1, ''_'', name2]]])
  )) (\<lambda>x. (x, x, x))) expr"

definition "print_astype_lemmas_cp =
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [Lemmas_simp (get_hierarchy_map
  (\<lambda>name1 name2 name3.
      flatten [''cp_'', const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
  (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_lemma_strict expr = (List_map Thy_lemma_by o
 get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_astype name1])))
             ''=''
             (Expr_basic [name2])]
      []
      (Some (if check_opt name1 name3 then [Tac_simp]
             else [Tac_rule ''ext'', Tac_simp_add (flatten [const_oclastype, isub_of_str name1, ''_'', name3]
                                                   # ''bot_option_def''
                                                   # (if name2 = ''invalid'' then [''invalid_def'']
                                                      else [''null_fun_def'',''null_option_def'']))]))
  )) (\<lambda>x. (x, [''invalid'',''null''], x))) expr"

definition "print_astype_lemmas_strict =
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp (get_hierarchy_map (\<lambda>name1 name2 name3.
        flatten [const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2]
      ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

subsection{* IsTypeOf *}

definition "print_istypeof_consts = List_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclistypeof) ty_boolean dot_oclistypeof name)"

definition "print_istypeof_class = List_map Thy_defs_overloaded o
  map_class_gen_h''' (\<lambda>isub_name name l_hierarchy _ l_inh _.
    List_map
      (let l_hierarchy = List_map fst l_hierarchy in
      (\<lambda> (h_name, hl_attr).
        Defs_overloaded
          (flatten [isub_name const_oclistypeof, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_istypeof name]))
             unicode_equiv
             (let var_tau = unicode_tau
                ; ocl_tau = (\<lambda>v. Expr_apply v [Expr_basic [var_tau]]) in
                Expr_lambda var_tau
                  (Expr_case
                    (ocl_tau var_x)
                    ( (Expr_basic [unicode_bottom], ocl_tau ''invalid'')
                    # (Expr_some (Expr_basic [unicode_bottom]), ocl_tau ''true'')
                    # (let l_false = [(Expr_basic [wildcard], ocl_tau ''false'')]
                         ; pattern_complex_gen = (\<lambda>f1 f2.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
                             (Expr_some (Expr_some
                               (Expr_apply (isub_h datatype_constr_name)
                                           ( Expr_apply (f2 (\<lambda>s. isub_name (s @@ ''_'')) (isub_h datatype_ext_constr_name))
                                                        (Expr_basic [wildcard] # f1)
                                           # List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr))), ocl_tau ''true'')
                             # (if h_name = last l_hierarchy then [] else l_false)) in
                       case compare_hierarchy l_hierarchy h_name name
                       of EQ \<Rightarrow> pattern_complex_gen (flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inh)) (\<lambda>_. id)
                        | GT \<Rightarrow> pattern_complex_gen [] id
                        | _ \<Rightarrow> l_false) ) ))) ))
      l_hierarchy)"

definition "print_istypeof_from_universe = List_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_istypeof = flatten [const_oclistypeof, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_istypeof]) ''=''
   (
   (Expr_function (List_map (\<lambda>h_name.
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
     , Expr_warning_parenthesis
       (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                   h_name)
                       (Expr_basic [dot_istypeof name])))) l_hierarchy)))))"

definition "print_istypeof_from_universe' = List_map Thy_definition_hol o
  map_class_h' (\<lambda>isub_name name l_hierarchy.
    let const_istypeof = flatten [const_oclistypeof, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_istypeof]) ''=''
   (
   (Expr_function (flatten (flatten (List_map
   (let l_hierarchy = List_map fst l_hierarchy in
    (\<lambda>(h_name, l_attr).
     let pattern_complex_gen = (\<lambda>f1 f2.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
                            [ (Expr_apply (isub_h datatype_in)
                                [Expr_apply (isub_h datatype_constr_name)
                                            [ Expr_basic [wildcard]
                                            , Expr_apply (f2 (\<lambda>s. isub_name (s @@ ''_'')) (isub_h datatype_ext_constr_name))
                                                         f1]], Expr_basic [''true''])]) in
             case compare_hierarchy l_hierarchy h_name name
             of EQ \<Rightarrow> pattern_complex_gen (List_map (\<lambda>_. Expr_basic [wildcard]) l_attr) (\<lambda>_. id)
              | GT \<Rightarrow> pattern_complex_gen [Expr_basic [wildcard]] id
              | _ \<Rightarrow> [])) l_hierarchy)
   # [[(Expr_basic [wildcard], Expr_basic [''false''])]]))))))"

definition "print_istypeof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_id expr =
  (let name_set = print_istypeof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp (List_map (\<lambda>((isub_name, _), name).
    flatten [isub_name const_oclistypeof, ''_'', name] ) name_set) ])"

definition "print_istypeof_lemma_cp expr = (List_map Thy_lemma_by o
  (get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
      (bug_ocaml_extraction (let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_istypeof name1])))]))
      []
      (Some [Tac_rule ''cpI1'', if check_opt name1 name2 then Tac_simp
                                else Tac_simp_add [flatten [const_oclistypeof, isub_of_str name1, ''_'', name2]]])
  )) (\<lambda>x. (x, x, x))) ) expr"

definition "print_istypeof_lemmas_cp =
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
   (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_istypeof_lemma_strict expr = (List_map Thy_lemma_by o
  get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 (name2,name2') name3.
    Lemma_by
      (flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_istypeof name1])))
             ''=''
             (Expr_basic [name2'])]
      []
      (Some (let l = ''bot_option_def'' # (if name2 = ''invalid'' then [''invalid_def'']
                                           else [''null_fun_def'',''null_option_def'']) in
       [Tac_rule ''ext'', Tac_simp_add (if check_opt name1 name3 then l
                                        else flatten [const_oclistypeof, isub_of_str name1, ''_'', name3] # l)]))
  )) (\<lambda>x. (x, [(''invalid'',''invalid''),(''null'',''true'')], x))) expr"

definition "print_istypeof_lemmas_strict_set =
  (if activate_simp_optimization then
    get_hierarchy_map (\<lambda>name1 name2 name3. (name1, name3, name2)) (\<lambda>x. (x, [''invalid'',''null''], x))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_strict expr = List_map Thy_lemmas_simp
  (case print_istypeof_lemmas_strict_set expr
   of [] \<Rightarrow> []
    | l \<Rightarrow> [ Lemmas_simp (List_map
      (\<lambda>(name1, name3, name2).
        flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
      l) ])"

subsection{* IsKindOf *}

definition "print_iskindof_consts = List_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_ocliskindof) ty_boolean dot_ocliskindof name)"

definition "print_iskindof_class = List_map Thy_defs_overloaded o map_class_gen_h''''
  (\<lambda>isub_name name l_hierarchy l_attr l_inherited l_cons. List_map (\<lambda> (h_name, _).
    Defs_overloaded
          (flatten [isub_name const_ocliskindof, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_iskindof name]))
             unicode_equiv
             (let isof = (\<lambda>f name. Expr_warning_parenthesis (Expr_postunary (Expr_basic [var_x]) (Expr_basic [f name]))) in
              case l_cons of [] \<Rightarrow> isof dot_istypeof name
                           | name_past # _ \<Rightarrow> Expr_binop (isof dot_istypeof name) ''or'' (isof dot_iskindof name_past))))
     l_hierarchy)"

definition "print_iskindof_from_universe = List_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_iskindof = flatten [const_ocliskindof, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_iskindof]) ''=''
   (
   (Expr_function (List_map (\<lambda>h_name.
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
     , Expr_warning_parenthesis
       (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                   h_name)
                       (Expr_basic [dot_iskindof name])))) l_hierarchy)))))"

definition "print_iskindof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_iskindof_lemmas_id expr =
  (let name_set = print_iskindof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp (List_map (\<lambda>((isub_name, _), name).
    flatten [isub_name const_ocliskindof, ''_'', name] ) name_set) ])"

definition "print_iskindof_lemma_cp expr = (List_map Thy_lemma_by o
  get_hierarchy_fold (\<lambda> (name1_previous, name1) name2 name3.
    let lemma_name = flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2]
      ; lemma_spec = let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_iskindof name1])))]
      ; lem_simp1 = Tac_simp_only [flatten [const_ocliskindof, isub_of_str name1, ''_'', name2]]
      ; lem_simp2 = Tac_simp_only [flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]] in
    let (tac1, tac2) = case name1_previous
    of None \<Rightarrow> ([], Some [ lem_simp1 , lem_simp2 ])
     | Some name1_previous \<Rightarrow>
      ( [ [ lem_simp1 ]
        , [ Tac_rule_where ''cpI2'' [(''f'', Expr_preunary (Expr_basic [''op'']) (Expr_basic [''or'']))]
          , Tac_plus (Tac_rule ''allI'')
          , Tac_rule ''cp_OclOr'' ] ]
      , Some [ lem_simp2 , Tac_simp_only [flatten [''cp_'', const_ocliskindof, isub_of_str name1_previous, ''_'', name3, ''_'', name2]] ])
    in Lemma_by lemma_name lemma_spec tac1 tac2
  ) (\<lambda>x. let rev_x = rev x in (rev_x, rev_x, x))) expr"

definition "print_iskindof_lemmas_cp =
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2]
  ) (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_lemma_strict expr = (List_map Thy_lemma_by o
  get_hierarchy_fold (\<lambda> (name1_previous, name1) (name2,name2') name3.
    Lemma_by
      (flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_iskindof name1])))
             ''=''
             (Expr_basic [name2'])]
      []
      (Some
        ( Tac_simp_only
            (flatten
              [ [flatten [const_ocliskindof, isub_of_str name1, ''_'', name3]]
              , [flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]]
              , case name1_previous
                of None \<Rightarrow> []
                 | Some name1_previous \<Rightarrow> [flatten [const_ocliskindof, isub_of_str name1_previous, ''_'', name3, ''_'', name2]] ])
        # (if name1_previous = None then [] else [Tac_simp])) )
  ) (\<lambda>x. (rev x, [(''invalid'',''invalid''),(''null'',''true'')], x))) expr"

definition "print_iskindof_lemmas_strict =
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp (get_hierarchy_map (\<lambda>name1 name2 name3.
      flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2]
  ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

subsection{* ... *}

definition "print_eval_extract _ = List_map Thy_definition_hol
  (let lets = (\<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_basic [def]))) in
  [ bug_ocaml_extraction
    (let var_x = ''x''
      ; var_f = ''f''
      ; var_tau = unicode_tau
      ; some_some = (\<lambda>x. Expr_some (Expr_some x))
      ; var_obj = ''obj'' in
    Definition (Expr_rewrite
                  (Expr_basic [var_eval_extract, var_x, var_f])
                  ''=''
                  (Expr_lambda
                     var_tau
                     (Expr_case (Expr_basic [var_x, var_tau])
                     [ (some_some (Expr_basic [var_obj]), Expr_apply var_f [Expr_apply ''oid_of'' [Expr_basic [var_obj]], Expr_basic [var_tau]])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau])]))))
  , lets var_in_pre_state ''fst''
  , lets var_in_post_state ''snd''
  , lets var_reconst_basetype ''id'' ])"

definition "print_deref_oid = List_map Thy_definition_hol o
  map_class (\<lambda>isub_name _ _ _ _ _.
    let var_fs = ''fst_snd''
      ; var_f = ''f''
      ; var_oid = ''oid''
      ; var_obj = ''obj''
      ; var_tau = unicode_tau in
    Definition (Expr_rewrite
                  (Expr_basic [isub_name var_deref_oid, var_fs, var_f, var_oid])
                  ''=''
                  (Expr_lambda
                     var_tau
                     (Expr_case (Expr_apply ''heap'' [Expr_basic [var_fs, var_tau], Expr_basic [var_oid]])
                     [ (Expr_some (Expr_basic [isub_name datatype_in, var_obj]), Expr_basic [var_f, var_obj, var_tau])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau]) ]))))"

definition "print_select = List_map Thy_definition_hol o
  map_class_arg_only (\<lambda>isub_name name l_attr.
    let var_f = ''f''
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [isup_attr (isub_name var_select), var_f])
                       ''=''
                       (let var_attr = attr in
                        Expr_function
                          (List_map (\<lambda>(lhs,rhs). ( Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( wildc
                                                         # flatten [l_wildl, [lhs], l_wildr])
                                                     , rhs))
                            [ ( Expr_basic [unicode_bottom], Expr_basic [''null''] )
                            , ( Expr_some (Expr_basic [var_attr])
                              , Expr_apply var_f [ bug_ocaml_extraction
                                                   (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))
                                                 , Expr_basic [var_attr]]) ]))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_attr), [])
      l_attr) in
    rev l)"

definition "print_select_inherited = List_map Thy_definition_hol o
  map_class_arg_only' (\<lambda>isub_name name l_attr l_inherited l_cons.
    let var_f = ''f''
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [isup_attr (isub_name var_select), var_f])
                       ''=''
                       (let var_attr = attr in
                        Expr_function
                          (flatten (List_map (\<lambda>(lhs,rhs). ( Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (isub_name datatype_ext_constr_name)
                                                             (wildc # flatten [l_wildl, [lhs], l_wildr])
                                                         # List_map (\<lambda>_. wildc) l_attr)
                                                     , rhs))
                            [ ( Expr_basic [unicode_bottom], Expr_basic [''null''] )
                            , ( Expr_some (Expr_basic [var_attr])
                              , Expr_apply var_f [ bug_ocaml_extraction
                                                   (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))
                                                 , Expr_basic [var_attr]]) ]
                            # (List_map (\<lambda>x. let var_x = x in
                                             (Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x)
                                                             [Expr_basic [var_x]]
                                                         # List_map (\<lambda>_. wildc) l_attr), (Expr_apply (isup_attr (var_select @@ isub_of_str x))
                                                                                                     (List_map (\<lambda>x. Expr_basic [x]) [var_f, var_x]) ))) l_cons)
                            # [])))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_inherited), [])
      l_inherited) in
    rev l)"

definition "print_dot = List_map Thy_definition_hol o
  map_class_arg_only (\<lambda>isub_name name l_attr.
    flatten (flatten (
    List_map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      List_map (\<lambda>(attr_name, attr_ty).
            let isup_attr = (\<lambda>s. s @@ isup_of_str attr_name)
              ; dot_attr = (\<lambda>s. Expr_postunary (Expr_parenthesis (Expr_basic [s])) (Expr_basic [mk_dot attr_name attr_when])) in
            [ Definition_abbrev
                (flatten [isup_attr (isub_name ''dot''), dot_at_when])
                (dot_attr wildcard, 50)
                (let var_x = ''x'' in
                 Expr_rewrite
                   (dot_attr var_x)
                   ''=''
                   (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = (\<lambda>l. Expr_apply (isub_name var_deref_oid) (Expr_basic [var_in_when_state] # l)) in
                    deref_oid [Expr_apply (isup_attr (isub_name var_select))
                          [case attr_ty of OclTy_base _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                         | OclTy_object _ \<Rightarrow> deref_oid [] ] ] ])) ])
          l_attr)
        [ (var_in_post_state, '''', '''')
        , (var_in_pre_state, ''_at_pre'', ''@pre'')])))"

definition "print_dot_inherited = List_map Thy_definition_hol o
  map_class_arg_only' (\<lambda>isub_name name l_attr l_inherited _.
    flatten (flatten (
    List_map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      List_map (\<lambda>(attr_name, attr_ty).
            let isup_attr = (\<lambda>s. flatten [s, isup_of_str attr_name])
              ; dot_attr = (\<lambda>s. Expr_postunary (Expr_parenthesis (Expr_basic [s])) (Expr_basic [mk_dot attr_name attr_when])) in
            [ Definition
                (Expr_rewrite
                   (Expr_basic [flatten [isup_attr (isub_name ''dot''), dot_at_when]])
                   ''=''
                   (let var_x = ''x'' in
                    Expr_lambda var_x (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = (\<lambda>l. Expr_apply (isub_name var_deref_oid) (Expr_basic [var_in_when_state] # l)) in
                    deref_oid [Expr_apply (isup_attr (isub_name var_select))
                          [case attr_ty of OclTy_base _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                         | OclTy_object _ \<Rightarrow> deref_oid [] ] ] ]))) ])
          l_inherited)
        [ (var_in_post_state, '''', '''')
        , (var_in_pre_state, ''_at_pre'', ''@pre'')])))"

subsection{* Conclusion *}

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

definition "fold_thy f univ = fold (\<lambda>x. fold f (x univ)) thy_object"

section{* OCaml *}
subsection{* beginning *}

code_include OCaml "" {*

let (<<) f g x = f (g x)

module To = struct
  type nat = Zero_nat | Suc of nat

  type nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
    | NibbleE | NibbleF

  type char = Char of nibble * nibble

  module M = struct
    let to_nibble = function
      Nibble0 -> 0x0 | Nibble1 -> 0x1 | Nibble2 -> 0x2 | Nibble3 -> 0x3 | Nibble4 -> 0x4 | Nibble5 -> 0x5 |
       Nibble6 -> 0x6 | Nibble7 -> 0x7 | Nibble8 -> 0x8 | Nibble9 -> 0x9 | NibbleA -> 0xA | NibbleB -> 0xB | NibbleC -> 0xC | NibbleD -> 0xD
      | NibbleE -> 0xE | NibbleF -> 0xF

    let to_char = function Char (n1, n2) -> char_of_int (to_nibble n1 lsl 4 + to_nibble n2)

    let to_string l = (String.concat "" (List.map (fun c -> String.make 1 (to_char c)) l))
  (*
    let to_num =
      let rec aux mot n = function
        | Bit0 p -> aux mot (succ n) p
        | bit ->
          let mot = mot + (1 lsl n) in
          match bit with
          | Bit1 p -> aux mot (succ n) p
          | _ -> mot in
      aux 0 0

    let to_int = function
      | ZeroInt -> 0
      | Pos n -> to_num n
      | Neg n -> - (to_num n)
  *)
    let to_nat =
      let rec aux n = function Zero_nat -> n | Suc xs -> aux (succ n) xs in
      aux 0
  end

  let string nibble_rec char_rec =
    let ofN = nibble_rec
      Nibble0 Nibble1 Nibble2 Nibble3 Nibble4 Nibble5
      Nibble6 Nibble7 Nibble8 Nibble9 NibbleA NibbleB
      NibbleC NibbleD NibbleE NibbleF in
    M.to_string << List.map (char_rec (fun c1 c2 -> Char (ofN c1, ofN c2)))

  let nat nat_rec =
    M.to_nat << nat_rec Zero_nat (fun _ x -> Suc x)

end

module CodeType = struct
  module Cancel_rec = struct
    type i = int
  end
  type int = Cancel_rec.i
end

module CodeConst = struct
  (* here contain functions using characters
     not allowed in a Isabelle 'code_const' expr
     (e.g. '_', '"', ...) *)

  let outFile1 f file =
    let () = if Sys.file_exists file then Printf.eprintf "File exists %s\n" file else () in
    let oc = open_out file in
    let () = f (Printf.fprintf oc) in
    close_out oc

  module Sys = struct open Sys
    let isDirectory = is_directory
    let argv = Array.to_list argv
  end

  module Printf = Printf
  module String = String
  module To = To
end

*}

subsection{* ML type *}

type_synonym ml_string = String.literal
datatype ml_nat = ML_nat
datatype ml_nibble = ML_nibble
datatype ml_char = ML_char
datatype ml_int = ML_int

code_type ml_int (OCaml "CodeType.int")

subsection{* ML code const *}

text{* ... *}

consts out_file0 :: "((ml_string \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
code_const out_file1 (OCaml "CodeConst.outFile1")

text{* module To *}

consts ToString :: "(ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> nibble \<Rightarrow> ml_nibble) \<Rightarrow>
                    ((nibble \<Rightarrow> nibble \<Rightarrow> ml_char) \<Rightarrow> char \<Rightarrow> ml_char) \<Rightarrow>
                    string \<Rightarrow> ml_string"
code_const ToString (OCaml "CodeConst.To.string")
definition "To_string = ToString nibble_rec char_rec"

consts ToNat :: "(ml_nat \<Rightarrow> (nat \<Rightarrow> ml_nat \<Rightarrow> ml_nat) \<Rightarrow> nat \<Rightarrow> ml_nat) \<Rightarrow>
                 nat \<Rightarrow> ml_int"
code_const ToNat (OCaml "CodeConst.To.nat")
definition "To_nat = ToNat nat_rec"

text{* module Printf *}

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
consts sprintf6 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> '\<alpha>6 \<Rightarrow> ml_string"

code_const sprintf0 (OCaml "CodeConst.Printf.sprintf")
code_const sprintf1 (OCaml "CodeConst.Printf.sprintf")
code_const sprintf2 (OCaml "CodeConst.Printf.sprintf")
code_const sprintf3 (OCaml "CodeConst.Printf.sprintf")
code_const sprintf4 (OCaml "CodeConst.Printf.sprintf")
code_const sprintf5 (OCaml "CodeConst.Printf.sprintf")
code_const sprintf6 (OCaml "CodeConst.Printf.sprintf")

consts eprintf0 :: "ml_string \<Rightarrow> unit"
code_const eprintf0 (OCaml "CodeConst.Printf.eprintf")

(* Monomorph *)

consts sprintf1s :: "ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string"
code_const sprintf1s (OCaml "CodeConst.Printf.sprintf")
consts sprintf2ss :: "ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string"
code_const sprintf2ss (OCaml "CodeConst.Printf.sprintf")

text{* module String *}

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_const String_concat (OCaml "CodeConst.String.concat")

text{* module List *}

definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "List_mapi f l = (let (l, _) = foldl (\<lambda>(acc, n) x. (f n x # acc, Suc n)) ([], 0) l in rev l)"

text{* module Sys *}

consts Sys_is_directory :: "ml_string \<Rightarrow> bool"
code_const Sys_is_directory (OCaml "CodeConst.Sys.isDirectory")

consts Sys_argv :: "ml_string list"
code_const Sys_argv (OCaml "CodeConst.Sys.argv")

text{* module Unicode *}

definition "Unicode_mk_u = sprintf1s (STR (Char Nibble5 NibbleC # ''<%s>''))"
definition "Unicode_u_Rightarrow = Unicode_mk_u (STR ''Rightarrow'')"
definition "Unicode_u_alpha = Unicode_mk_u (STR ''alpha'')"
definition "Unicode_u_lambda = Unicode_mk_u (STR ''lambda'')"
definition "Unicode_u_lfloor = Unicode_mk_u (STR ''lfloor'')"
definition "Unicode_u_rfloor = Unicode_mk_u (STR ''rfloor'')"
definition "Unicode_u_Longrightarrow = Unicode_mk_u (STR ''Longrightarrow'')"

section{* s of ... *} (* s_of *)

definition "s_of_dataty = (\<lambda> Datatype n l \<Rightarrow>
  sprintf2 (STR ''datatype %s = %s'')
    (To_string n)
    (String_concat (STR ''
                        | '')
      (List_map
        (\<lambda>(n,l).
         sprintf2 (STR ''%s %s'')
           (To_string n)
           (String_concat (STR '' '')
            (List_map
              (\<lambda> Opt o_ \<Rightarrow> sprintf1 (STR ''\"%s option\"'') (To_string o_)
               | Raw o_ \<Rightarrow> sprintf1 (STR ''%s'') (To_string o_))
              l))) l) ))"

fun s_of_rawty where "s_of_rawty rawty = (case rawty of
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name))"

definition "s_of_ty_synonym = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

fun s_of_expr where "s_of_expr expr = (
  case expr of
    Expr_case e l \<Rightarrow> sprintf2 (STR ''(case %s of %s)'') (s_of_expr e) (String_concat (STR ''
    | '') (map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l))
  | Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (map To_string l))
  | Expr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (To_string s)
  | Expr_lambda s e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') Unicode_u_lambda (To_string s) (s_of_expr e)
  | Expr_lambdas l e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') Unicode_u_lambda (String_concat (STR '' '') (map To_string l)) (s_of_expr e)
  | Expr_function l \<Rightarrow> sprintf2 (STR ''(%s %s)'') Unicode_u_lambda (String_concat (STR ''
    | '') (map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l))
  (*| Expr_apply s [e] \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (s_of_expr e)*)
  | Expr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_applys e l \<Rightarrow> sprintf2 (STR ''((%s) %s)'') (s_of_expr e) (String_concat (STR '' '') (map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_some (Expr_function l) \<Rightarrow> sprintf4 (STR ''%s%s %s%s'') Unicode_u_lfloor Unicode_u_lambda (String_concat (STR ''
    | '') (map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l)) Unicode_u_rfloor
  | Expr_some e \<Rightarrow> sprintf3 (STR ''%s%s%s'') Unicode_u_lfloor (s_of_expr e) Unicode_u_rfloor
  | Expr_postunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_preunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_warning_parenthesis e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)
  | Expr_parenthesis e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e))"

definition "s_of_instantiation_class = (\<lambda> Instantiation n n_def expr \<Rightarrow>
    let name = To_string n in
    sprintf4 (STR ''instantiation %s :: object
begin
  definition %s_%s_def : \"%s\"
  instance ..
end'')
      name
      (To_string n_def)
      name
      (s_of_expr expr))"

definition "s_of_defs_overloaded = (\<lambda> Defs_overloaded n e \<Rightarrow>
    sprintf2 (STR ''defs(overloaded) %s : \"%s\"'') (To_string n) (s_of_expr e))"

definition "s_of_consts_class = (\<lambda> Consts n ty_out symb1 symb2 \<Rightarrow>
    sprintf6 (STR ''consts %s :: \"'%s %s %s\" (\"(_) %s'(%s')\")'') (To_string n) Unicode_u_alpha Unicode_u_Rightarrow (To_string ty_out) (To_string symb1) (To_string symb2))"

definition "s_of_definition_hol = (\<lambda>
    Definition e \<Rightarrow> sprintf1 (STR ''definition \"%s\"'') (s_of_expr e)
  | Definition_abbrev name (abbrev, prio) e \<Rightarrow> sprintf4 (STR ''definition %s (\"(1%s)\" %d)
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (To_nat prio) (s_of_expr e))"

definition "s_of_lemmas_simp = (\<lambda> Lemmas_simp l \<Rightarrow>
    sprintf1 (STR ''lemmas [simp] = %s'') (String_concat (STR ''
                '') (List_map (To_string) l)))"

fun s_of_tactic where "s_of_tactic expr = (\<lambda>
    Tac_rule s \<Rightarrow> sprintf1 (STR ''rule %s'') (To_string s)
  | Tac_rule_where s l \<Rightarrow> sprintf2 (STR ''rule %s[where %s]'')
      (To_string s)
      (String_concat (STR '', '') (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l))
  | Tac_plus t \<Rightarrow> sprintf1 (STR ''(%s)+'') (s_of_tactic t)
  | Tac_simp \<Rightarrow> sprintf0 (STR ''simp'')
  | Tac_simp_add l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_simp_only l \<Rightarrow> sprintf1 (STR ''simp only: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_simp_all \<Rightarrow> sprintf0 (STR ''simp_all'')
  | Tac_simp_all_add s \<Rightarrow> sprintf1 (STR ''simp_all add: %s'') (To_string s)) expr"

definition "s_of_lemma_by =
 (\<lambda> Lemma_by n l_spec l_apply o_by \<Rightarrow>
    sprintf4 (STR ''lemma %s : \"%s\"
%s%s'')
      (To_string n)
      (String_concat (sprintf1 (STR '' %s '') Unicode_u_Longrightarrow) (List_map s_of_expr l_spec))
      (String_concat (STR '''') (List_map (\<lambda> [] \<Rightarrow> STR '''' | l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))) l_apply))
      (case o_by of None \<Rightarrow> STR ''done''
                  | Some l_apply \<Rightarrow> sprintf1 (STR ''by(%s)'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))))"

definition "s_of_thy =
            (\<lambda> Thy_dataty dataty \<Rightarrow> s_of_dataty dataty
             | Thy_ty_synonym ty_synonym \<Rightarrow> s_of_ty_synonym ty_synonym
             | Thy_instantiation_class instantiation_class \<Rightarrow> s_of_instantiation_class instantiation_class
             | Thy_defs_overloaded defs_overloaded \<Rightarrow> s_of_defs_overloaded defs_overloaded
             | Thy_consts_class consts_class \<Rightarrow> s_of_consts_class consts_class
             | Thy_definition_hol definition_hol \<Rightarrow> s_of_definition_hol definition_hol
             | Thy_lemmas_simp lemmas_simp \<Rightarrow> s_of_lemmas_simp lemmas_simp
             | Thy_lemma_by lemma_by \<Rightarrow> s_of_lemma_by lemma_by)"

definition "s_of_thy_list name fic_import l_thy =
  flatten
        [ [ sprintf2ss (STR ''theory %s imports \"%s\" begin'') name fic_import ]
        , flatten (List_mapi (\<lambda>i l.
            ( STR ''''
            # sprintf1 (STR ''(* %d *********************************** *)'') (To_nat (Suc i))
            # List_map s_of_thy l )) l_thy)
        , [ STR '''', STR ''end'' ] ]"

section{* SML *}
subsection{* global *}

code_reflect OCL
   functions nat_rec nibble_rec char_rec
             fold_thy

ML{*
structure To = struct
  datatype nat = Zero_nat | Suc of nat

  datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
    | NibbleE | NibbleF

  datatype char = Char of nibble * nibble

  structure M = struct
    val to_nibble = fn
      Nibble0 => 0x0 | Nibble1 => 0x1 | Nibble2 => 0x2 | Nibble3 => 0x3 | Nibble4 => 0x4 | Nibble5 => 0x5 |
       Nibble6 => 0x6 | Nibble7 => 0x7 | Nibble8 => 0x8 | Nibble9 => 0x9 | NibbleA => 0xA | NibbleB => 0xB | NibbleC => 0xC | NibbleD => 0xD
      | NibbleE => 0xE | NibbleF => 0xF

    val to_char = fn Char (n1, n2) => Char.chr ((to_nibble n1) * 16 + to_nibble n2)

    fun to_string l = (String.concat (map (fn c => str (to_char c)) l))

    val to_nat =
      let fun aux n = fn Zero_nat => n | Suc xs => aux (n + 1) xs in
      aux 0
      end
  end

  fun string nibble_rec char_rec =
    let val ofN = nibble_rec
      Nibble0 Nibble1 Nibble2 Nibble3 Nibble4 Nibble5
      Nibble6 Nibble7 Nibble8 Nibble9 NibbleA NibbleB
      NibbleC NibbleD NibbleE NibbleF in
    M.to_string o List.map (char_rec (fn c1 => fn c2 => Char (ofN c1, ofN c2)))
    end

  fun nat nat_rec =
    M.to_nat o nat_rec Zero_nat (fn _ => Suc)
end

 val To_string = To.string OCL.nibble_rec OCL.char_rec
 val To_nat = To.nat OCL.nat_rec
*}

ML{* 
type class_inline = { attr_base : (binding * binding) list
                    , attr_object : binding list
                    , child : binding list
                    , univ : OCL.univ option }

structure Data = Theory_Data
  (type T = class_inline Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

structure From = struct local
 open OCL
 val from_nibble = fn
       0x0 => Nibble0 | 0x1 => Nibble1 | 0x2 => Nibble2 | 0x3 => Nibble3 | 0x4 => Nibble4 | 0x5 => Nibble5 |
        0x6 => Nibble6 | 0x7 => Nibble7 | 0x8 => Nibble8 | 0x9 => Nibble9 | 0xA => NibbleA | 0xB => NibbleB | 0xC => NibbleC | 0xD => NibbleD
       | 0xE => NibbleE | 0xF => NibbleF
 fun from_string n = map (fn c => let val c = Char.ord c in OCL.Char (from_nibble (c div 16), from_nibble (c mod 16)) end) (String.explode n)
 val from_binding = from_string o Binding.name_of
 in
 fun mk_univ (n, ({attr_base = attr_base, attr_object = attr_object, child = child, ...}:class_inline)) t = 
   Mk_univ ( from_string n
           , List.concat [ map (fn (b, ty) => (from_binding b, OclTy_base (from_binding ty))) attr_base
                         , map (fn b => (from_binding b, object)) attr_object]
           , case child of [] => NONE | [x] => SOME (mk_univ (let val x = Binding.name_of x in (x, let val SOME v = Symtab.lookup t x in v end) end) t))
end end

val () =
  Outer_Syntax.command @{command_spec "Class"} "Class definition"
    ((Parse.binding --| Parse.$$$ "=") --
      Scan.repeat (@{keyword "attr_base"} |-- Parse.!!! (Parse.binding -- (Parse.$$$ "::" |-- Parse.!!! Parse.binding))) --
      Scan.repeat (@{keyword "attr_object"} |-- Parse.!!! Parse.binding) --
      Scan.repeat (@{keyword "child"} |-- Parse.!!! Parse.binding)
        >> (fn (((binding, attr_base), attr_object), child) => fn x =>
              x |> Toplevel.theory (fn thy => thy |> Data.map (fn t =>
                                                     let val name = Binding.name_of binding
                                                     fun mk univ = { attr_base = attr_base
                                                                   , attr_object = attr_object
                                                                   , child = child
                                                                   , univ = univ } in
                                                     Symtab.insert (op =) (name, mk (SOME (From.mk_univ (name, mk NONE) t))) t
                                                     end))))
*}
ML{* 
fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global
*}

subsection{* Deep *}

definition "write_file file_out example path_dep = (
  case filter Sys_is_directory Sys_argv
  of dir # _ \<Rightarrow>
    out_file1
      (\<lambda>fprintf1.
        List_iter (fprintf1 (STR ''%s
''))
                  (s_of_thy_list
                     file_out
                     path_dep
                     (map (\<lambda>f. f example) thy_object)))
      (sprintf2 (STR ''%s/%s.thy'') dir file_out)
   | _ \<Rightarrow> eprintf0 (STR ''No directory in argument''))"

ML{*
fun i_of_string s = "''" ^ To_string s ^ "''"
val i_of_oclTy = fn OCL.OclTy_base s => "OclTy_base " ^ i_of_string s
                  | OCL.OclTy_object s => "OclTy_object " ^ i_of_string s

fun i_of_univ (OCL.Mk_univ (s, l, opt)) = 
  "Mk_univ " ^
    i_of_string s ^ " [" ^
    (String.concatWith ", " (map (fn (s,t) => "(" ^ i_of_string s ^ ", " ^ i_of_oclTy t ^ ")") l)) ^ "] " ^
    (i_of_option i_of_univ opt)

and i_of_option f = fn NONE => "None"
                 | SOME s => "(Some (" ^ f s ^ "))"
*}

ML{*
local
fun prep_destination "" = NONE
  | prep_destination "-" = (legacy_feature "drop \"file\" argument entirely instead of \"-\""; NONE)
  | prep_destination s = SOME (Path.explode s)

fun export_code_cmd raw_cs seris thy = Code_Target.export_code thy (Code_Target.read_const_exprs thy raw_cs)
  ((map o apfst o apsnd) prep_destination seris)

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Args.parse --| @{keyword ")"}) []
in

val () =
  Outer_Syntax.command @{command_spec "Class.end_deep"} "Class generation in deep form"
    ((Parse.binding -- Parse.name -- Parse.name -- Parse.name -- Parse.name
      -- (* code_expr_inP *) Scan.repeat (@{keyword "in"} |-- Parse.!!! (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- Scan.optional (@{keyword "file"} |-- Parse.name) ""
        -- code_expr_argsP))) >> (fn (((((name, name_var), name_main), file_out), path_dep), seri_args) =>
      let val name = Binding.name_of name
          fun def s = in_local (snd o Specification.definition_cmd (NONE, ((@{binding ""}, []), s)) false) in
      Toplevel.theory (fn thy =>
        thy |> def let val SOME { attr_base = attr_base
                                , attr_object = attr_object
                                , child = child
                                , univ = SOME univ} = Symtab.lookup (Data.get thy) name in
                   name_var ^ " = " ^ i_of_univ univ
                   end
            |> def (name_main ^ " = write_file (" ^ file_out ^ ") (" ^ name_var ^ ") (" ^ path_dep ^ ")")
            |> (fn thy => let val () = export_code_cmd [name_main] seri_args thy in thy end))
      end))
end
*}

subsection{* Shallow *}

ML{*
 fun To_binding s = Binding.make (s, Position.none)
 val To_sbinding = To_binding o To_string
 fun s_of_rawty rawty = case rawty of
    OCL.Ty_base s => To_string s
  | OCL.Ty_apply (name, l) => (let val s = String.concatWith ", " (map s_of_rawty l) in
                                                 case l of [_] => s | _ => "(" ^ s ^ ")" end)
                              ^ " " ^
                              (s_of_rawty name)

val STR = I

val Unicode_mk_u = fn s => (STR ("\\" ^ "<" ^ s ^ ">"))
val Unicode_u_Rightarrow = Unicode_mk_u (STR "Rightarrow")
val Unicode_u_alpha = Unicode_mk_u (STR "alpha")
val Unicode_u_lambda = Unicode_mk_u (STR "lambda")
val Unicode_u_lfloor = Unicode_mk_u (STR "lfloor")
val Unicode_u_rfloor = Unicode_mk_u (STR "rfloor")
val Unicode_u_Longrightarrow = Unicode_mk_u (STR "Longrightarrow")

fun s_of_expr expr = let open OCL in
  case expr of
    Expr_case (e, l) => let val s1 =
 (s_of_expr e)
val s2 = (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ")
 [(s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) in
(STR "(case " ^ s1 ^ " of " ^ s2 ^ ")") end
  | Expr_rewrite (e1, symb, e2) => String.concatWith (STR " ") [(s_of_expr e1), (To_string symb), (s_of_expr e2)]
  | Expr_basic l =>  (String.concatWith (STR " ") (map To_string l))
  | Expr_binop (e1, s, e2) => String.concatWith (STR " ") [(s_of_expr e1), (s_of_expr (Expr_basic [s])), (s_of_expr e2)]
  | Expr_annot (e, s) => (STR "(" ^ (s_of_expr e)  ^ "::" ^ (To_string s) ^ ")")
  | Expr_lambda (s, e) =>  (STR "(" ^ Unicode_u_lambda  ^ "" ^ (To_string s)  ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_lambdas (l, e) => (STR "(" ^ Unicode_u_lambda ^ "" ^ (String.concatWith (STR " ") (map To_string l)) ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_function l =>  (STR "(" ^ Unicode_u_lambda  ^ " " ^ (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1),Unicode_u_Rightarrow, (s_of_expr s2)]) l)) ^ ")")
  (*| Expr_apply s [e] => sprintf2 (STR "(" ^ s ^ " " ^ s ^ ")") (To_string s) (s_of_expr e)*)
  | Expr_apply (s, l) =>  let val s1 = (To_string s) val s2 = (String.concatWith (STR " ") (map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
(STR "(" ^ s1 ^ " " ^ s2 ^ ")") end
  | Expr_applys (e, l) => let val s1 = (s_of_expr e) val s2 = (String.concatWith (STR " ") (map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
 (STR "((" ^ s1 ^ ") " ^ s2 ^ ")") end
  | Expr_some (Expr_function l) => let val s1 = Unicode_u_lfloor val s2 = Unicode_u_lambda val s3 = (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) val s4 = Unicode_u_rfloor in
(STR "" ^ s1 ^ "" ^ s2 ^ " " ^ s3 ^ "" ^ s4 ^ "") end
  | Expr_some e => String.concatWith (STR "") [Unicode_u_lfloor, (s_of_expr e), Unicode_u_rfloor]
  | Expr_postunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_preunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_warning_parenthesis e =>  (STR "(" ^ (s_of_expr e) ^ ")")
  | Expr_parenthesis e => (STR "(" ^ (s_of_expr e) ^ ")")
end

fun simp_tac f = Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac (f ctxt) 1))

fun m_of_tactic expr = let open OCL in let open Method in case expr of
    Tac_rule s => Basic (fn ctxt => rule [Proof_Context.get_thm ctxt (To_string s)])
  | Tac_rule_where (s, l) => Basic (fn ctxt => rule [read_instantiate ctxt (map (fn (var, expr) => ((To_string var, 0), s_of_expr expr)) l) (Proof_Context.get_thm ctxt (To_string s))])
  | Tac_plus t => Repeat1 (m_of_tactic t)
  | Tac_simp => simp_tac I
  | Tac_simp_add l => simp_tac (fn ctxt => ctxt addsimps (map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_only l => simp_tac (fn ctxt => clear_simpset ctxt addsimps (map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_all => m_of_tactic (Tac_plus Tac_simp)
  | Tac_simp_all_add s => m_of_tactic (Tac_plus (Tac_simp_add [s]))
end end
*}

ML{*
fun perform_instantiation thy tycos vs f_eq add_def tac (*add_eq_thms*) =
    thy
    |> Class.instantiation (tycos, vs, f_eq)
    |> fold_map add_def tycos
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) (fn _ => tac)
(*    |-> fold Code.del_eqn
    |> fold add_eq_thms tycos*)
    |-> K I
local
fun read_abbrev b ctxt raw_rhs =
  let
    val rhs = Proof_Context.read_typ_syntax (ctxt |> Proof_Context.set_defsort []) raw_rhs;
    val ignored = Term.fold_atyps_sorts (fn (_, []) => I | (T, _) => insert (op =) T) rhs [];
    val _ =
      if null ignored then ()
      else Context_Position.if_visible ctxt warning
        ("Ignoring sort constraints in type variables(s): " ^
          commas_quote (map (Syntax.string_of_typ ctxt) (rev ignored)) ^
          "\nin type abbreviation " ^ (case b of NONE => "" | SOME b => Binding.print b));
  in rhs end
in
fun read_typ_syntax b = read_abbrev b
                      o Proof_Context.init_global
end

fun s_of_tactic l = (Method.Then (map m_of_tactic l), (Position.none, Position.none))

fun apply_results l =
  fn p => p |> Proof.apply_results (s_of_tactic l)
            |> Seq.the_result ""

fun global_terminal_proof o_by = case o_by of
   NONE => Proof.global_done_proof
 | SOME l_apply => Proof.global_terminal_proof (s_of_tactic l_apply, NONE)
*}

ML{*
val OCL_main = let open OCL in fold_thy ((*let val f = *)fn
  Thy_dataty (Datatype (n, l)) =>
    (snd oo Datatype.add_datatype_cmd Datatype_Aux.default_config)
      [((To_sbinding n, [], NoSyn),
       map (fn (n, l) => (To_sbinding n, map (fn OCL.Opt o_ => To_string o_ ^ " option"
                                             |   Raw o_ => To_string o_) l, NoSyn)) l)]
| Thy_ty_synonym (Type_synonym (n, l)) =>
    (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global (s_bind, [], NoSyn)
                                   (read_typ_syntax (SOME s_bind) thy (s_of_rawty l))) thy
     end)
| Thy_instantiation_class (Instantiation (n, n_def, expr)) =>
    (fn thy =>
     let val name = To_string n in
     perform_instantiation
       thy
       [ let val Type (s, _) = (read_typ_syntax NONE thy name) in s end ]
       []
       (Syntax.read_sort (Proof_Context.init_global thy) "object")
       (fn _ => fn thy =>
        let val ((_, (_, ty)), thy) = Specification.definition_cmd
           (NONE, ((To_binding (To_string n_def ^ "_" ^ name ^ "_def"), []), s_of_expr expr)) false thy in
         (ty, thy)
        end)
       (fn thms => Class.intro_classes_tac [] THEN ALLGOALS (Proof_Context.fact_tac thms))
     end)
| Thy_defs_overloaded (Defs_overloaded (n, e)) =>
    Isar_Cmd.add_defs ((false, true), [((To_sbinding n, s_of_expr e), [])])
| Thy_consts_class (Consts (n, ty_out, symb1, symb2)) =>
    Sign.add_consts [( To_sbinding n
                     , String.concatWith " " [ "'" ^ Unicode_u_alpha, Unicode_u_Rightarrow, (To_string ty_out) ]
                     , Mixfix ("(_) " ^ (To_string symb1) ^ "'(" ^ (To_string symb2) ^ "')", [], 1000))]
| Thy_definition_hol def =>
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_abbrev (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e) in
    in_local (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Thy_lemmas_simp (Lemmas_simp l) =>
    in_local (snd o Specification.theorems_cmd Thm.lemmaK
      [((@{binding ""}, [Args.src (("simp", []), Position.none)]),
        map (fn s => (Facts.Named ((To_string s, Position.none), NONE), [])) l)]
      []
      false)
| Thy_lemma_by (Lemma_by (n, l_spec, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, []), [((String.concatWith ((STR " " ^ Unicode_u_Longrightarrow ^ " ")) (map s_of_expr l_spec)), [])])])
             false lthy
        |> fold apply_results l_apply
        |> global_terminal_proof o_by)
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
)
end
*}

ML{*
val () =
  Outer_Syntax.command @{command_spec "Class.end_shallow"} "Class generation in shallow form"
    (Parse.binding >> (fn name =>
      let val name = Binding.name_of name in
      Toplevel.theory (fn thy => OCL_main (let val SOME { attr_base = attr_base
                                                        , attr_object = attr_object
                                                        , child = child
                                                        , univ = SOME univ} = Symtab.lookup (Data.get thy) name in
                                           univ
                                           end) thy)
      end))

(*val _ = print_depth 100*)
*}

end
