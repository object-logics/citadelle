(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_UML.thy ---
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

theory  OCL_compiler_meta_UML
imports OCL_compiler_meta_Pure
        "../OCL_compiler_init_rbt"
begin

section{* OCL Meta-Model aka. AST definition of OCL *}

subsection{* type definition *}

datatype ocl_collection =   Set | Sequence

datatype ocl_multiplicity_single = Mult_nat nat
                                 | Mult_star

datatype ocl_multiplicity = OclMult "(ocl_multiplicity_single \<times> ocl_multiplicity_single option) list"
                                    ocl_collection (* return type of the association *)

record ocl_ty_class_node =  TyObjN_ass_switch :: nat
                            TyObjN_role_multip :: ocl_multiplicity
                            TyObjN_role_name :: "string option"
                            TyObjN_role_ty :: string
record ocl_ty_class =       TyObj_name :: string
                            TyObj_ass_id :: nat
                            TyObj_ass_arity :: nat
                            TyObj_from :: ocl_ty_class_node
                            TyObj_to :: ocl_ty_class_node
datatype ocl_ty =           OclTy_base_void
                          | OclTy_base_boolean
                          | OclTy_base_integer
                          | OclTy_base_unlimitednatural
                          | OclTy_base_real
                          | OclTy_base_string
                          | OclTy_class ocl_ty_class
                          | OclTy_collection ocl_collection ocl_ty
                          | OclTy_raw string (* denoting raw HOL-type.*)


datatype ocl_association_type = OclAssTy_association
                              | OclAssTy_composition
                              | OclAssTy_aggregation
record ocl_association =        OclAss_type     :: ocl_association_type
                                OclAss_relation :: "( string (* name class *)
                                                    \<times> ocl_multiplicity (* multiplicity *)
                                                    \<times> string option (* role *)) list"

datatype ocl_ctxt_prefix = OclCtxtPre | OclCtxtPost

datatype ocl_ctxt_term = T_pure pure_term
                       | T_to_be_parsed string

record ocl_ctxt_pre_post = Ctxt_ty :: string (* class ty *)
                           Ctxt_fun_name :: string (* function name *)
                           Ctxt_fun_ty_arg :: "(string (* arg name *) \<times> ocl_ty) list"
                           Ctxt_fun_ty_out :: "ocl_ty option" (* None : Void *)
                           Ctxt_expr :: "(ocl_ctxt_prefix \<times> ocl_ctxt_term (* expr *)) list"

record ocl_ctxt_inv =      Ctxt_inv_ty :: string
                           Ctxt_inv_expr :: "(string (* name *) \<times> ocl_ctxt_term (* expr *)) list"

datatype ocl_class =   OclClass
                         string (* name of the class *)
                         "(string (* name *) \<times> ocl_ty) list" (* attribute *)
                         "ocl_class list" (* link to subclasses *)

record ocl_class_raw = ClassRaw_name :: string
                       ClassRaw_own :: "(string (* name *) \<times> ocl_ty) list" (* attribute *)
                       ClassRaw_contract :: "ocl_ctxt_pre_post list" (* contract *)
                       ClassRaw_invariant :: "ocl_ctxt_inv list" (* invariant *)
                       ClassRaw_inh :: "string option" (* superclass *)

datatype ocl_ass_class = OclAssClass ocl_association
                                     ocl_class_raw

subsection{* Class Translation Preliminaries *}

definition "const_oid = ''oid''"
definition "const_oid_list = ''list''"
definition "const_oclany = ''OclAny''"

definition "single_multip = (\<lambda> OclMult l _ \<Rightarrow>
  List.list_all (\<lambda> (_, Some (Mult_nat n)) \<Rightarrow> n \<le> 1
                 | (Mult_nat n, None) \<Rightarrow> n \<le> 1
                 | _ \<Rightarrow> False) l)"

fun_quick fold_max_aux where
   "fold_max_aux f l l_acc accu = (case l of
      [] \<Rightarrow> accu
    | x # xs \<Rightarrow> fold_max_aux f xs (x # l_acc) (f x (flatten [rev l_acc, xs]) accu))"

definition "fold_max f l = fold_max_aux f (List_mapi Pair l) []"

function (sequential) class_unflat_aux where
(* (* FIXME replace with this simplified form *)
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        (List_map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          (case lookup rbt_inv r of None \<Rightarrow> [] | Some l \<Rightarrow> l)))"
*)
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_inv r of
  None \<Rightarrow>
(case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        ( ( [])))
| Some l \<Rightarrow>
(case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        (List_map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          ( l))))"
by pat_completeness auto

termination
proof -
 have arith_diff: "\<And>a1 a2 (b :: Nat.nat). a1 = a2 \<Longrightarrow> a1 > b \<Longrightarrow> a1 - (b + 1) < a2 - b"
 by arith

 have arith_less: "\<And>(a:: Nat.nat) b c. b \<ge> max (a + 1) c \<Longrightarrow> a < b"
 by arith

 have rbt_length: "\<And>rbt_cycle r v. lookup rbt_cycle r = None \<Longrightarrow>
     length (keys (insert r v rbt_cycle)) = length (keys rbt_cycle) + 1"
  apply(subst (1 2) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric], simp)
 by (metis card_insert_if domIff finite_dom_lookup)

 have rbt_fold_union'': "\<And>ab a x k. dom (\<lambda>b. if b = ab then Some a else k b) = {ab} \<union> dom k"
 by(auto)

 have rbt_fold_union': "\<And>l rbt_inv a.
       dom (lookup (List.fold (\<lambda>(k, _). RBT.insert k a) l rbt_inv)) =
       dom (map_of l) \<union> dom (lookup rbt_inv)"
  apply(rule_tac P = "\<lambda>rbt_inv . dom (lookup (List.fold (\<lambda>(k, _). RBT.insert k a) l rbt_inv)) =
       dom (map_of l) \<union> dom (lookup rbt_inv)" in allE, simp_all)
  apply(induct_tac l, simp, rule allI)
  apply(case_tac aa, simp)
  apply(simp add: rbt_fold_union'')
 done

 have rbt_fold_union: "\<And>rbt_cycle rbt_inv a.
   dom (lookup (RBT.fold (\<lambda>k _. RBT.insert k a) rbt_cycle rbt_inv)) =
   dom (lookup rbt_cycle) \<union> dom (lookup rbt_inv)"
  apply(simp add: fold_fold)
  apply(subst (2) map_of_entries[symmetric])
  apply(rule rbt_fold_union')
 done

 have rbt_fold_eq: "\<And>rbt_cycle rbt_inv a b.
   dom (lookup (RBT.fold (\<lambda>k _. RBT.insert k a) rbt_cycle rbt_inv)) =
   dom (lookup (RBT.fold (\<lambda>k _. RBT.insert k b) rbt_inv rbt_cycle))"
 by(simp add: rbt_fold_union Un_commute)

 let ?len = "\<lambda>x. length (keys x)"
 let ?len_merge = "\<lambda>rbt_cycle rbt_inv. ?len (fold (\<lambda>k _. insert k []) rbt_cycle rbt_inv)"

 have rbt_fold_large: "\<And>rbt_cycle rbt_inv. ?len_merge rbt_cycle rbt_inv \<ge> max (?len rbt_cycle) (?len rbt_inv)"
  apply(subst (1 2 3) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric], simp)
  apply(subst (1 2) card_mono, simp_all)
  apply(simp add: rbt_fold_union)+
 done

 have rbt_fold_eq: "\<And>rbt_cycle rbt_inv r a.
     lookup rbt_inv r = Some a \<Longrightarrow>
     ?len_merge (insert r () rbt_cycle) rbt_inv = ?len_merge rbt_cycle rbt_inv"
  apply(subst (1 2) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric])
  apply(simp add: rbt_fold_union)
 by (metis Un_insert_right insert_dom)

 show ?thesis
  apply(relation "measure (\<lambda>(_, rbt_inv, rbt_cycle, r).
    ?len_merge rbt_cycle rbt_inv - length (keys rbt_cycle)
    )", simp+)
  apply(subst rbt_length, simp)
  apply(rule arith_diff)
  apply(rule rbt_fold_eq, simp)
  apply(rule arith_less)
  apply(subst rbt_length[symmetric], simp)
  apply(rule rbt_fold_large)
 done
qed

definition "class_unflat l_class l_ass =
 (let l =
    let rbt = (* fold classes:
                 set ''OclAny'' as default inherited class (for all classes linking to zero inherited classes) *)
              insert
                const_oclany
                (ocl_class_raw.make const_oclany [] [] [] None)
                (List.fold
                  (\<lambda> cflat \<Rightarrow>
                    insert (ClassRaw_name cflat) (cflat \<lparr> ClassRaw_inh := case ClassRaw_inh cflat of None \<Rightarrow> Some const_oclany | x \<Rightarrow> x \<rparr>))
                  l_class
                  empty) in
    (* fold associations:
       add remaining 'object' attributes *)
    List_map snd (entries (List.fold (\<lambda> (ass_oid, ass) \<Rightarrow>
      let l_rel = OclAss_relation ass in
      fold_max
        (bug_ocaml_extraction (let n_rel = natural_of_nat (List.length l_rel) in
         \<lambda> (cpt_to, (name_to, multip_to, Some role_to)) \<Rightarrow> List.fold (\<lambda> (cpt_from, (name_from, multip_from, role_from)).
            map_entry name_from (\<lambda>cflat. cflat \<lparr> ClassRaw_own := (role_to,
              OclTy_class (ocl_ty_class_ext const_oid ass_oid n_rel
                (ocl_ty_class_node_ext cpt_from multip_from role_from name_from ())
                (ocl_ty_class_node_ext cpt_to multip_to (Some role_to) name_to ())
                ())) # ClassRaw_own cflat \<rparr>))
         | _ \<Rightarrow> \<lambda>_. id))
        l_rel) (List_mapi Pair l_ass) rbt)) in
  class_unflat_aux
    (List.fold (\<lambda> cflat. insert (ClassRaw_name cflat) (ClassRaw_own cflat)) l empty)
    (List.fold (\<lambda> cflat. case ClassRaw_inh cflat of Some k \<Rightarrow> modify_def [] k (\<lambda>l. ClassRaw_name cflat # l) | _ \<Rightarrow> id) l empty)
    empty
    const_oclany)"

definition "apply_optim_ass_arity ty_obj v =
  (if TyObj_ass_arity ty_obj \<le> 2 then None
   else Some v)"

definition "is_higher_order = (\<lambda> OclTy_collection _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition "parse_ty_raw = (\<lambda> OclTy_raw s \<Rightarrow> (case s of ''int'' \<Rightarrow> OclTy_base_integer)
                            | x \<Rightarrow> x)"

fun_quick str_of_ty where
    "str_of_ty OclTy_base_void = ''Void''"
   |"str_of_ty OclTy_base_boolean = ''Boolean''"
   |"str_of_ty OclTy_base_integer = ''Integer''"
   |"str_of_ty OclTy_base_unlimitednatural = ''UnlimitedNatural''"
   |"str_of_ty OclTy_base_real = ''Real''"
   |"str_of_ty OclTy_base_string = ''String''"
   |"str_of_ty (OclTy_collection Set ocl_ty) = flatten [''Set('', str_of_ty ocl_ty,'')'']"
   |"str_of_ty (OclTy_collection Sequence ocl_ty) = flatten [''Sequence('', str_of_ty ocl_ty,'')'']"
   |"str_of_ty (OclTy_raw s) = flatten [unicode_acute, s, unicode_acute]"

definition "ty_void = str_of_ty OclTy_base_void"
definition "ty_boolean = str_of_ty OclTy_base_boolean"
definition "ty_integer = str_of_ty OclTy_base_integer"
definition "ty_unlimitednatural = str_of_ty OclTy_base_unlimitednatural"
definition "ty_real = str_of_ty OclTy_base_real"
definition "ty_string = str_of_ty OclTy_base_string"

fun_quick str_hol_of_ty where
    "str_hol_of_ty OclTy_base_void = ''unit''"
   |"str_hol_of_ty OclTy_base_boolean = ''bool''"
   |"str_hol_of_ty OclTy_base_integer = ''int''"
   |"str_hol_of_ty OclTy_base_unlimitednatural = ''nat''"
   |"str_hol_of_ty OclTy_base_real = ''real''"
   |"str_hol_of_ty OclTy_base_string = ''string''"
   |"str_hol_of_ty (OclTy_class ty_obj) = flatten [TyObj_name ty_obj, '' '', const_oid_list]"
   |"str_hol_of_ty (OclTy_raw s) = s"

definition "print_infra_type_synonym_class_set_name name = ''Set_'' @@ name"

fun_quick print_ctxt_ty where
   "print_ctxt_ty c = (\<lambda> OclTy_collection Set t \<Rightarrow> print_infra_type_synonym_class_set_name (print_ctxt_ty t)
                       | OclTy_raw t \<Rightarrow> t
                       | OclTy_base_void \<Rightarrow> str_of_ty c
                       | OclTy_base_boolean \<Rightarrow> str_of_ty c
                       | OclTy_base_integer \<Rightarrow> str_of_ty c
                       | OclTy_base_unlimitednatural \<Rightarrow> str_of_ty c
                       | OclTy_base_real \<Rightarrow> str_of_ty c
                       | OclTy_base_string \<Rightarrow> str_of_ty c) c"

fun_quick get_class_hierarchy_strict_aux where
   "get_class_hierarchy_strict_aux dataty l_res =
   (List.fold
     (\<lambda> OclClass name l_attr dataty \<Rightarrow> \<lambda> l_res.
       get_class_hierarchy_strict_aux dataty (OclClass name l_attr dataty # l_res))
     dataty
     l_res)"
definition "get_class_hierarchy_strict d = get_class_hierarchy_strict_aux d []"

fun_quick get_class_hierarchy'_aux where
   "get_class_hierarchy'_aux l_res (OclClass name l_attr dataty) =
   (let l_res = OclClass name l_attr dataty # l_res in
    case dataty of [] \<Rightarrow> rev l_res
                 | dataty \<Rightarrow> List.fold (\<lambda>x acc. get_class_hierarchy'_aux acc x) dataty l_res)"
definition "get_class_hierarchy' = get_class_hierarchy'_aux []"

definition "get_class_hierarchy e = List_map (\<lambda> OclClass n l _ \<Rightarrow> (n, l)) (get_class_hierarchy' e)"
definition "get_class_hierarchy_sub = (\<lambda> None \<Rightarrow> []
                                       | Some next_dataty \<Rightarrow> get_class_hierarchy next_dataty)"
definition "get_class_hierarchy_sub' = (\<lambda> None \<Rightarrow> []
                                        | Some next_dataty \<Rightarrow> get_class_hierarchy' next_dataty)"

datatype position = EQ (* equal *) | LT (* less *) | GT (* greater *) | UN' (* uncomparable *)

fun_quick fold_less_gen where "fold_less_gen f_gen f_jump f l = (case l of
    x # xs \<Rightarrow> \<lambda>acc. fold_less_gen f_gen f_jump f xs (f_gen (f x) xs (f_jump acc))
  | [] \<Rightarrow> id)"

definition "fold_less2 = fold_less_gen List.fold"

section{* Translation of AST *}

definition "var_in_pre_state = ''in_pre_state''"
definition "var_in_post_state = ''in_post_state''"
definition "var_at_when_hol_post = ''''"
definition "var_at_when_hol_pre = ''at_pre''"
definition "var_at_when_ocl_post = ''''"
definition "var_at_when_ocl_pre = ''@pre''"

datatype 'a tmp_sub = Tsub 'a
record 'a inheritance =
  Inh :: 'a
  Inh_sib :: "('a \<times> 'a list (* flat version of the 1st component *)) list" (* sibling *)
  Inh_sib_unflat :: "'a list" (* sibling *)
datatype 'a tmp_inh = Tinh 'a
datatype 'a tmp_univ = Tuniv 'a
definition "of_inh = (\<lambda>Tinh l \<Rightarrow> l)"
definition "of_linh = List_map Inh"
definition "of_linh_sib l = flatten (List_map snd (flatten (List_map Inh_sib l)))"
definition "of_sub = (\<lambda>Tsub l \<Rightarrow> l)"
definition "of_univ = (\<lambda>Tuniv l \<Rightarrow> l)"
definition "map_inh f = (\<lambda>Tinh l \<Rightarrow> Tinh (f l))"
definition "map_linh f cl = \<lparr> Inh = f (Inh cl)
                            , Inh_sib = List_map (map_pair f (List_map f)) (Inh_sib cl)
                            , Inh_sib_unflat = List_map f (Inh_sib_unflat cl) \<rparr>"

fun_quick fold_class_gen_aux where
   "fold_class_gen_aux l_inh f accu (OclClass name l_attr dataty) =
 (let accu = f (\<lambda>s. s @@ isub_of_str name)
               name
               l_attr
               (Tinh l_inh)
               (Tsub (get_class_hierarchy_strict dataty)) (* order: bfs or dfs (modulo reversing) *)
               dataty
               accu in
  case dataty of [] \<Rightarrow> accu
               | _ \<Rightarrow>
    fst (List.fold
       (\<lambda> node (accu, l_inh_l, l_inh_r).
         ( fold_class_gen_aux
             ( \<lparr> Inh = OclClass name l_attr dataty
               , Inh_sib = flatten (List_map (List_map (\<lambda>l. (l, get_class_hierarchy' l))) [l_inh_l, tl l_inh_r])
               , Inh_sib_unflat = flatten [l_inh_l, tl l_inh_r] \<rparr>
             # l_inh)
             f accu node
         , hd l_inh_r # l_inh_l
         , tl l_inh_r))
      dataty
      (accu, [], dataty)))"

definition "fold_class_gen f accu expr =
 (let (l_res, accu) =
    fold_class_gen_aux
      []
      (\<lambda> isub_name name l_attr l_inh l_subtree next_dataty (l_res, accu).
        let (r, accu) = f isub_name name l_attr l_inh l_subtree next_dataty accu in
        (r # l_res, accu))
      ([], accu)
      expr in
  (flatten l_res, accu))"

definition "map_class_gen f = fst o fold_class_gen
  (\<lambda> isub_name name l_attr l_inh l_subtree last_d. \<lambda> () \<Rightarrow>
    (f isub_name name l_attr l_inh l_subtree last_d, ())) ()"

definition "add_hierarchy f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (Tuniv (List_map fst (get_class_hierarchy x))))"
definition "add_hierarchy' f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (Tuniv (get_class_hierarchy x)))"
definition "add_hierarchy'' f x = (\<lambda>isub_name name l_attr _ _ _. f isub_name name (Tuniv (get_class_hierarchy x)) l_attr)"
definition "add_hierarchy''' f x = (\<lambda>isub_name name l_attr l_inh _ next_dataty. f isub_name name (Tuniv (get_class_hierarchy x)) l_attr (map_inh (List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) o of_linh) l_inh) next_dataty)"
definition "add_hierarchy'''' f x = (\<lambda>isub_name name l_attr l_inh l_subtree _. f isub_name name (Tuniv (get_class_hierarchy x)) l_attr (map_inh (List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) o of_linh) l_inh) l_subtree)"
definition "add_hierarchy''''' f = (\<lambda>isub_name name l_attr l_inh l_subtree. f isub_name name l_attr (of_inh l_inh) (of_sub l_subtree))"
definition "map_class f = map_class_gen (\<lambda>isub_name name l_attr l_inh l_subtree next_dataty. [f isub_name name l_attr l_inh (Tsub (List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) (of_sub l_subtree))) next_dataty])"
definition "map_class' f = map_class_gen (\<lambda>isub_name name l_attr l_inh l_subtree next_dataty. [f isub_name name l_attr l_inh l_subtree next_dataty])"
definition "fold_class f = fold_class_gen (\<lambda>isub_name name l_attr l_inh l_subtree next_dataty accu. let (x, accu) = f isub_name name l_attr (map_inh of_linh l_inh) (Tsub (List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) (of_sub l_subtree))) next_dataty accu in ([x], accu))"
definition "map_class_gen_h f x = map_class_gen (add_hierarchy f x) x"
definition "map_class_gen_h' f x = map_class_gen (add_hierarchy' f x) x"
definition "map_class_gen_h'' f x = map_class_gen (add_hierarchy'' f x) x"
definition "map_class_gen_h''' f x = map_class_gen (add_hierarchy''' f x) x"
definition "map_class_gen_h'''' f x = map_class_gen (add_hierarchy'''' (\<lambda>isub_name name l_inherited l_attr l_inh l_subtree. f isub_name name l_inherited l_attr l_inh (Tsub (List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) (of_sub l_subtree)))) x) x"
definition "map_class_gen_h''''' f x = map_class_gen (add_hierarchy''''' f) x"
definition "map_class_h f x = map_class (add_hierarchy f x) x"
definition "map_class_h' f x = map_class (add_hierarchy' f x) x"
definition "map_class_h'' f x = map_class (add_hierarchy'' f x) x"
definition "map_class_h''' f x = map_class (add_hierarchy''' f x) x"
definition "map_class_h'''' f x = map_class (add_hierarchy'''' f x) x"
definition "map_class_h''''' f x = map_class' (add_hierarchy''''' f) x"
definition "map_class_arg_only f = map_class_gen (\<lambda> isub_name name l_attr _ _ _. case l_attr of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name l)"
definition "map_class_arg_only' f = map_class_gen (\<lambda> isub_name name l_attr l_inh l_subtree _.
  case filter (\<lambda> OclClass _ [] _ \<Rightarrow> False | _ \<Rightarrow> True) (of_linh (of_inh l_inh)) of
    [] \<Rightarrow> []
  | l \<Rightarrow> f isub_name name (l_attr, Tinh l, l_subtree))"
definition "map_class_arg_only0 f1 f2 u = map_class_arg_only f1 u @@ map_class_arg_only' f2 u"
definition "map_class_arg_only_var0 = (\<lambda>f_expr f_app f_lattr isub_name name l_attr.
  flatten (flatten (
    List_map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      flatten (List_map (\<lambda> l_attr. List_map (\<lambda>(attr_name, attr_ty).
        f_app
          isub_name
          name
          (var_in_when_state, dot_at_when)
          attr_ty
          (\<lambda>s. s @@ isup_of_str attr_name)
          (\<lambda>s. f_expr s
            [ case case attr_ty of
                     OclTy_class ty_obj \<Rightarrow>
                       apply_optim_ass_arity ty_obj
                       (bug_ocaml_extraction (let ty_obj = TyObj_from ty_obj in
                       case TyObjN_role_name ty_obj of
                          None => natural_of_str (TyObjN_ass_switch ty_obj)
                        | Some s => s))
                   | _ \<Rightarrow> None of
                None \<Rightarrow> mk_dot attr_name attr_when
              | Some s2 \<Rightarrow> mk_dot_comment attr_name attr_when s2 ])) l_attr)
     (f_lattr l_attr)))
   [ (var_in_post_state, var_at_when_hol_post, var_at_when_ocl_post)
   , (var_in_pre_state, var_at_when_hol_pre, var_at_when_ocl_pre)])))"
definition "map_class_arg_only_var_gen f_expr f1 f2 = map_class_arg_only0 (map_class_arg_only_var0 f_expr f1 (\<lambda>l. [l])) (map_class_arg_only_var0 f_expr f2 (\<lambda> (_, Tinh l, _) \<Rightarrow> List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) l))"
definition "map_class_arg_only_var'_gen f_expr f = map_class_arg_only0 (map_class_arg_only_var0 f_expr f (\<lambda>l. [l])) (map_class_arg_only_var0 f_expr f (\<lambda> (_, Tinh l, _) \<Rightarrow> List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) l))"
definition "map_class_one f_l f expr =
  (case f_l (fst (fold_class (\<lambda>isub_name name l_attr l_inh l_inh_sib next_dataty _. ((isub_name, name, l_attr, l_inh, l_inh_sib, next_dataty), ())) () expr)) of
     (isub_name, name, l_attr, l_inh, l_inh_sib, next_dataty) # _ \<Rightarrow>
     f isub_name name l_attr l_inh l_inh_sib next_dataty)"
definition "map_class_top = map_class_one rev"
definition "get_hierarchy_map f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  List_map (\<lambda>name1. List_map (\<lambda>name2. List_map (f name1 name2) l3) l2) l1))"

definition "class_arity = keys o (\<lambda>l. List.fold (\<lambda>x. insert x ()) l empty) o
  flatten o flatten o map_class (\<lambda> _ _ l_attr _ _ _.
    List_map (\<lambda> (_, OclTy_class ty_obj) \<Rightarrow> [TyObj_ass_arity ty_obj]
              | _ \<Rightarrow> []) l_attr)"

definition "map_class_gen_h'_inh f =
  map_class_gen_h''''' (\<lambda>isub_name name _ l_inh l_subtree _.
    let l_mem = \<lambda>l. List.member (List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) l) in
    f isub_name
      name
      (\<lambda>n. if n = name then EQ else
           if l_mem (of_linh l_inh) n then GT else
           if l_mem l_subtree n then LT else
           UN'))"

definition "m_class_gen2 base_attr f print =
 (let m_base_attr = \<lambda> OclClass n l b \<Rightarrow> OclClass n (base_attr l) b
    ; f_base_attr = List_map m_base_attr in
  map_class_gen_h''''' (\<lambda>isub_name name nl_attr l_inh l_subtree next_dataty.
    f name
      l_inh
      l_subtree
      (flatten (flatten (List_map (
        let print_astype =
              print
                (List_map (map_linh m_base_attr) l_inh)
                (f_base_attr l_subtree)
                next_dataty
          ; nl_attr = base_attr nl_attr in
        (\<lambda>(l_hierarchy, l).
          List_map
            (print_astype l_hierarchy (isub_name, name, nl_attr) o m_base_attr)
            l))
        [ (EQ, [OclClass name nl_attr next_dataty])
        , (GT, of_linh l_inh)
        , (LT, l_subtree)
        , (UN', of_linh_sib l_inh) ])))))"

definition "f_less2 =
  (\<lambda>f l. rev (fst (fold_less2 (\<lambda>(l, _). (l, None)) (\<lambda>x y (l, acc). (f x y acc # l, Some y)) l ([], None))))
    (\<lambda>a b _. (a,b))"

definition "m_class_gen3_GE base_attr f print =
 (let m_base_attr = \<lambda> OclClass n l b \<Rightarrow> OclClass n (base_attr l) b
    ; f_base_attr = List_map m_base_attr in
  map_class_gen_h''''' (\<lambda>isub_name name nl_attr l_inh l_subtree next_dataty.
    let print_astype =
         print
           (List_map (map_linh m_base_attr) l_inh)
           (f_base_attr l_subtree)
           next_dataty in
    flatten
      [ f (flatten (List_map (\<lambda> (l_hierarchy, l).
          List_map (\<lambda> OclClass h_name _ _ \<Rightarrow> print_astype name h_name h_name) l)
          [ (GT, of_linh l_inh) ]))
      , f (flatten (List_map (\<lambda> (l_hierarchy, l).
          List_map (\<lambda> (h_name, hh_name). print_astype name h_name hh_name) (f_less2 (List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) l)))
          [ (GT, of_linh l_inh) ]))
      , f (flatten (List_map (\<lambda> (l_hierarchy, l).
          flatten (List_map (\<lambda> OclClass h_name _ _ \<Rightarrow>
            List_map (\<lambda> OclClass sib_name _ _ \<Rightarrow> print_astype name sib_name h_name) (of_linh_sib l_inh)) l))
          [ (GT, of_linh l_inh) ])) ]))"

definition "m_class_gen3 base_attr f print =
 (let m_base_attr = \<lambda> OclClass n l b \<Rightarrow> OclClass n (base_attr l) b
    ; f_base_attr = List_map m_base_attr in
  map_class_gen_h''''' (\<lambda>isub_name name nl_attr l_inh l_subtree next_dataty.
    let print_astype =
         print
           (List_map (map_linh m_base_attr) l_inh)
           (f_base_attr l_subtree)
           next_dataty in
    f (flatten (
        let l_tree = List_map (\<lambda>(cmp,l). (cmp, f_base_attr l))
          [ (EQ, [OclClass name nl_attr next_dataty])
          , (GT, of_linh l_inh)
          , (LT, l_subtree)
          , (UN', of_linh_sib l_inh) ] in
        (\<lambda>f. flatten (List_map (\<lambda> (l_hierarchy, l). List_map (f l_hierarchy) l) l_tree))
        (\<lambda> l_hierarchy1. \<lambda> OclClass h_name hl_attr hb \<Rightarrow>
        (\<lambda>f. flatten (List_map (\<lambda> (l_hierarchy, l). List_map (f l_hierarchy) l) l_tree))
        (\<lambda> l_hierarchy2. \<lambda> OclClass hh_name hhl_attr hhb \<Rightarrow>
          print_astype
            name
            h_name
            hh_name))))))"

definition "m_class_default = (\<lambda>_ _ _. id)"
definition "m_class base_attr f print = m_class_gen2 base_attr f (\<lambda>_ _ _. print)"
definition "m_class3_GE base_attr f print = m_class_gen3_GE base_attr f (\<lambda>_ _ _. print)"
definition "m_class' base_attr print =
  m_class base_attr m_class_default (\<lambda> l_hierarchy x0 x1. [ print l_hierarchy x0 x1 ])"

definition "map_class_nupl2'_inh f = List.map_filter id o
 (m_class' id (\<lambda>compare (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    if compare = GT then Some (f name h_name) else None))"

definition "map_class_nupl2'_inh_large f = List.map_filter id o
 (m_class' id (\<lambda>compare (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    if compare = GT
     | compare = UN' then Some (f name h_name) else None))"

definition "map_class_nupl2''_inh f = List.map_filter id o
 (m_class_gen2 id m_class_default (\<lambda> l_inh _ _ compare (_, name, _). \<lambda> OclClass h_name _ h_subtree \<Rightarrow>
    [ if compare = GT then
        Some (f name h_name (List_map (\<lambda>x. (x, List.member (of_linh l_inh) x)) h_subtree))
      else
        None]))"

definition "map_class_nupl2l'_inh_gen f = List.map_filter id o
 (m_class_gen2 id m_class_default (\<lambda> l_inh l_subtree _ compare (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    [ if compare = GT then
        Some (f l_subtree name (fst (List.fold (\<lambda>x. \<lambda> (l, True, prev_x) \<Rightarrow> (l, True, prev_x)
                                          | (l, False, prev_x) \<Rightarrow>
                                              case Inh x of OclClass n _ next_d \<Rightarrow>
                                              ( (x, List_map (\<lambda> OclClass n l next_d \<Rightarrow>
                                                               (OclClass n l next_d, n = prev_x))
                                                             next_d)
                                                # l
                                              , n = h_name
                                              , n))
                                     l_inh
                                     ([], False, name))))
      else
        None]))"

definition "map_class_nupl2l'_inh f = map_class_nupl2l'_inh_gen (\<lambda>_ x l. f x l)"

definition "map_class_nupl3'_LE'_inh f = flatten o map_class_nupl2l'_inh_gen (\<lambda>l_subtree x l.
  List_map
    (\<lambda>name_bot. f name_bot x l)
    (x # List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) l_subtree))"

definition "map_class_nupl3'_GE_inh = m_class3_GE id id"

definition "map_class_inh l_inherited = List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh (map_inh of_linh l_inherited))"

end
