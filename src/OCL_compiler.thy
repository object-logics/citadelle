(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler.thy ---
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

theory  OCL_compiler
imports OCL_compiler_aux
        "~~/src/HOL/Library/Code_Char"
  keywords (* hol syntax *)
           "lazy_code_printing" "apply_code_printing" "apply_code_printing_reflect" "fun_sorry" "fun_quick"

           :: thy_decl
begin

section{* Preliminaries *}

subsection{* Misc. (to be removed) *}
definition "bug_ocaml_extraction = id"
definition "bug_scala_extraction = id"
  (* In this theory, this identifier can be removed everywhere it is used.
     However without this, there is a syntax error when the code is extracted to OCaml. *)

subsection{* Infra-structure that skip lengthy termination proofs *}

ML{*
structure Fun_quick = struct
val quick_dirty = false
  (* false: "fun_quick" behaves as "fun"
     true: "fun_quick" behaves as "fun", but it proves completeness and termination with "sorry" *)

val proof_by_patauto = Proof.global_terminal_proof
  ( ( Method.Then
        [ Method.Basic (fn ctxt => SIMPLE_METHOD (Pat_Completeness.pat_completeness_tac ctxt 1) )
        , Method.Basic (fn ctxt => SIMPLE_METHOD (auto_tac (ctxt addsimps [])))]
    , (Position.none, Position.none))
  , NONE)
val proof_by_sorry = Proof.global_skip_proof true

fun mk_fun quick_dirty cmd_spec tac =
  Outer_Syntax.local_theory' cmd_spec
    "define general recursive functions (short version)"
    (Function_Common.function_parser
      (if quick_dirty then
         Function_Common.FunctionConfig { sequential=true, default=NONE
                                        , domintros=false, partials=true}
       else
         Function_Fun.fun_config)
      >> (if quick_dirty then
            fn ((config, fixes), statements) => fn b => fn ctxt =>
            ctxt |> Function.function_cmd fixes statements config b
                 |> tac
                 |> Function.termination_cmd NONE
                 |> proof_by_sorry
          else
            fn ((config, fixes), statements) => Function_Fun.add_fun_cmd fixes statements config))

val () = mk_fun quick_dirty @{command_spec "fun_quick"} proof_by_sorry
val () = mk_fun true @{command_spec "fun_sorry"} proof_by_patauto
end
*}


section{* Lambda_pure Meta-Model aka. AST definition of Lambda_pure *}

subsection{* type definition *}

datatype pure_indexname = PureIndexname string nat
datatype pure_class = PureClass string
datatype pure_sort = PureSort "pure_class list"
datatype pure_typ =
  PureType string "pure_typ list" |
  PureTFree string pure_sort |
  PureTVar pure_indexname pure_sort
datatype pure_term =
  PureConst string pure_typ |
  PureFree string pure_typ |
  PureVar pure_indexname pure_typ |
  PureBound nat |
  PureAbs string pure_typ pure_term |
  PureApp pure_term pure_term (infixl "$" 200)

subsection{* *}

fun_quick map_Const where
   "map_Const f expr = (\<lambda> PureConst s ty \<Rightarrow> PureConst (f s ty) ty
                        | PureFree s ty \<Rightarrow> PureFree s ty
                        | PureVar i ty \<Rightarrow> PureVar i ty
                        | PureBound n \<Rightarrow> PureBound n
                        | PureAbs s ty term \<Rightarrow> PureAbs s ty (map_Const f term)
                        | PureApp term1 term2 \<Rightarrow> PureApp (map_Const f term1)
                                                         (map_Const f term2))
                        expr"

section{* OCL Meta-Model aka. AST definition of OCL *}

subsection{* type definition *}

datatype ocl_collection =   Set | Sequence

datatype ocl_multiplicity_single = Mult_nat nat
                                 | Mult_star

datatype ocl_multiplicity = OclMult "(ocl_multiplicity_single \<times> ocl_multiplicity_single option) list"

record ocl_ty_class_node =  TyObjN_ass_switch :: nat
                            TyObjN_role_multip :: ocl_multiplicity
                            TyObjN_role_name :: "string option"
                            TyObjN_role_ty :: string
record ocl_ty_class =       TyObj_name :: string
                            TyObj_ass_id :: nat
                            TyObj_ass_arity :: nat
                            TyObj_from :: ocl_ty_class_node
                            TyObj_to :: ocl_ty_class_node
datatype ocl_ty =           OclTy_boolean
                          | OclTy_integer
                          | OclTy_class ocl_ty_class
                          | OclTy_collection ocl_collection ocl_ty
                          | OclTy_raw string (* denoting raw HOL-type.*)


record ocl_operation = Op_args :: "(string \<times> ocl_ty) list"
                       Op_result :: ocl_ty
                       Op_pre :: "(string \<times> string) list"
                       Op_post :: "(string \<times> string) list"

datatype ocl_class =   OclClass
                         string (* name of the class *)
                         "(string (* name *) \<times> ocl_ty) list" (* attribute *)
                         (*"(string (* name *) \<times> ocl_operation) list" (* contract *)
                         "(string (* name *) \<times> string) list" (* invariant *) *)
                         "ocl_class list" (* link to subclasses *)

record ocl_class_raw = ClassRaw_name :: string
                       ClassRaw_own :: "(string (* name *) \<times> ocl_ty) list" (* attribute *)
                      (*ClassRaw_contract :: "(string (* name *) \<times> ocl_operation) list" (* contract *)
                       ClassRaw_inv :: "(string (* name *) \<times> string) list" (* invariant *) *)
                       ClassRaw_inh :: "string option" (* superclass *)



datatype ocl_association_type = OclAssTy_association
                              | OclAssTy_composition
                              | OclAssTy_aggregation
record ocl_association =        OclAss_type     :: ocl_association_type
                                OclAss_relation :: "( string (* name class *)
                                                    \<times> ocl_multiplicity (* multiplicity *)
                                                    \<times> string option (* role *)) list"
datatype ocl_ass_class =        OclAssClass ocl_association ocl_class_raw

datatype ocl_data_shallow_base = ShallB_str string
                               | ShallB_self internal_oid
datatype ocl_data_shallow =      Shall_base ocl_data_shallow_base
                               | Shall_list "ocl_data_shallow_base list"

datatype 'a ocl_list_attr = OclAttrNoCast 'a (* inh, own *)
                          | OclAttrCast
                              string (* cast from *)
                              "'a ocl_list_attr" (* cast entity *)
                              'a (* inh, own *)

record ocl_instance_single = Inst_name :: string
                             Inst_ty :: string (* type *)
                             Inst_attr :: "((string (*name*) \<times> ocl_data_shallow) list) (* inh and own *)
                                           ocl_list_attr"

datatype ocl_instance = OclInstance "ocl_instance_single list" (* mutual recursive *)

datatype ocl_def_int = OclDefI "string list"

datatype 'a ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                               | OclDefCoreSkip
                               | OclDefCoreBinding 'a

datatype ocl_def_state = OclDefSt  string (* name *)
                                  "string (* name *) ocl_def_state_core list"

datatype ocl_def_pre_post = OclDefPP
                              string (* pre *)
                              string (* post *)

datatype ocl_ctxt_prefix = OclCtxtPre | OclCtxtPost

datatype ocl_ctxt_term = T_pure pure_term
                       | T_to_be_parsed string

record ocl_ctxt_pre_post = Ctxt_ty :: string (* class ty *)
                           Ctxt_fun_name :: string (* function name *)
                           Ctxt_fun_ty_arg :: "(string (* arg name *) \<times> ocl_ty) list"
                           Ctxt_fun_ty_out :: "ocl_ty option" (* None : Void *)
                           Ctxt_expr :: "(ocl_ctxt_prefix \<times> ocl_ctxt_term (* expr *)) list"

type_synonym ocl_ctxt2_pre_post = ocl_ctxt_pre_post

record ocl_ctxt_inv =      Ctxt_inv_ty :: string
                           Ctxt_inv_expr :: "(string (* name *) \<times> ocl_ctxt_term (* expr *)) list"

type_synonym ocl_ctxt2_inv = ocl_ctxt_inv

datatype ocl_flush_all = OclFlushAll

(* le meta-model de "tout le monde" - frederic. *)
datatype ocl_deep_embed_ast = OclAstClassRaw ocl_class_raw
                            | OclAstAssociation ocl_association
                            | OclAstAssClass ocl_ass_class
                            | OclAstInstance ocl_instance
                            | OclAstDefInt ocl_def_int
                            | OclAstDefState ocl_def_state
                            | OclAstDefPrePost ocl_def_pre_post
                            | OclAstCtxtPrePost ocl_ctxt_pre_post
                            | OclAstCtxt2PrePost ocl_ctxt2_pre_post
                            | OclAstCtxtInv ocl_ctxt_inv
                            | OclAstCtxt2Inv ocl_ctxt2_inv
                            | OclAstFlushAll ocl_flush_all

datatype ocl_deep_mode = Gen_design | Gen_analysis


record ocl_compiler_config =  D_disable_thy_output :: bool
                              D_file_out_path_dep :: "(string (* theory *)
                                                      \<times> string list (* imports *)
                                                      \<times> string (* import optional (compiler bootstrap) *)) option"
                              D_oid_start :: internal_oids
                              D_output_position :: "nat \<times> nat"
                              D_design_analysis :: ocl_deep_mode
                              D_class_spec :: "ocl_class option"
                                              (* last class considered for the generation *)
                              D_ocl_env :: "ocl_deep_embed_ast list"
                              D_instance_rbt :: "(string (* name (as key for rbt) *)
                                                 \<times> ocl_instance_single
                                                 \<times> internal_oid) list"
                                                (* instance namespace environment *)
                              D_state_rbt :: "(string (* name (as key for rbt) *)
                                              \<times> (internal_oids
                                              \<times> (string (* name *)
                                                  \<times> ocl_instance_single (* alias *))
                                                      ocl_def_state_core) list) list"
                                             (* state namespace environment *)
                              D_generation_syntax_shallow :: bool (* true : the header should import the compiler for bootstrapping *)
                              D_accessor_rbt :: " string (* name of the constant added *) list (* pre *)
                                                \<times> string (* name of the constant added *) list (* post *)"

subsection{* Auxilliary *}

definition "map_ctxt2_term f = (\<lambda>
    OclAstCtxt2PrePost ocl \<Rightarrow> OclAstCtxt2PrePost (Ctxt_expr_update (List_map (\<lambda>(s, x). (s, f x))) ocl)
  | OclAstCtxt2Inv ocl \<Rightarrow> OclAstCtxt2Inv (Ctxt_inv_expr_update (List_map (\<lambda>(s, x). (s, f x))) ocl)
  | x \<Rightarrow> x)"

definition "ocl_compiler_config_more_map f ocl =
            ocl_compiler_config.extend  (ocl_compiler_config.truncate ocl) (f (ocl_compiler_config.more ocl))"




subsection{* Class Translation Preliminaries *}

definition "const_oid = ''oid''"
definition "const_oid_list = ''list''"
definition "const_oclany = ''OclAny''"

definition "single_multip = (\<lambda> OclMult l \<Rightarrow>
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

definition "class_unflat l =
 (let l =
    let rbt = (* fold classes:
                 set ''OclAny'' as default inherited class (for all classes linking to zero inherited classes) *)
              insert
                const_oclany
                (ocl_class_raw.make const_oclany [] None)
                (List.fold
                  (\<lambda> cflat \<Rightarrow>
                    insert (ClassRaw_name cflat) (cflat \<lparr> ClassRaw_inh := case ClassRaw_inh cflat of None \<Rightarrow> Some const_oclany | x \<Rightarrow> x \<rparr>))
                  (List.map_filter (\<lambda> OclAstClassRaw cflat \<Rightarrow> Some cflat
                                    | OclAstAssClass (OclAssClass _ cflat) \<Rightarrow> Some cflat
                                    | _ \<Rightarrow> None) l)
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
        l_rel) (List_mapi Pair (List.map_filter (\<lambda> OclAstAssociation ass \<Rightarrow> Some ass
                                                 | OclAstAssClass (OclAssClass ass _) \<Rightarrow> Some ass
                                                 | _ \<Rightarrow> None) l)) rbt)) in
  class_unflat_aux
    (List.fold (\<lambda> cflat. insert (ClassRaw_name cflat) (ClassRaw_own cflat)) l empty)
    (List.fold (\<lambda> cflat. case ClassRaw_inh cflat of Some k \<Rightarrow> modify_def [] k (\<lambda>l. ClassRaw_name cflat # l) | _ \<Rightarrow> id) l empty)
    empty
    const_oclany)"

definition "apply_optim_ass_arity ty_obj v =
  (if TyObj_ass_arity ty_obj \<le> 2 then None
   else Some v)"

fun_quick str_of_ty where
    "str_of_ty OclTy_boolean = ''Boolean''"
   |"str_of_ty OclTy_integer = ''Integer''"
   |"str_of_ty (OclTy_class ty_obj) = flatten [TyObj_name ty_obj, '' '', const_oid_list]"
   |"str_of_ty (OclTy_collection Set ocl_ty) = flatten [''Set('', str_of_ty ocl_ty,'')'']"
   |"str_of_ty (OclTy_collection Sequence ocl_ty) = flatten [''Sequence('', str_of_ty ocl_ty,'')'']"
   |"str_of_ty (OclTy_raw s) = s"

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

section{* SML Meta-Model aka. AST definition of SML *}
subsection{* type definition *}

datatype sml_expr = Sexpr_string "string list"
                  | Sexpr_rewrite_val sml_expr (* left *) string (* symb rewriting *) sml_expr (* right *)
                  | Sexpr_rewrite_fun sml_expr (* left *) string (* symb rewriting *) sml_expr (* right *)
                  | Sexpr_basic "string list"
                  | Sexpr_oid string (* prefix *) internal_oid
                  | Sexpr_binop sml_expr string sml_expr
                  | Sexpr_annot sml_expr string (* type *)
                  | Sexpr_function "(sml_expr (* pattern *) \<times> sml_expr (* to return *)) list"
                  | Sexpr_apply string "sml_expr list"
                  | Sexpr_paren string (* left *) string (* right *) sml_expr
                  | Sexpr_let_open string sml_expr

datatype sml_expr_extended = Sexpr_extended sml_expr
                           | Sexpr_ocl ocl_compiler_config

section{* Isabelle/HOL Meta-Model aka. AST definition of HOL *}
subsection{* type definition *}

datatype hol_simplety = Opt string | Raw string

datatype hol_dataty = Datatype string (* name *)
                           "(string (* name *) \<times> hol_simplety list (* arguments *)) list" (* constructors *)

datatype hol_raw_ty =
   Ty_apply hol_raw_ty "hol_raw_ty list"
 | Ty_base string
 | Ty_arrow hol_raw_ty hol_raw_ty
 | Ty_times hol_raw_ty hol_raw_ty

datatype hol_ty_synonym = Type_synonym string (* name *)
                                       hol_raw_ty (* content *)

datatype hol_expr = Expr_case hol_expr (* value *)
                              "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_rewrite hol_expr (* left *) string (* symb rewriting *) hol_expr (* right *)
                  | Expr_basic "string list"
                  | Expr_oid string (* prefix *) internal_oid
                  | Expr_binop hol_expr string hol_expr
                  | Expr_annot0 hol_expr hol_raw_ty
                  | Expr_bind string (* symbol *) "string list" (* arg *) hol_expr
                  | Expr_bind0 string (* symbol *) hol_expr (* arg *) hol_expr
                  | Expr_function "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_apply string "hol_expr list"
                  | Expr_applys hol_expr "hol_expr list"
                  | Expr_preunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_postunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_paren string (* left *) string (* right *) hol_expr
                  | Expr_if_then_else hol_expr hol_expr hol_expr
                  | Expr_inner pure_term (* inner syntax term *)

datatype hol_instantiation_class = Instantiation string (* name *)
                                                 string (* name in definition *)
                                                 hol_expr

datatype hol_defs_overloaded = Defs_overloaded string (* name *) hol_expr (* content *)

datatype hol_consts_class = Consts_raw string (* name *)
                                       hol_raw_ty
                                       string (* ocl 'post' mixfix *)

datatype hol_definition_hol = Definition hol_expr
                            | Definition_abbrev string (* name *) "hol_expr (* syntax extension *) \<times> nat (* priority *)" hol_expr
                            | Definition_abbrev0 string (* name *) hol_expr (* syntax extension *) hol_expr

datatype hol_ntheorem = Thm_str string
                      | Thm_THEN hol_ntheorem hol_ntheorem
                      | Thm_simplified hol_ntheorem hol_ntheorem
                      | Thm_symmetric hol_ntheorem
                      | Thm_where hol_ntheorem "(string \<times> hol_expr) list"
                      | Thm_of hol_ntheorem "hol_expr list"
                      | Thm_OF hol_ntheorem hol_ntheorem

datatype hol_lemmas_simp = Lemmas_simp string (* name *)
                                       "hol_ntheorem list"
                         | Lemmas_simps string (* name *)
                                        "string (* thms *) list"

datatype hol_tactic = Tac_rule hol_ntheorem
                    | Tac_drule hol_ntheorem
                    | Tac_erule hol_ntheorem
                    | Tac_intro "hol_ntheorem list"
                    | Tac_elim hol_ntheorem
                    | Tac_subst_l "string (* nat *) list" (* pos *) hol_ntheorem
                    | Tac_insert "hol_ntheorem list"
                    | Tac_plus "hol_tactic list"
                    | Tac_option "hol_tactic list"
                    | Tac_simp | Tac_simp_add "string list" | Tac_simp_add_del "string list" "string list" | Tac_simp_only "hol_ntheorem list" | Tac_simp_add0 "hol_ntheorem list"
                    | Tac_simp_all | Tac_simp_all_add string
                    | Tac_auto_simp_add "string list"
                    | Tac_auto_simp_add_split "hol_ntheorem list" "string list"
                    | Tac_rename_tac "string list"
                    | Tac_case_tac hol_expr
                    | Tac_blast "nat option"

datatype hol_tactic_last = Tacl_done
                         | Tacl_by "hol_tactic list"
                         | Tacl_sorry

datatype hol_tac_apply = App "hol_tactic list" (* apply (... ',' ...) *)
                       | App_using "hol_ntheorem list" (* using ... *)
                       | App_unfolding "hol_ntheorem list" (* unfolding ... *)
                       | App_let hol_expr (* name *) hol_expr
                       | App_have string (* name *) hol_expr hol_tactic_last
                       | App_fix "string list"

datatype hol_lemma_by = Lemma_by string (* name *) "hol_expr list" (* specification to prove *)
                          "hol_tactic list list" (* tactics : apply (... ',' ...) '\n' apply ... *)
                          hol_tactic_last
                      | Lemma_by_assum string (* name *)
                          "(string (* name *) \<times> bool (* true: add [simp] *) \<times> hol_expr) list" (* specification to prove (assms) *)
                          hol_expr (* specification to prove (conclusion) *)
                          "hol_tac_apply list"
                          hol_tactic_last

datatype hol_axiom = Axiom string (* name *)
                           hol_expr

datatype hol_section_title = Section_title nat (* nesting level *)
                                           string (* content *)

datatype hol_text = Text string

datatype hol_ml = Ml sml_expr

datatype hol_thm = Thm "hol_ntheorem list"

datatype hol_thy = Theory_dataty hol_dataty
                 | Theory_ty_synonym hol_ty_synonym
                 | Theory_instantiation_class hol_instantiation_class
                 | Theory_defs_overloaded hol_defs_overloaded
                 | Theory_consts_class hol_consts_class
                 | Theory_definition_hol hol_definition_hol
                 | Theory_lemmas_simp hol_lemmas_simp
                 | Theory_lemma_by hol_lemma_by
                 | Theory_axiom hol_axiom
                 | Theory_section_title hol_section_title
                 | Theory_text hol_text
                 | Theory_ml hol_ml
                 | Theory_thm hol_thm

datatype hol_generation_syntax = Generation_syntax_shallow ocl_deep_mode

datatype hol_ml_extended = Ml_extended sml_expr_extended

datatype hol_thy_extended = (* pure Isabelle *)
                            Isab_thy hol_thy

                            (* bootstrapping embedded languages *)
                          | Isab_thy_generation_syntax hol_generation_syntax
                          | Isab_thy_ml_extended hol_ml_extended
                          | Isab_thy_ocl_deep_embed_ast ocl_deep_embed_ast

subsection{* ... *}

definition "Thy_dataty = Isab_thy o Theory_dataty"
definition "Thy_ty_synonym = Isab_thy o Theory_ty_synonym"
definition "Thy_instantiation_class = Isab_thy o Theory_instantiation_class"
definition "Thy_defs_overloaded = Isab_thy o Theory_defs_overloaded"
definition "Thy_consts_class = Isab_thy o Theory_consts_class"
definition "Thy_definition_hol = Isab_thy o Theory_definition_hol"
definition "Thy_lemmas_simp = Isab_thy o Theory_lemmas_simp"
definition "Thy_lemma_by = Isab_thy o Theory_lemma_by"
definition "Thy_axiom = Isab_thy o Theory_axiom"
definition "Thy_section_title = Isab_thy o Theory_section_title"
definition "Thy_text = Isab_thy o Theory_text"
definition "Thy_ml = Isab_thy o Theory_ml"
definition "Thy_thm = Isab_thy o Theory_thm"

subsection{* ... *}

definition "wildcard = ''_''"

definition "escape_unicode c = flatten [[Char Nibble5 NibbleC], ''<'', c, ''>'']"

definition "isub_of_str = flatten o List_map (\<lambda>c. escape_unicode ''^sub'' @@ [c])"
definition "isup_of_str = flatten o List_map (\<lambda>c. escape_unicode [char_of_nat (nat_of_char c - 32)])"
definition "lowercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "uppercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then c else char_of_nat (n - 32))"
definition "number_of_str = flatten o List_map (\<lambda>c. escape_unicode ([''zero'', ''one'', ''two'', ''three'', ''four'', ''five'', ''six'', ''seven'', ''eight'', ''nine''] ! (nat_of_char c - 48)))"
definition "nat_raw_of_str = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
fun_quick nat_of_str_aux where
   "nat_of_str_aux l (n :: Nat.nat) = (if n < 10 then n # l else nat_of_str_aux (n mod 10 # l) (n div 10))"
definition "nat_of_str n = nat_raw_of_str (nat_of_str_aux [] n)"
definition "natural_of_str = nat_of_str o nat_of_natural"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, ''_'', isub_of_str x])"
definition "mk_dot s1 s2 = flatten [''.'', s1, s2]"
definition "mk_dot_par_gen dot l_s = flatten [dot, ''('', case l_s of [] \<Rightarrow> '''' | x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. '', '' @@ s) xs) ], '')'']"
definition "mk_dot_par dot s = mk_dot_par_gen dot [s]"
definition "mk_dot_comment s1 s2 s3 = mk_dot s1 (flatten [s2, '' /*'', s3, ''*/''])"

definition "hol_definition s = flatten [s, ''_def'']"
definition "hol_split s = flatten [s, ''.split'']"

subsection{* ... *}

definition "ty_boolean = ''Boolean''"

definition "unicode_AA = escape_unicode ''AA''"
definition "unicode_alpha = escape_unicode ''alpha''"
definition "unicode_and = escape_unicode ''and''"
definition "unicode_And = escape_unicode ''And''"
definition "unicode_bottom = escape_unicode ''bottom''"
definition "unicode_circ = escape_unicode ''circ''"
definition "unicode_delta = escape_unicode ''delta''"
definition "unicode_doteq = escape_unicode ''doteq''"
definition "unicode_equiv = escape_unicode ''equiv''"
definition "unicode_exists = escape_unicode ''exists''"
definition "unicode_forall = escape_unicode ''forall''"
definition "unicode_in = escape_unicode ''in''"
definition "unicode_lambda = escape_unicode ''lambda''"
definition "unicode_lceil = escape_unicode ''lceil''"
definition "unicode_lfloor = escape_unicode ''lfloor''"
definition "unicode_longrightarrow = escape_unicode ''longrightarrow''"
definition "unicode_Longrightarrow = escape_unicode ''Longrightarrow''"
definition "unicode_mapsto = escape_unicode ''mapsto''"
definition "unicode_noteq = escape_unicode ''noteq''"
definition "unicode_not = escape_unicode ''not''"
definition "unicode_or = escape_unicode ''or''"
definition "unicode_rceil = escape_unicode ''rceil''"
definition "unicode_rfloor = escape_unicode ''rfloor''"
definition "unicode_Rightarrow = escape_unicode ''Rightarrow''"
definition "unicode_subseteq = escape_unicode ''subseteq''"
definition "unicode_tau = escape_unicode ''tau''"
definition "unicode_times = escape_unicode ''times''"
definition "unicode_triangleq = escape_unicode ''triangleq''"
definition "unicode_Turnstile = escape_unicode ''Turnstile''"
definition "unicode_upsilon = escape_unicode ''upsilon''"

definition "datatype_ext_name = ''type''"
definition "datatype_name = datatype_ext_name @@ const_oid"
definition "datatype_ext_constr_name = ''mk''"
definition "datatype_constr_name = datatype_ext_constr_name @@ const_oid"
definition "datatype_in = ''in''"

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "const_mixfix dot_ocl name = (let t = \<lambda>s. Char Nibble2 Nibble7 # s in
                                         flatten [dot_ocl, t ''('', name, t '')''])"
definition "const_oid_of s = flatten [''oid_of_'', s]"
definition "dot_oclastype = ''.oclAsType''"
definition "dot_oclistypeof = ''.oclIsTypeOf''"
definition "dot_ocliskindof = ''.oclIsKindOf''"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_in_pre_state = ''in_pre_state''"
definition "var_in_post_state = ''in_post_state''"
definition "var_reconst_basetype = ''reconst_basetype''"
definition "var_oid_uniq = ''oid''"
definition "var_eval_extract = ''eval_extract''"
definition "var_deref = ''deref''"
definition "var_deref_oid = ''deref_oid''"
definition "var_deref_assocs = ''deref_assocs''"
definition "var_deref_assocs_list = ''deref_assocs_list''"
definition "var_inst_assoc = ''inst_assoc''"
definition "var_select = ''select''"
definition "var_select_object = ''select_object''"
definition "var_select_object_set = ''select_object_set''"
definition "var_select_object_set_any = ''select_object_set_any''"
definition "var_choose = ''choose''"
definition "var_switch = ''switch''"
definition "var_assocs = ''assocs''"
definition "var_map_of_list = ''map_of_list''"
definition "var_at_when_hol_post = ''''"
definition "var_at_when_hol_pre = ''at_pre''"
definition "var_at_when_ocl_post = ''''"
definition "var_at_when_ocl_pre = ''@pre''"
definition "var_OclInt = ''OclInt''"

definition "update_D_accessor_rbt_pre f = (\<lambda>(l_pre, l_post). (f l_pre, l_post))"
definition "update_D_accessor_rbt_post f = (\<lambda>(l_pre, l_post). (l_pre, f l_post))"

section{* Translation of AST *}

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
definition "map_class_arg_only_var0 = (\<lambda>f_app f_lattr isub_name name l_attr.
  flatten (flatten (
    List_map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      flatten (List_map (\<lambda> l_attr. List_map (\<lambda>(attr_name, attr_ty).
        f_app
          isub_name
          name
          (var_in_when_state, dot_at_when)
          attr_ty
          (\<lambda>s. s @@ isup_of_str attr_name)
          (\<lambda>s. Expr_postunary s (Expr_basic
            [ case case attr_ty of
                     OclTy_class ty_obj \<Rightarrow>
                       apply_optim_ass_arity ty_obj
                       (bug_ocaml_extraction (let ty_obj = TyObj_from ty_obj in
                       case TyObjN_role_name ty_obj of
                          None => natural_of_str (TyObjN_ass_switch ty_obj)
                        | Some s => s))
                   | _ \<Rightarrow> None of
                None \<Rightarrow> mk_dot attr_name attr_when
              | Some s2 \<Rightarrow> mk_dot_comment attr_name attr_when s2 ]))) l_attr)
     (f_lattr l_attr)))
   [ (var_in_post_state, var_at_when_hol_post, var_at_when_ocl_post)
   , (var_in_pre_state, var_at_when_hol_pre, var_at_when_ocl_pre)])))"
definition "map_class_arg_only_var f1 f2 = map_class_arg_only0 (map_class_arg_only_var0 f1 (\<lambda>l. [l])) (map_class_arg_only_var0 f2 (\<lambda> (_, Tinh l, _) \<Rightarrow> List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) l))"
definition "map_class_arg_only_var' f = map_class_arg_only0 (map_class_arg_only_var0 f (\<lambda>l. [l])) (map_class_arg_only_var0 f (\<lambda> (_, Tinh l, _) \<Rightarrow> List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) l))"
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

definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"
definition "thm_OF s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "thm_simplified s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
definition "Expr_annot e s = Expr_annot0 e (Ty_base s)"
definition "Expr_lambdas = Expr_bind unicode_lambda"
definition "Expr_lambda x = Expr_lambdas [x]"
definition "Expr_lambdas0 = Expr_bind0 unicode_lambda"
definition "Expr_lam x f = Expr_lambdas0 (Expr_basic [x]) (f x)"
definition "Expr_some = Expr_paren unicode_lfloor unicode_rfloor"
definition "Sexpr_none = Sexpr_basic [''NONE'']"
definition "Sexpr_some s = Sexpr_apply ''SOME'' [s]"
definition "Sexpr_option' f l = (case Option.map f l of None \<Rightarrow> Sexpr_none | Some s \<Rightarrow> Sexpr_some s)"
definition "Sexpr_option = Sexpr_option' id"
definition "Expr_parenthesis (* mandatory parenthesis *) = Expr_paren ''('' '')''"
definition "Sexpr_parenthesis (* mandatory parenthesis *) = Sexpr_paren ''('' '')''"
definition "Expr_warning_parenthesis (* optional parenthesis that can be removed but a warning will be raised *) = Expr_parenthesis"
definition "Expr_pat b = Expr_basic [Char Nibble3 NibbleF # b]"
definition "Expr_And x f = Expr_bind0 unicode_And (Expr_basic [x]) (f x)"
definition "Expr_exists x f = Expr_bind0 unicode_exists (Expr_basic [x]) (f x)"
definition "expr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_binop x s) xs x)"
definition "sexpr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Sexpr_binop x s) xs x)"
definition "expr_binop' s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_parenthesis o Expr_binop x s) xs x)"
definition "Expr_set l = (case l of [] \<Rightarrow> Expr_basic [''{}''] | _ \<Rightarrow> Expr_paren ''{'' ''}'' (expr_binop '','' l))"
definition "Expr_oclset l = (case l of [] \<Rightarrow> Expr_basic [''Set{}''] | _ \<Rightarrow> Expr_paren ''Set{'' ''}'' (expr_binop '','' l))"
definition "Expr_list l = (case l of [] \<Rightarrow> Expr_basic [''[]''] | _ \<Rightarrow> Expr_paren ''['' '']'' (expr_binop '','' l))"
definition "Expr_list' f l = Expr_list (List_map f l)"
definition "Sexpr_list l = (case l of [] \<Rightarrow> Sexpr_basic [''[]''] | _ \<Rightarrow> Sexpr_paren ''['' '']'' (sexpr_binop '','' l))"
definition "Sexpr_list' f l = Sexpr_list (List_map f l)"
definition "Expr_pair e1 e2 = Expr_parenthesis (Expr_binop e1 '','' e2)"
definition "Sexpr_pair e1 e2 = Sexpr_parenthesis (Sexpr_binop e1 '','' e2)"
definition "Sexpr_pair' f1 f2 = (\<lambda> (e1, e2) \<Rightarrow> Sexpr_parenthesis (Sexpr_binop (f1 e1) '','' (f2 e2)))"
definition "Expr_string s = Expr_basic [flatten [[Char Nibble2 Nibble2], s, [Char Nibble2 Nibble2]]]"
definition "Consts_value = ''(_)''"
definition "Consts_raw0 s l e o_arg = Consts_raw s l (e @@ (case o_arg of
         None \<Rightarrow> ''''
       | Some arg \<Rightarrow>
           let ap = \<lambda>s. '''('' @@ s @@ ''')'' in
           ap (if arg = 0 then
                ''''
              else
                Consts_value @@ (flatten (List_map (\<lambda>_. '','' @@ Consts_value) (List_upto 2 arg))))))"
definition "Consts s l e = Consts_raw0 s (Ty_arrow (Ty_base (Char Nibble2 Nibble7 # unicode_alpha)) l) e None"
definition "Tac_subst = Tac_subst_l [''0'']"
definition "Tac_auto = Tac_auto_simp_add []"
definition "ty_arrow l = (case rev l of x # xs \<Rightarrow> List.fold Ty_arrow xs x)"

definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_design_analysis ocl
    ; base_attr = (if design_analysis = Gen_design then id else List_filter (\<lambda> (_, OclTy_class _) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, List_map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') ocl)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> ocl. start_map f (fl (D_design_analysis ocl)) ocl)"

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

definition "start_m_gen final f print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class_gen2 base_attr f print expr)"
definition "start_m final f print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class base_attr f print expr)"
definition "start_m' final print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class' base_attr print expr)"
definition "start_m'3_gen final print = start_map'' final o (\<lambda>expr base_attr _ _.
  m_class_gen3 base_attr id print expr)"

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

subsection{* ... *}

definition "activate_simp_optimization = True"

definition "print_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited) in
    [ Datatype
        (isub_name datatype_ext_name)
        (  (rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ isub_of_str x)])) (of_sub l_cons))
        @@ [(isub_name datatype_ext_constr_name, Raw const_oid # flatten ( List_map (List_map (\<lambda>(_, x). Opt (str_of_ty x))) l_inherited))])
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, [ Raw (isub_name datatype_ext_name) ] @@ List_map (\<lambda>(_, x). Opt (str_of_ty x)) l_attr ) ] ]) expr)"

definition "print_infra_datatype_universe expr = start_map Thy_dataty
  [ Datatype unicode_AA
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_infra_type_synonym_class expr = start_map Thy_ty_synonym
  (Type_synonym (* FIXME generate this automatically *)
                ty_boolean (Ty_apply (Ty_base ty_boolean) [Ty_base unicode_AA]) #
   Type_synonym (* FIXME generate this automatically *)
                ''Set_int'' (Ty_apply (Ty_base ''Set'') [Ty_base unicode_AA,
     let option = (\<lambda>x. Ty_apply (Ty_base ''option'') [x]) in
     option (option (Ty_base ''int'')) ]) #
   (map_class (\<lambda>isub_name name _ _ _ _.
     Type_synonym name (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
     let option = (\<lambda>x. Ty_apply (Ty_base ''option'') [x]) in
     option (option (Ty_base (isub_name datatype_name))) ])) expr))"

definition "print_infra_type_synonym_class_set_name name = ''Set_'' @@ name"
definition "print_infra_type_synonym_class_set = start_map Thy_ty_synonym o
  map_class (\<lambda>isub_name name _ _ _ _.
    Type_synonym (print_infra_type_synonym_class_set_name name) (Ty_apply (Ty_base ''Set'') [Ty_base unicode_AA,
    let option = (\<lambda>x. Ty_apply (Ty_base ''option'') [x]) in
    option (option (Ty_base (isub_name datatype_name))) ]))"

definition "print_infra_instantiation_class = start_map'' Thy_instantiation_class o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited) in
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
                         ( ( Expr_apply
                               (isub_name datatype_ext_constr_name)
                               (Expr_basic [var_oid] # flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inherited))
                           , Expr_basic [var_oid])
                         # List_map (\<lambda>x. ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x) [Expr_basic [var_oid]]
                                         , Expr_apply oid_of [Expr_basic [var_oid]])) (of_sub l_cons)))]))
    ]) expr)"

definition "print_infra_instantiation_universe expr = start_map Thy_instantiation_class
  [ let oid_of = ''oid_of'' in
    Instantiation unicode_AA oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        ''=''
        (Expr_function (map_class (\<lambda>isub_name name _ _ _ _.
    let esc = (\<lambda>h. Expr_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of)) expr))) ]"


definition "print_instantia_def_strictrefeq_name mk_strict name = mk_strict [''_'', isub_of_str name]"
definition "print_instantia_def_strictrefeq = start_map Thy_defs_overloaded o
  map_class (\<lambda>isub_name name _ _ _ _.
    let mk_strict = (\<lambda>l. flatten (''StrictRefEq'' # isub_of_str ''Object'' # l))
      ; s_strict = mk_strict [''_'', isub_of_str name]
      ; var_x = ''x''
      ; var_y = ''y'' in
    Defs_overloaded
      (print_instantia_def_strictrefeq_name mk_strict name)
      (Expr_rewrite (Expr_binop (Expr_annot (Expr_basic [var_x]) name)
                                unicode_doteq
                                (Expr_basic [var_y]))
                    unicode_equiv
                    (Expr_basic [mk_strict [], var_x, var_y])) )"

definition "print_instantia_lemmas_strictrefeq = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let mk_strict = (\<lambda>l. flatten (''StrictRefEq'' # isub_of_str ''Object'' # l))
         ; name_set = map_class (\<lambda>_ name _ _ _ _. print_instantia_def_strictrefeq_name mk_strict name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map (Thm_str) name_set) ]
  else (\<lambda>_. []))"

subsection{* AsType *}

definition "print_astype_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclastype) (Ty_base name) (const_mixfix dot_oclastype name))"

definition "print_astype_class = start_m' Thy_defs_overloaded
  (\<lambda> compare (isub_name, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
    Defs_overloaded
          (flatten [isub_name const_oclastype, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_astype name]))
             unicode_equiv
             (case compare
              of EQ \<Rightarrow>
                Expr_basic [var_x]
              | x \<Rightarrow>
                Expr_lam unicode_tau
                  (\<lambda>var_tau. let val_invalid = Expr_apply ''invalid'' [Expr_basic [var_tau]] in
                  Expr_case
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
                         let l = [(Expr_basic [wildcard], val_invalid)] in
                         if x = GT then
                           (some_some (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)), some_some (pattern_simple name))
                           # l
                         else l) ) ))))"

definition "print_astype_from_universe =
 (let f_finish = (\<lambda> [] \<Rightarrow> ((id, Expr_binop (Expr_basic [''Some'']) ''o''), [])
                  | _ \<Rightarrow> ((Expr_some, id), [(Expr_basic [wildcard], Expr_basic [''None''])])) in
  start_m_gen Thy_definition_hol
  (\<lambda> name l_inh _ l.
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    [ Definition (Expr_rewrite (Expr_basic [const_astype]) ''=''
        (case f_finish l_inh of ((_, finish_with_some2), last_case_none) \<Rightarrow>
          finish_with_some2 (Expr_function (flatten [l, last_case_none]))))])
  (\<lambda> l_inh _ _ compare (_, name, nl_attr). \<lambda> OclClass h_name hl_attr _ \<Rightarrow>
     if compare = UN' then [] else
     let ((finish_with_some1, _), _) = f_finish l_inh
       ; isub_h = (\<lambda> s. s @@ isub_of_str h_name)
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
       ; case_branch = (\<lambda>pat res. [(Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)]) in
             case compare
             of GT \<Rightarrow> case_branch (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)) (pattern_simple name)
              | EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [''None'']) nl_attr))))"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclastype, ''_'', name])) name_set) ]))"

definition "print_astype_lemma_cp_set2 =
  (if activate_simp_optimization then
     \<lambda>expr base_attr.
       flatten (m_class' base_attr (\<lambda> compare (isub_name, name, _). \<lambda> OclClass name2 _ _ \<Rightarrow>
         if compare = EQ then
           []
         else
           [((isub_name, name), ((\<lambda>s. s @@ isub_of_str name2), name2))]) expr)
   else (\<lambda>_ _. []))"

definition "print_astype_lemmas_id2 = start_map'' id o (\<lambda>expr base_attr _ _.
  (let name_set = print_astype_lemma_cp_set2 expr base_attr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name_h, _), (_, name)).
    Thm_str (flatten [isub_name_h const_oclastype, ''_'', name])) name_set) ]))"

definition "print_astype_lemma_cp expr = (start_map Thy_lemma_by o get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [''cp_'', const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      (bug_ocaml_extraction (let var_p = ''p'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lam ''x''
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_astype name1])))]))
      []
      (Tacl_by [Tac_rule (Thm_str ''cpI1''), if check_opt name1 name2 then Tac_simp
                                             else Tac_simp_add [flatten [const_oclastype, isub_of_str name1, ''_'', name2]]])
  )) (\<lambda>x. (x, x, x))) expr"

definition "print_astype_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [Lemmas_simp '''' (get_hierarchy_map
  (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2]))
  (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_lemma_strict expr = (start_map Thy_lemma_by o
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
      (Tacl_by (if check_opt name1 name3 then [Tac_simp]
                else [Tac_rule (Thm_str ''ext'')
                                      , Tac_simp_add (flatten [const_oclastype, isub_of_str name1, ''_'', name3]
                                                      # hol_definition ''bot_option''
                                                      # List_map hol_definition (if name2 = ''invalid'' then [''invalid'']
                                                         else [''null_fun'',''null_option'']))]))
  )) (\<lambda>x. (x, [''invalid'',''null''], x))) expr"

definition "print_astype_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp '''' (get_hierarchy_map (\<lambda>name1 name2 name3.
        Thm_str (flatten [const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_defined = start_m Thy_lemma_by m_class_default
  (\<lambda> compare (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let var_X = ''X''
       ; var_isdef = ''isdef''
       ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
     case compare of LT \<Rightarrow>
        [ Lemma_by_assum
          (flatten [isub_name const_oclastype, ''_'', h_name, ''_defined''])
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_astype name])))
          [App_using [Thm_str var_isdef]]
          (Tacl_by [Tac_auto_simp_add (flatten [isub_name const_oclastype, ''_'', h_name]
                                        # ''foundation16''
                                        # List_map hol_definition [''null_option'', ''bot_option'' ])]) ]
      | _ \<Rightarrow> [])"

definition "print_astype_up_d_cast0_name name_any name_pers = flatten [''up'', isub_of_str name_any, ''_down'', isub_of_str name_pers, ''_cast0'']"
definition "print_astype_up_d_cast0 = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_astype_up_d_cast0_name name_any name_pers)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop
             (bug_ocaml_extraction (let asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x
               (Expr_basic [dot_astype ty])) in
               asty (asty (Expr_annot (Expr_basic [var_X]) name_pers) name_any) name_pers))
             unicode_triangleq (Expr_basic [var_X])))
        [App_using [Thm_str var_isdef]]
        (Tacl_by [Tac_auto_simp_add_split
                                    (List_map Thm_str
                                    ( flatten [const_oclastype, isub_of_str name_any, ''_'', name_pers]
                                    # flatten [const_oclastype, isub_of_str name_pers, ''_'', name_any]
                                    # ''foundation22''
                                    # ''foundation16''
                                    # List_map hol_definition [''null_option'', ''bot_option'' ]))
                                    (split_ty name_pers) ]))"

definition "print_astype_up_d_cast = start_map Thy_lemma_by o
  map_class_nupl2'_inh (\<lambda>name_pers name_any.
    let var_X = ''X''
      ; var_tau = unicode_tau in
    Lemma_by_assum
        (flatten [''up'', isub_of_str name_any, ''_down'', isub_of_str name_pers, ''_cast''])
        []
        (Expr_binop
             (bug_ocaml_extraction (let asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x
               (Expr_basic [dot_astype ty])) in
               asty (asty (Expr_annot (Expr_basic [var_X]) name_pers) name_any) name_pers))
             ''='' (Expr_basic [var_X]))
        (List_map App
          [[Tac_rule (Thm_str ''ext''), Tac_rename_tac [var_tau]]
          ,[Tac_rule (Thm_THEN (Thm_str ''foundation22'') (Thm_str ''iffD1''))]
          ,[Tac_case_tac (Expr_binop (Expr_basic [var_tau]) unicode_Turnstile
              (Expr_apply unicode_delta [Expr_basic [var_X]])), Tac_simp_add [print_astype_up_d_cast0_name name_any name_pers]]
          ,[Tac_simp_add [''def_split_local''], Tac_elim (Thm_str ''disjE'')]
          ,[Tac_plus [Tac_erule (Thm_str ''StrongEq_L_subst2_rev''), Tac_simp, Tac_simp]]])
        Tacl_done)"

subsection{* IsTypeOf *}

definition "print_istypeof_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclistypeof) (Ty_base ty_boolean) (const_mixfix dot_oclistypeof name))"

definition "print_istypeof_class = start_m_gen Thy_defs_overloaded m_class_default
  (\<lambda> l_inh _ _ compare (isub_name, name, _). \<lambda> OclClass h_name hl_attr h_last \<Rightarrow>
   [Defs_overloaded
          (flatten [isub_name const_oclistypeof, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_istypeof name]))
             unicode_equiv
             (Expr_lam unicode_tau
                  (\<lambda>var_tau. let ocl_tau = (\<lambda>v. Expr_apply v [Expr_basic [var_tau]]) in
                  Expr_case
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
                             # (if h_last = [] then [] else l_false)) in
                       case compare
                       of EQ \<Rightarrow> pattern_complex_gen (flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard]) o (\<lambda> OclClass _ l _ \<Rightarrow> l)) (of_linh l_inh))) (\<lambda>_. id)
                        | GT \<Rightarrow> pattern_complex_gen [] id
                        | _ \<Rightarrow> l_false) ) )))] )"

definition "print_istypeof_from_universe = start_m Thy_definition_hol
  (\<lambda> name _ _ l.
    let const_istypeof = flatten [const_oclistypeof, isub_of_str name, ''_'', unicode_AA] in
    [ Definition (Expr_rewrite (Expr_basic [const_istypeof]) ''='' (Expr_function l))])
  (\<lambda>_ (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     [( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
      , Expr_warning_parenthesis
        (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                       Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                    h_name)
                        (Expr_basic [dot_istypeof name])))])"

definition "print_istypeof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_istypeof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclistypeof, ''_'', name] )) name_set) ]))"

definition "print_istypeof_lemma_cp expr = (start_map Thy_lemma_by o
  (get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
      (bug_ocaml_extraction (let var_p = ''p'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lam ''x''
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_istypeof name1])))]))
      []
      (Tacl_by [Tac_rule (Thm_str ''cpI1''), if check_opt name1 name2 then Tac_simp
                                             else Tac_simp_add [flatten [const_oclistypeof, isub_of_str name1, ''_'', name2]]])
  )) (\<lambda>x. (x, x, x))) ) expr"

definition "print_istypeof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp ''''
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]))
   (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_istypeof_lemma_strict expr = (start_map Thy_lemma_by o
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
      (Tacl_by (let l = List_map hol_definition (''bot_option'' # (if name2 = ''invalid'' then [''invalid'']
                                                              else [''null_fun'',''null_option''])) in
                [Tac_rule (Thm_str ''ext''), Tac_simp_add (if check_opt name1 name3 then l
                                                           else flatten [const_oclistypeof, isub_of_str name1, ''_'', name3] # l)]))
  )) (\<lambda>x. (x, [(''invalid'',''invalid''),(''null'',''true'')], x))) expr"

definition "print_istypeof_lemmas_strict_set =
  (if activate_simp_optimization then
    get_hierarchy_map (\<lambda>name1 name2 name3. (name1, name3, name2)) (\<lambda>x. (x, [''invalid'',''null''], x))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_strict expr = start_map Thy_lemmas_simp
  (case print_istypeof_lemmas_strict_set expr
   of [] \<Rightarrow> []
    | l \<Rightarrow> [ Lemmas_simp '''' (List_map
      (\<lambda>(name1, name3, name2).
        Thm_str (flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]))
      l) ])"

definition "print_istypeof_defined_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'']"
definition "print_istypeof_defined = start_m Thy_lemma_by m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      [ Lemma_by_assum
          (print_istypeof_defined_name isub_name h_name)
          [(var_isdef, False, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          [App [Tac_insert [Thm_simplified (Thm_str var_isdef) (Thm_str (''foundation18'' @@ [Char Nibble2 Nibble7])) ]
               ,Tac_simp_only [Thm_str (hol_definition ''OclValid'')]
               ,Tac_subst (Thm_str ''cp_defined'')]]
          (Tacl_by [Tac_auto_simp_add_split ( Thm_symmetric (Thm_str ''cp_defined'')
                                            # List_map Thm_str ( hol_definition ''bot_option''
                                                          # [ flatten [isub_name const_oclistypeof, ''_'', h_name] ]))
                                            (''option.split'' # split_ty h_name) ]) ])"

definition "print_istypeof_defined'_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'',  [Char Nibble2 Nibble7]]"
definition "print_istypeof_defined' = start_m Thy_lemma_by m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      [ Lemma_by_assum
          (print_istypeof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_istypeof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str ''foundation20'')))]) ])"

definition "print_istypeof_up_larger_name name_pers name_any = flatten [''actualType'', isub_of_str name_pers, ''_larger_staticType'', isub_of_str name_any]"
definition "print_istypeof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2'_inh_large (\<lambda>name_pers name_any.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_istypeof_up_larger_name name_pers name_any)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_pers)
               (Expr_basic [dot_istypeof name_any]))
             ) unicode_triangleq (Expr_basic [''false''])))
        [App_using [Thm_str var_isdef]]
        (Tacl_by [Tac_auto_simp_add ( flatten [const_oclistypeof, isub_of_str name_any, ''_'', name_pers]
                                    # ''foundation22''
                                    # ''foundation16''
                                    # List_map hol_definition [''null_option'', ''bot_option'' ])]))"

definition "print_istypeof_up_d_cast_name name_mid name_any name_pers = flatten [''down_cast_type'', isub_of_str name_mid, ''_from_'', name_any, ''_to_'', name_pers]"
definition "print_istypeof_up_d_cast expr = (start_map Thy_lemma_by o
  map_class_nupl3'_GE_inh (\<lambda>name_pers name_mid name_any.
    let var_X = ''X''
      ; var_istyp = ''istyp''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_istypeof_up_d_cast_name name_mid name_any name_pers)
        [(var_istyp, False, f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_istypeof name_mid]))))
        ,(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_basic [var_X])
               (Expr_basic [dot_astype name_pers]))
             ) unicode_triangleq (Expr_basic [''invalid''])))
        [App_using (List_map Thm_str [var_istyp, var_isdef])
        ,App [Tac_auto_simp_add_split (List_map Thm_str
                                      ( flatten [const_oclastype, isub_of_str name_pers, ''_'', name_any]
                                      # ''foundation22''
                                      # ''foundation16''
                                      # List_map hol_definition [''null_option'', ''bot_option'' ]))
                                      (split_ty name_any) ]]
        (Tacl_by [Tac_simp_add (let l = List_map hol_definition [''OclValid'', ''false'', ''true''] in
                                if name_mid = name_any & ~(print_istypeof_lemma_cp_set expr = []) then
                                  l
                                else
                                  flatten [const_oclistypeof, isub_of_str name_mid, ''_'', name_any] # l)]))) expr"

subsection{* IsKindOf *}

definition "print_iskindof_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_ocliskindof) (Ty_base ty_boolean) (const_mixfix dot_ocliskindof name))"

definition "print_iskindof_class_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name]"
definition "print_iskindof_class = start_m_gen Thy_defs_overloaded m_class_default
  (\<lambda> _ _ next_dataty _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    [ Defs_overloaded
          (print_iskindof_class_name isub_name h_name)
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_iskindof name]))
             unicode_equiv
             (let isof = (\<lambda>f name. Expr_warning_parenthesis (Expr_postunary (Expr_basic [var_x]) (Expr_basic [f name]))) in
              expr_binop ''or'' (isof dot_istypeof name # List_map (\<lambda> OclClass name_past _ _ \<Rightarrow> isof dot_iskindof name_past) next_dataty)))])"

definition "print_iskindof_from_universe = start_m Thy_definition_hol
  (\<lambda>name _ _ l.
    let const_iskindof = flatten [const_ocliskindof, isub_of_str name, ''_'', unicode_AA] in
    [ Definition (Expr_rewrite (Expr_basic [const_iskindof]) ''='' (Expr_function l)) ])
  (\<lambda> _ (_, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
    let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
    [ ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
      , Expr_warning_parenthesis
        (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                       Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                    h_name)
                        (Expr_basic [dot_iskindof name])))])"

definition "print_iskindof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_iskindof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_iskindof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_ocliskindof, ''_'', name] )) name_set) ]))"

definition "print_iskindof_lemma_cp = start_m'3_gen Thy_lemma_by
 (\<lambda> _ _ next_dataty name1 name2 name3.
    let lemma_name = flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2]
      ; lemma_spec = let var_p = ''p'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lam ''x''
             (\<lambda>var_x. Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_iskindof name1])))]
      ; lem_simp1 = Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name1, ''_'', name2])]
      ; lem_simp2 = Tac_simp_only [Thm_str (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])] in
    let (tac1, tac2) =
      if next_dataty = [] then ([], Tacl_by [ lem_simp1 , lem_simp2 ])
      else
      ( [ [ lem_simp1 ]
        , [ Tac_plus
            [ Tac_rule (Thm_where (Thm_str ''cpI2'') [(''f'', Expr_preunary (Expr_basic [''op'']) (Expr_basic [''or'']))])
            , Tac_plus [Tac_rule (Thm_str ''allI'')]
            , Tac_rule (Thm_str ''cp_OclOr'') ]]
        , [ lem_simp2 ] ]
      , Tacl_by (List_map
            (\<lambda> OclClass n _ _ \<Rightarrow> Tac_simp_only [Thm_str (flatten [''cp_'', const_ocliskindof, isub_of_str n, ''_'', name3, ''_'', name2])] )
            next_dataty))
    in Lemma_by lemma_name lemma_spec tac1 tac2)"

definition "print_iskindof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp ''''
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
  ) (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_lemma_strict = start_m_gen Thy_lemma_by m_class_default
 (\<lambda> _ _ next_dataty _ (_, name1, _). \<lambda> OclClass name3 _ _ \<Rightarrow>
  List_map (\<lambda>(name2, name2').
    Lemma_by
      (flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_iskindof name1])))
             ''=''
             (Expr_basic [name2'])]
      []
      (Tacl_by
        (Tac_simp_only
           (List_map Thm_str (flatten
              [ [flatten [const_ocliskindof, isub_of_str name1, ''_'', name3]]
              , [flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]]
              , List_map
                  (\<lambda> OclClass n _ _ \<Rightarrow>
                    flatten [const_ocliskindof, isub_of_str n, ''_'', name3, ''_'', name2])
                  next_dataty ]))
        # (if next_dataty = [] then [] else [Tac_simp])) ))
    [(''invalid'',''invalid''),(''null'',''true'')])"

definition "print_iskindof_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp '''' (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
  ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_defined_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name, ''_defined'']"
definition "print_iskindof_defined = start_m_gen Thy_lemma_by m_class_default
  (\<lambda> _ _ next_dataty _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      [ Lemma_by_assum
          (print_iskindof_defined_name isub_name h_name)
          [(var_isdef, False, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [ Tac_simp_only [Thm_str (flatten [isub_name const_ocliskindof, ''_'', h_name])]
                   , Tac_rule
                      (let mk_OF = \<lambda>f. Thm_OF (Thm_str (f h_name)) (Thm_str var_isdef) in
                       List.fold
                         (\<lambda> OclClass n _ _ \<Rightarrow> \<lambda> prf.
                           thm_OF
                             (Thm_str ''defined_or_I'')
                             [ prf
                             , mk_OF (print_iskindof_defined_name (\<lambda>name. name @@ isub_of_str n))])
                         next_dataty
                         (mk_OF (print_istypeof_defined_name isub_name))) ])])"

definition "print_iskindof_defined'_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name, ''_defined'', [Char Nibble2 Nibble7]]"
definition "print_iskindof_defined' = start_m Thy_lemma_by m_class_default
  (\<lambda> _ (isub_name, name, _). \<lambda> OclClass h_name _ _ \<Rightarrow>
      let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      [ Lemma_by_assum
          (print_iskindof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_iskindof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str ''foundation20'')))]) ])"

definition "print_iskindof_up_eq_asty_name name = (flatten [''actual_eq_static'', isub_of_str name])"
definition "print_iskindof_up_eq_asty = start_map Thy_lemma_by o map_class_gen_h'''''
  (\<lambda> _ name l_attr _ l_subtree next_dataty.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    [Lemma_by_assum
        (print_iskindof_up_eq_asty_name name)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name)
               (Expr_basic [dot_iskindof name]))))
        (List_map App
        [ [ Tac_simp_only [Thm_str (hol_definition ''OclValid'')]
          , Tac_insert [Thm_str var_isdef]]
        , flatten (fst (fold_list
                      (\<lambda> OclClass n _ next \<Rightarrow> \<lambda>accu.
                        let (l_subst, accu) = fold_list (\<lambda> _ (cpt, l_sub).
                          let l_sub = natural_of_str cpt # l_sub in
                          ( Tac_subst_l
                              l_sub (* subst could fail without the list of integers *)
                              (Thm_str ''cp_OclOr'')
                          , Succ cpt
                          , l_sub)) next accu in
                        ( Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str n, ''_'', name])]
                        # l_subst
                        , accu))
                      (OclClass name l_attr next_dataty # rev l_subtree) (1, [])))
        , [ Tac_auto_simp_add_split (bug_ocaml_extraction (let l =
                                                      List_map Thm_str (flatten ([''foundation16'', hol_definition ''bot_option'']
                                                    # List_map
                                                        (\<lambda> OclClass n _ _ \<Rightarrow> [flatten [const_oclistypeof, isub_of_str n, ''_'', name]])
                                                        l_subtree)) in
                                                     if l_subtree = [] then l else Thm_symmetric (Thm_str ''cp_OclOr'') # l))
                                                    (''option.split'' # flatten (split_ty name # List_map (\<lambda> OclClass n _ _ \<Rightarrow> split_ty n) l_subtree))]])
        (Tacl_by [Tac_option [Tac_plus [Tac_simp_add (List_map hol_definition [''false'', ''true'', ''OclOr'', ''OclAnd'', ''OclNot''])]]])])"

definition "print_iskindof_up_larger_name name_pers name_any = flatten [''actualKind'', isub_of_str name_pers, ''_larger_staticKind'', isub_of_str name_any]"
definition "print_iskindof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2''_inh (\<lambda>name_pers name_any name_pred.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile
      ; disjI1 = ''foundation25''
      ; disjI2 = ''foundation25'' @@ [Char Nibble2 Nibble7] in
    Lemma_by_assum
      (print_iskindof_up_larger_name name_pers name_any)
      [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
      (f (Expr_warning_parenthesis (Expr_postunary
             (Expr_annot (Expr_basic [var_X]) name_pers)
             (Expr_basic [dot_iskindof name_any]))))
      [App [Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name_any, ''_'', name_pers])]] ]
      (Tacl_by
        (case
            fst (List.fold (\<lambda> cl. \<lambda> (l, True) \<Rightarrow> (l, True)
                                  | (l, False) \<Rightarrow>
                                     let v =
                                       case cl of (OclClass n _ _, inh) \<Rightarrow>
                                         if n = name_pers then
                                           Some (print_iskindof_up_eq_asty_name name_pers)
                                         else if inh then
                                           Some (print_iskindof_up_larger_name name_pers n)
                                         else None in
                                     (v # l, v \<noteq> None))
              (rev (* priority of '_ or _' is right to left so we reverse *) name_pred)
              ([], False))
         of Some tac_last # l \<Rightarrow>
           List_map Tac_rule
             (flatten [ List_map (\<lambda>_. Thm_str disjI1) l
                      , [ Thm_str disjI2]
                      , [ Thm_OF (Thm_str tac_last) (Thm_str var_isdef)] ]))))"

datatype ('a, 'b, 'c, 'd, 'e) print_iskindof_up_istypeof_output
  = I_simp_only 'a
  | I_erule 'b
  | I_simp_add_iskin 'c
  | I_simp 'd
  | I_blast 'e

fun_quick print_iskindof_up_istypeof_child
      and print_iskindof_up_istypeof_child_l where
 (* *)
 "print_iskindof_up_istypeof_child l = (case l of
   [] \<Rightarrow> []
 | (cl, next_dataty) # xs \<Rightarrow>
    case Inh cl of OclClass name_pred _ _ \<Rightarrow>
      I_simp_only name_pred # print_iskindof_up_istypeof_child_l name_pred xs [] (rev next_dataty))"
 (* *) |
 "print_iskindof_up_istypeof_child_l name_pred l l_tac lc = (case lc of
   [] \<Rightarrow> l_tac
 | (x, path_inh) # next_dataty \<Rightarrow>
    let get_n = \<lambda> OclClass n _ _ \<Rightarrow> n
      ; n = get_n x in
    flatten [ [I_erule (name_pred, (x, path_inh) # next_dataty)]
            , if next_dataty = [] then [I_blast n] else []
            , print_iskindof_up_istypeof_child_l name_pred l
                (flatten [ if path_inh then
                             if l = [] then
                               [I_simp_add_iskin n]
                             else print_iskindof_up_istypeof_child l
                           else [I_simp n]
                         , l_tac ])
                next_dataty ])"

definition "print_iskindof_up_istypeof_erule var_isdef next_dataty name_pers name_any =
 (let mk_OF = \<lambda>f. Thm_OF (Thm_str (f name_any)) (Thm_str var_isdef)
    ; next_dataty = case next_dataty of x # xs \<Rightarrow>
                      rev ((''foundation26'', x) # List_map (Pair ''defined_or_I'') xs) in
  Tac_erule (List.fold
              (\<lambda> (rule_name, OclClass n _ _) \<Rightarrow> \<lambda> prf.
                thm_OF
                  (Thm_str rule_name)
                  [ prf
                  , mk_OF (print_iskindof_defined'_name (\<lambda>name. name @@ isub_of_str n))])
              next_dataty
              (mk_OF (print_istypeof_defined'_name (\<lambda>name. name @@ isub_of_str name_pers)))))"

definition "print_iskindof_up_istypeof_unfold_name name_pers name_any = flatten [''not_'', const_ocliskindof, isub_of_str name_pers, ''_then_'', name_any, ''_'', const_oclistypeof, ''_others_unfold'']"
definition "print_iskindof_up_istypeof_unfold = start_m_gen Thy_lemma_by m_class_default
  (\<lambda> _ name_pred0 next_dataty compare (isub_name, name_pers, _). \<lambda> OclClass name_any _ _ \<Rightarrow>
  if compare = GT then
    let var_X = ''X''
      ; var_iskin = ''iskin''
      ; var_isdef = ''isdef''
      ; f = \<lambda>f. f o Expr_parenthesis o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    [ Lemma_by_assum
        (print_iskindof_up_istypeof_unfold_name name_pers name_any)
        [(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))
        ,(var_iskin, False, f id (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
                 (Expr_basic [dot_iskindof name_pers]))))]
        (expr_binop' unicode_or
          (flatten
            (List_map (\<lambda>(f_dot, l). List_map
                 (\<lambda>name_pred. f id (Expr_warning_parenthesis (Expr_postunary
                   (Expr_annot (Expr_basic [var_X]) name_any)
                   (Expr_basic [f_dot name_pred])))) l)
               [ (dot_istypeof, name_pers # List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) name_pred0) ])))
        (App_using [Thm_str var_iskin]
         # App [Tac_simp_only [Thm_str (flatten [isub_name const_ocliskindof, ''_'', name_any])]]
         # (if next_dataty = [] then [] else flatten
              [ fst (fold_list
                  (\<lambda>_ next_dataty.
                      ( App [print_iskindof_up_istypeof_erule var_isdef next_dataty name_pers name_any]
                      , tl next_dataty))
                  next_dataty
                  (rev next_dataty))
              , [ App [Tac_simp] ]
              , List_map (\<lambda> OclClass n _ _ \<Rightarrow>
                  App [Tac_drule (Thm_OF (Thm_str (print_iskindof_up_istypeof_unfold_name n name_any)) (Thm_str var_isdef)), Tac_blast None]) next_dataty ]))
        Tacl_done ]
  else [])"

definition "print_iskindof_up_istypeof_name name_pers name_any = flatten [''not_'', const_ocliskindof, isub_of_str name_pers, ''_then_'', name_any, ''_'', const_oclistypeof, ''_others'']"
definition "print_iskindof_up_istypeof = start_map Thy_lemma_by o
  map_class_nupl2l'_inh (\<lambda>name_pers name_pred0.
    case name_pred0 of (name_any, _) # name_pred \<Rightarrow>
    let name_any = case Inh name_any of OclClass name_any _ _ \<Rightarrow> name_any
      ; var_X = ''X''
      ; var_iskin = ''iskin''
      ; var_isdef = ''isdef''
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
      (print_iskindof_up_istypeof_name name_pers name_any)
      [(var_iskin, False, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
             (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_pers]))))
      ,(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
      (expr_binop' unicode_or
        (flatten
          (List_map (\<lambda>(f_dot, l). List_map
               (\<lambda>name_pred. f id (Expr_warning_parenthesis (Expr_postunary
                 (Expr_annot (Expr_basic [var_X]) name_any)
                 (Expr_basic [f_dot name_pred])))) l)
             [ (dot_istypeof, List_map (\<lambda> (name_pred, _). case Inh name_pred of OclClass n _ _ \<Rightarrow> n) name_pred0)
             , (dot_iskindof, flatten (List_map (\<lambda> (name_pred, _). case Inh_sib_unflat name_pred of l \<Rightarrow> List_map (\<lambda> OclClass n _ _ \<Rightarrow> n) l) name_pred0)) ])))
      (App_using [Thm_OF (Thm_str (print_iskindof_up_eq_asty_name name_any)) (Thm_str var_isdef)]
       # List_map (\<lambda>x. App [x])
         (List_map
           (\<lambda> I_simp_only name_pred \<Rightarrow> Tac_simp_only [Thm_str (print_iskindof_class_name (\<lambda>s. s @@ isub_of_str name_pred) name_any)]
            | I_erule (name_pred, next_dataty) \<Rightarrow>
                print_iskindof_up_istypeof_erule var_isdef (List_map fst next_dataty) name_pred name_any
            | I_simp_add_iskin _ \<Rightarrow> Tac_simp_add [var_iskin]
            | _ \<Rightarrow> Tac_simp)
           (print_iskindof_up_istypeof_child name_pred0)))
        Tacl_done)"

definition "print_iskindof_up_d_cast expr = (start_map Thy_lemma_by o
  map_class_nupl3'_LE'_inh (\<lambda>name_pers name_mid name_pred0.
    case name_pred0 of (name_any, _) # name_pred \<Rightarrow>
    let name_any = case Inh name_any of OclClass name_any _ _ \<Rightarrow> name_any
      ; var_X = ''X''
      ; var_iskin = ''iskin''
      ; var_isdef = ''isdef''
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (flatten [''down_cast_kind'', isub_of_str name_mid, ''_from_'', name_any, ''_to_'', name_pers])
        [(var_iskin, False, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_mid]))))
        ,(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f id (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_basic [var_X])
               (Expr_basic [dot_astype name_pers]))
             ) unicode_triangleq (Expr_basic [''invalid''])))
        (flatten
          (let name_pred_inh = List_map (\<lambda> (name_pred, _). Inh name_pred) name_pred0
             ; name_pred_inh_sib_gen = flatten (List_map (\<lambda> (name_pred, _). case Inh_sib name_pred of l \<Rightarrow> l) name_pred0)
             ; name_pred_inh_sib = List_map fst name_pred_inh_sib_gen
             ; f0 = \<lambda>name_pred. let name_pred = case name_pred of OclClass n _ _ \<Rightarrow> n in
                                [ Tac_rule (Thm_str (print_istypeof_up_d_cast_name name_pred name_any name_pers))
                                , Tac_simp_only [] (* FIXME use wildcard *)
                                , Tac_simp_only [Thm_str var_isdef]] in
           [ App (  Tac_insert [thm_OF (Thm_str (print_iskindof_up_istypeof_name name_mid name_any)) (List_map Thm_str [var_iskin, var_isdef])]
                  # (case flatten [ name_pred_inh, name_pred_inh_sib ]
                     of [] \<Rightarrow> [] | [_] \<Rightarrow> [] | _ \<Rightarrow> [ Tac_elim (Thm_str ''disjE'') ]))]
           # List_map (App o f0) name_pred_inh
           # List_map (\<lambda> (OclClass name_pred l_attr next_d, l_subtree) \<Rightarrow>
                         List_map App
                           [ [ Tac_drule (Thm_OF (Thm_str (print_iskindof_up_istypeof_unfold_name name_pred name_any)) (Thm_str var_isdef))]
                           , if next_d = [] then
                               f0 (OclClass name_pred l_attr next_d)
                             else
                               [ Tac_auto_simp_add
                                 (var_isdef # List_map
                                                (\<lambda> OclClass name_pred _ _ \<Rightarrow>
                                                  print_istypeof_up_d_cast_name name_pred name_any name_pers)
                                                l_subtree)] ])
                      name_pred_inh_sib_gen))
        Tacl_done)) expr"

subsection{* allInstances *}

definition "print_allinst_def_id = start_map Thy_definition_hol o
  map_class (\<lambda>isub_name name _ _ _ _.
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [name]) ''='' (Expr_basic [const_astype])))"

definition "print_allinst_lemmas_id = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let name_set = map_class (\<lambda>_ name _ _ _ _. name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map (Thm_str o hol_definition) name_set) ]
  else (\<lambda>_. []))"

definition "print_allinst_astype_name isub_name = flatten [isub_name const_oclastype, ''_'', unicode_AA, ''_some'']"
definition "print_allinst_astype = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; var_x = ''x''
    ; d = hol_definition in
  [Lemma_by
    (print_allinst_astype_name isub_name)
    [ Expr_rewrite
        (Expr_apply (flatten [isub_name const_oclastype, ''_'', unicode_AA]) [b var_x])
        unicode_noteq
        (b ''None'')]
    []
    (Tacl_by [Tac_simp_add [d (flatten [isub_name const_oclastype, ''_'', unicode_AA])]])])"

definition "gen_pre_post f_tit spec f_lemma tac_last =
  (let b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; f_allinst = \<lambda>s. ''OclAllInstances_'' @@ s
     ; f_tit = f_tit o f_allinst
     ; var_pre_post = ''pre_post''
     ; var_mk = ''mk''
     ; var_st = ''st''
     ; s_generic = ''generic''
     ; lem_gen = f_tit s_generic
     ; mk_pre_post = \<lambda>pre_post at_when f_cpl.
         let s_allinst = f_allinst at_when in
         Lemma_by_assum
           (f_tit at_when)
           []
           (spec (Expr_apply s_allinst) f_cpl pre_post)
           [App_unfolding [Thm_str (d s_allinst)]]
           (Tacl_by (Tac_rule (Thm_str lem_gen) # tac_last)) in
  [ f_lemma lem_gen (spec (\<lambda>l. Expr_apply (f_allinst s_generic) (b var_pre_post # l)) (\<lambda>e. Expr_apply var_mk [e]) var_pre_post) var_pre_post var_mk var_st
  , mk_pre_post ''snd'' ''at_post'' (Expr_pair (b var_st))
  , mk_pre_post ''fst'' ''at_pre'' (\<lambda>e. Expr_pair e (b var_st)) ])"

definition "print_allinst_exec = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; a = \<lambda>f x. Expr_apply f [x]
    ; d = hol_definition
    ; f = Expr_paren unicode_lfloor unicode_rfloor
    ; f_img = \<lambda>e1. Expr_binop (b e1) ''`''
    ; ran_heap = \<lambda>var_pre_post var_tau. f_img name (a ''ran'' (a ''heap'' (Expr_apply var_pre_post [b var_tau])))
    ; f_incl = \<lambda>v1 v2.
        let var_tau = unicode_tau in
        Expr_bind0 unicode_And (b var_tau) (Expr_binop (Expr_applys (Expr_pat v1) [b var_tau]) unicode_subseteq (Expr_applys (Expr_pat v2) [b var_tau]))
    ; var_B = ''B''
    ; var_C = ''C'' in
  gen_pre_post
    (\<lambda>s. flatten [isub_name s, ''_exec''])
    (\<lambda>f_expr _ var_pre_post.
      Expr_rewrite
       (f_expr [b name])
       ''=''
       (Expr_lam unicode_tau (\<lambda>var_tau. Expr_apply ''Abs_Set_0'' [f (f (f_img ''Some'' (ran_heap var_pre_post var_tau))) ])))
    (\<lambda>lem_tit lem_spec var_pre_post _ _.
      Lemma_by_assum
        lem_tit
        []
        lem_spec
        (bug_ocaml_extraction (let var_S1 = ''S1''
           ; var_S2 = ''S2'' in
         [ App_let (Expr_pat var_S1) (Expr_lam unicode_tau (ran_heap var_pre_post))
         , App_let (Expr_pat var_S2) (Expr_lam unicode_tau (\<lambda>var_tau. Expr_binop (Expr_applys (Expr_pat var_S1) [b var_tau]) ''-'' (Expr_paren ''{'' ''}'' (b ''None''))))
         , App_have var_B (f_incl var_S2 var_S1) (Tacl_by [Tac_auto])
         , App_have var_C (f_incl var_S1 var_S2) (Tacl_by [Tac_auto_simp_add [print_allinst_astype_name isub_name]])
         , App [Tac_simp_add_del [d ''OclValid''] [d ''OclAllInstances_generic'', flatten [isub_name const_ocliskindof, ''_'', name]]] ]))
        (Tacl_by [Tac_insert [thm_OF (Thm_str ''equalityI'') (List_map Thm_str [var_B, var_C])], Tac_simp]))
    [])"

definition "print_allinst_istypeof_pre_name1 = ''ex_ssubst''"
definition "print_allinst_istypeof_pre_name2 = ''ex_def''"
definition "print_allinst_istypeof_pre = start_map Thy_lemma_by o (\<lambda>_.
  [ Lemma_by
      print_allinst_istypeof_pre_name1
      (bug_ocaml_extraction (let var_x = ''x''
         ; var_B = ''B''
         ; var_s = ''s''
         ; var_t = ''t''
         ; var_P = ''P''
         ; b = \<lambda>s. Expr_basic [s]
         ; a = \<lambda>f x. Expr_apply f [x]
         ; bind = \<lambda>symb. Expr_bind0 symb (Expr_binop (b var_x) unicode_in (b var_B))
         ; f = \<lambda>v. bind unicode_exists (a var_P (a v (b var_x))) in
       [ Expr_bind0 unicode_forall (Expr_binop (b var_x) unicode_in (b var_B)) (Expr_rewrite (a var_s (b var_x)) ''='' (a var_t (b var_x)))
       , Expr_rewrite (f var_s) ''='' (f var_t) ]))
      []
      (Tacl_by [Tac_simp])
  , Lemma_by
      print_allinst_istypeof_pre_name2
      (bug_ocaml_extraction (let var_x = ''x''
         ; var_X = ''X''
         ; var_y = ''y''
         ; b = \<lambda>s. Expr_basic [s]
         ; c = Expr_paren unicode_lceil unicode_rceil
         ; f = Expr_paren unicode_lfloor unicode_rfloor
         ; p = Expr_paren ''{'' ''}'' in
       [ Expr_binop (b var_x) unicode_in (c (c (f (f (Expr_binop (b ''Some'') ''`'' (Expr_parenthesis (Expr_binop (b var_X) ''-'' (p (b ''None'')))))))))
       , Expr_bind0 unicode_exists (b var_y) (Expr_rewrite (b var_x) ''='' (f (f (b var_y)))) ]))
      []
      (Tacl_by [Tac_auto_simp_add []]) ])"

definition "print_allinst_istypeof_single isub_name name isub_name2 name2 const_oclisof dot_isof f_simp1 f_simp2 =
  (let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [''1'',''2'',''3'']
    ; var_tau = unicode_tau in
  gen_pre_post
    (\<lambda>s. flatten [name, ''_'', s, ''_'', isub_name2 const_oclisof])
    (\<lambda>f_expr _ _. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply ''OclForall'' [f_expr [b name], b (isub_name2 const_oclisof) ]))
    (\<lambda>lem_tit lem_spec _ _ _. Lemma_by
      lem_tit
      [lem_spec]
      [ [Tac_simp_add_del [d ''OclValid''] (d ''OclAllInstances_generic'' # f_simp1 [flatten [isub_name2 const_oclisof, ''_'', name]])]
      , [Tac_simp_only (flatten [List_map Thm_str [ d ''OclForall'', ''refl'', ''if_True'' ], [Thm_simplified (Thm_str ''OclAllInstances_generic_defined'') (Thm_str (d ''OclValid''))]])]
      , [Tac_simp_only [Thm_str (d ''OclAllInstances_generic'')]]
      , [s (Thm_str ''Abs_Set_0_inverse''), Tac_simp_add [d ''bot_option'']]
      , [s (Thm_where
             (Thm_str print_allinst_istypeof_pre_name1)
             [ (''s'', Expr_lam ''x'' (\<lambda>var_x. Expr_applys (Expr_postunary (Expr_lambda wildcard (b var_x)) (b (dot_isof name2))) [b var_tau]))
             , (''t'', Expr_lambda wildcard (Expr_apply ''true'' [b var_tau]))])]
      , [Tac_intro [ Thm_str ''ballI''
                   , thm_simplified
                       (Thm_str (if name = name2 then
                                   print_iskindof_up_eq_asty_name name
                                 else
                                   print_iskindof_up_larger_name name name2))
                       (List_map Thm_str (d ''OclValid'' # f_simp2 [flatten [isub_name const_ocliskindof, ''_'', name]]))]]
      , [Tac_drule (Thm_str print_allinst_istypeof_pre_name2), Tac_erule (Thm_str (''exE'')), Tac_simp]]
      (Tacl_by [Tac_simp]))
      [])"

definition "print_allinst_istypeof = start_map'' Thy_lemma_by o (\<lambda>expr base_attr _ _. map_class_gen (\<lambda>isub_name name l_attr _ _ next_dataty.
  let l_attr = base_attr l_attr in
  let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [''1'',''2'',''3'']
    ; var_tau = unicode_tau in
  case next_dataty of [] \<Rightarrow>
    print_allinst_istypeof_single isub_name name isub_name name const_oclistypeof dot_istypeof (\<lambda>_. []) id
  | OclClass name_next _ _ # _ \<Rightarrow>
    flatten
    [ gen_pre_post
        (\<lambda>s. flatten [name, ''_'', s, ''_'', isub_name const_oclistypeof, ''1''])
        (\<lambda>f_expr _ _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply ''OclForall'' [f_expr [b name], b (isub_name const_oclistypeof) ])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_by_assum
           lem_tit
           [('''', True, Expr_And ''x'' (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) '','' (b var_x))]) ''='' (b var_x)) )]
           lem_spec
           (List_map App
              [ bug_ocaml_extraction (let var_tau0 = var_tau @@ isub_of_str ''0'' in
                [Tac_rule (Thm_where (Thm_str ''exI'') [(''x'', b var_tau0)]), Tac_simp_add_del (List_map d [var_tau0, ''OclValid'']) [d ''OclAllInstances_generic'']])
              , [Tac_simp_only (flatten [List_map Thm_str [ d ''OclForall'', ''refl'', ''if_True'' ], [Thm_simplified (Thm_str ''OclAllInstances_generic_defined'') (Thm_str (d ''OclValid''))]])]
              , [Tac_simp_only [Thm_str (d ''OclAllInstances_generic'')]]
              , [s (Thm_str ''Abs_Set_0_inverse''), Tac_simp_add [d ''bot_option'']] ] )
           (Tacl_by [Tac_simp (*Tac_simp_add [flatten [isub_name const_oclistypeof, ''_'', name]]*)]))
        [Tac_simp]
    , gen_pre_post
        (\<lambda>s. flatten [name, ''_'', s, ''_'', isub_name const_oclistypeof, ''2''])
        (\<lambda>f_expr _ _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply ''not'' [Expr_apply ''OclForall'' [f_expr [b name], b (isub_name const_oclistypeof) ]])))
        (\<lambda>lem_tit lem_spec var_pre_post _ _. Lemma_by_assum
           lem_tit
           [('''', True, Expr_And ''x'' (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) '','' (b var_x))]) ''='' (b var_x)) )]
           lem_spec
           (bug_ocaml_extraction (let var_oid = ''oid''
              ; var_a = ''a''
              ; var_t0 = ''t0''
              ; s_empty = ''Map.empty'' in
            [ App_fix [var_oid, var_a]
            , App_let (Expr_pat var_t0) (Expr_apply ''state.make''
                [ Expr_apply s_empty [Expr_binop (b var_oid) unicode_mapsto (Expr_apply (isub_name datatype_in) [Expr_apply (isub_name datatype_constr_name) (Expr_apply (datatype_ext_constr_name @@ mk_constr_name name name_next) [b var_a] # List_map (\<lambda>_. b ''None'') l_attr)])]
                , b s_empty])
            , App [Tac_rule (Thm_where (Thm_str ''exI'') [(''x'', Expr_parenthesis (Expr_binop (Expr_pat var_t0) '','' (Expr_pat var_t0)))]), Tac_simp_add_del [d ''OclValid''] [d ''OclAllInstances_generic'']]
            , App [Tac_simp_only (flatten [List_map Thm_str [ d ''OclForall'', ''refl'', ''if_True'' ], [Thm_simplified (Thm_str ''OclAllInstances_generic_defined'') (Thm_str (d ''OclValid''))]])]
            , App [Tac_simp_only (List_map (\<lambda>x. Thm_str (d x)) [''OclAllInstances_generic'', flatten [isub_name const_oclastype, ''_'', unicode_AA]])]
            , App [s (Thm_str ''Abs_Set_0_inverse''), Tac_simp_add [d ''bot_option'']] ] ))
           (Tacl_by [Tac_simp_add [d ''state.make'', d ''OclNot'']]))
        [Tac_simp]]) expr)"

definition "print_allinst_iskindof_eq = start_map Thy_lemma_by o map_class_gen (\<lambda>isub_name name _ _ _ _.
  print_allinst_istypeof_single isub_name name isub_name name const_ocliskindof dot_iskindof id (\<lambda>_. []))"

definition "print_allinst_iskindof_larger = start_map Thy_lemma_by o flatten o map_class_nupl2'_inh (\<lambda>name name2.
  print_allinst_istypeof_single (\<lambda>s. s @@ isub_of_str name) name (\<lambda>s. s @@ isub_of_str name2) name2 const_ocliskindof dot_iskindof id (\<lambda>_. []))"

subsection{* accessors *}

definition "print_access_oid_uniq_name name_from_nat isub_name attr = flatten [ isub_name var_oid_uniq, ''_'', natural_of_str name_from_nat, ''_'', isup_of_str attr ]"
definition "print_access_oid_uniq_mlname name_from_nat name attr = flatten [ var_oid_uniq, name, ''_'', natural_of_str name_from_nat, ''_'', attr ]"
definition "print_access_oid_uniq_gen Thy_def D_oid_start_upd def_rewrite =
  (\<lambda>expr ocl.
      (\<lambda>(l, oid_start). (List_map Thy_def l, D_oid_start_upd ocl oid_start))
      (let (l, (acc, _)) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inh) in
         let (l, cpt) = fold_list (fold_list
           (\<lambda> (attr, OclTy_class ty_obj) \<Rightarrow> bug_ocaml_extraction (let obj_oid = TyObj_ass_id ty_obj
                                                                     ; obj_name_from_nat = TyObjN_ass_switch (TyObj_from ty_obj) in \<lambda>(cpt, rbt) \<Rightarrow>
             let (cpt_obj, cpt_rbt) =
               case lookup rbt obj_oid of
                 None \<Rightarrow> (cpt, oidSucAssoc cpt, insert obj_oid cpt rbt)
               | Some cpt_obj \<Rightarrow> (cpt_obj, cpt, rbt) in
             ( [def_rewrite obj_name_from_nat name isub_name attr (oidGetAssoc cpt_obj)]
             , cpt_rbt))
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (flatten (flatten l), cpt)) (D_oid_start ocl, empty) expr in
       (flatten l, acc)))"
definition "print_access_oid_uniq_ml =
  print_access_oid_uniq_gen
    Thy_ml
    (\<lambda>x _. x)
    (\<lambda>obj_name_from_nat name _ attr cpt_obj.
      Ml (Sexpr_rewrite_val
                   (Sexpr_basic [print_access_oid_uniq_mlname obj_name_from_nat name attr])
                   ''=''
                   (Sexpr_oid '''' cpt_obj)))"
definition "print_access_oid_uniq =
  print_access_oid_uniq_gen
    Thy_definition_hol
    (\<lambda>ocl oid_start. ocl \<lparr> D_oid_start := oid_start \<rparr>)
    (\<lambda>obj_name_from_nat _ isub_name attr cpt_obj.
      Definition (Expr_rewrite
                   (Expr_basic [print_access_oid_uniq_name obj_name_from_nat isub_name attr])
                   ''=''
                   (Expr_oid '''' cpt_obj)))"

definition "print_access_eval_extract _ = start_map Thy_definition_hol
  (let lets = \<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_basic [def])) in
  [ bug_ocaml_extraction
    (let var_x = ''x''
      ; var_f = ''f''
      ; some_some = (\<lambda>x. Expr_some (Expr_some x))
      ; var_obj = ''obj'' in
    Definition (Expr_rewrite
                  (Expr_basic [var_eval_extract, var_x, var_f])
                  ''=''
                  (Expr_lam unicode_tau
                     (\<lambda>var_tau. Expr_case (Expr_basic [var_x, var_tau])
                     [ (some_some (Expr_basic [var_obj]), Expr_apply var_f [Expr_apply ''oid_of'' [Expr_basic [var_obj]], Expr_basic [var_tau]])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau])]))))
  , lets var_in_pre_state ''fst''
  , lets var_in_post_state ''snd''
  , lets var_reconst_basetype ''id'' ])"

definition "print_access_choose_name n i j =
  flatten [var_switch, isub_of_str (natural_of_str n), ''_'', natural_of_str i, natural_of_str j]"
definition "print_access_choose_mlname n i j =
  flatten [var_switch, natural_of_str n, ''_'', natural_of_str i, natural_of_str j]"
definition "print_access_choose_switch
              lets mk_var expr
              print_access_choose_n
              sexpr_list sexpr_function sexpr_pair =
  flatten
       (List_map
          (\<lambda>n.
           let l = List_upto 0 (n - 1) in
           List_map (let l = sexpr_list (List_map mk_var l) in (\<lambda>(i,j).
             (lets
                (print_access_choose_n n i j)
                (sexpr_function [(l, (sexpr_pair (mk_var i) (mk_var j)))]))))
             ((flatten o flatten) (List_map (\<lambda>i. List_map (\<lambda>j. if i = j then [] else [(i, j)]) l) l)))
          (class_arity expr))"
definition "print_access_choose_ml = start_map'''' Thy_ml o (\<lambda>expr _.
  (let a = \<lambda>f x. Sexpr_apply f [x]
     ; b = \<lambda>s. Sexpr_basic [s]
     ; lets = \<lambda>var exp. Ml (Sexpr_rewrite_val (Sexpr_basic [var]) ''='' exp)
     ; mk_var = \<lambda>i. b (flatten [''x'', natural_of_str i]) in
   flatten
   [ print_access_choose_switch
       lets mk_var expr
       print_access_choose_mlname
       Sexpr_list Sexpr_function Sexpr_pair ]))"
definition "print_access_choose = start_map'''' Thy_definition_hol o (\<lambda>expr _.
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; lets = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' exp)
     ; lets' = bug_scala_extraction (\<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' (b exp)))
     ; lets'' = bug_scala_extraction (\<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_lam ''l'' (\<lambda>var_l. Expr_binop (b var_l) ''!'' (b exp)))))
     ; l_flatten = ''List_flatten'' in
  flatten
  [ (bug_ocaml_extraction
    (let a = \<lambda>f x. Expr_apply f [x]
       ; b = \<lambda>s. Expr_basic [s]
       ; lets = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' exp)
       ; mk_var = \<lambda>i. b (flatten [''x'', natural_of_str i]) in
     print_access_choose_switch
       lets mk_var expr
       print_access_choose_name
       Expr_list Expr_function Expr_pair))
  ,
  [ lets l_flatten (let fun_foldl = \<lambda>f base.
                       Expr_lam ''l'' (\<lambda>var_l. Expr_apply ''foldl'' [Expr_lam ''acc'' f, base, a ''rev'' (b var_l)]) in
                     fun_foldl (\<lambda>var_acc.
                       fun_foldl (\<lambda>var_acc.
                         Expr_lam ''l'' (\<lambda>var_l. Expr_apply ''Cons'' (List_map b [var_l, var_acc]))) (b var_acc)) (b ''Nil''))
  , lets var_map_of_list (Expr_apply ''foldl''
      [ Expr_lam ''map'' (\<lambda>var_map.
          let var_x = ''x''
            ; var_l0 = ''l0''
            ; var_l1 = ''l1''
            ; f_map = a var_map in
          Expr_lambdas0 (Expr_pair (b var_x) (b var_l1))
            (Expr_case (f_map (b var_x))
              (List_map (\<lambda>(pat, e). (pat, f_map (Expr_binop (b var_x) unicode_mapsto e)))
                [ (b ''None'', b var_l1)
                , (Expr_some (b var_l0), a l_flatten (Expr_list (List_map b [var_l0, var_l1])))])))
      , b ''Map.empty''])
  ,   let var_pre_post = ''pre_post''
        ; var_to_from = ''to_from''
        ; var_assoc_oid = ''assoc_oid''
        ; var_f = ''f''
        ; var_oid = ''oid'' in
      Definition (Expr_rewrite
        (Expr_basic [var_deref_assocs, var_pre_post, var_to_from, var_assoc_oid, var_f, var_oid ])
        ''=''
        (Expr_lam
           unicode_tau
           (\<lambda>var_tau.
           Expr_case (Expr_apply var_assocs [Expr_apply var_pre_post [Expr_basic [var_tau]]
                                                                      ,Expr_basic [var_assoc_oid]])
             [ bug_ocaml_extraction (let var_S = ''S'' in
               ( Expr_some (Expr_basic [var_S])
               , Expr_apply var_f
                   [ Expr_apply var_deref_assocs_list (List_map b [var_to_from, var_oid, var_S])
                   , Expr_basic [var_tau]]))
             , (Expr_basic[wildcard], Expr_apply ''invalid'' [Expr_basic [var_tau]]) ]))) ]] ))"

definition "print_access_deref_oid = start_map Thy_definition_hol o
  map_class (\<lambda>isub_name _ _ _ _ _.
    let var_fs = ''fst_snd''
      ; var_f = ''f''
      ; var_oid = ''oid''
      ; var_obj = ''obj'' in
    Definition (Expr_rewrite
                  (Expr_basic [isub_name var_deref_oid, var_fs, var_f, var_oid])
                  ''=''
                  (Expr_lam unicode_tau
                     (\<lambda>var_tau. Expr_case (Expr_apply ''heap'' [Expr_basic [var_fs, var_tau], Expr_basic [var_oid]])
                     [ (Expr_some (Expr_basic [isub_name datatype_in, var_obj]), Expr_basic [var_f, var_obj, var_tau])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau]) ]))))"

definition "print_access_deref_assocs_name' name_from isub_name isup_attr =
  flatten [var_deref, ''_'', isub_name var_assocs, ''_'', natural_of_str name_from, isup_attr ''_'']"
definition "print_access_deref_assocs_name name_from isub_name attr =
  print_access_deref_assocs_name' name_from isub_name (\<lambda>s. s @@ isup_of_str attr)"
definition "print_access_deref_assocs = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (if design_analysis = Gen_design then \<lambda>_. [] else (\<lambda>expr. flatten (flatten (map_class (\<lambda>isub_name name l_attr l_inherited _ _.
  let l_inherited = map_class_inh l_inherited in
  let var_fst_snd = ''fst_snd''
    ; var_f = ''f''
    ; b = \<lambda>s. Expr_basic [s] in
    flatten (List_map (List_map
      (\<lambda> (attr, OclTy_class ty_obj) \<Rightarrow>
           let name_from = TyObjN_ass_switch (TyObj_from ty_obj) in
           [Definition (Expr_rewrite
                  (Expr_basic [print_access_deref_assocs_name name_from isub_name attr, var_fst_snd, var_f])
                  ''=''
                  (Expr_binop
                    (Expr_apply
                      var_deref_assocs
                        (List_map b [ var_fst_snd
                               , print_access_choose_name (TyObj_ass_arity ty_obj) name_from (TyObjN_ass_switch (TyObj_to ty_obj))
                               , print_access_oid_uniq_name name_from isub_name attr
                               , var_f ]))
                    unicode_circ
                    (b ''oid_of'')))]
       | _ \<Rightarrow> []))
      (l_attr # l_inherited))) expr)))) expr)"

definition "print_access_select_object = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (\<lambda>_.
   bug_ocaml_extraction
   (let var_mt = ''mt''
      ; var_incl = ''incl''
      ; var_smash = ''smash''
      ; var_deref = ''deref''
      ; var_l = ''l''
      ; b = \<lambda>s. Expr_basic [s] in
    Definition (Expr_rewrite
                  (Expr_basic [var_select_object, var_mt, var_incl, var_smash, var_deref, var_l])
                  ''=''
                  (Expr_apply var_smash
                     [ Expr_apply ''foldl''
                         [ b var_incl
                         , b var_mt
                         , Expr_apply ''List.map''
                             [ b var_deref
                             , b var_l ] ]])))
  #
   (if design_analysis = Gen_design then
  [ bug_ocaml_extraction
    (let var_f = ''f''
       ; var_p = ''p''
       ; a = \<lambda>f x. Expr_apply f [x]
       ; b = \<lambda>s. Expr_basic [s] in
    Definition
      (Expr_rewrite
        (Expr_basic [var_select_object_set, var_f, var_p])
        ''=''
        (Expr_apply var_select_object
           [ b ''mtSet''
           , b ''OclIncluding''
           , b ''id''
           , a var_f (b var_p)])))
  , (let var_f = ''f''
       ; var_p = ''p''
       ; var_s_set = ''s_set''
       ; a = \<lambda>f x. Expr_apply f [x]
       ; b = \<lambda>s. Expr_basic [s] in
    Definition
      (Expr_rewrite
        (Expr_basic [var_select_object_set_any, var_f, var_p, var_s_set])
        ''=''
        (a ''OclANY'' (Expr_apply var_select_object_set (List_map b [var_f, var_p, var_s_set]))))) ]
    else [])) expr)"

definition "print_access_select = start_map'' Thy_definition_hol o (\<lambda>expr base_attr _ base_attr''.
  map_class_arg_only0 (\<lambda>isub_name name l_attr.
    let l_attr = base_attr l_attr in
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
    rev l)
  (\<lambda>isub_name name (l_attr, l_inherited, l_cons).
    let l_inherited = flatten (List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inherited)) in
    let (l_attr, l_inherited) = base_attr'' (l_attr, l_inherited) in
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
                            # (List_map (\<lambda> OclClass x _ _ \<Rightarrow> let var_x = lowercase_of_str x in
                                             (Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x)
                                                             [Expr_basic [var_x]]
                                                         # List_map (\<lambda>_. wildc) l_attr), (Expr_apply (isup_attr (var_select @@ isub_of_str x))
                                                                                                     (List_map (\<lambda>x. Expr_basic [x]) [var_f, var_x]) ))) (of_sub l_cons))
                            # [])))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_inherited), [])
      l_inherited) in
    rev l) expr)"

definition "print_access_select_obj = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (if design_analysis = Gen_design then \<lambda>_. [] else (\<lambda>expr. flatten (flatten (map_class (\<lambda>isub_name name l_attr l_inh _ _.
    let l_inh = map_class_inh l_inh in
    flatten (fst (fold_list (fold_list
      (\<lambda> (attr, OclTy_class ty_obj) \<Rightarrow> \<lambda>rbt.
          if lookup2 rbt (name, attr) = None then
           ([Definition (let var_f = ''f''
                          ; b = \<lambda>s. Expr_basic [s] in
              Expr_rewrite
                  (Expr_basic [isub_name var_select @@ isup_of_str attr, var_f])
                  ''=''
                  (Expr_apply var_select_object
                    [ b ''mtSet''
                    , b ''OclIncluding''
                    , b (if single_multip (TyObjN_role_multip (TyObj_to ty_obj)) then ''OclANY'' else ''id'')
                    , Expr_apply var_f [let var_x = ''x'' in
                                        Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x])))]]))], insert2 (name, attr) () rbt)
         else ([], rbt)
       | _ \<Rightarrow> Pair []))
      (l_attr # l_inh) empty))) expr)))) expr)"

definition "print_access_dot_consts =
 (fold_list (\<lambda>(f_update, x) ocl. (Thy_consts_class x, ocl \<lparr> D_accessor_rbt := f_update (D_accessor_rbt ocl) \<rparr> ))) o
  (flatten o flatten o map_class (\<lambda>isub_name name l_attr _ _ _.
    List_map (\<lambda>(attr_n, attr_ty).
      List_map
        (\<lambda>(var_at_when_hol, var_at_when_ocl, f_update_ocl).
          let name =
             flatten [ ''dot''
                     , case attr_ty of
                         OclTy_class ty_obj \<Rightarrow> flatten [''_'', natural_of_str (TyObjN_ass_switch (TyObj_from ty_obj)), ''_'']
                       | _ \<Rightarrow> ''''
                     , isup_of_str attr_n, var_at_when_hol] in
          ( f_update_ocl (\<lambda> l. name # l)
          , Consts_raw0
            name
            (Ty_arrow
              (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA, Ty_base (Char Nibble2 Nibble7 # unicode_alpha)])

              (case attr_ty of
                  OclTy_raw attr_ty \<Rightarrow> Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
                    let option = \<lambda>x. Ty_apply (Ty_base ''option'') [x] in
                    option (option (Ty_base attr_ty))]
                | OclTy_class ty_obj \<Rightarrow>
                    let ty_obj = TyObj_to ty_obj
                      ; name = TyObjN_role_ty ty_obj in
                    Ty_base (if single_multip (TyObjN_role_multip ty_obj) then
                               name
                             else
                               print_infra_type_synonym_class_set_name name)))
            (let dot_name = mk_dot attr_n var_at_when_ocl
               ; mk_par =
                   let esc = \<lambda>s. Char Nibble2 Nibble7 # s in
                   (\<lambda>s1 s2. flatten [s1, '' '', esc ''/'', ''* '', s2, '' *'', esc ''/'']) in
             case attr_ty of OclTy_class ty_obj \<Rightarrow>
               (case apply_optim_ass_arity ty_obj (mk_par dot_name (bug_ocaml_extraction (let ty_obj = TyObj_from ty_obj in case TyObjN_role_name ty_obj of None => natural_of_str (TyObjN_ass_switch ty_obj) | Some s => s))) of
                  None \<Rightarrow> dot_name
                | Some dot_name \<Rightarrow> dot_name)
                           | _ \<Rightarrow> dot_name)
            None))
        [ (var_at_when_hol_post, var_at_when_ocl_post, update_D_accessor_rbt_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre, update_D_accessor_rbt_pre)]) l_attr))"

definition "print_access_dot_name isub_name dot_at_when attr_ty isup_attr =
  flatten [isup_attr (let dot_name = isub_name ''dot'' in
                      case attr_ty of
                        OclTy_class ty_obj \<Rightarrow> flatten [dot_name, ''_'', natural_of_str (TyObjN_ass_switch (TyObj_from ty_obj)), ''_'']
                      | _ \<Rightarrow> dot_name), dot_at_when]"

definition "print_access_dot = start_map'''' Thy_defs_overloaded o (\<lambda>expr design_analysis.
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_ty isup_attr dot_attr.
            [ Defs_overloaded
                (print_access_dot_name isub_name dot_at_when attr_ty isup_attr)
                (let var_x = ''x'' in
                 Expr_rewrite
                   (dot_attr (Expr_annot (Expr_basic [var_x]) name))
                   unicode_equiv
                   (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = \<lambda>attr_orig l. Expr_apply (case attr_orig of None \<Rightarrow> isub_name var_deref_oid
                                                                              | Some orig_n \<Rightarrow> var_deref_oid @@ isub_of_str orig_n) (Expr_basic [var_in_when_state] # l) in
                    deref_oid None
                      [ ( case (design_analysis, attr_ty) of
                            (Gen_analysis, OclTy_class ty_obj) \<Rightarrow>
                              \<lambda>l. Expr_apply (print_access_deref_assocs_name' (TyObjN_ass_switch (TyObj_from ty_obj)) isub_name isup_attr) (Expr_basic [var_in_when_state] # [l])
                        | _ \<Rightarrow> id)
                          (Expr_apply (isup_attr (isub_name var_select))
                            [case attr_ty of OclTy_raw _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                           | OclTy_class ty_obj \<Rightarrow>
                             let ty_obj = TyObj_to ty_obj
                               ; der_name = deref_oid (Some (TyObjN_role_ty ty_obj)) [] in
                             if design_analysis = Gen_design then
                               Expr_apply (if single_multip (TyObjN_role_multip ty_obj) then
                                             var_select_object_set_any
                                           else
                                             var_select_object_set) [der_name]
                             else
                               der_name]) ] ])) ]) expr)"

definition "print_access_dot_lemmas_id_set =
  (if activate_simp_optimization then
     map_class_arg_only_var'
       (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _. [print_access_dot_name isub_name dot_at_when attr_ty isup_attr])
   else (\<lambda>_. []))"

definition "print_access_dot_lemmas_id = start_map' (\<lambda>expr.
       (let name_set = print_access_dot_lemmas_id_set expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map Thm_str name_set) ]))"

definition "print_access_dot_cp_lemmas_set =
  (if activate_simp_optimization then [hol_definition var_eval_extract] else [])"

definition "print_access_dot_cp_lemmas = start_map' (\<lambda>_.
  List_map (\<lambda>x. Thy_lemmas_simp (Lemmas_simp '''' [Thm_str x])) print_access_dot_cp_lemmas_set)"

definition "print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr = flatten [''cp_'', print_access_dot_name isub_name dot_at_when attr_ty isup_attr]"
definition "print_access_dot_lemma_cp = start_map Thy_lemma_by o
  map_class_arg_only_var
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            [ Lemma_by
                (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr)
                [Expr_apply ''cp'' [Expr_lam ''X'' (\<lambda>var_x. dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]
                []
                (Tacl_by [if print_access_dot_cp_lemmas_set = [] then
                            Tac_auto_simp_add (List_map hol_definition [''cp'', var_eval_extract, flatten [isup_attr (isub_name ''dot''), dot_at_when]])
                          else
                            Tac_auto_simp_add (List_map hol_definition [''cp''])]) ])
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            [ Lemma_by
                (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr)
                [Expr_apply ''cp'' [Expr_lam ''X'' (\<lambda>var_x. dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]
                []
                (if print_access_dot_cp_lemmas_set = [] then Tacl_sorry (* fold l_hierarchy, take only subclass, unfold the corresponding definition *)
                 else Tacl_by [Tac_auto_simp_add (List_map hol_definition [''cp''])]) ])"

definition "print_access_dot_lemmas_cp = start_map Thy_lemmas_simp o (\<lambda>expr.
  case map_class_arg_only_var'
    (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _.
      [Thm_str (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr) ])
    expr
  of [] \<Rightarrow> []
   | l \<Rightarrow> [Lemmas_simp '''' l])"

definition "print_access_lemma_strict expr = (start_map Thy_lemma_by o
  map_class_arg_only_var' (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            List_map (\<lambda>(name_invalid, tac_invalid). Lemma_by
                  (flatten [print_access_dot_name isub_name dot_at_when attr_ty isup_attr, ''_'', name_invalid])
                  [Expr_rewrite
                     (dot_attr (Expr_annot (Expr_basic [name_invalid]) name))
                     ''=''
                     (Expr_basic [''invalid''])]
                  []
                  (if print_access_dot_lemmas_id_set expr = [] | print_access_dot_cp_lemmas_set = [] then
                     Tacl_sorry else
                   Tacl_by [ Tac_rule (Thm_str ''ext''),
                             Tac_simp_add (List_map hol_definition
                                             (let l = (let l = (''bot_option'' # tac_invalid) in
                                              if print_access_dot_lemmas_id_set expr = [] then
                                                flatten [isup_attr (isub_name ''dot''), dot_at_when] # l
                                              else l) in
                                              if print_access_dot_cp_lemmas_set = []
                                              then
                                                ''eval_extract'' # l
                                              else l))]) )
                [(''invalid'', [''invalid'']), (''null'', [''null_fun'', ''null_option''])])) expr"

subsection{* example *}

definition "print_examp_oclint = (\<lambda> OclDefI l \<Rightarrow> (start_map Thy_definition_hol o
  List_map (\<lambda>nb.
    let name = var_OclInt @@ nb
      ; b = \<lambda>s. Expr_basic [s] in
    Definition_abbrev0
      name
      (b (number_of_str nb))
      (Expr_rewrite (b name) ''='' (Expr_lambda wildcard (Expr_some (Expr_some (b nb))))))) l)"

datatype print_examp_instance_draw_list_attr = Return_obj ocl_ty_class | Return_exp hol_expr

definition "print_examp_instance_draw_list_attr f_oid =
  (let b = \<lambda>s. Expr_basic [s] in
   List_map (\<lambda> obj.
     case
       case obj of
         (t_obj, None) \<Rightarrow> (case t_obj of Some ty_obj \<Rightarrow> Return_obj ty_obj
                                       | _ \<Rightarrow> Return_exp (b ''None''))
       | (_, Some (OclTy_class ty_obj, _)) \<Rightarrow> Return_obj ty_obj
       | (_, Some (_, Shall_base (ShallB_str s))) \<Rightarrow> Return_exp (Expr_some (b s))
     of Return_obj ty_obj \<Rightarrow> f_oid ty_obj
      | Return_exp exp \<Rightarrow> exp))"

definition "print_examp_instance_app_constr_notmp f_oid = (\<lambda>isub_name app_x l_attr.
  Expr_apply
    (isub_name datatype_constr_name)
    ( app_x
    # print_examp_instance_draw_list_attr f_oid l_attr))"

definition "rbt_of_class ocl =
  (let rbt = (snd o fold_class_gen (\<lambda>_ name l_attr l_inh _ _ rbt.
     ( [()]
     , modify_def (empty, []) name
         (let fold = \<lambda>tag l rbt.
            let (rbt, _, n) = List.fold
                                   (\<lambda> (name_attr, ty) \<Rightarrow> \<lambda>(rbt, cpt, l_obj).
                                     (insert name_attr (ty, tag, OptIdent cpt) rbt, Succ cpt, (case ty of OclTy_class ty_obj \<Rightarrow> Some ty_obj | _ \<Rightarrow> None) # l_obj))
                                   l
                                   (rbt, 0, []) in
            (rbt, (tag, n)) in
          (\<lambda>(rbt, _).
           let (rbt, info_own) = fold OptOwn l_attr rbt in
           let (rbt, info_inh) = fold OptInh (flatten (map_class_inh l_inh)) rbt in
           (rbt, [info_own, info_inh])))
         rbt)) empty) (case D_class_spec ocl of Some c \<Rightarrow> c) in
   (\<lambda>name.
     let rbt = lookup rbt name in
     ( \<lambda> name_attr.
        Option_bind (\<lambda>(rbt, _). lookup rbt name_attr) rbt
     , \<lambda> v. Option_bind (\<lambda>(_, l).
        Option.map (\<lambda>l f accu.
          let (_, accu) =
            List.fold
              (let f_fold = \<lambda>b (n, accu). (Succ n, f b n accu) in
               if D_design_analysis ocl = Gen_design then
                 f_fold
               else
                 \<lambda> Some _ \<Rightarrow> (\<lambda>(n, accu). (Succ n, accu))
                 | None \<Rightarrow> f_fold None) (rev l) (0, accu) in
          accu) (List_assoc v l)) rbt)))"

definition "fill_blank f_blank =
  List_map (\<lambda> (attr_ty, l).
    case f_blank attr_ty of Some f_fold \<Rightarrow>
    let rbt = List.fold (\<lambda> ((ty, _, ident), shallow) \<Rightarrow> insert ident (ty, shallow)) l empty in
    (attr_ty, rev (f_fold (\<lambda>b n l. (b, lookup rbt (OptIdent n)) # l) [])))"

fun_quick split_inh_own where
   "split_inh_own f_class s_cast l_attr =
  (let (f_attr, f_blank) = f_class s_cast
     ; split = \<lambda>l. List.partition (\<lambda>((_, OptOwn, _), _) \<Rightarrow> True | _ \<Rightarrow> False) (List.map (\<lambda>(name_attr, data). (case f_attr name_attr of Some x \<Rightarrow> x, data)) l) in
   case l_attr of
     OclAttrNoCast l \<Rightarrow>
       let (l_own, l_inh) = split l in
       OclAttrNoCast (fill_blank f_blank [(OptOwn, l_own), (OptInh, l_inh)])
   | OclAttrCast s_cast l_attr l \<Rightarrow>
       case split l of (l_own, []) \<Rightarrow>
       OclAttrCast s_cast (split_inh_own f_class s_cast l_attr) (fill_blank f_blank [(OptOwn, l_own)]))"

fun_quick print_examp_instance_app_constr2_notmp where
   "print_examp_instance_app_constr2_notmp ty l_attr isub_name cpt f_oid =
  (let (l_inh, l_own) =
     let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt) in
     case l_attr of
       OclAttrNoCast [(OptOwn, l_own), (OptInh, l_inh)] \<Rightarrow> (Expr_apply (isub_name datatype_ext_constr_name) (var_oid # print_examp_instance_draw_list_attr (f_oid isub_name cpt) l_inh), l_own)
     | OclAttrCast x l_attr [(OptOwn, l_own)] \<Rightarrow>
                      (Expr_apply
                        (datatype_ext_constr_name @@ mk_constr_name ty x)
                        [ let isub_name = \<lambda>s. s @@ isub_of_str x in
                          print_examp_instance_app_constr2_notmp x l_attr isub_name cpt f_oid ], l_own) in
   print_examp_instance_app_constr_notmp (f_oid isub_name cpt) isub_name l_inh l_own)"

fun_quick fold_list_attr where
   "fold_list_attr cast_from f l_attr accu = (case l_attr of
        OclAttrNoCast x \<Rightarrow> f cast_from x accu
      | OclAttrCast c_from l_attr x \<Rightarrow> fold_list_attr c_from f l_attr (f cast_from x accu))"

definition "fold_instance_single f ocli = fold_list_attr (Inst_ty ocli) f (Inst_attr ocli)"

definition "init_map_class ocl l =
  (let (rbt_nat, rbt_str, _, _) =
     List.fold
       (\<lambda> ocl (rbt_nat, rbt_str, oid_start, accu).
         ( insert (Oid accu) oid_start rbt_nat
         , insert (Inst_name ocl) oid_start rbt_str
         , oidSucInh oid_start
         , Succ accu))
       l
       (empty, empty, D_oid_start ocl, 0) in
   (rbt_of_class ocl, lookup rbt_nat, lookup rbt_str))"

definition "print_examp_def_st_assoc_build_rbt rbt map_self map_username l_assoc =
  List.fold
     (\<lambda> (ocli, cpt). fold_instance_single
       (\<lambda> ty l_attr.
         let (f_attr_ty, _) = rbt ty in
         modify_def empty ty
         (List.fold (\<lambda>(name_attr, shall).
           case f_attr_ty name_attr of
             Some (OclTy_class ty_obj, _, _) \<Rightarrow>
               modify_def ([], ty_obj) name_attr
               (\<lambda>(l, accu). case let find_map = \<lambda> ShallB_str s \<Rightarrow> map_username s | ShallB_self s \<Rightarrow> map_self s in
                                 case shall of
                                   Shall_base shall \<Rightarrow> Option.map (\<lambda>x. [x]) (find_map shall)
                                 | Shall_list l \<Rightarrow> Some (List_map (\<lambda>shall. case find_map shall of Some cpt \<Rightarrow> cpt) l) of
                      None \<Rightarrow> (l, accu)
                    | Some oid \<Rightarrow> (List_map (List_map oidGetInh) [[cpt], oid] # l, accu))
           | _ \<Rightarrow> id) l_attr)) ocli) l_assoc empty"

definition "print_examp_def_st_assoc rbt map_self map_username l_assoc =
  (let b = \<lambda>s. Expr_basic [s]
     ; rbt = print_examp_def_st_assoc_build_rbt rbt map_self map_username l_assoc in
   Expr_apply var_map_of_list [Expr_list (fold (\<lambda>name. fold (\<lambda>name_attr (l_attr, ty_obj) l_cons.
         let cpt_from = TyObjN_ass_switch (TyObj_from ty_obj) in
         Expr_pair
           (Expr_basic [print_access_oid_uniq_name cpt_from (\<lambda>s. s @@ isub_of_str name) name_attr])
           (Expr_apply ''List.map''
             [ Expr_binop (bug_ocaml_extraction (let var_x = ''x''
                             ; var_y = ''y'' in
                           Expr_lambdas0
                             (Expr_pair (b var_x) (b var_y))
                             (Expr_list [b var_x, b var_y])))
                          ''o''
                          (b (print_access_choose_name
                                (TyObj_ass_arity ty_obj)
                                cpt_from
                                (TyObjN_ass_switch (TyObj_to ty_obj))))
             , Expr_list' (Expr_list' (Expr_list' (Expr_oid var_oid_uniq))) l_attr ])
         # l_cons)) rbt [])])"

definition "print_examp_instance_oid l ocl =
  (\<lambda>(l, _). ((List_map Thy_definition_hol o flatten o flatten) l))
    (fold_list
      (\<lambda> (f1, f2) _.
        fold_list (\<lambda> o_ocli cpt.
          case o_ocli of None \<Rightarrow> ([], oidSucInh cpt)
          | Some ocli \<Rightarrow>
            ( let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
                ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
              if List.fold (\<lambda>(_, _, cpt0) b. b | cpt0 = oidGetInh cpt) (D_instance_rbt ocl) False
               | List.fold (\<lambda>(_, l). List.fold (\<lambda>(cpt0, _) b. b | cpt0 = cpt) l) (D_state_rbt ocl) False then
                   []
              else [Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))]
            , oidSucInh cpt)) l (D_oid_start ocl))
      [ (\<lambda> var_oid _ _. var_oid,
         \<lambda> _ _ cpt. Expr_oid '''' (oidGetInh cpt)) ]
      (D_oid_start ocl))"

definition "choose_0 = fst"
definition "choose_1 = snd"

definition "deref_assocs_list to_from oid S =
  flatten (List_map (choose_1 o to_from) (filter (\<lambda>p. List.member (choose_0 (to_from p)) oid) S))"

datatype reporting = Warning
                   | Error
                   | Writeln

definition "check_single = (\<lambda> (name_attr, oid, l_oid) l_mult l.
  let l = (keys o bulkload o List_map (\<lambda>x. (x, ()))) l
    ; assoc = \<lambda>x. case map_of l_oid x of Some s \<Rightarrow> s
    ; attr_len = natural_of_nat (length l)
    ; l_typed = 
       List_map (\<lambda> (mult_min, mult_max0) \<Rightarrow>
         let mult_max = case mult_max0 of None \<Rightarrow> mult_min | Some mult_max \<Rightarrow> mult_max
           ; s_mult = \<lambda> Mult_nat n \<Rightarrow> natural_of_str n | Mult_star \<Rightarrow> ''*''
           ; f = \<lambda>s. flatten [ '' // ''
                             , s
                             , '' constraint [''
                             , s_mult mult_min
                             , if mult_max0 = None then '''' else flatten ['' .. '', s_mult mult_max]
                             , ''] not satisfied'' ] in
         List_map (\<lambda> (b, msg) \<Rightarrow> (b, flatten [ assoc oid
                                             , '' ''
                                             , case name_attr of None \<Rightarrow> ''/* unnamed attribute */'' | Some s \<Rightarrow> ''.'' @@ s
                                             , '' = Set{''
                                             , let l = List_map assoc l in
                                               if l = [] then '''' else '' '' @@ String_concatWith '' , '' l @@ '' ''
                                             , ''}''
                                             , if b then '''' else f msg ]))
                  [(case mult_min of Mult_nat mult_min \<Rightarrow> mult_min \<le> attr_len | _ \<Rightarrow> True, ''minimum'')
                  ,(case mult_max of Mult_nat mult_max \<Rightarrow> mult_max \<ge> attr_len | _ \<Rightarrow> True, ''maximum'')]) l_mult
    ; (stop, l_typed) =
       if list_ex (list_all fst) l_typed then
         ( Warning
         , if list_ex (list_ex (Not o fst)) l_typed then
             (* at least 1 warning *)
             List_map (filter (Not o fst)) l_typed
           else
             (* 0 warning *)
             [[hd (hd l_typed)]])
       else
         (Error, List_map (filter (Not o fst)) l_typed) in
  flatten (List_map (List_map (\<lambda> (b, s) \<Rightarrow> (if b then Writeln else stop, s))) l_typed))"

definition "check f_writeln f_warning f_error f_raise l_oid l = 
 (let l_out =
        fold
          (\<lambda>_ l.
            case l of ((name_from, name_to), ((OclMult l_mult_from, OclMult l_mult_to), _)) # _ \<Rightarrow>
            let l = List_map (\<lambda> (a, b) \<Rightarrow> [a, b]) (flatten (List_map (snd o snd) l)) in
            List.fold
              (\<lambda> (x, _) acc.
                let s = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                  ; s' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                  ; s'' = (*01*) \<lambda> [x0, x1] \<Rightarrow> (x0, x1)
                  ; l1 = check_single ((snd o s'') [name_from, name_to], x, l_oid) ((snd o s') [l_mult_from, l_mult_to]) (deref_assocs_list s x l)
                  ; s = (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)
                  ; s' = (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)
                  ; s'' = (*10*) \<lambda> [x0, x1] \<Rightarrow> (x1, x0)
                  ; l2 = check_single ((snd o s'') [name_from, name_to], x, l_oid) ((snd o s') [l_mult_from, l_mult_to]) (deref_assocs_list s x l) in
                flatten [acc, l1, l2])
              l_oid)
          (List.fold
            (\<lambda> ((oid, name_attr), l_o) \<Rightarrow>
              modify_def [] oid (\<lambda>l. (name_attr, l_o) # l))
            l
            empty)
          []
    ; l_err =
        List.fold
          (\<lambda> (Writeln, s) \<Rightarrow> \<lambda>acc. case f_writeln s of () \<Rightarrow> acc
           | (Warning, s) \<Rightarrow> \<lambda>acc. case f_warning s of () \<Rightarrow> acc
           | (Error, s) \<Rightarrow> \<lambda>acc. case f_error s of () \<Rightarrow> s # acc)
          l_out
          [] in
  if l_err = [] then
    ()
  else
    f_raise (nat_of_str (length l_err) @@ '' error(s) in multiplicity constraints''))"

definition "check_export_code (* polymorphism weakening needed by code_reflect *)
        f_writeln f_warning f_error f_raise (l_oid :: (string \<times> _) list) (l :: ((nat \<times> _) \<times> _) list) = 
  check f_writeln f_warning f_error f_raise l_oid l"

definition "print_examp_instance_defassoc_gen name l_ocli ocl =
 (if D_design_analysis ocl = Gen_analysis then [] else
  let a = \<lambda>f x. Expr_apply f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; (rbt :: _ \<Rightarrow> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> natural \<Rightarrow> _ \<Rightarrow> (ocl_ty \<times> ocl_data_shallow) option list) \<Rightarrow> _ \<Rightarrow> _) option)
      , (map_self, map_username)) =
        init_map_class ocl (List_map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_ocli) in
  [Definition
     (Expr_rewrite name
     ''=''
     (bug_ocaml_extraction
     (let var_oid_class = ''oid_class''
        ; var_to_from = ''to_from''
        ; var_oid = ''oid''
        ; mk_ty = bug_scala_extraction (\<lambda>l. (flatten o flatten) (List_map (\<lambda>x. ['' '', x, '' '']) l))
        ; a_l = \<lambda>s. Ty_apply (Ty_base const_oid_list) [s] in
      Expr_lambdas
        [var_oid_class, var_to_from, var_oid]
        (Expr_annot0 (Expr_case
          (Expr_apply var_deref_assocs_list
            [ Expr_annot0 (b var_to_from) (Ty_arrow
                                            (a_l (a_l (Ty_base const_oid)))
                                            (let t = a_l (Ty_base const_oid) in
                                             Ty_times t t))
            , Expr_annot (b var_oid) const_oid
            , a ''drop''
              (Expr_applys (print_examp_def_st_assoc rbt map_self map_username
                             (flatten (fst (fold_list (\<lambda>ocli cpt. (case ocli of None \<Rightarrow> [] | Some ocli \<Rightarrow> [(ocli, cpt)], oidSucInh cpt)) l_ocli (D_oid_start ocl)))))
                           [Expr_annot (b var_oid_class) const_oid])])
          [ (b ''Nil'', b ''None'')
          , let b_l = b ''l'' in
            (b_l, a ''Some'' b_l)] ) (Ty_apply (Ty_base ''option'') [a_l (Ty_base const_oid)])))))])"

definition "print_examp_instance_defassoc_typecheck_gen name l_ocli ocl =
 (let l_assoc = flatten (fst (fold_list (\<lambda>ocli cpt. (case ocli of None \<Rightarrow> []
                                                                | Some ocli \<Rightarrow> [(ocli, cpt)], oidSucInh cpt)) l_ocli (D_oid_start ocl)))
    ; b = \<lambda>s. Sexpr_basic [s]
    ; rbt = let (rbt :: _ \<Rightarrow> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> natural \<Rightarrow> _ \<Rightarrow> (ocl_ty \<times> ocl_data_shallow) option list) \<Rightarrow> _ \<Rightarrow> _) option)
                , (map_self, map_username)) =
              init_map_class ocl (List_map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_ocli) in
            print_examp_def_st_assoc_build_rbt rbt map_self map_username l_assoc
    ; var_Nat = ''Code_Numeral.Nat'' in

  [ Ml (Sexpr_apply ''Ty'.check''
    [ Sexpr_list'
        (\<lambda>(ocli, oids). case oidGetInh oids of Oid n \<Rightarrow>
          Sexpr_pair (Sexpr_string [flatten [var_oid_uniq, natural_of_str n]])
                     (Sexpr_string [Inst_name ocli]))
        l_assoc
    , Sexpr_list (fold (\<lambda>name.
       fold (\<lambda>name_attr (l_attr, ty_obj) l_cons.
         let cpt_from = TyObjN_ass_switch (TyObj_from ty_obj)
           ; cpt_to = TyObjN_ass_switch (TyObj_to ty_obj)
           ; smult = \<lambda>m. case TyObjN_role_multip m of OclMult l \<Rightarrow>
               let f = \<lambda> Mult_nat n \<Rightarrow> Sexpr_apply ''OCL.Mult_nat'' [Sexpr_apply var_Nat [Sexpr_basic [natural_of_str n]]]
                       | Mult_star \<Rightarrow> Sexpr_basic [''OCL.Mult_star''] in
               Sexpr_apply ''OCL.OclMult'' [Sexpr_list' (Sexpr_pair' f (Sexpr_option' f)) l]
           ; srole = Sexpr_option' (\<lambda>x. Sexpr_string [x]) o TyObjN_role_name
           ; (f_from, f_to) = if cpt_from < cpt_to then (TyObj_from, TyObj_to) else (TyObj_to, TyObj_from) in
         (Sexpr_pair
           (Sexpr_pair
             (Sexpr_apply var_Nat [Sexpr_basic [print_access_oid_uniq_mlname cpt_from name name_attr]])
             (Sexpr_pair (srole (f_from ty_obj)) (srole (f_to ty_obj))))
           (Sexpr_pair
             ( Sexpr_pair (smult (f_from ty_obj)) (smult (f_to ty_obj)))
             ( Sexpr_apply ''List.map''
               [ b (print_access_choose_mlname
                                (TyObj_ass_arity ty_obj)
                                cpt_from
                                cpt_to)
               , Sexpr_list' (Sexpr_list' (Sexpr_list' (\<lambda>Oid n \<Rightarrow> Sexpr_string [flatten [var_oid_uniq, natural_of_str n]]))) l_attr ])))
         # l_cons)) rbt [])])])"

definition "print_examp_instance_defassoc = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res.
    ( print_examp_instance_oid (List_map Some l) ocl
      @@ List_map Thy_definition_hol l_res
    , ocl))
  (print_examp_instance_defassoc_gen
    (Expr_oid var_inst_assoc (oidGetInh (D_oid_start ocl)))
    (List_map Some l)
    ocl))"

definition "print_examp_instance_defassoc_typecheck = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res. (List_map Thy_ml l_res, ocl))
  (print_examp_instance_defassoc_typecheck_gen
    (Expr_oid var_inst_assoc (oidGetInh (D_oid_start ocl)))
    (List_map Some l)
    ocl))"

definition "print_examp_instance_app_constr2_notmp_norec = (\<lambda>(rbt, self_username) ocl cpt_start ocli isub_name cpt.
  print_examp_instance_app_constr2_notmp
    (Inst_ty ocli)
    (split_inh_own rbt (Inst_ty ocli) (Inst_attr ocli))
    isub_name
    cpt
    (\<lambda>isub_name oid ty_obj.
      let b = \<lambda>s. Expr_basic [s] in
      Expr_applys
        cpt_start
        (bug_ocaml_extraction
        (let ty_objfrom = TyObj_from ty_obj
           ; ty_objto = TyObj_to ty_obj in
         [ b (print_access_oid_uniq_name (TyObjN_ass_switch ty_objfrom) isub_name (case TyObjN_role_name ty_objto of Some s \<Rightarrow> s))
         , b (print_access_choose_name (TyObj_ass_arity ty_obj) (TyObjN_ass_switch ty_objfrom) (TyObjN_ass_switch ty_objto))
         , Expr_oid var_oid_uniq (oidGetInh oid) ]))))"

definition "print_examp_instance_name = id"
definition "print_examp_instance = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>((l_res, oid_start), instance_rbt).
    ((List_map Thy_definition_hol o flatten) l_res, ocl \<lparr> D_oid_start := oid_start, D_instance_rbt := instance_rbt \<rparr>))
    (let (rbt, (map_self, map_username)) = init_map_class ocl l in
    ( fold_list
      (\<lambda> (f1, f2) _.
        fold_list (\<lambda> ocli cpt.
          let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
            ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
          ( Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))
          , oidSucInh cpt)) l (D_oid_start ocl))
      (let a = \<lambda>f x. Expr_apply f [x]
         ; b = \<lambda>s. Expr_basic [s] in
       [ bug_ocaml_extraction (let var_inst_ass = ''inst_assoc'' in
         (\<lambda> _ isub_name ocli. Expr_basic (print_examp_instance_name isub_name (Inst_name ocli) # (if D_design_analysis ocl = Gen_design then [ var_inst_ass ] else [])),
          print_examp_instance_app_constr2_notmp_norec (rbt, (map_self, map_username)) ocl (b var_inst_ass)))
       , (\<lambda> _ _ ocli. Expr_annot (b (Inst_name ocli)) (Inst_ty ocli),
          \<lambda> ocli isub_name _. Expr_lambda wildcard (Expr_some (Expr_some (let name_pers = print_examp_instance_name isub_name (Inst_name ocli) in
                                                                          if D_design_analysis ocl = Gen_design then
                                                                            a name_pers (Expr_oid var_inst_assoc (oidGetInh (D_oid_start ocl)))
                                                                          else
                                                                            b name_pers)))) ])
      (D_oid_start ocl)
    , List.fold (\<lambda>ocli instance_rbt.
        let n = Inst_name ocli in
        (n, ocli, case map_username n of Some oid \<Rightarrow> oidGetInh oid) # instance_rbt) l (D_instance_rbt ocl))))"

definition "print_examp_def_st_mapsto_gen f ocl cpt_start = (\<lambda> (rbt, (map_self, map_username)).
  List_map (\<lambda>(cpt, ocore).
    let a = \<lambda>f x. Expr_apply f [x]
      ; b = \<lambda>s. Expr_basic [s]
      ; (ocli, exp) = case ocore of
        OclDefCoreBinding (name, ocli) \<Rightarrow> (ocli, let name = print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) name in
                                                 if D_design_analysis ocl = Gen_design then
                                                   a name cpt_start
                                                 else
                                                   b name)
      | OclDefCoreAdd ocli \<Rightarrow> (ocli, print_examp_instance_app_constr2_notmp_norec (rbt, (map_self, map_username)) ocl cpt_start ocli (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) cpt) in
    f ocore cpt ocli exp))"

definition "print_examp_def_st_mapsto =
  print_examp_def_st_mapsto_gen
    (\<lambda>_ cpt ocli exp.
      Expr_binop (Expr_oid var_oid_uniq (oidGetInh cpt)) unicode_mapsto (Expr_apply (datatype_in @@ isub_of_str (Inst_ty ocli)) [exp]))"

definition "print_examp_def_st_defassoc_name name = Expr_basic [flatten [var_inst_assoc, name]]"
definition "print_examp_def_st_defassoc = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 let ocl_old = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
   ; l_ocli = List_map (\<lambda> OclDefCoreAdd ocli \<Rightarrow> Some ocli
                                       | OclDefCoreBinding name \<Rightarrow>
                                           (case List_assoc name (D_instance_rbt ocl_old) of Some (ocli, _) \<Rightarrow> Some ocli)
                                       | _ \<Rightarrow> None) l in
 (\<lambda>l. (print_examp_instance_oid l_ocli ocl_old @@ List_map Thy_definition_hol l, ocl))
  (print_examp_instance_defassoc_gen
    (print_examp_def_st_defassoc_name name)
    l_ocli
    ocl_old))"

definition "print_examp_def_st = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 let ocl_old = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
   ; l_ocli = List_map (\<lambda> OclDefCoreAdd ocli \<Rightarrow> Some ocli
                                       | OclDefCoreBinding name \<Rightarrow>
                                           (case List_assoc name (D_instance_rbt ocl_old) of Some (ocli, _) \<Rightarrow> Some ocli)
                                       | _ \<Rightarrow> None) l in
 (\<lambda>(l, l_st). (print_examp_instance_oid l_ocli ocl_old @@ List_map Thy_definition_hol l, ocl \<lparr> D_state_rbt := (name, l_st) # D_state_rbt ocl \<rparr>))
  (let ocl = ocl_old
     ; b = \<lambda>s. Expr_basic [s]
     ; (rbt, (map_self, map_username)) =
         init_map_class ocl (List_map (\<lambda> Some ocli \<Rightarrow> ocli | None \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_ocli)
     ; (l_st, cpt, l_assoc) = fold_list (\<lambda> ocore (cpt, l_assoc).
         let f = \<lambda>ocore ocli. ([( cpt, ocore )], Some ocli)
           ; (def, o_ocli) = case ocore of OclDefCoreSkip \<Rightarrow> ([], None)
                       | OclDefCoreBinding name \<Rightarrow>
                           case List_assoc name (D_instance_rbt ocl) of Some (ocli, cpt_registered) \<Rightarrow>
                           if oidGetInh cpt = cpt_registered then
                             f (OclDefCoreBinding (name, ocli)) ocli
                           else
                             ([], None) (* TODO
                                   check that all oid appearing in this expression-alias
                                   all appear in this defining state *)
                       | OclDefCoreAdd ocli \<Rightarrow> f (OclDefCoreAdd ocli) ocli in
         (def, oidSucInh cpt, case o_ocli of None \<Rightarrow> l_assoc | Some ocli \<Rightarrow> (ocli, cpt) # l_assoc)) l (D_oid_start ocl, [])
     ; l_st = flatten l_st
     ; expr_app = print_examp_def_st_mapsto ocl (print_examp_def_st_defassoc_name name) (rbt, (map_self, map_username)) l_st in

   ( [ let s_empty = ''Map.empty'' in
       Definition (Expr_rewrite (b name) ''='' (Expr_apply ''state.make''
        ( Expr_apply s_empty expr_app
        # [ if D_design_analysis ocl = Gen_analysis then
              print_examp_def_st_assoc rbt map_self map_username l_assoc
            else
              b s_empty ]))) ]
   , l_st)))"

definition "print_examp_def_st_inst_var_name ocli name = flatten [Inst_name ocli, name]"
definition "print_examp_def_st_inst_var = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda> ocl.
 let ocl_old = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
   ; l_ocli = List_map (\<lambda> OclDefCoreBinding name \<Rightarrow>
                            (case List_assoc name (D_instance_rbt ocl_old) of Some (ocli, _) \<Rightarrow> Some ocli)
                        | _ \<Rightarrow> None) l in
  (\<lambda>l_res. ((List_map Thy_definition_hol o flatten) l_res, ocl))
    (let ocl = ocl_old in
     if D_design_analysis ocl = Gen_analysis then [] else
     fst (fold_list
      (\<lambda> (f1, f2) _.
        let (l, accu) =
        fold_list (\<lambda> ocli cpt.
          ( case ocli of None \<Rightarrow> [] | Some ocli \<Rightarrow> bug_ocaml_extraction (let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
            ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
            [Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))])
          , oidSucInh cpt)) l_ocli (D_oid_start ocl) in
          (flatten l, accu))
      (let a = \<lambda>f x. Expr_apply f [x]
         ; b = \<lambda>s. Expr_basic [s] in
       [ (\<lambda> _ _ ocli. Expr_annot (b (flatten [Inst_name ocli, name])) (Inst_ty ocli),
          \<lambda> ocli isub_name _. Expr_lambda wildcard (Expr_some (Expr_some (a (print_examp_instance_name isub_name (Inst_name ocli))
                                                                            (print_examp_def_st_defassoc_name name))))) ])
      (D_oid_start ocl))))"

definition "print_examp_def_st_dom_name name = flatten [''dom_'', name]"
definition "print_examp_def_st_dom = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let (name, l_st) = hd (D_state_rbt ocl)
     ; a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition in
   [ Lemma_by
       (print_examp_def_st_dom_name name)
       [Expr_rewrite (a ''dom'' (a ''heap'' (b name))) ''='' (Expr_set (List_map (\<lambda>(cpt, _). Expr_oid var_oid_uniq (oidGetInh cpt)) l_st))]
       []
       (Tacl_by [Tac_auto_simp_add [d name]])]))"

definition "print_examp_def_st_dom_lemmas = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemmas_simp l, ocl))
  (let (name, _) = hd (D_state_rbt ocl) in
   [ Lemmas_simp ''''
       [Thm_str (print_examp_def_st_dom_name name)] ]))"

definition "print_examp_def_st_perm_name name = flatten [''perm_'', name]"
definition "print_examp_def_st_perm = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let (name, l_st) = hd (D_state_rbt ocl)
     ; expr_app = let ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr> in
                  print_examp_def_st_mapsto
                    ocl
                    (print_examp_def_st_defassoc_name name)
                    (init_map_class ocl (List_map (\<lambda> (_, OclDefCoreAdd ocli) \<Rightarrow> ocli
                                                   | (_, OclDefCoreBinding (_, ocli)) \<Rightarrow> ocli
                                                   | _ \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_st))
                    (rev l_st)
     ; a = bug_scala_extraction (\<lambda>f x. Expr_apply f [x])
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; (l_app, l_last) =
         case l_st of [] \<Rightarrow> ([], Tacl_by [Tac_simp_add [d name]])
         | [_] \<Rightarrow> ([], Tacl_by [Tac_simp_add [d name]])
         | _ \<Rightarrow>
           ( [ Tac_simp_add (List_map d (name # List_map (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case oidGetInh cpt of Oid i \<Rightarrow> i)) l_st))]
             # flatten (List_map (\<lambda>i_max. List_map (\<lambda>i. [Tac_subst_l (List_map nat_of_str [i_max - i]) (Thm_str ''fun_upd_twist''), Tac_simp]) (List.upt 0 i_max)) (List.upt 1 (List.length l_st)))
           , Tacl_by [Tac_simp]) in
   [ Lemma_by
       (print_examp_def_st_perm_name name)
       [Expr_rewrite (b name) ''='' (Expr_apply ''state.make''
          (let s_empty = ''Map.empty'' in
           Expr_apply s_empty expr_app # [Expr_apply var_assocs [b name]]))]
       l_app
       l_last ]))"

definition "extract_state ocl name_st l_st =
 (let b = \<lambda>s. Expr_basic [s]
    ; ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr> in
                  print_examp_def_st_mapsto_gen
                    (\<lambda>ocore cpt ocli exp.
                      ( ocore
                      , oidGetInh cpt
                      , ocli
                      , case ocore of
                          OclDefCoreBinding (name, ocli) \<Rightarrow>
                            b (if D_design_analysis ocl = Gen_analysis then
                                 name
                               else
                                 print_examp_def_st_inst_var_name ocli name_st)
                        | _ \<Rightarrow> Expr_lambda wildcard (Expr_some (Expr_some exp))))
                    ocl
                    (print_examp_def_st_defassoc_name name_st)
                    (init_map_class ocl (List_map (\<lambda> (_, OclDefCoreAdd ocli) \<Rightarrow> ocli
                                                   | (_, OclDefCoreBinding (_, ocli)) \<Rightarrow> ocli
                                                   | _ \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l_st))
                    l_st)"

definition "print_examp_def_st_allinst = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let (name_st, l_st) = hd (D_state_rbt ocl)
     ; b = \<lambda>s. Expr_basic [s]
     ; expr_app = extract_state ocl name_st l_st
     ; a = \<lambda>f x. Expr_apply f [x]
     ; d = hol_definition
     ; l_st_oid = List_map (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case oidGetInh cpt of Oid i \<Rightarrow> i)) l_st in
   map_class_gen_h'_inh (\<lambda> isub_name name compare.
     let expr_app = List_map (\<lambda>(ocore, cpt, ocli, exp).
              ( ocore
              , let exp_annot = [(Expr_postunary (case ocore of OclDefCoreBinding _ \<Rightarrow> exp | _ \<Rightarrow> Expr_annot exp (Inst_ty ocli)) (b (dot_astype name)), True, ocore, cpt)] in
                case compare (Inst_ty ocli) of
                  EQ \<Rightarrow> [(exp, False, ocore, cpt)]
                | LT \<Rightarrow> exp_annot
                | GT \<Rightarrow> (case Inst_attr ocli of OclAttrCast name2 _ _ \<Rightarrow>
                           if name = name2 then exp_annot
                           else [] | _ \<Rightarrow> [])
                | UN' \<Rightarrow> [])) expr_app
       ; (l_spec, l_body) = List_split (flatten (List_map snd expr_app)) in
     gen_pre_post
       (\<lambda>s. flatten [ name_st, ''_'', s, ''_exec_'', name ])
       (\<lambda>f_expr f_mk _. Expr_binop
            (f_mk (b name_st))
            unicode_Turnstile
            (Expr_binop (f_expr [b name]) unicode_doteq (Expr_oclset l_spec)))
       (\<lambda>lem_tit lem_spec var_pre_post var_mk _. Lemma_by_assum
         lem_tit
         [('''', True, Expr_And ''a'' (\<lambda>var_a. Expr_rewrite (a var_pre_post (a var_mk (b var_a))) ''='' (b var_a)))]
         lem_spec
         (List_map App
           (flatten
            [ [[Tac_subst (Thm_str (print_examp_def_st_perm_name name_st))]]
            , [[Tac_simp_only
                 (List_map
                   (Thm_str o d)
                   (flatten
                      [ [''state.make'']
                      , l_st_oid
                      , flatten (List_map (\<lambda>(_, ocore, _).
                          case ocore of
                            OclDefCoreBinding (n, ocli) \<Rightarrow>
                              [if D_design_analysis ocl = Gen_analysis then
                                 n
                               else
                                 print_examp_def_st_inst_var_name ocli name_st]
                          | _ \<Rightarrow> []) l_body)
                      , flatten (List_map (\<lambda>(cast, ocore, _).
                          if cast then
                            case
                              case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some ocli | OclDefCoreAdd _ \<Rightarrow> None
                            of Some ocli \<Rightarrow> [print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli)]
                             | None \<Rightarrow> []
                          else []) l_body) ]))]]
            , fst (fold_list (\<lambda> expr l_spec.
                let mk_StrictRefEq_including = \<lambda>l.
                      Tac_rule (Thm_str (flatten [''const_StrictRefEq'', isub_of_str ''Set'', ''_including'']))
                      # Tac_simp # Tac_simp # Tac_simp # l
                  ; (state_update_vs_allInstances_generic, l_spec, l_print_examp, l_OclIncluding_cong) =
                  case expr of (ocore, []) \<Rightarrow>
                    ( ''state_update_vs_allInstances_generic_ntc''
                    , l_spec
                    , case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> [print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli)] | _ \<Rightarrow> []
                    , if l_spec = [] then
                        [Tac_rule (Thm_str (flatten [''const_StrictRefEq'', isub_of_str ''Set'', ''_empty''])), Tac_simp]
                      else
                        mk_StrictRefEq_including [])
                  | _ \<Rightarrow>
                    ( ''state_update_vs_allInstances_generic_tc''
                    , tl l_spec
                    , []
                    , mk_StrictRefEq_including [ Tac_rule (Thm_str ''OclIncluding_cong''), Tac_simp, Tac_simp ]) in
                ( Tac_subst (Thm_str state_update_vs_allInstances_generic)
                  # Tac_simp # Tac_simp
                  # Tac_simp_add (List_map d ((flatten [isub_name const_oclastype, ''_'', unicode_AA]) # l_print_examp))
                  # Tac_simp
                  # l_OclIncluding_cong
                , l_spec) ) expr_app l_spec)
            , [[Tac_rule (Thm_str ''state_update_vs_allInstances_generic_empty'')]] ]))
         (Tacl_by [ if l_spec = [] then Tac_simp
                    else Tac_plus [Tac_simp_add [d (flatten [isub_name const_oclastype, ''_'', unicode_AA])]]]) )
       [Tac_simp])
     (case D_class_spec ocl of Some class_spec \<Rightarrow> class_spec)))"

definition "print_examp_def_st_defs = (\<lambda> _ \<Rightarrow> start_map Thy_lemmas_simp
  [ Lemmas_simps '''' [ ''state.defs'', ''const_ss'' ] ])"

definition "merge_unique_gen f l = List.fold (List.fold (\<lambda>x. case f x of Some (x, v) \<Rightarrow> insert x v | None \<Rightarrow> id)) l empty"
definition "merge_unique f l = entries (merge_unique_gen f l)"

definition "print_pre_post_wff = (\<lambda> OclDefPP s_pre s_post \<Rightarrow> \<lambda> ocl.
 (\<lambda> l. (List_map Thy_lemma_by l, ocl))
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; l_st = D_state_rbt ocl in
   case (List_assoc s_pre l_st, List_assoc s_post l_st) of (Some l_pre, Some l_post) \<Rightarrow>
   [ Lemma_by
      (flatten [''basic_'', s_pre, ''_'', s_post, ''_wff''])
      [a ''WFF'' (Expr_pair (b s_pre) (b s_post))]
      []
      (Tacl_by [Tac_simp_add (List_map d (flatten
        [ [ ''WFF'', s_pre, s_post, const_oid_of unicode_AA ]
        , List_map
            (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case cpt of Oid i \<Rightarrow> i))
            (merge_unique ((\<lambda>x. Some (x, ())) o oidGetInh o fst) [l_pre, l_post])
        , List_map fst (merge_unique (\<lambda>(_, ocore). case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some (print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli), ()) | _ \<Rightarrow> None) [l_pre, l_post])
        , List_map
            (\<lambda>(s_ty, _). const_oid_of (datatype_name @@ isub_of_str s_ty))
            (merge_unique (\<lambda>(_, ocore). case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some (Inst_ty ocli, ()) | _ \<Rightarrow> None) [l_pre, l_post]) ]))]) ] ))"

definition "print_pre_post_where = (\<lambda> OclDefPP s_pre s_post \<Rightarrow> \<lambda> ocl.
 (\<lambda> l. ((List_map Thy_lemma_by o flatten) l, ocl))
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; l_st = D_state_rbt ocl in
   case (List_assoc s_pre l_st, List_assoc s_post l_st) of (Some l_pre, Some l_post) \<Rightarrow>
   let f_name = \<lambda>(cpt, ocore). Some (oidGetInh cpt, ocore)
     ; rbt_pre = merge_unique_gen f_name [l_pre]
     ; rbt_post = merge_unique_gen f_name [l_post]
     ; filter_ocore = \<lambda>x_pers_oid. case (lookup rbt_pre x_pers_oid, lookup rbt_post x_pers_oid) of
             (Some ocore1, Some ocore2) \<Rightarrow> (''OclIsMaintained'', case (ocore1, ocore2) of (OclDefCoreBinding _, OclDefCoreBinding _) \<Rightarrow> [(ocore1, s_pre), (ocore2, s_post)] | (OclDefCoreBinding _, _) \<Rightarrow> [(ocore1, s_pre)] | _ \<Rightarrow> [(ocore2, s_post)])
           | (Some ocore, None) \<Rightarrow> (''OclIsDeleted'', [(ocore, s_pre)])
           | (None, Some ocore) \<Rightarrow> (''OclIsNew'', [(ocore, s_post)])
     ; rbt = union rbt_pre rbt_post
     ; l_oid_of = keys (fold (\<lambda>_. \<lambda> OclDefCoreBinding (_, ocli) \<Rightarrow> insert (const_oid_of (datatype_name @@ isub_of_str (Inst_ty ocli))) ()
                            | _ \<Rightarrow> id) rbt empty) in
   List_map
     (\<lambda>x_pers_oid.
       let (x_where, l_ocore) = filter_ocore x_pers_oid in
       List_map (\<lambda>(ocore, name_st).
         let (x_where, x_name, x_pers_expr) =
           ( x_where
           , case ocore of OclDefCoreBinding (name, ocli) \<Rightarrow>
               let name =
                 if D_design_analysis ocl = Gen_analysis then
                   name
                 else
                   print_examp_def_st_inst_var_name ocli name_st in
               (Some (name, print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (Inst_name ocli)), b name)) in
         Lemma_by (flatten [var_oid_uniq, natural_of_str (case x_pers_oid of Oid i \<Rightarrow> i), s_pre, s_post, ''_'', name_st, ''_'', x_where])
          [Expr_binop (Expr_pair (b s_pre) (b s_post)) unicode_Turnstile (a x_where (x_pers_expr))]
          []
          (Tacl_by [Tac_simp_add (List_map d (flatten
            [ case x_name of Some (x_pers, x_name) \<Rightarrow> [x_pers, x_name] | _ \<Rightarrow> []
            , [ x_where, ''OclValid'', s_pre, s_post, const_oid_of ''option'' ]
            , List_map
                (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case cpt of Oid i \<Rightarrow> i))
                (merge_unique ((\<lambda>x. Some (x, ())) o oidGetInh o fst) [l_pre, l_post])
            , l_oid_of ]))])) l_ocore)
     (filter (\<lambda>x_pers_oid. list_ex (\<lambda> (OclDefCoreBinding _, _) \<Rightarrow> True | _ \<Rightarrow> False)
       (snd (filter_ocore x_pers_oid)))
       (keys rbt)) ))"

subsection{* context *}

fun_quick print_ctxt_ty where
   "print_ctxt_ty c = (\<lambda> OclTy_collection Set t \<Rightarrow> Ty_apply (Ty_base ''Set'') [print_ctxt_ty t]
                       | OclTy_raw t \<Rightarrow> Ty_base t) c"

definition "print_ctxt_const_name attr_n var_at_when_hol = flatten [ ''dot'', isup_of_str attr_n, var_at_when_hol]"
definition "print_ctxt_const = List_map (map_pair id Thy_consts_class) o (\<lambda> ctxt.
  let attr_n = Ctxt_fun_name ctxt in
      List_map
        (\<lambda>(var_at_when_hol, var_at_when_ocl, f_update_ocl).
          let name = print_ctxt_const_name attr_n var_at_when_hol in
          ( f_update_ocl (\<lambda> l. name # l)
          , Consts_raw0
              name
              (ty_arrow (Ty_base (Ctxt_ty ctxt) # List_map
                (\<lambda> OclTy_collection Set (OclTy_raw s) \<Rightarrow> (* optimization *) Ty_base (print_infra_type_synonym_class_set_name s)
                 | e \<Rightarrow> print_ctxt_ty e)
                (flatten
                  [ List_map snd (Ctxt_fun_ty_arg ctxt)
                  , [ case Ctxt_fun_ty_out ctxt of None \<Rightarrow> OclTy_raw ''Void'' | Some s \<Rightarrow> s ] ])))
              (mk_dot attr_n var_at_when_ocl)
              (Some (natural_of_nat (length (Ctxt_fun_ty_arg ctxt))))))
        [ (var_at_when_hol_post, var_at_when_ocl_post, update_D_accessor_rbt_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre, update_D_accessor_rbt_pre)])"

definition "print_ctxt_gen_syntax_header_l l = Isab_thy (Theory_thm (Thm (List_map Thm_str l)))"
definition "print_ctxt_gen_syntax_header f_x l ocl =
 ( let (l, ocl) = f_x l ocl in
   if D_generation_syntax_shallow ocl then
     l
   else
     Isab_thy_generation_syntax (Generation_syntax_shallow (D_design_analysis ocl))
     # Isab_thy_ml_extended (Ml_extended (Sexpr_ocl (ocl \<lparr> D_disable_thy_output := True
                                                         , D_file_out_path_dep := None
                                                         , D_output_position := (0, 0) \<rparr>) ))
     # l
 , ocl \<lparr> D_generation_syntax_shallow := True \<rparr> )"

definition "print_ctxt2_pre_post_name attr_n var_at_when_hol = hol_definition (print_ctxt_const_name attr_n var_at_when_hol)"
definition "print_ctxt_pre_post = (\<lambda>ctxt. print_ctxt_gen_syntax_header
  (\<lambda>l ocl.
    let (l_name, l_isab) = List_split (print_ctxt_const ctxt) in
    (l_isab @@ l, List.fold (\<lambda>f_update ocl. ocl \<lparr> D_accessor_rbt := f_update (D_accessor_rbt ocl) \<rparr>) l_name ocl))
  [ Isab_thy_ocl_deep_embed_ast (OclAstCtxt2PrePost ctxt)
  , print_ctxt_gen_syntax_header_l [print_ctxt2_pre_post_name (Ctxt_fun_name ctxt) var_at_when_hol_post] ])"

definition "print_ctxt2_inv_name n tit var_at_when = hol_definition (flatten [n, ''_'', tit, var_at_when])"
definition "print_ctxt_inv = (\<lambda>ctxt. print_ctxt_gen_syntax_header Pair
  [ Isab_thy_ocl_deep_embed_ast (OclAstCtxt2Inv ctxt)
  , print_ctxt_gen_syntax_header_l
      (flatten (List_map (\<lambda> (tit, _).
        List_map (print_ctxt2_inv_name (Ctxt_inv_ty ctxt) tit)
          [ var_at_when_hol_pre
          , var_at_when_hol_post ]) (Ctxt_inv_expr ctxt))) ])"

subsection{* context2 *}
(* (* ERROR this lambda term type-checks expensively *)
definition "print_ctxt2_is_accessor =
  (\<lambda> PureType ''fun''
               [PureType ''fun''
                       [PureType ''Product_Type.prod''
                               [PureType ''OCL_core.state.state_ext''
                                       [PureType _ (* AA *) [], PureType ''Product_Type.unit'' []],
                                PureType ''OCL_core.state.state_ext''
                                       [PureType _ (* AA *) [], PureType ''Product_Type.unit'' []]],
                        PureTFree _ (* 'a *) (PureSort [PureClass ''HOL.type''])],
                PureType ''fun''
                       [PureType ''Product_Type.prod''
                               [PureType ''OCL_core.state.state_ext''
                                       [PureType _ (* AA *) [], PureType ''Product_Type.unit'' []],
                                PureType ''OCL_core.state.state_ext''
                                       [PureType _ (* AA *) [], PureType ''Product_Type.unit'' []]],
                        PureType ''Option.option''
                               [PureType ''Option.option''
                                       [PureType _ (* class name *) []]]]]
       \<Rightarrow> True
   | _ \<Rightarrow> False)"
*)
definition "print_ctxt2_is_name_at_gen var s =
 (case var of _ # _ \<Rightarrow>
    let lg_var = length var in
    if List_take_last lg_var s = var then
      Some (List_take_first (length s - lg_var) s)
    else
      None)"

definition "print_ctxt2_is_name_at_pre = print_ctxt2_is_name_at_gen var_at_when_hol_pre"
definition "print_ctxt2_is_name_at_post = (case var_at_when_hol_post of [] \<Rightarrow>
  \<lambda>s. case print_ctxt2_is_name_at_pre s of None \<Rightarrow> Some s
                                         | _ \<Rightarrow> None)"

definition "print_ctxt2_to_ocl_gen l_access f var = (\<lambda> T_pure t \<Rightarrow>
  T_pure (map_Const (\<lambda> s ty.
    if (*print_ctxt2_is_accessor ty*)
       list_ex (case List_split_at (\<lambda> s. s = Char Nibble2 NibbleE) s of
                  (_, Some _, s) \<Rightarrow> \<lambda>n. n = s
                | _ \<Rightarrow> \<lambda>_. False) l_access then
      case f s of
        Some s \<Rightarrow> s @@ var
      | _ \<Rightarrow> s
    else
      s) t))"

definition "print_ctxt2_to_ocl_pre ocl = print_ctxt2_to_ocl_gen (snd (D_accessor_rbt ocl)) print_ctxt2_is_name_at_post var_at_when_hol_pre"
definition "print_ctxt2_to_ocl_post ocl = print_ctxt2_to_ocl_gen (fst (D_accessor_rbt ocl)) print_ctxt2_is_name_at_pre var_at_when_hol_post"

definition "print_ctxt2_pre_post = fold_list (\<lambda>x ocl. (x ocl, ocl)) o (\<lambda> ctxt.
  let (l_pre, l_post) = List.partition (\<lambda> (OclCtxtPre, _) \<Rightarrow> True | _ \<Rightarrow> False) (Ctxt_expr ctxt)
    ; attr_n = Ctxt_fun_name ctxt
    ; a = \<lambda>f x. Expr_apply f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; var_tau = unicode_tau
    ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) unicode_Turnstile (Expr_warning_parenthesis s))
    ; expr_binop = \<lambda>s_op. \<lambda> [] \<Rightarrow> b ''True'' | l \<Rightarrow> Expr_parenthesis (expr_binop s_op l)
    ; to_s = \<lambda>f_to l_pre. expr_binop unicode_and (List_map (\<lambda>(_, expr) \<Rightarrow> f_tau (Expr_inner (case f_to expr of T_pure expr \<Rightarrow> expr))) l_pre)
    ; f = \<lambda> (var_at_when_hol, var_at_when_ocl).
        let var_self = ''self''
          ; var_result = ''result'' in
        [ \<lambda>ocl. Thy_axiom (Axiom
            (print_ctxt2_pre_post_name attr_n var_at_when_hol)
            (Expr_rewrite
              (Expr_parenthesis (f_tau (Expr_rewrite
                  (Expr_postunary (b var_self) (b (mk_dot_par_gen (flatten [''.'', attr_n, var_at_when_ocl]) (List_map fst (Ctxt_fun_ty_arg ctxt)))))
                  unicode_triangleq
                  (b var_result))))
              ''=''
              (Expr_parenthesis (Expr_if_then_else
                (f_tau (a unicode_delta (b var_self)))
                (Expr_warning_parenthesis (Expr_binop
                  (to_s (print_ctxt2_to_ocl_pre ocl) l_pre)
                  unicode_longrightarrow
                  (to_s (print_ctxt2_to_ocl_post ocl) l_post)))
                (f_tau (Expr_rewrite (b var_result) unicode_triangleq (b ''invalid''))))))) ] in
  f (var_at_when_hol_post, var_at_when_ocl_post))"

definition "print_ctxt2_inv = fold_list (\<lambda>x ocl. (x ocl, ocl)) o flatten o flatten o (\<lambda> ctxt.
  let a = \<lambda>f x. Expr_apply f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; var_tau = unicode_tau
    ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) unicode_Turnstile s) in
  List_map (\<lambda> (tit, e) \<Rightarrow>
    List_map (\<lambda> (allinst_at_when, var_at_when, e) \<Rightarrow>
        let var_self = ''self''
          ; var_result = ''result'' in
        [ \<lambda>ocl. Thy_axiom (Axiom
            (print_ctxt2_inv_name (Ctxt_inv_ty ctxt) tit var_at_when)
            (f_tau (Expr_apply ''OclForall''
              [ a allinst_at_when (b (Ctxt_inv_ty ctxt))
              , Expr_lam ''self'' (\<lambda>var_self. Expr_inner (case e ocl of T_pure e \<Rightarrow> e))]))) ])
      [(''OclAllInstances_at_pre'', var_at_when_hol_pre, \<lambda>ocl. print_ctxt2_to_ocl_pre ocl e)
      ,(''OclAllInstances_at_post'', var_at_when_hol_post, \<lambda>ocl. print_ctxt2_to_ocl_post ocl e)])
    (Ctxt_inv_expr ctxt))"

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
    None [] [] [] False ([], [])"

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
       let (l_class, l_ocl) = List.partition (\<lambda> OclAstClassRaw _ \<Rightarrow> True
                                              | OclAstAssociation _ \<Rightarrow> True
                                              | OclAstAssClass _ \<Rightarrow> True
                                              | _ \<Rightarrow> False) (rev (D_ocl_env ocl)) in
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
           (let univ = class_unflat l_class
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

section{* Generation to both Form (setup part) *}

definition "ocl_ty_class_node_rec0 f ocl = f
  (TyObjN_ass_switch ocl)
  (TyObjN_role_multip ocl)
  (TyObjN_role_name ocl)
  (TyObjN_role_ty ocl)"

definition "ocl_ty_class_node_rec f ocl = ocl_ty_class_node_rec0 f ocl
  (ocl_ty_class_node.more ocl)"

definition "ocl_ty_class_rec0 f ocl = f
  (TyObj_name ocl)
  (TyObj_ass_id ocl)
  (TyObj_ass_arity ocl)
  (TyObj_from ocl)
  (TyObj_to ocl)"

definition "ocl_ty_class_rec f ocl = ocl_ty_class_rec0 f ocl
  (ocl_ty_class.more ocl)"

definition "ocl_class_raw_rec0 f ocl = f
  (ClassRaw_name ocl)
  (ClassRaw_own ocl)
  (ClassRaw_inh ocl)"

definition "ocl_class_raw_rec f ocl = ocl_class_raw_rec0 f ocl
  (ocl_class_raw.more ocl)"

definition "ocl_association_rec0 f ocl = f
  (OclAss_type ocl)
  (OclAss_relation ocl)"

definition "ocl_association_rec f ocl = ocl_association_rec0 f ocl
  (ocl_association.more ocl)"

definition "ocl_instance_single_rec0 f ocl = f
  (Inst_name ocl)
  (Inst_ty ocl)
  (Inst_attr ocl)"

definition "ocl_instance_single_rec f ocl = ocl_instance_single_rec0 f ocl
  (ocl_instance_single.more ocl)"

definition "ocl_ctxt_pre_post_rec0 f ocl = f
  (Ctxt_ty ocl)
  (Ctxt_fun_name ocl)
  (Ctxt_fun_ty_arg ocl)
  (Ctxt_fun_ty_out ocl)
  (Ctxt_expr ocl)"

definition "ocl_ctxt_pre_post_rec f ocl = ocl_ctxt_pre_post_rec0 f ocl
  (ocl_ctxt_pre_post.more ocl)"

definition "ocl_ctxt_inv_rec0 f ocl = f
  (Ctxt_inv_ty ocl)
  (Ctxt_inv_expr ocl)"

definition "ocl_ctxt_inv_rec f ocl = ocl_ctxt_inv_rec0 f ocl
  (ocl_ctxt_inv.more ocl)"

definition "ocl_compiler_config_rec0 f ocl = f
  (D_disable_thy_output ocl)
  (D_file_out_path_dep ocl)
  (D_oid_start ocl)
  (D_output_position ocl)
  (D_design_analysis ocl)
  (D_class_spec ocl)
  (D_ocl_env ocl)
  (D_instance_rbt ocl)
  (D_state_rbt ocl)
  (D_generation_syntax_shallow ocl)
  (D_accessor_rbt ocl)"

definition "ocl_compiler_config_rec f ocl = ocl_compiler_config_rec0 f ocl
  (ocl_compiler_config.more ocl)"

(* *)

definition "K x _ = x"

definition "co1 = op o"
definition "co2 f g x1 x2 = f (g x1 x2)"
definition "co3 f g x1 x2 x3 = f (g x1 x2 x3)"
definition "co4 f g x1 x2 x3 x4 = f (g x1 x2 x3 x4)"
definition "co5 f g x1 x2 x3 x4 x5 = f (g x1 x2 x3 x4 x5)"
definition "co6 f g x1 x2 x3 x4 x5 x6 = f (g x1 x2 x3 x4 x5 x6)"
definition "co7 f g x1 x2 x3 x4 x5 x6 x7 = f (g x1 x2 x3 x4 x5 x6 x7)"
definition "co8 f g x1 x2 x3 x4 x5 x6 x7 x8 = f (g x1 x2 x3 x4 x5 x6 x7 x8)"
definition "co9 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9)"
definition "co10 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)"
definition "co11 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)"
definition "co12 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)"

definition "ap1 a v0 f1 v1 = a v0 [f1 v1]"
definition "ap2 a v0 f1 f2 v1 v2 = a v0 [f1 v1, f2 v2]"
definition "ap3 a v0 f1 f2 f3 v1 v2 v3 = a v0 [f1 v1, f2 v2, f3 v3]"
definition "ap4 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4]"
definition "ap5 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5]"
definition "ap6 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6]"
definition "ap7 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7]"
definition "ap8 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8]"
definition "ap9 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v1 v2 v3 v4 v5 v6 v7 v8 v9 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9]"
definition "ap10 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10]"
definition "ap11 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11]"
definition "ap12 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, f12 v12]"

definition "ar1 a v0 z = a v0 [z]"
definition "ar2 a v0 f1 v1 z = a v0 [f1 v1, z]"
definition "ar3 a v0 f1 f2 v1 v2 z = a v0 [f1 v1, f2 v2, z]"
definition "ar4 a v0 f1 f2 f3 v1 v2 v3 z = a v0 [f1 v1, f2 v2, f3 v3, z]"
definition "ar5 a v0 f1 f2 f3 f4 v1 v2 v3 v4 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, z]"
definition "ar6 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, z]"
definition "ar7 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, z]"
definition "ar8 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, z]"
definition "ar9 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, z]"
definition "ar10 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v1 v2 v3 v4 v5 v6 v7 v8 v9 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, z]"
definition "ar11 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, z]"
definition "ar12 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, z]"

(* *)

lemma [code]: "ocl_class_raw.extend = (\<lambda>ocl v. ocl_class_raw_rec0 (co3 (\<lambda>f. f v) ocl_class_raw_ext) ocl)"
by(intro ext, simp add: ocl_class_raw_rec0_def
                        ocl_class_raw.extend_def
                        co3_def K_def)
lemma [code]: "ocl_class_raw.make = co3 (\<lambda>f. f ()) ocl_class_raw_ext"
by(intro ext, simp add: ocl_class_raw.make_def
                        co3_def)
lemma [code]: "ocl_class_raw.truncate = ocl_class_raw_rec (co3 K ocl_class_raw.make)"
by(intro ext, simp add: ocl_class_raw_rec0_def
                        ocl_class_raw_rec_def
                        ocl_class_raw.truncate_def
                        ocl_class_raw.make_def
                        co3_def K_def)

lemma [code]: "ocl_association.extend = (\<lambda>ocl v. ocl_association_rec0 (co2 (\<lambda>f. f v) ocl_association_ext) ocl)"
by(intro ext, simp add: ocl_association_rec0_def
                        ocl_association.extend_def
                        co2_def K_def)
lemma [code]: "ocl_association.make = co2 (\<lambda>f. f ()) ocl_association_ext"
by(intro ext, simp add: ocl_association.make_def
                        co2_def)
lemma [code]: "ocl_association.truncate = ocl_association_rec (co2 K ocl_association.make)"
by(intro ext, simp add: ocl_association_rec0_def
                        ocl_association_rec_def
                        ocl_association.truncate_def
                        ocl_association.make_def
                        co2_def K_def)

lemma [code]: "ocl_instance_single.extend = (\<lambda>ocl v. ocl_instance_single_rec0 (co3 (\<lambda>f. f v) ocl_instance_single_ext) ocl)"
by(intro ext, simp add: ocl_instance_single_rec0_def
                        ocl_instance_single.extend_def
                        co3_def K_def)
lemma [code]: "ocl_instance_single.make = co3 (\<lambda>f. f ()) ocl_instance_single_ext"
by(intro ext, simp add: ocl_instance_single.make_def
                        co3_def)
lemma [code]: "ocl_instance_single.truncate = ocl_instance_single_rec (co3 K ocl_instance_single.make)"
by(intro ext, simp add: ocl_instance_single_rec0_def
                        ocl_instance_single_rec_def
                        ocl_instance_single.truncate_def
                        ocl_instance_single.make_def
                        co3_def K_def)

lemma [code]: "ocl_compiler_config.extend = (\<lambda>ocl v. ocl_compiler_config_rec0 (co11 (\<lambda>f. f v) ocl_compiler_config_ext) ocl)"
by(intro ext, simp add: ocl_compiler_config_rec0_def
                        ocl_compiler_config.extend_def
                        co11_def K_def)
lemma [code]: "ocl_compiler_config.make = co11 (\<lambda>f. f ()) ocl_compiler_config_ext"
by(intro ext, simp add: ocl_compiler_config.make_def
                        co11_def)
lemma [code]: "ocl_compiler_config.truncate = ocl_compiler_config_rec (co11 K ocl_compiler_config.make)"
by(intro ext, simp add: ocl_compiler_config_rec0_def
                        ocl_compiler_config_rec_def
                        ocl_compiler_config.truncate_def
                        ocl_compiler_config.make_def
                        co11_def K_def)

subsection{* i of ... *} (* i_of *)

subsubsection{* general *}

locale i_of =
  fixes ext :: "char list \<Rightarrow> char list"

  (* (effective) first order *)
  fixes i_of_string :: "('a \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (char list \<Rightarrow> 'a) \<Rightarrow> char list \<Rightarrow> 'a"
  fixes i_of_nat :: "('a \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (char list \<Rightarrow> 'a) \<Rightarrow> natural \<Rightarrow> 'a"
  fixes i_of_unit :: "(char list \<Rightarrow> 'a) \<Rightarrow> unit \<Rightarrow> 'a"
  fixes i_of_bool :: "(char list \<Rightarrow> 'a) \<Rightarrow> bool \<Rightarrow> 'a"

  (* (simulation) higher order *)
  fixes i_Pair i_Nil i_Cons i_None i_Some :: "char list"
begin

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b i_Pair) f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b i_Nil)
  (ar2 a (b i_Cons) f)"

definition "i_of_option a b f = option_rec
  (b i_None)
  (ap1 a (b i_Some) f)"

(* *)

definition "i_of_pure_indexname a b = pure_indexname_rec
  (ap2 a (b ''PureIndexname'') (i_of_string a b) (i_of_nat a b))"

definition "i_of_pure_class a b = pure_class_rec
  (ap1 a (b ''PureClass'') (i_of_string a b))"

definition "i_of_pure_sort a b = pure_sort_rec
  (ap1 a (b ''PureSort'') (i_of_list a b (i_of_pure_class a b)))"

definition "i_of_pure_typ a b = (\<lambda>f1 f2 f3 f4 f5. pure_typ_rec_1 (co1 K f1) f2 f3 f4 (\<lambda>_ _. f5))
  (ar2 a (b ''PureType'') (i_of_string a b))
  (ap2 a (b ''PureTFree'') (i_of_string a b) (i_of_pure_sort a b))
  (ap2 a (b ''PureTVar'') (i_of_pure_indexname a b) (i_of_pure_sort a b))
  (* *)
  (b i_Nil)
  (ar2 a (b i_Cons) id)"

definition "i_of_pure_term a b = (\<lambda>f0 f1 f2 f3 f4 f5. pure_term_rec f0 f1 f2 f3 (co2 K f4) (\<lambda>_ _. f5))
  (ap2 a (b ''PureConst'') (i_of_string a b) (i_of_pure_typ a b))
  (ap2 a (b ''PureFree'') (i_of_string a b) (i_of_pure_typ a b))
  (ap2 a (b ''PureVar'') (i_of_pure_indexname a b) (i_of_pure_typ a b))
  (ap1 a (b ''PureBound'') (i_of_nat a b))
  (ar3 a (b ''PureAbs'') (i_of_string a b) (i_of_pure_typ a b))
  (ar2 a (b ''PureApp'') id)"

definition "i_of_internal_oid a b = internal_oid_rec
  (ap1 a (b ''Oid'') (i_of_nat a b))"

definition "i_of_internal_oids a b = internal_oids_rec
  (ap3 a (b ''Oids'')
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_nat a b))"

definition "i_of_ocl_collection b = ocl_collection_rec
  (b ''Set'')
  (b ''Sequence'')"

definition "i_of_ocl_multiplicity_single a b = ocl_multiplicity_single_rec
  (ap1 a (b ''Mult_nat'') (i_of_nat a b))
  (b ''Mult_star'')"

definition "i_of_ocl_multiplicity a b = ocl_multiplicity_rec
  (ap1 a (b ''OclMult'') (i_of_list a b (i_of_pair a b (i_of_ocl_multiplicity_single a b) (i_of_option a b (i_of_ocl_multiplicity_single a b)))))"

definition "i_of_ocl_ty_class_node a b f = ocl_ty_class_node_rec
  (ap5 a (b (ext ''ocl_ty_class_node_ext''))
    (i_of_nat a b)
    (i_of_ocl_multiplicity a b)
    (i_of_option a b (i_of_string a b))
    (i_of_string a b)
    (f a b))"

definition "i_of_ocl_ty_class a b f = ocl_ty_class_rec
  (ap6 a (b (ext ''ocl_ty_class_ext''))
    (i_of_string a b)
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_ocl_ty_class_node a b (K i_of_unit))
    (i_of_ocl_ty_class_node a b (K i_of_unit))
    (f a b))"

definition "i_of_ocl_ty a b = (\<lambda>f1 f2 f3. ocl_ty_rec f1 f2 f3 o co1 K)
  (b ''OclTy_boolean'')
  (b ''OclTy_integer'')
  (ap1 a (b ''OclTy_class'') (i_of_ocl_ty_class a b (K i_of_unit)))
  (ar2 a (b ''OclTy_collection'') (i_of_ocl_collection b))
  (ap1 a (b ''OclTy_raw'') (i_of_string a b))"

definition "i_of_ocl_class a b = (\<lambda>f0 f1 f2 f3 f4. ocl_class_rec_1 (co2 K (ar3 a f0 f1 f2)) f3 (\<lambda>_ _. f4))
  (b ''OclClass'')
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (* *)
    (b i_Nil)
    (ar2 a (b i_Cons) id)"

definition "i_of_ocl_class_raw a b f = ocl_class_raw_rec
  (ap4 a (b (ext ''ocl_class_raw_ext''))
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_option a b (i_of_string a b))
    (f a b))"

definition "i_of_ocl_association_type a b = ocl_association_type_rec
  (b ''OclAssTy_association'')
  (b ''OclAssTy_composition'')
  (b ''OclAssTy_aggregation'')"

definition "i_of_ocl_association a b f = ocl_association_rec
  (ap3 a (b (ext ''ocl_association_ext''))
    (i_of_ocl_association_type a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_ocl_multiplicity a b) (i_of_option a b (i_of_string a b)))))
    (f a b))"

definition "i_of_ocl_ass_class a b = ocl_ass_class_rec
  (ap2 a (b ''OclAssClass'')
    (i_of_ocl_association a b (K i_of_unit))
    (i_of_ocl_class_raw a b (K i_of_unit)))"

definition "i_of_ocl_data_shallow_base a b = ocl_data_shallow_base_rec
  (ap1 a (b ''ShallB_str'') (i_of_string a b))
  (ap1 a (b ''ShallB_self'') (i_of_internal_oid a b))"

definition "i_of_ocl_data_shallow a b = ocl_data_shallow_rec
  (ap1 a (b ''Shall_base'') (i_of_ocl_data_shallow_base a b))
  (ap1 a (b ''Shall_list'') (i_of_list a b (i_of_ocl_data_shallow_base a b)))"

definition "i_of_ocl_list_attr a b f = (\<lambda>f0. co4 (\<lambda>f1. ocl_list_attr_rec f0 (\<lambda>s _ a rec. f1 s rec a)) (ap3 a))
  (ap1 a (b ''OclAttrNoCast'') f)
  (b ''OclAttrCast'')
    (i_of_string a b)
    id
    f"

definition "i_of_ocl_instance_single a b f = ocl_instance_single_rec
  (ap4 a (b (ext ''ocl_instance_single_ext''))
    (i_of_string a b)
    (i_of_string a b)
    (i_of_ocl_list_attr a b (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_data_shallow a b))))
    (f a b))"

definition "i_of_ocl_instance a b = ocl_instance_rec
  (ap1 a (b ''OclInstance'')
    (i_of_list a b (i_of_ocl_instance_single a b (K i_of_unit))))"

definition "i_of_ocl_def_int a b = ocl_def_int_rec
  (ap1 a (b ''OclDefI'') (i_of_list a b (i_of_string a b)))"

definition "i_of_ocl_def_state_core a b f = ocl_def_state_core_rec
  (ap1 a (b ''OclDefCoreAdd'') (i_of_ocl_instance_single a b (K i_of_unit)))
  (b ''OclDefCoreSkip'')
  (ap1 a (b ''OclDefCoreBinding'') f)"

definition "i_of_ocl_def_state a b = ocl_def_state_rec
  (ap2 a (b ''OclDefSt'') (i_of_string a b) (i_of_list a b (i_of_ocl_def_state_core a b (i_of_string a b))))"

definition "i_of_ocl_def_pre_post a b = ocl_def_pre_post_rec
  (ap2 a (b ''OclDefPP'') (i_of_string a b) (i_of_string a b))"

definition "i_of_ocl_ctxt_prefix a b = ocl_ctxt_prefix_rec
  (b ''OclCtxtPre'')
  (b ''OclCtxtPost'')"

definition "i_of_ocl_ctxt_term a b = ocl_ctxt_term_rec
  (ap1 a (b ''T_pure'') (i_of_pure_term a b))
  (ap1 a (b ''T_to_be_parsed'') (i_of_string a b))"

definition "i_of_ocl_ctxt_pre_post a b f = ocl_ctxt_pre_post_rec
  (ap6 a (b (ext ''ocl_ctxt_pre_post_ext''))
    (i_of_string a b)
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_option a b (i_of_ocl_ty a b))
    (i_of_list a b (i_of_pair a b (i_of_ocl_ctxt_prefix a b) (i_of_ocl_ctxt_term a b)))
    (f a b))"

definition "i_of_ocl_ctxt2_pre_post = i_of_ocl_ctxt_pre_post"

definition "i_of_ocl_ctxt_inv a b f = ocl_ctxt_inv_rec
  (ap3 a (b (ext ''ocl_ctxt_inv_ext''))
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ctxt_term a b)))
    (f a b))"

definition "i_of_ocl_ctxt2_inv = i_of_ocl_ctxt_inv"

definition "i_of_ocl_flush_all a b = ocl_flush_all_rec
  (b ''OclFlushAll'')"

definition "i_of_ocl_deep_embed_ast a b = ocl_deep_embed_ast_rec
  (ap1 a (b ''OclAstClassRaw'') (i_of_ocl_class_raw a b (K i_of_unit)))
  (ap1 a (b ''OclAstAssociation'') (i_of_ocl_association a b (K i_of_unit)))
  (ap1 a (b ''OclAstAssClass'') (i_of_ocl_ass_class a b))
  (ap1 a (b ''OclAstInstance'') (i_of_ocl_instance a b))
  (ap1 a (b ''OclAstDefInt'') (i_of_ocl_def_int a b))
  (ap1 a (b ''OclAstDefState'') (i_of_ocl_def_state a b))
  (ap1 a (b ''OclAstDefPrePost'') (i_of_ocl_def_pre_post a b))
  (ap1 a (b ''OclAstCtxtPrePost'') (i_of_ocl_ctxt_pre_post a b (K i_of_unit)))
  (ap1 a (b ''OclAstCtxt2PrePost'') (i_of_ocl_ctxt2_pre_post a b (K i_of_unit)))
  (ap1 a (b ''OclAstCtxtInv'') (i_of_ocl_ctxt_inv a b (K i_of_unit)))
  (ap1 a (b ''OclAstCtxt2Inv'') (i_of_ocl_ctxt2_inv a b (K i_of_unit)))
  (ap1 a (b ''OclAstFlushAll'') (i_of_ocl_flush_all a b))"

definition "i_of_ocl_deep_mode a b = ocl_deep_mode_rec
  (b ''Gen_design'')
  (b ''Gen_analysis'')"

definition "i_of_ocl_compiler_config a b f = ocl_compiler_config_rec
  (ap12 a (b (ext ''ocl_compiler_config_ext''))
    (i_of_bool b)
    (i_of_option a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_list a b (i_of_string a b)) (i_of_string a b))))
    (i_of_internal_oids a b)
    (i_of_pair a b (i_of_nat a b) (i_of_nat a b))
    (i_of_ocl_deep_mode a b)
    (i_of_option a b (i_of_ocl_class a b))
    (i_of_list a b (i_of_ocl_deep_embed_ast a b))
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_ocl_instance_single a b (K i_of_unit)) (i_of_internal_oid a b))))
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_list a b (i_of_pair a b (i_of_internal_oids a b) (i_of_ocl_def_state_core a b (i_of_pair a b (i_of_string a b) (i_of_ocl_instance_single a b  (K i_of_unit))))))))
    (i_of_bool b)
    (i_of_pair a b (i_of_list a b (i_of_string a b)) (i_of_list a b (i_of_string a b)))
    (f a b))"

end

lemmas [code] =
  i_of.i_of_pair_def
  i_of.i_of_list_def
  i_of.i_of_option_def
  (* *)
  i_of.i_of_pure_indexname_def
  i_of.i_of_pure_class_def
  i_of.i_of_pure_sort_def
  i_of.i_of_pure_typ_def
  i_of.i_of_pure_term_def
  i_of.i_of_internal_oid_def
  i_of.i_of_internal_oids_def
  i_of.i_of_ocl_collection_def
  i_of.i_of_ocl_multiplicity_single_def
  i_of.i_of_ocl_multiplicity_def
  i_of.i_of_ocl_ty_class_node_def
  i_of.i_of_ocl_ty_class_def
  i_of.i_of_ocl_ty_def
  i_of.i_of_ocl_class_def
  i_of.i_of_ocl_class_raw_def
  i_of.i_of_ocl_association_type_def
  i_of.i_of_ocl_association_def
  i_of.i_of_ocl_ass_class_def
  i_of.i_of_ocl_data_shallow_base_def
  i_of.i_of_ocl_data_shallow_def
  i_of.i_of_ocl_list_attr_def
  i_of.i_of_ocl_instance_single_def
  i_of.i_of_ocl_instance_def
  i_of.i_of_ocl_def_int_def
  i_of.i_of_ocl_def_state_core_def
  i_of.i_of_ocl_def_state_def
  i_of.i_of_ocl_def_pre_post_def
  i_of.i_of_ocl_ctxt_prefix_def
  i_of.i_of_ocl_ctxt_term_def
  i_of.i_of_ocl_ctxt_pre_post_def
  i_of.i_of_ocl_ctxt2_pre_post_def
  i_of.i_of_ocl_ctxt_inv_def
  i_of.i_of_ocl_ctxt2_inv_def
  i_of.i_of_ocl_flush_all_def
  i_of.i_of_ocl_deep_embed_ast_def
  i_of.i_of_ocl_deep_mode_def
  i_of.i_of_ocl_compiler_config_def

subsubsection{* Isabelle *}

locale isabelle_of
begin

definition "i_Pair = ''Pair''"
definition "i_Nil = ''Nil''"
definition "i_Cons = ''Cons''"
definition "i_None = ''None''"
definition "i_Some = ''Some''"

(* *)

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b i_Pair) f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b i_Nil)
  (ar2 a (b i_Cons) f)"

definition "i_of_option a b f = option_rec
  (b i_None)
  (ap1 a (b i_Some) f)"

(* *)

definition "i_of_unit b = unit_rec
  (b ''()'')"

definition "i_of_bool b = bool_rec
  (b ''True'')
  (b ''False'')"

definition "i_of_nibble b = nibble_rec
  (b ''Nibble0'')
  (b ''Nibble1'')
  (b ''Nibble2'')
  (b ''Nibble3'')
  (b ''Nibble4'')
  (b ''Nibble5'')
  (b ''Nibble6'')
  (b ''Nibble7'')
  (b ''Nibble8'')
  (b ''Nibble9'')
  (b ''NibbleA'')
  (b ''NibbleB'')
  (b ''NibbleC'')
  (b ''NibbleD'')
  (b ''NibbleE'')
  (b ''NibbleF'')"

definition "i_of_char a b = char_rec
  (ap2 a (b ''Char'') (i_of_nibble b) (i_of_nibble b))"

definition "i_of_string a b = i_of_list a b (i_of_char a b)"

definition "i_of_nat a b = b o natural_of_str"

end

sublocale isabelle_of < i_of "id"
                             isabelle_of.i_of_string
                             isabelle_of.i_of_nat
                             isabelle_of.i_of_unit
                             isabelle_of.i_of_bool
                             isabelle_of.i_Pair
                             isabelle_of.i_Nil
                             isabelle_of.i_Cons
                             isabelle_of.i_None
                             isabelle_of.i_Some
done

context isabelle_of begin
  definition "ocl_embed a b =
    i_of_ocl_compiler_config a b (\<lambda> a b.
      i_of_pair a b
        (i_of_list a b (i_of_ocl_deep_embed_ast a b))
        (i_of_option a b (i_of_string a b)))"
end

definition "isabelle_of_ocl_embed = isabelle_of.ocl_embed"

lemmas [code] =
  isabelle_of.i_Pair_def
  isabelle_of.i_Nil_def
  isabelle_of.i_Cons_def
  isabelle_of.i_None_def
  isabelle_of.i_Some_def

  isabelle_of.i_of_pair_def
  isabelle_of.i_of_list_def
  isabelle_of.i_of_option_def
  isabelle_of.i_of_unit_def
  isabelle_of.i_of_bool_def
  isabelle_of.i_of_nibble_def
  isabelle_of.i_of_char_def
  isabelle_of.i_of_string_def
  isabelle_of.i_of_nat_def

  isabelle_of.ocl_embed_def

(* *)

definition "isabelle_apply s l = flatten [s, flatten (List_map (\<lambda> s. flatten ['' ('', s, '')'']) l)]"

subsubsection{* SML *}

locale sml_of
begin

definition "i_Pair = ''I''"
definition "i_Nil = ''nil''"
definition "i_Cons = ''uncurry cons''" (* val cons2 = uncurry cons *)
definition "i_None = ''NONE''"
definition "i_Some = ''SOME''"

(* *)

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b i_Pair) f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b i_Nil)
  (ar2 a (b i_Cons) f)"

definition "i_of_option a b f = option_rec
  (b i_None)
  (ap1 a (b i_Some) f)"

(* *)

definition "i_of_unit b = unit_rec
  (b ''()'')"

definition "i_of_bool b = bool_rec
  (b ''true'')
  (b ''false'')"

definition "i_of_string a b =
 (let c = [Char Nibble2 Nibble2] in
  (\<lambda>x. b (flatten [''(String.explode '', c, List_replace x (Char Nibble0 NibbleA) (Char Nibble5 NibbleC # ''n''), c,'')''])))"

definition "i_of_nat a b = (\<lambda>x. b (flatten [''(Code_Numeral.Nat '', natural_of_str x, '')'']))"

end

sublocale sml_of < i_of "\<lambda>x # xs \<Rightarrow> flatten [uppercase_of_str [x], xs]"
                        sml_of.i_of_string
                        sml_of.i_of_nat
                        sml_of.i_of_unit
                        sml_of.i_of_bool
                        sml_of.i_Pair
                        sml_of.i_Nil
                        sml_of.i_Cons
                        sml_of.i_None
                        sml_of.i_Some
done

context sml_of begin
  definition "ocl_unit a b = i_of_ocl_compiler_config a b (\<lambda> _. i_of_unit)"
end

definition "sml_of_ocl_unit = sml_of.ocl_unit"

lemmas [code] =
  sml_of.i_Pair_def
  sml_of.i_Nil_def
  sml_of.i_Cons_def
  sml_of.i_None_def
  sml_of.i_Some_def

  sml_of.i_of_pair_def
  sml_of.i_of_list_def
  sml_of.i_of_option_def
  sml_of.i_of_unit_def
  sml_of.i_of_bool_def
  sml_of.i_of_string_def
  sml_of.i_of_nat_def

  sml_of.ocl_unit_def

(* *)

definition "sml_apply s l = flatten [s, '' ('', bug_ocaml_extraction (case l of x # xs \<Rightarrow> flatten [x, flatten (List_map (\<lambda>s. flatten ['', '', s]) xs)]), '')'' ]"

section{* Generation to Deep Form: OCaml *}

subsection{* beginning (lazy code printing) *}

ML{*
structure Code_printing = struct
datatype code_printing = Code_printing of (string * (bstring * Code_Printer.const_syntax option) list, string * (bstring * Code_Printer.tyco_syntax option) list,
              string * (bstring * string option) list, (string * string) * (bstring * unit option) list, (string * string) * (bstring * unit option) list,
              bstring * (bstring * (string * string list) option) list)
              Code_Symbol.attr
              list

structure Data_code = Theory_Data
  (type T = code_printing list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_empty = ""

local
val parse_classrel_ident = Parse.class --| @{keyword "<"} -- Parse.class
val parse_inst_ident = Parse.xname --| @{keyword "::"} -- Parse.class

(* *)
fun parse_single_symbol_pragma parse_keyword parse_isa parse_target =
  parse_keyword |-- Parse.!!! (parse_isa --| (@{keyword "\<rightharpoonup>"} || @{keyword "=>"})
    -- Parse.and_list1 (@{keyword "("} |-- (Parse.name --| @{keyword ")"} -- Scan.option parse_target)))

fun parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  parse_single_symbol_pragma @{keyword "constant"} Parse.term parse_const
    >> Code_Symbol.Constant
  || parse_single_symbol_pragma @{keyword "type_constructor"} Parse.type_const parse_tyco
    >> Code_Symbol.Type_Constructor
  || parse_single_symbol_pragma @{keyword "type_class"} Parse.class parse_class
    >> Code_Symbol.Type_Class
  || parse_single_symbol_pragma @{keyword "class_relation"} parse_classrel_ident parse_classrel
    >> Code_Symbol.Class_Relation
  || parse_single_symbol_pragma @{keyword "class_instance"} parse_inst_ident parse_inst
    >> Code_Symbol.Class_Instance
  || parse_single_symbol_pragma @{keyword "code_module"} Parse.name parse_module
    >> Code_Symbol.Module

fun parse_symbol_pragmas parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  Parse.enum1 "|" (Parse.group (fn () => "code symbol pragma")
    (parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module))

in
val () =
  Outer_Syntax.command @{command_spec "lazy_code_printing"} "declare dedicated printing for code symbols"
    (parse_symbol_pragmas (Code_Printer.parse_const_syntax) (Code_Printer.parse_tyco_syntax)
      Parse.string (Parse.minus >> K ()) (Parse.minus >> K ())
      (Parse.text -- Scan.optional (@{keyword "attach"} |-- Scan.repeat1 Parse.term) [])
      >> (fn code =>
            Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn l => Code_printing code :: l)))))
end

fun apply_code_printing thy =
    (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
 |> (fn l => fold (fn Code_printing l => fold Code_Target.set_printings l) l thy)

val () =
  Outer_Syntax.command @{command_spec "apply_code_printing"} "apply dedicated printing for code symbols"
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory apply_code_printing))

fun reflect_ml txt thy =
  case ML_Context.exec (fn () => ML_Context.eval_text false Position.none txt) (Context.Theory thy) of
    Context.Theory thy => thy

fun apply_code_printing_reflect thy =
    (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
 |> (fn l => fold (fn Code_printing l =>
      fold (fn Code_Symbol.Module (_, l) =>
                 fold (fn ("SML", SOME (txt, _)) => reflect_ml txt
                        | _ => I) l
             | _ => I) l) l thy)

val () =
  Outer_Syntax.command @{command_spec "apply_code_printing_reflect"} "apply dedicated printing for code symbols"
    (Parse.ML_source >> (fn (txt, _) => Toplevel.theory (apply_code_printing_reflect o reflect_ml txt)))

end
*}

subsection{* beginning *}

  (* We put in 'CodeConst' functions using characters
     not allowed in a Isabelle 'code_const' expr
     (e.g. '_', '"', ...) *)

lazy_code_printing code_module "CodeType" \<rightharpoonup> (Haskell) {*
  type MlInt = Integer
; type MlMonad a = IO a
*} | code_module "CodeConst" \<rightharpoonup> (Haskell) {*
  import System.Directory
; import System.IO
; import qualified CodeConst.Printf

; outFile1 f file = (do
  fileExists <- doesFileExist file
  if fileExists then error ("File exists " ++ file ++ "\n") else do
    h <- openFile file WriteMode
    f (\pat -> hPutStr h . CodeConst.Printf.sprintf1 pat)
    hClose h)

; outStand1 :: ((String -> String -> IO ()) -> IO ()) -> IO ()
; outStand1 f = f (\pat -> putStr . CodeConst.Printf.sprintf1 pat)
*} | code_module "CodeConst.Monad" \<rightharpoonup> (Haskell) {*
  bind a = (>>=) a
; return :: a -> IO a
; return = Prelude.return
*} | code_module "CodeConst.Printf" \<rightharpoonup> (Haskell) {*
  import Text.Printf
; sprintf0 = id

; sprintf1 :: PrintfArg a => String -> a -> String
; sprintf1 = printf

; sprintf2 :: PrintfArg a => PrintfArg b => String -> a -> b -> String
; sprintf2 = printf

; sprintf3 :: PrintfArg a => PrintfArg b => PrintfArg c => String -> a -> b -> c -> String
; sprintf3 = printf

; sprintf4 :: PrintfArg a => PrintfArg b => PrintfArg c => PrintfArg d => String -> a -> b -> c -> d -> String
; sprintf4 = printf

; sprintf5 :: PrintfArg a => PrintfArg b => PrintfArg c => PrintfArg d => PrintfArg e => String -> a -> b -> c -> d -> e -> String
; sprintf5 = printf
*} | code_module "CodeConst.String" \<rightharpoonup> (Haskell) {*
  concat s [] = []
; concat s (x : xs) = x ++ concatMap ((++) s) xs
*} | code_module "CodeConst.Sys" \<rightharpoonup> (Haskell) {*
  import System.Directory
; isDirectory2 = doesDirectoryExist
*} | code_module "CodeConst.To" \<rightharpoonup> (Haskell) {*
  nat = id

*} | code_module "" \<rightharpoonup> (OCaml) {*
module CodeType = struct
  type mlInt = int

  type 'a mlMonad = 'a option
end

module CodeConst = struct
  let outFile1 f file =
    try
      let () = if Sys.file_exists file then Printf.eprintf "File exists \"%S\"\n" file else () in
      let oc = open_out file in
      let b = f (fun s a -> try Some (Printf.fprintf oc s a) with _ -> None) in
      let () = close_out oc in
      b
    with _ -> None

  let outStand1 f =
    f (fun s a -> try Some (Printf.fprintf stdout s a) with _ -> None)

  module Monad = struct
    let bind = function
        None -> fun _ -> None
      | Some a -> fun f -> f a
    let return a = Some a
  end

  module Printf = struct
    include Printf
    let sprintf0 = sprintf
    let sprintf1 = sprintf
    let sprintf2 = sprintf
    let sprintf3 = sprintf
    let sprintf4 = sprintf
    let sprintf5 = sprintf
  end

  module String = String

  module Sys = struct open Sys
    let isDirectory2 s = try Some (is_directory s) with _ -> None
  end

  module To = struct
    let nat big_int x = Big_int.int_of_big_int (big_int x)
  end
end

*} | code_module "" \<rightharpoonup> (Scala) {*
object CodeType {
  type mlMonad [A] = Option [A]
  type mlInt = Int
}

object CodeConst {
  def outFile1 [A] (f : (String => A => Option [Unit]) => Option [Unit], file0 : String) : Option [Unit] = {
    val file = new java.io.File (file0)
    if (file .isFile) {
      None
    } else {
      val writer = new java.io.PrintWriter (file)
      f ((fmt : String) => (s : A) => Some (writer .write (fmt .format (s))))
      Some (writer .close ())
    }
  }

  def outStand1 [A] (f : (String => A => Option [Unit]) => Option [Unit]) : Option[Unit] = {
    f ((fmt : String) => (s : A) => Some (print (fmt .format (s))))
  }

  object Monad {
    def bind [A, B] (x : Option [A], f : A => Option [B]) : Option [B] = x match {
      case None => None
      case Some (a) => f (a)
    }
    def Return [A] (a : A) = Some (a)
  }
  object Printf {
    def sprintf0 (x0 : String) = x0
    def sprintf1 [A1] (fmt : String, x1 : A1) = fmt .format (x1)
    def sprintf2 [A1, A2] (fmt : String, x1 : A1, x2 : A2) = fmt .format (x1, x2)
    def sprintf3 [A1, A2, A3] (fmt : String, x1 : A1, x2 : A2, x3 : A3) = fmt .format (x1, x2, x3)
    def sprintf4 [A1, A2, A3, A4] (fmt : String, x1 : A1, x2 : A2, x3 : A3, x4 : A4) = fmt .format (x1, x2, x3, x4)
    def sprintf5 [A1, A2, A3, A4, A5] (fmt : String, x1 : A1, x2 : A2, x3 : A3, x4 : A4, x5 : A5) = fmt .format (x1, x2, x3, x4, x5)
  }
  object String {
    def concat (s : String, l : List [String]) = l filter (_ .nonEmpty) mkString s
  }
  object Sys {
    def isDirectory2 (s : String) = Some (new java.io.File (s) .isDirectory)
  }
  object To {
    def nat [A] (f : A => BigInt, x : A) = f (x) .intValue ()
  }
}

*} | code_module "" \<rightharpoonup> (SML) {*
structure CodeType = struct
  type mlInt = string
  type 'a mlMonad = 'a option
end

structure CodeConst = struct
  structure Monad = struct
    val bind = fn
        NONE => (fn _ => NONE)
      | SOME a => fn f => f a
    val return = SOME
  end

  structure Printf = struct
    local
      fun sprintf s l =
        case String.fields (fn #"%" => true | _ => false) s of
          [] => ""
        | [x] => x
        | x :: xs =>
            let fun aux acc l_pat l_s =
              case l_pat of
                [] => rev acc
              | x :: xs => aux (String.extract (x, 1, NONE) :: hd l_s :: acc) xs (tl l_s) in
            String.concat (x :: aux [] xs l)
      end
    in
      fun sprintf0 s_pat = s_pat
      fun sprintf1 s_pat s1 = sprintf s_pat [s1]
      fun sprintf2 s_pat s1 s2 = sprintf s_pat [s1, s2]
      fun sprintf3 s_pat s1 s2 s3 = sprintf s_pat [s1, s2, s3]
      fun sprintf4 s_pat s1 s2 s3 s4 = sprintf s_pat [s1, s2, s3, s4]
      fun sprintf5 s_pat s1 s2 s3 s4 s5 = sprintf s_pat [s1, s2, s3, s4, s5]
    end
  end

  structure String = struct
    val concat = String.concatWith
  end

  structure Sys = struct
    val isDirectory2 = SOME o File.is_dir o Path.explode handle ERROR _ => K NONE
  end

  structure To = struct
    fun nat f = Int.toString o f
  end

  fun outFile1 f file =
    let
      val pfile = Path.explode file
      val () = if File.exists pfile then error ("File exists \"" ^ file ^ "\"\n") else ()
      val oc = Unsynchronized.ref []
      val _ = f (fn a => fn b => SOME (oc := Printf.sprintf1 a b :: (Unsynchronized.! oc))) in
      SOME (File.write_list pfile (rev (Unsynchronized.! oc))) handle _ => NONE
    end

  fun outStand1 f = outFile1 f (Unsynchronized.! stdout_file)
end

*}

subsection{* ML type *}

datatype ml_int = ML_int
code_printing type_constructor ml_int \<rightharpoonup> (Haskell) "CodeType.MlInt" (* syntax! *)
            | type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (Scala) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (SML) "CodeType.mlInt"

datatype 'a ml_monad = ML_monad 'a
code_printing type_constructor ml_monad \<rightharpoonup> (Haskell) "CodeType.MlMonad _" (* syntax! *)
            | type_constructor ml_monad \<rightharpoonup> (OCaml) "_ CodeType.mlMonad"
            | type_constructor ml_monad \<rightharpoonup> (Scala) "CodeType.mlMonad [_]"
            | type_constructor ml_monad \<rightharpoonup> (SML) "_ CodeType.mlMonad"

(* *)

type_synonym ml_string = String.literal

subsection{* ML code const *}

text{* ... *}

consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) (* fprintf *) \<Rightarrow> unit ml_monad) \<Rightarrow> ml_string \<Rightarrow> unit ml_monad"
code_printing constant out_file1 \<rightharpoonup> (Haskell) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (Scala) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (SML) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) (* fprintf *) \<Rightarrow> unit ml_monad) \<Rightarrow> unit ml_monad"
code_printing constant out_stand1 \<rightharpoonup> (Haskell) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (Scala) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (SML) "CodeConst.outStand1"

text{* module Monad *}

consts bind :: "'a ml_monad \<Rightarrow> ('a \<Rightarrow> 'b ml_monad) \<Rightarrow> 'b ml_monad"
code_printing constant bind \<rightharpoonup> (Haskell) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (OCaml) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (Scala) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (SML) "CodeConst.Monad.bind"

consts return :: "'a \<Rightarrow> 'a ml_monad"
code_printing constant return \<rightharpoonup> (Haskell) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (OCaml) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (Scala) "CodeConst.Monad.Return" (* syntax! *)
            | constant return \<rightharpoonup> (SML) "CodeConst.Monad.return"

text{* module Printf *}

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
code_printing constant sprintf0 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf0"

consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
code_printing constant sprintf1 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf1"

consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
code_printing constant sprintf2 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf2"

consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
code_printing constant sprintf3 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf3"

consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
code_printing constant sprintf4 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf4"

consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
code_printing constant sprintf5 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf5"

text{* module String *}

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_printing constant String_concat \<rightharpoonup> (Haskell) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (OCaml) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (Scala) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (SML) "CodeConst.String.concat"

text{* module Sys *}

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool ml_monad"
code_printing constant Sys_is_directory2 \<rightharpoonup> (Haskell) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (Scala) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (SML) "CodeConst.Sys.isDirectory2"

text{* module To *}

consts ToNat :: "(nat \<Rightarrow> integer) \<Rightarrow> nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (Haskell) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (Scala) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (SML) "CodeConst.To.nat"

subsection{* ... *}

locale s_of =
  fixes To_string :: "string \<Rightarrow> ml_string"
  fixes To_nat :: "nat \<Rightarrow> ml_int"
begin
definition "To_oid = internal_oid_rec To_nat"
end

subsection{* s of ... *} (* s_of *)

context s_of
begin
definition "s_of_dataty _ = (\<lambda> Datatype n l \<Rightarrow>
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

fun_quick s_of_rawty where "s_of_rawty e = (\<lambda>
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (List.map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name)
  | Ty_arrow ty1 ty2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_rawty ty1) (To_string unicode_Rightarrow) (s_of_rawty ty2)
  | Ty_times ty1 ty2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_rawty ty1) (To_string unicode_times) (s_of_rawty ty2)) e"

definition "s_of_ty_synonym _ = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

fun_quick s_of_pure_term where "s_of_pure_term e = (\<lambda>
    PureConst s _ \<Rightarrow> To_string s
  | PureFree s _ \<Rightarrow> To_string s
  | PureApp t1 t2 \<Rightarrow> sprintf2 (STR ''(%s) (%s)'') (s_of_pure_term t1) (s_of_pure_term t2)) e"

fun_quick s_of_expr where "s_of_expr e = (\<lambda>
    Expr_case e l \<Rightarrow> sprintf2 (STR ''(case %s of %s)'') (s_of_expr e) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  | Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Expr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Expr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot0 e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (s_of_rawty s)
  | Expr_bind symb l e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (String_concat (STR '' '') (List_map To_string l)) (s_of_expr e)
  | Expr_bind0 symb e1 e2 \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (s_of_expr e1) (s_of_expr e2)
  | Expr_function l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string unicode_lambda) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  (*| Expr_apply s [e] \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (s_of_expr e)*)
  | Expr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_applys e l \<Rightarrow> sprintf2 (STR ''((%s) %s)'') (s_of_expr e) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_postunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_preunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_expr e) (To_string p_right)
  | Expr_if_then_else e_if e_then e_else \<Rightarrow> sprintf3 (STR ''if %s then %s else %s'') (s_of_expr e_if) (s_of_expr e_then) (s_of_expr e_else)
  | Expr_inner pure \<Rightarrow> s_of_pure_term pure) e"

fun_quick s_of_sexpr where "s_of_sexpr e = (\<lambda>
    Sexpr_string l \<Rightarrow> let c = STR [Char Nibble2 Nibble2] in
                      sprintf3 (STR ''%s%s%s'') c (String_concat (STR '' '') (List_map To_string l)) c
  | Sexpr_rewrite_val e1 symb e2 \<Rightarrow> sprintf3 (STR ''val %s %s %s'') (s_of_sexpr e1) (To_string symb) (s_of_sexpr e2)
  | Sexpr_rewrite_fun e1 symb e2 \<Rightarrow> sprintf3 (STR ''fun %s %s %s'') (s_of_sexpr e1) (To_string symb) (s_of_sexpr e2)
  | Sexpr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Sexpr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Sexpr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_sexpr e1) (s_of_sexpr (Sexpr_basic [s])) (s_of_sexpr e2)
  | Sexpr_annot e s \<Rightarrow> sprintf2 (STR ''(%s:%s)'') (s_of_sexpr e) (To_string s)
  | Sexpr_function l \<Rightarrow> sprintf1 (STR ''(fn %s)'') (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf2 (STR ''%s => %s'') (s_of_sexpr s1) (s_of_sexpr s2)) l))
  | Sexpr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_sexpr e)) l))
  | Sexpr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_sexpr e) (To_string p_right)
  | Sexpr_let_open s e \<Rightarrow> sprintf2 (STR ''let open %s in %s end'') (To_string s) (s_of_sexpr e)) e"

definition "s_of_sexpr_extended = (\<lambda>
    Sexpr_extended s \<Rightarrow> s_of_sexpr s
  | Sexpr_ocl ocl \<Rightarrow> s_of_sexpr
     (Sexpr_apply ''Generation_mode.update_compiler_config''
       [Sexpr_apply ''K'' [Sexpr_let_open ''OCL'' (Sexpr_basic [sml_of_ocl_unit sml_apply id ocl])]]))"

definition "s_of_instantiation_class _ = (\<lambda> Instantiation n n_def expr \<Rightarrow>
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

definition "s_of_defs_overloaded _ = (\<lambda> Defs_overloaded n e \<Rightarrow>
    sprintf2 (STR ''defs(overloaded) %s : \"%s\"'') (To_string n) (s_of_expr e))"

definition "s_of_consts_class _ = (\<lambda> Consts_raw n ty symb \<Rightarrow>
    sprintf4 (STR ''consts %s :: \"%s\" (\"%s %s\")'') (To_string n) (s_of_rawty ty) (To_string Consts_value) (To_string symb))"

definition "s_of_definition_hol _ = (\<lambda>
    Definition e \<Rightarrow> sprintf1 (STR ''definition \"%s\"'') (s_of_expr e)
  | Definition_abbrev name (abbrev, prio) e \<Rightarrow> sprintf4 (STR ''definition %s (\"(1%s)\" %d)
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (To_nat prio) (s_of_expr e)
  | Definition_abbrev0 name abbrev e \<Rightarrow> sprintf3 (STR ''definition %s (\"%s\")
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (s_of_expr e))"

fun_quick s_of_ntheorem_aux where "s_of_ntheorem_aux lacc e =
  ((* FIXME regroup all the 'let' declarations at the beginning *)
   (*let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l)))
     ; f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l)))
     ; f_symmetric = (STR ''symmetric'', STR '''')
     ; s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
   *)\<lambda> Thm_str s \<Rightarrow> To_string s
   | Thm_THEN (Thm_str s) e2 \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
       s_base s ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_THEN e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_simplified (Thm_str s) e2 \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
       s_base s ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_simplified e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_symmetric (Thm_str s) \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
let f_symmetric = (STR ''symmetric'', STR '''') in
       s_base s (f_symmetric # lacc)
   | Thm_symmetric e1 \<Rightarrow>
let f_symmetric = (STR ''symmetric'', STR '''') in
       s_of_ntheorem_aux (f_symmetric # lacc) e1
   | Thm_where (Thm_str s) l \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l))) in
       s_base s (f_where l # lacc)
   | Thm_where e1 l \<Rightarrow>
let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l))) in
       s_of_ntheorem_aux (f_where l # lacc) e1
   | Thm_of (Thm_str s) l \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
let f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l))) in
       s_base s (f_of l # lacc)
   | Thm_of e1 l \<Rightarrow>
let f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l))) in
       s_of_ntheorem_aux (f_of l # lacc) e1
   | Thm_OF (Thm_str s) e2 \<Rightarrow>
let s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
       s_base s ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_OF e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc) e1) e"

definition "s_of_ntheorem = s_of_ntheorem_aux []"

definition "s_of_ntheorem_list l = String_concat (STR ''
                            '') (List_map s_of_ntheorem l)"

definition "s_of_lemmas_simp _ = (\<lambda> Lemmas_simp s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (s_of_ntheorem_list l)
                                  | Lemmas_simps s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map To_string l)))"

fun_quick s_of_tactic where "s_of_tactic expr = (\<lambda>
    Tac_rule s \<Rightarrow> sprintf1 (STR ''rule %s'') (s_of_ntheorem s)
  | Tac_drule s \<Rightarrow> sprintf1 (STR ''drule %s'') (s_of_ntheorem s)
  | Tac_erule s \<Rightarrow> sprintf1 (STR ''erule %s'') (s_of_ntheorem s)
  | Tac_intro l \<Rightarrow> sprintf1 (STR ''intro %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_elim s \<Rightarrow> sprintf1 (STR ''elim %s'') (s_of_ntheorem s)
  | Tac_subst_l l s =>
      if l = [''0''] then
        sprintf1 (STR ''subst %s'') (s_of_ntheorem s)
      else
        sprintf2 (STR ''subst (%s) %s'') (String_concat (STR '' '') (List_map To_string l)) (s_of_ntheorem s)
  | Tac_insert l => sprintf1 (STR ''insert %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_plus t \<Rightarrow> sprintf1 (STR ''(%s)+'') (String_concat (STR '', '') (List.map s_of_tactic t))
  | Tac_option t \<Rightarrow> sprintf1 (STR ''(%s)?'') (String_concat (STR '', '') (List.map s_of_tactic t))
  | Tac_blast None \<Rightarrow> sprintf0 (STR ''blast'')
  | Tac_blast (Some n) \<Rightarrow> sprintf1 (STR ''blast %d'') (To_nat n)
  | Tac_simp \<Rightarrow> sprintf0 (STR ''simp'')
  | Tac_simp_add l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_simp_add0 l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_simp_add_del l_add l_del \<Rightarrow> sprintf2 (STR ''simp add: %s del: %s'') (String_concat (STR '' '') (List_map To_string l_add)) (String_concat (STR '' '') (List_map To_string l_del))
  | Tac_simp_only l \<Rightarrow> sprintf1 (STR ''simp only: %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_simp_all \<Rightarrow> sprintf0 (STR ''simp_all'')
  | Tac_simp_all_add s \<Rightarrow> sprintf1 (STR ''simp_all add: %s'') (To_string s)
  | Tac_auto_simp_add l \<Rightarrow> sprintf1 (STR ''auto simp: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_auto_simp_add_split l_simp l_split \<Rightarrow>
      let f = String_concat (STR '' '') in
      sprintf2 (STR ''auto simp: %s split: %s'') (f (List_map s_of_ntheorem l_simp)) (f (List_map To_string l_split))
  | Tac_rename_tac l \<Rightarrow> sprintf1 (STR ''rename_tac %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_case_tac e \<Rightarrow> sprintf1 (STR ''case_tac \"%s\"'') (s_of_expr e)) expr"

definition "s_of_tactic_last = (\<lambda> Tacl_done \<Rightarrow> STR ''done''
                                | Tacl_by l_apply \<Rightarrow> sprintf1 (STR ''by(%s)'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
                                | Tacl_sorry \<Rightarrow> STR ''sorry'')"

definition "s_of_tac_apply = (
  let scope_thesis = sprintf1 (STR ''  proof - %s show ?thesis
'') in
  \<lambda> App [] \<Rightarrow> STR ''''
  | App l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
  | App_using l \<Rightarrow> sprintf1 (STR ''  using %s
'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | App_unfolding l \<Rightarrow> sprintf1 (STR ''  unfolding %s
'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | App_let e_name e_body \<Rightarrow> scope_thesis (sprintf2 (STR ''let %s = \"%s\"'') (s_of_expr e_name) (s_of_expr e_body))
  | App_have n e e_last \<Rightarrow> scope_thesis (sprintf3 (STR ''have %s: \"%s\" %s'') (To_string n) (s_of_expr e) (s_of_tactic_last e_last))
  | App_fix l \<Rightarrow> scope_thesis (sprintf1 (STR ''fix %s'') (String_concat (STR '' '') (List_map To_string l))))"

definition "s_of_lemma_by _ =
 (\<lambda> Lemma_by n l_spec l_apply tactic_last \<Rightarrow>
    sprintf4 (STR ''lemma %s : \"%s\"
%s%s'')
      (To_string n)
      (String_concat (sprintf1 (STR '' %s '') (To_string unicode_Longrightarrow)) (List_map s_of_expr l_spec))
      (String_concat (STR '''') (List_map (\<lambda> [] \<Rightarrow> STR '''' | l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))) l_apply))
      (s_of_tactic_last tactic_last)
  | Lemma_by_assum n l_spec concl l_apply tactic_last \<Rightarrow>
    sprintf5 (STR ''lemma %s : %s
%s%s %s'')
      (To_string n)
      (String_concat (STR '''') (List_map (\<lambda>(n, b, e).
          sprintf2 (STR ''
assumes %s\"%s\"'')
            (let n = if b then flatten [n, ''[simp]''] else n in
             if n = '''' then STR '''' else sprintf1 (STR ''%s: '') (To_string n))
            (s_of_expr e)) l_spec
       @@
       [sprintf1 (STR ''
shows \"%s\"'') (s_of_expr concl)]))
      (String_concat (STR '''') (List_map s_of_tac_apply l_apply))
      (s_of_tactic_last tactic_last)
      (String_concat (STR '' '')
        (List_map
          (\<lambda>_. STR ''qed'')
          (filter (\<lambda> App_let _ _ \<Rightarrow> True | App_have _ _ _ \<Rightarrow> True | App_fix _ \<Rightarrow> True | _ \<Rightarrow> False) l_apply))))"

definition "s_of_axiom _ = (\<lambda> Axiom n e \<Rightarrow> sprintf2 (STR ''axiomatization where %s:
\"%s\"'') (To_string n) (s_of_expr e))"

definition "s_of_section_title ocl = (\<lambda> Section_title n section_title \<Rightarrow>
  if D_disable_thy_output ocl then
    STR ''''
  else
    sprintf2 (STR ''%s{* %s *}'')
      (To_string ((if n = 0 then ''''
                   else if n = 1 then ''sub''
                   else ''subsub'') @@ ''section''))
      (To_string section_title))"

definition "s_of_text _ = (\<lambda> Text s \<Rightarrow> sprintf1 (STR ''text{* %s *}'') (To_string s))"

definition "s_of_ml _ = (\<lambda> Ml e \<Rightarrow> sprintf1 (STR ''ML{* %s *}'') (s_of_sexpr e))"

definition "s_of_thm _ = (\<lambda> Thm thm \<Rightarrow> sprintf1 (STR ''thm %s'') (s_of_ntheorem_list thm))"

definition "s_of_ctxt2_term = (\<lambda> T_pure pure \<Rightarrow> s_of_pure_term pure
                               | T_to_be_parsed s \<Rightarrow> To_string s)"

definition "s_of_ocl_deep_embed_ast _ =
 (\<lambda> OclAstCtxt2PrePost ctxt \<Rightarrow>
      sprintf5 (STR ''Context[shallow] %s :: %s (%s) : %s
%s'')
        (To_string (Ctxt_ty ctxt))
        (To_string (Ctxt_fun_name ctxt))
        (String_concat (STR '', '')
          (List_map
            (\<lambda> (s, ty). sprintf2 (STR ''%s : %s'') (To_string s) (To_string (str_of_ty ty)))
            (Ctxt_fun_ty_arg ctxt)))
        (case Ctxt_fun_ty_out ctxt of None \<Rightarrow> STR ''Void''
                                     | Some ty \<Rightarrow> To_string (str_of_ty ty))
        (String_concat (STR ''
'')
          (List_map
            (\<lambda> (pref, s). sprintf2 (STR ''  %s : `%s`'')
              (case pref of OclCtxtPre \<Rightarrow> STR ''Pre''
                          | OclCtxtPost \<Rightarrow> STR ''Post'')
              (s_of_ctxt2_term s))
            (Ctxt_expr ctxt)))
  | OclAstCtxt2Inv ctxt \<Rightarrow>
      sprintf2 (STR ''Context[shallow] %s
%s'')
        (To_string (Ctxt_inv_ty ctxt))
        (String_concat (STR ''
'')
          (List_map
            (\<lambda> (n, s). sprintf2 (STR ''  Inv %s : `%s`'')
              (To_string n)
              (s_of_ctxt2_term s))
            (Ctxt_inv_expr ctxt))))"

definition "s_of_thy ocl =
            (\<lambda> Theory_dataty dataty \<Rightarrow> s_of_dataty ocl dataty
             | Theory_ty_synonym ty_synonym \<Rightarrow> s_of_ty_synonym ocl ty_synonym
             | Theory_instantiation_class instantiation_class \<Rightarrow> s_of_instantiation_class ocl instantiation_class
             | Theory_defs_overloaded defs_overloaded \<Rightarrow> s_of_defs_overloaded ocl defs_overloaded
             | Theory_consts_class consts_class \<Rightarrow> s_of_consts_class ocl consts_class
             | Theory_definition_hol definition_hol \<Rightarrow> s_of_definition_hol ocl definition_hol
             | Theory_lemmas_simp lemmas_simp \<Rightarrow> s_of_lemmas_simp ocl lemmas_simp
             | Theory_lemma_by lemma_by \<Rightarrow> s_of_lemma_by ocl lemma_by
             | Theory_axiom axiom \<Rightarrow> s_of_axiom ocl axiom
             | Theory_section_title section_title \<Rightarrow> s_of_section_title ocl section_title
             | Theory_text text \<Rightarrow> s_of_text ocl text
             | Theory_ml ml \<Rightarrow> s_of_ml ocl ml
             | Theory_thm thm \<Rightarrow> s_of_thm ocl thm)"

definition "s_of_generation_syntax _ = (\<lambda> Generation_syntax_shallow mode \<Rightarrow>
  sprintf1 (STR ''generation_syntax [ shallow (generation_semantics [ %s ]) ]'') (case mode of Gen_design \<Rightarrow> STR ''design'' | Gen_analysis \<Rightarrow> STR ''analysis''))"

definition "s_of_ml_extended _ = (\<lambda> Ml_extended e \<Rightarrow> sprintf1 (STR ''setup{* %s *}'') (s_of_sexpr_extended e))"

definition "s_of_thy_extended ocl = (\<lambda>
    Isab_thy thy \<Rightarrow> s_of_thy ocl thy
  | Isab_thy_generation_syntax generation_syntax \<Rightarrow> s_of_generation_syntax ocl generation_syntax
  | Isab_thy_ml_extended ml_extended \<Rightarrow> s_of_ml_extended ocl ml_extended
  | Isab_thy_ocl_deep_embed_ast ocl_deep_embed_ast \<Rightarrow> s_of_ocl_deep_embed_ast ocl ocl_deep_embed_ast)"

definition "s_of_thy_list ocl l_thy =
  (let (th_beg, th_end) = case D_file_out_path_dep ocl of None \<Rightarrow> ([], [])
   | Some (name, fic_import, fic_import_boot) \<Rightarrow>
       ( [ sprintf2 (STR ''theory %s imports %s begin'') (To_string name) (s_of_expr (expr_binop '' '' (List_map Expr_string (fic_import @@ (if D_generation_syntax_shallow ocl then [fic_import_boot] else []))))) ]
       , [ STR '''', STR ''end'' ]) in
  flatten
        [ th_beg
        , flatten (fst (fold_list (\<lambda>l (i, cpt).
            let (l_thy, lg) = fold_list (\<lambda>l n. (s_of_thy_extended ocl l, Succ n)) l 0 in
            (( STR ''''
             # sprintf4 (STR ''%s(* %d ************************************ %d + %d *)'')
                 (To_string (if ocl_compiler_config.more ocl then '''' else [char_escape])) (To_nat (Succ i)) (To_nat cpt) (To_nat lg)
             # l_thy), Succ i, cpt + lg)) l_thy (D_output_position ocl)))
        , th_end ])"
end

subsection{* conclusion *}

definition "List_iterM f l =
  List.fold (\<lambda>x m. bind m (\<lambda> () \<Rightarrow> f x)) l (return ())"

context s_of
begin
definition "write_file ocl = (
  let (l_thy, Sys_argv) = ocl_compiler_config.more ocl
    ; (is_file, f_output) = case (D_file_out_path_dep ocl, Sys_argv)
     of (Some (file_out, _), Some dir) \<Rightarrow>
          let dir = To_string dir in
          (True, \<lambda>f. bind (Sys_is_directory2 dir) (\<lambda> Sys_is_directory2_dir.
                     out_file1 f (if Sys_is_directory2_dir then sprintf2 (STR ''%s/%s.thy'') dir (To_string file_out) else dir)))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iterM (fprintf1 (STR ''%s
''                                 ))
        (bug_ocaml_extraction (let (ocl, l) =
           fold_thy'
             (\<lambda>f. f ())
             (\<lambda>_ _. [])
             (\<lambda>x acc1 acc2. (acc1, Cons x acc2))
             l_thy
             (ocl_compiler_config.truncate ocl, []) in
         s_of_thy_list (ocl_compiler_config_more_map (\<lambda>_. is_file) ocl) (rev l)))))"
end

definition "write_file = s_of.write_file implode (ToNat integer_of_natural)"

lemmas [code] =
  (* def *)
  s_of.To_oid_def

  s_of.s_of_dataty_def
  s_of.s_of_ty_synonym_def
  s_of.s_of_sexpr_extended_def
  s_of.s_of_instantiation_class_def
  s_of.s_of_defs_overloaded_def
  s_of.s_of_consts_class_def
  s_of.s_of_definition_hol_def
  s_of.s_of_ntheorem_def
  s_of.s_of_ntheorem_list_def
  s_of.s_of_lemmas_simp_def
  s_of.s_of_tactic_last_def
  s_of.s_of_tac_apply_def
  s_of.s_of_lemma_by_def
  s_of.s_of_axiom_def
  s_of.s_of_section_title_def
  s_of.s_of_text_def
  s_of.s_of_ml_def
  s_of.s_of_thm_def
  s_of.s_of_ctxt2_term_def
  s_of.s_of_ocl_deep_embed_ast_def
  s_of.s_of_thy_def
  s_of.s_of_generation_syntax_def
  s_of.s_of_ml_extended_def
  s_of.s_of_thy_extended_def
  s_of.s_of_thy_list_def

  s_of.write_file_def

  (* fun *)
  s_of.s_of_rawty.simps
  s_of.s_of_pure_term.simps
  s_of.s_of_expr.simps
  s_of.s_of_ntheorem_aux.simps
  s_of.s_of_tactic.simps
  s_of.s_of_sexpr.simps

subsection{* General Compiling Process: Test Scenario: Deep (without reflection) *}

definition "Employee_DesignModel_UMLPart =
  [ ocl_class_raw.make ''Galaxy'' [(''sound'', OclTy_raw ''unit''), (''moving'', OclTy_raw ''bool'')] None
  , ocl_class_raw.make ''Planet'' [(''weight'', OclTy_raw ''nat'')] (Some ''Galaxy'')
  , ocl_class_raw.make ''Person'' [(''salary'', OclTy_raw ''int'')] (Some ''Planet'') ]"

definition "main = write_file
 (ocl_compiler_config.extend
   (ocl_compiler_config_empty True None (oidInit (Oid 0)) Gen_design
      \<lparr> D_disable_thy_output := False
      , D_file_out_path_dep := Some (''Employee_DesignModel_UMLPart_generated''
                                    ,[''../src/OCL_main'']
                                    ,''../src/OCL_class_diagram_generator'') \<rparr>)
   ( List_map OclAstClassRaw Employee_DesignModel_UMLPart
     @@ [ OclAstAssociation (ocl_association.make OclAssTy_association
            [ (''Person'', OclMult [(Mult_star, None)], None)
            , (''Person'', OclMult [(Mult_nat 0, Some (Mult_nat 1))], Some ''boss'')])
        , OclAstFlushAll OclFlushAll]
   , None))"
(*
apply_code_printing ()
export_code main
  in OCaml module_name M
  (no_signatures)
*)
end
