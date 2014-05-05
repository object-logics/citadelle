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

theory OCL_compiler
imports "~~/src/HOL/Library/RBT"
        "~~/src/HOL/Library/Char_ord"
        "~~/src/HOL/Library/List_lexord"
        "~~/src/HOL/Library/Code_Char"
        OCL_compiler_ast
  keywords (* hol syntax *)
           "lazy_code_printing" "apply_code_printing" "fun_sorry" "fun_quick"

           :: thy_decl
begin

section{* ... *}

definition "bug_ocaml_extraction = id"
  (* In this theory, this identifier can be removed everywhere it is used.
     However without this, there is a syntax error when the code is extracted to OCaml. *)

section{* ... *}

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

section{* ... *}

definition "Succ x = x + 1"

datatype internal_oid = Oid nat
datatype internal_oids =
  Oids nat (* start *)
       nat (* oid for assoc (incremented from start) *)
       nat (* oid for inh (incremented from start) *)

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Succ n2) (Succ n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Succ n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitAll = (\<lambda>Oids n1 _ _ \<Rightarrow> Oids n1 n1 n1)"
definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"

section{* AST Definition: OCL *}
subsection{* type definition *}

datatype ocl_collection = Set | Sequence

record ocl_ty_object_node =
  TyObjN_ass_switch :: nat
  TyObjN_role_multip :: ocl_multiplicity
  TyObjN_role_name :: "string option"
  TyObjN_role_ty :: string

record ocl_ty_object =
  TyObj_name :: string (* ty: name *)
  TyObj_ass_id :: nat
  TyObj_ass_arity :: nat
  TyObj_from :: ocl_ty_object_node
  TyObj_to :: ocl_ty_object_node

datatype ocl_ty = OclTy_base string (* ty: name *)
                | OclTy_object ocl_ty_object
                | OclTy_collection ocl_collection ocl_ty
                | OclTy_base_raw string

record ocl_operation =
  Op_args :: "(string \<times> ocl_ty) list"
  Op_result :: ocl_ty
  Op_pre :: "(string \<times> string) list"
  Op_post :: "(string \<times> string) list"

datatype ocl_class =
  OclClass
    string (* name of the class *)
    "(string (* name *) \<times> ocl_ty) list" (* attribute *)
    (*"(string (* name *) \<times> ocl_operation) list" (* contract *)
    "(string (* name *) \<times> string) list" (* invariant *) *)
    "ocl_class list" (* link to subclasses *)

record ocl_class_flat =
  Cflat_name :: string
  Cflat_own :: "(string (* name *) \<times> ocl_ty) list" (* attribute *)
  (*Cflat_contract :: "(string (* name *) \<times> ocl_operation) list" (* contract *)
    Cflat_inv :: "(string (* name *) \<times> string) list" (* invariant *) *)
  Cflat_inh :: "string option" (* inherits *)

datatype ocl_association_type = OclAssTy_association
                              | OclAssTy_composition
                              | OclAssTy_aggregation

record ocl_association =
  OclAss_type :: ocl_association_type
  OclAss_relation :: "( string (* name class *)
                      \<times> ocl_multiplicity (* multiplicity *)
                      \<times> string option (* role *)) list"

datatype ocl_data_shallow_base = ShallB_str string
                               | ShallB_self internal_oid

datatype ocl_data_shallow = Shall_base ocl_data_shallow_base
                          | Shall_list "ocl_data_shallow_base list"

datatype 'a ocl_list_attr = OclAttrNoCast 'a (* inh, own *)
                          | OclAttrCast
                              string (* cast from *)
                              "'a ocl_list_attr" (* cast entity *)
                              'a (* inh, own *)

record ocl_instance_single =
  Inst_name :: string
  Inst_ty :: string (* type *)
  Inst_attr :: "((string (* name *) \<times> ocl_data_shallow) list) (* inh and own *) ocl_list_attr"

datatype ocl_instance =
  OclInstance "ocl_instance_single list" (* mutual recursive *)

datatype ocl_def_int = OclDefI "string list"

datatype 'a ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                               | OclDefCoreSkip
                               | OclDefCoreBinding 'a

datatype ocl_def_state = OclDefSt
                           string (* name *)
                           "string (* name *) ocl_def_state_core list"

datatype ocl_def_pre_post = OclDefPP
                              string (* pre *)
                              string (* post *)

datatype ocl_flush_all = OclFlushAll

datatype ocl_deep_embed_ast = OclAstClassFlat ocl_class_flat
                            | OclAstAssociation ocl_association
                            | OclAstInstance ocl_instance
                            | OclAstDefInt ocl_def_int
                            | OclAstDefState ocl_def_state
                            | OclAstDefPrePost ocl_def_pre_post
                            | OclAstFlushAll ocl_flush_all

datatype ocl_deep_mode = Gen_design
                       | Gen_analysis

record ocl_deep_embed_input =
  D_disable_thy_output :: bool
  D_file_out_path_dep :: "(string (* theory *) \<times> string list (* imports *)) option"
  D_oid_start :: internal_oids
  D_output_position :: "nat \<times> nat"
  D_design_analysis :: ocl_deep_mode
  D_class_spec :: "ocl_class option" (* last class considered for the generation *)
  D_ocl_env :: "ocl_deep_embed_ast list"
  D_instance_rbt :: "(string (* name (as key for rbt) *) \<times> ocl_instance_single \<times> internal_oid) list" (* instance namespace environment *)
  D_state_rbt :: "(string (* name (as key for rbt) *) \<times> (internal_oids \<times> (string (* name *) \<times> ocl_instance_single (* alias *)) ocl_def_state_core) list) list" (* state namespace environment *)

definition "ocl_deep_embed_input_more_map f ocl =
  ocl_deep_embed_input.extend
    (ocl_deep_embed_input.truncate ocl)
    (f (ocl_deep_embed_input.more ocl))"

record ocl_definition =
  Def_expr :: string
  Def_args :: "(string \<times> ocl_ty) list"
  Def_result :: ocl_ty

record ocl_association_end =
  Ass_coltyp :: "ocl_collection option"
  Ass_cardinality :: "(nat option \<times> nat option) option"
  Ass_role :: "string option"

record ocl_class_model =
  Mod_id :: string
  Mod_class :: "ocl_class list"
  Mod_assocs\<^sub>2 :: "(string \<times> (ocl_association_end \<times> ocl_association_end)) list"
  Mod_assocs\<^sub>3 :: "(string \<times> (ocl_association_end \<times> ocl_association_end \<times> ocl_association_end)) list"
  Mod_definition :: "(string \<times> ocl_definition) list"

subsection{* ... *} (* optimized data-structure version *)

datatype opt_attr_type = OptInh | OptOwn
datatype opt_ident = OptIdent nat

instantiation internal_oid :: linorder
begin
 definition "n_of_internal_oid = (\<lambda> Oid n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_internal_oid n \<le> n_of_internal_oid m"
 definition "n < m \<longleftrightarrow> n_of_internal_oid n < n_of_internal_oid m"
 instance
   apply(default)
   apply (metis less_eq_internal_oid_def less_imp_le less_internal_oid_def not_less)
   apply (metis less_eq_internal_oid_def order_refl)
   apply (metis less_eq_internal_oid_def order.trans)
   apply(simp add: less_eq_internal_oid_def n_of_internal_oid_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_internal_oid_def)
end

instantiation opt_ident :: linorder
begin
 definition "n_of_opt_ident = (\<lambda> OptIdent n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_opt_ident n \<le> n_of_opt_ident m"
 definition "n < m \<longleftrightarrow> n_of_opt_ident n < n_of_opt_ident m"
 instance
 apply(default)
 apply (metis less_eq_opt_ident_def less_imp_le less_opt_ident_def not_less)
 apply (metis less_eq_opt_ident_def order_refl)
   apply (metis less_eq_opt_ident_def order.trans)
   apply(simp add: less_eq_opt_ident_def n_of_opt_ident_def, case_tac x, case_tac y, simp)
 by (metis le_cases less_eq_opt_ident_def)
end

subsection{* ... *}

definition "List_map f l = rev (foldl (\<lambda>l x. f x # l) [] l)"
definition "List_mapi f l = rev (fst (foldl (\<lambda>(l,cpt) x. (f cpt x # l, Succ cpt)) ([], 0::nat) l))"
definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "flatten l = foldl (\<lambda>acc l. foldl (\<lambda>acc x. x # acc) acc (rev l)) [] (rev l)"
definition List_append (infixr "@@" 65) where "List_append a b = flatten [a, b]"
definition "List_filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"
definition "fold_list f l accu =
  (let (l, accu) = List.fold (\<lambda>x (l, accu). let (x, accu) = f x accu in (x # l, accu)) l ([], accu) in
   (rev l, accu))"
definition "char_escape = Char Nibble0 Nibble9"
definition "modify_def v k f rbt =
  (case lookup rbt k of None \<Rightarrow> insert k (f v) rbt
                      | Some _ \<Rightarrow> map_entry k f rbt)"
definition "Option_bind f = (\<lambda> None \<Rightarrow> None | Some x \<Rightarrow> f x)"
definition "List_assoc x1 l = List.fold (\<lambda>(x2, v). \<lambda>None \<Rightarrow> if x1 = x2 then Some v else None | x \<Rightarrow> x) l None"
definition "List_split l = (List_map fst l, List_map snd l)"
definition "List_upto i j = 
 (let to_i = \<lambda>n. int_of_integer (integer_of_natural n) in
  List_map (natural_of_integer o integer_of_int) (upto (to_i i) (to_i j)))"
definition "lookup2 rbt = (\<lambda>(x1, x2). Option_bind (\<lambda>rbt. lookup rbt x2) (lookup rbt x1))"
definition "insert2 = (\<lambda>(x1, x2) v. modify_def empty x1 (insert x2 v))"


subsection{* ... *}

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

fun_sorry class_unflat_aux where
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_cycle r of (None (* cycle detection *)) \<Rightarrow>
      OclClass
        r
        (bug_ocaml_extraction (case lookup rbt r of Some l \<Rightarrow> l))
        (List_map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          (case lookup rbt_inv r of None \<Rightarrow> [] | Some l \<Rightarrow> l)))"

definition "class_unflat l = 
 (let l = 
    let (l_class, l_assoc) = List.partition (\<lambda> OclAstClassFlat cflat \<Rightarrow> True | _ => False) l
      ; rbt = (* fold classes:
                 set ''OclAny'' as default inherited class (for all classes linking to zero inherited classes) *)
              insert
                const_oclany
                (ocl_class_flat.make const_oclany [] None)
                (List.fold
                  (\<lambda> OclAstClassFlat cflat \<Rightarrow>
                    insert (Cflat_name cflat) (cflat \<lparr> Cflat_inh := case Cflat_inh cflat of None \<Rightarrow> Some const_oclany | x \<Rightarrow> x \<rparr>))
                  l_class
                  empty) in
    (* fold associations:
       add remaining 'object' attributes *)
    List_map snd (entries (List.fold (\<lambda> (ass_oid, OclAstAssociation ass) \<Rightarrow> 
      let l_rel = OclAss_relation ass in
      fold_max
        (bug_ocaml_extraction (let n_rel = natural_of_nat (List.length l_rel) in
         \<lambda> (cpt_to, (name_to, multip_to, Some role_to)) \<Rightarrow> List.fold (\<lambda> (cpt_from, (name_from, multip_from, role_from)).
            map_entry name_from (\<lambda>cflat. cflat \<lparr> Cflat_own := (role_to,
              OclTy_object (ocl_ty_object_ext const_oid ass_oid n_rel
                (ocl_ty_object_node_ext cpt_from multip_from role_from name_from ())
                (ocl_ty_object_node_ext cpt_to multip_to (Some role_to) name_to ())
                ())) # Cflat_own cflat \<rparr>))
         | _ \<Rightarrow> \<lambda>_. id))
        l_rel) (List_mapi Pair l_assoc) rbt)) in
  class_unflat_aux
    (List.fold (\<lambda> cflat. insert (Cflat_name cflat) (Cflat_own cflat)) l empty)
    (List.fold (\<lambda> cflat. case Cflat_inh cflat of Some k \<Rightarrow> modify_def [] k (\<lambda>l. Cflat_name cflat # l) | _ \<Rightarrow> id) l empty)
    empty
    const_oclany)"

definition "apply_optim_ass_arity ty_obj v =
  (if TyObj_ass_arity ty_obj \<le> 2 then None
   else Some v)"

definition "str_of_ty = (\<lambda> OclTy_base x \<Rightarrow> x | OclTy_object ty_obj \<Rightarrow> flatten [TyObj_name ty_obj, '' '', const_oid_list])"

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

fun_quick less_than_hierarchy where
  "less_than_hierarchy l item1 item2 =
    (case l of x # xs \<Rightarrow>
               if x = item1 then GT
               else if x = item2 then LT
               else less_than_hierarchy xs item1 item2)"
definition "compare_hierarchy = (\<lambda>l x1 x2. if x1 = x2 then EQ else less_than_hierarchy l x1 x2)"

fun_quick fold_less_gen where "fold_less_gen f_gen f_jump f l = (case l of
    x # xs \<Rightarrow> \<lambda>acc. fold_less_gen f_gen f_jump f xs (f_gen (f x) xs (f_jump acc))
  | [] \<Rightarrow> id)"

definition "fold_less2 = fold_less_gen List.fold"
definition "fold_less3 = fold_less_gen o fold_less2"

section{* AST Definition: SML *}
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

section{* AST Definition: HOL *}
subsection{* type definition *}

datatype hol_simplety = Opt string | Raw string

datatype hol_dataty = Datatype string (* name *)
                           "(string (* name *) \<times> hol_simplety list (* arguments *)) list" (* constructors *)

datatype hol_raw_ty =
   Ty_apply hol_raw_ty "hol_raw_ty list"
 | Ty_base string

datatype hol_ty_synonym = Type_synonym string (* name *)
                                       hol_raw_ty (* content *)

datatype hol_expr = Expr_case hol_expr (* value *)
                              "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_rewrite hol_expr (* left *) string (* symb rewriting *) hol_expr (* right *)
                  | Expr_basic "string list"
                  | Expr_oid string (* prefix *) internal_oid
                  | Expr_binop hol_expr string hol_expr
                  | Expr_annot hol_expr string (* type *)
                  | Expr_bind string (* symbol *) "string list" (* arg *) hol_expr
                  | Expr_bind0 string (* symbol *) hol_expr (* arg *) hol_expr
                  | Expr_function "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_apply string "hol_expr list"
                  | Expr_applys hol_expr "hol_expr list"
                  | Expr_preunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_postunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_paren string (* left *) string (* right *) hol_expr

datatype hol_instantiation_class = Instantiation string (* name *)
                                                 string (* name in definition *)
                                                 hol_expr

datatype hol_defs_overloaded = Defs_overloaded string (* name *) hol_expr (* content *)

datatype hol_consts_class = Consts_raw string (* name *)
                                       hol_raw_ty (* type in *)
                                       hol_raw_ty (* type out *)
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

datatype hol_section_title = Section_title nat (* nesting level *)
                                           string (* content *)

datatype hol_text = Text string

datatype hol_ml = Ml sml_expr

datatype hol_thy = Thy_dataty hol_dataty
                 | Thy_ty_synonym hol_ty_synonym
                 | Thy_instantiation_class hol_instantiation_class
                 | Thy_defs_overloaded hol_defs_overloaded
                 | Thy_consts_class hol_consts_class
                 | Thy_definition_hol hol_definition_hol
                 | Thy_lemmas_simp hol_lemmas_simp
                 | Thy_lemma_by hol_lemma_by
                 | Thy_section_title hol_section_title
                 | Thy_text hol_text
                 | Thy_ml hol_ml

subsection{* ... *}

definition "wildcard = ''_''"

definition "escape_unicode c = flatten [[Char Nibble5 NibbleC], ''<'', c, ''>'']"

definition "isub_of_str = flatten o List_map (\<lambda>c. escape_unicode ''^sub'' @@ [c])"
definition "isup_of_str = flatten o List_map (\<lambda>c. escape_unicode [char_of_nat (nat_of_char c - 32)])"
definition "lowercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "number_of_str = flatten o List_map (\<lambda>c. escape_unicode ([''zero'', ''one'', ''two'', ''three'', ''four'', ''five'', ''six'', ''seven'', ''eight'', ''nine''] ! (nat_of_char c - 48)))"
definition "nat_raw_of_str = List_map (\<lambda>i. char_of_nat (nat_of_char (Char Nibble3 Nibble0) + i))"
fun_quick nat_of_str_aux where
   "nat_of_str_aux l (n :: Nat.nat) = (if n < 10 then n # l else nat_of_str_aux (n mod 10 # l) (n div 10))"
definition "nat_of_str n = nat_raw_of_str (nat_of_str_aux [] n)"
definition "natural_of_str = nat_of_str o nat_of_natural"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, ''_'', isub_of_str x])"
definition "mk_dot s1 s2 = flatten [''.'', s1, s2]"
definition "mk_dot_par dot s = flatten [dot, ''('', s, '')'']"
definition "mk_dot_comment s1 s2 s3 = mk_dot s1 (flatten [s2, '' /*'', s3, ''*/''])"

definition "hol_definition s = flatten [s, ''_def'']"
definition "hol_split s = flatten [s, ''.split'']"

subsection{* ... *}

definition "ty_boolean = ''Boolean''"

definition "unicode_equiv = escape_unicode ''equiv''"
definition "unicode_doteq = escape_unicode ''doteq''"
definition "unicode_tau = escape_unicode ''tau''"
definition "unicode_alpha = escape_unicode ''alpha''"
definition "unicode_delta = escape_unicode ''delta''"
definition "unicode_lambda = escape_unicode ''lambda''"
definition "unicode_upsilon = escape_unicode ''upsilon''"
definition "unicode_bottom = escape_unicode ''bottom''"
definition "unicode_AA = escape_unicode ''AA''"
definition "unicode_Turnstile = escape_unicode ''Turnstile''"
definition "unicode_triangleq = escape_unicode ''triangleq''"
definition "unicode_not = escape_unicode ''not''"
definition "unicode_noteq = escape_unicode ''noteq''"
definition "unicode_or = escape_unicode ''or''"
definition "unicode_circ = escape_unicode ''circ''"
definition "unicode_mapsto = escape_unicode ''mapsto''"
definition "unicode_forall = escape_unicode ''forall''"
definition "unicode_exists = escape_unicode ''exists''"
definition "unicode_in = escape_unicode ''in''"
definition "unicode_lfloor = escape_unicode ''lfloor''"
definition "unicode_rfloor = escape_unicode ''rfloor''"
definition "unicode_lceil = escape_unicode ''lceil''"
definition "unicode_rceil = escape_unicode ''rceil''"
definition "unicode_And = escape_unicode ''And''"
definition "unicode_subseteq = escape_unicode ''subseteq''"
definition "unicode_Rightarrow = escape_unicode ''Rightarrow''"
definition "unicode_Longrightarrow = escape_unicode ''Longrightarrow''"
definition "unicode_times = escape_unicode ''times''"

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
                     OclTy_object ty_obj \<Rightarrow>
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
definition "map_class_nupl2 f x = rev (fst (fold_less2 (\<lambda>(l, _). (l, None)) (\<lambda>x y (l, acc). (f x y acc # l, Some y)) (rev (get_class_hierarchy x)) ([], None)))"
definition "map_class_nupl3 f x = rev (fold_less3 id id (\<lambda>x y z l. f x y z # l) (rev (get_class_hierarchy x)) [])"
definition "map_class_nupl2' f = map_class_nupl2 (\<lambda>(x,_) (y,_) _. f x y)"
definition "map_class_nupl2'' f = map_class_nupl2 (\<lambda>(x,_) (y,_) opt. f x y (Option.map fst opt))"
definition "map_class_nupl2l f x = rev (fst (fold_less2 (\<lambda>(l, _). (l, [])) (\<lambda>x y (l, acc). (f x y acc # l, y # acc)) (rev (get_class_hierarchy x)) ([], [])))"
definition "map_class_nupl2l' f = map_class_nupl2l (\<lambda>(x,_) (y,_) l. f x y (List_map fst l))"
definition "map_class_nupl3' f = map_class_nupl3 (\<lambda>(x,_) (y,_) (z,_). f x y z)"
definition "map_class_nupl3l f x = rev (fst (fold_less3 (\<lambda>(l, _). (l, [])) id (\<lambda>x y z (l, acc). (f x y z acc # l, z # acc)) (rev (get_class_hierarchy x)) ([], [])))"
definition "map_class_nupl3l' f = map_class_nupl3l (\<lambda>(x,_) (y,_) (z,_) l. f x y z (List_map fst l))"
definition "map_class_nupl3'_GE f x = map_class_nupl2' (\<lambda>x y. f x y y) x @@ map_class_nupl3' f x"
definition "map_class_nupl3'_LE f x = map_class_nupl2' (\<lambda>x y. f x x y) x @@ map_class_nupl3' f x"
definition "map_class_nupl3'_LE' f x = map_class_nupl2l' (\<lambda>x y l. f x x y l) x @@ map_class_nupl3l' f x"
definition "map_class_one f_l f expr =
  (case f_l (fst (fold_class (\<lambda>isub_name name l_attr l_inh l_inh_sib next_dataty _. ((isub_name, name, l_attr, l_inh, l_inh_sib, next_dataty), ())) () expr)) of
     (isub_name, name, l_attr, l_inh, l_inh_sib, next_dataty) # _ \<Rightarrow>
     f isub_name name l_attr l_inh l_inh_sib next_dataty)"
definition "map_class_top = map_class_one rev"
definition "map_class_bot = map_class_one id"
definition "get_hierarchy_fold f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  let (_, l) = foldl (\<lambda> (name1_last, l1) name1. (Some name1, List_map (\<lambda>name2. List_map (
  f (name1_last, name1) name2) l3) l2 # l1)) (None, []) l1 in rev l))"
definition "get_hierarchy_map f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  List_map (\<lambda>name1. List_map (\<lambda>name2. List_map (f name1 name2) l3) l2) l1))"

definition "class_arity = keys o (\<lambda>l. List.fold (\<lambda>x. insert x ()) l empty) o 
  flatten o flatten o map_class (\<lambda> _ _ l_attr _ _ _.
    List_map (\<lambda> (_, OclTy_object ty_obj) \<Rightarrow> [TyObj_ass_arity ty_obj]
              | _ \<Rightarrow> []) l_attr)"

definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"
definition "thm_OF s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "thm_simplified s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
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
definition "Consts s = Consts_raw s (Ty_base (Char Nibble2 Nibble7 # unicode_alpha))"
definition "Tac_subst = Tac_subst_l [''0'']"
definition "Tac_auto = Tac_auto_simp_add []"

definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_design_analysis ocl
    ; base_attr = (if design_analysis = Gen_design then id else List_filter (\<lambda> (_, OclTy_object _) \<Rightarrow> False | _ \<Rightarrow> True))
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
  (Type_synonym ty_boolean (Ty_apply (Ty_base ty_boolean) [Ty_base unicode_AA]) #
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
definition "print_access_oid_uniq =
  (\<lambda>expr ocl.
      (\<lambda>(l, oid_start). (List_map Thy_definition_hol l, ocl \<lparr> D_oid_start := oid_start \<rparr>))
      (let (l, (acc, _)) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inh) in
         let (l, cpt) = fold_list (fold_list
           (\<lambda> (attr, OclTy_object ty_obj) \<Rightarrow> bug_ocaml_extraction (let obj_oid = TyObj_ass_id ty_obj
                                                                     ; obj_name_from_nat = TyObjN_ass_switch (TyObj_from ty_obj) in \<lambda>(cpt, rbt) \<Rightarrow>
             let (cpt_obj, cpt_rbt) = 
               case lookup rbt obj_oid of
                 None \<Rightarrow> (cpt, oidSucAssoc cpt, insert obj_oid cpt rbt)
               | Some cpt_obj \<Rightarrow> (cpt_obj, cpt, rbt) in
             ([Definition (Expr_rewrite
                   (Expr_basic [print_access_oid_uniq_name obj_name_from_nat isub_name attr])
                   ''=''
                   (Expr_oid '''' (oidGetAssoc cpt_obj)))], cpt_rbt))
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (flatten (flatten l), cpt)) (D_oid_start ocl, empty) expr in
       (flatten l, acc)))"

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

definition "print_access_choose = start_map'''' Thy_definition_hol o (\<lambda>expr _.
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; lets = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' exp)
     ; lets' = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' (b exp))
     ; lets'' = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_lam ''l'' (\<lambda>var_l. Expr_binop (b var_l) ''!'' (b exp))))
     ; l_flatten = ''List_flatten'' in
  flatten
  [ (bug_ocaml_extraction 
    (let a = \<lambda>f x. Expr_apply f [x]
       ; b = \<lambda>s. Expr_basic [s]
       ; lets = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' exp)
       ; mk_var = \<lambda>i. b (flatten [''x'', natural_of_str i]) in
     flatten
       (List_map
          (\<lambda>n.
           let l = List_upto 0 (n - 1) in
           List_map (let l = Expr_list (List_map mk_var l) in (\<lambda>(i,j). 
             (lets
                (print_access_choose_name n i j)
                (Expr_function [(l, (Expr_pair (mk_var i) (mk_var j)))]))))
             ((flatten o flatten) (List_map (\<lambda>i. List_map (\<lambda>j. if i = j then [] else [(i, j)]) l) l)))
          (class_arity expr))))
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
      (\<lambda> (attr, OclTy_object ty_obj) \<Rightarrow>
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
      (\<lambda> (attr, OclTy_object ty_obj) \<Rightarrow> \<lambda>rbt.
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

definition "print_access_dot_consts = start_map Thy_consts_class o
  flatten o flatten o map_class (\<lambda>isub_name name l_attr _ _ _.
    List_map (\<lambda>(attr_n, attr_ty).
      List_map
        (\<lambda>(var_at_when_hol, var_at_when_ocl).
          Consts_raw
            (flatten [ ''dot''
                     , case attr_ty of
                         OclTy_object ty_obj \<Rightarrow> flatten [''_'', natural_of_str (TyObjN_ass_switch (TyObj_from ty_obj)), ''_'']
                       | _ \<Rightarrow> ''''
                     , isup_of_str attr_n, var_at_when_hol])
            (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA, Ty_base (Char Nibble2 Nibble7 # unicode_alpha)])
            (case attr_ty of
                OclTy_base attr_ty \<Rightarrow> Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
                  let option = \<lambda>x. Ty_apply (Ty_base ''option'') [x] in
                  option (option (Ty_base attr_ty))]
              | OclTy_object ty_obj \<Rightarrow> 
                  let ty_obj = TyObj_to ty_obj
                    ; name = TyObjN_role_ty ty_obj in
                  Ty_base (if single_multip (TyObjN_role_multip ty_obj) then
                             name
                           else
                             print_infra_type_synonym_class_set_name name))
            (let dot_name = mk_dot attr_n var_at_when_ocl
               ; mk_par = 
                   let esc = \<lambda>s. Char Nibble2 Nibble7 # s in
                   (\<lambda>s1 s2. flatten [s1, '' '', esc ''/'', ''* '', s2, '' *'', esc ''/'']) in
             case attr_ty of OclTy_object ty_obj \<Rightarrow> 
               (case apply_optim_ass_arity ty_obj (mk_par dot_name (bug_ocaml_extraction (let ty_obj = TyObj_from ty_obj in case TyObjN_role_name ty_obj of None => natural_of_str (TyObjN_ass_switch ty_obj) | Some s => s))) of
                  None \<Rightarrow> dot_name
                | Some dot_name \<Rightarrow> dot_name)
                           | _ \<Rightarrow> dot_name))
        [ (var_at_when_hol_post, var_at_when_ocl_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre)]) l_attr)"

definition "print_access_dot_name isub_name dot_at_when attr_ty isup_attr =
  flatten [isup_attr (let dot_name = isub_name ''dot'' in
                      case attr_ty of
                        OclTy_object ty_obj \<Rightarrow> flatten [dot_name, ''_'', natural_of_str (TyObjN_ass_switch (TyObj_from ty_obj)), ''_'']
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
                            (Gen_analysis, OclTy_object ty_obj) \<Rightarrow>
                              \<lambda>l. Expr_apply (print_access_deref_assocs_name' (TyObjN_ass_switch (TyObj_from ty_obj)) isub_name isup_attr) (Expr_basic [var_in_when_state] # [l])
                        | _ \<Rightarrow> id)
                          (Expr_apply (isup_attr (isub_name var_select))
                            [case attr_ty of OclTy_base _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                           | OclTy_object ty_obj \<Rightarrow> 
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

definition "print_access_dot_lemmas_cp = start_map Thy_lemmas_simp o (\<lambda>expr. [Lemmas_simp ''''
  (map_class_arg_only_var'
    (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _.
      [Thm_str (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr) ])
    expr)])"

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

datatype print_examp_instance_draw_list_attr = Return_obj ocl_ty_object | Return_exp hol_expr

definition "print_examp_instance_draw_list_attr f_oid =
  (let b = \<lambda>s. Expr_basic [s] in
   List_map (\<lambda> obj.
     case
       case obj of
         (t_obj, None) \<Rightarrow> (case t_obj of Some ty_obj \<Rightarrow> Return_obj ty_obj
                                       | _ \<Rightarrow> Return_exp (b ''None''))
       | (_, Some (OclTy_object ty_obj, _)) \<Rightarrow> Return_obj ty_obj
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
                                     (insert name_attr (ty, tag, OptIdent cpt) rbt, Succ cpt, (case ty of OclTy_object ty_obj \<Rightarrow> Some ty_obj | _ \<Rightarrow> None) # l_obj))
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

definition "print_examp_def_st_assoc rbt map_self map_username l_assoc =
  (let b = \<lambda>s. Expr_basic [s]
     ; rbt = List.fold
     (\<lambda> (ocli, cpt). fold_instance_single
       (\<lambda> ty l_attr.
         let (f_attr_ty, _) = rbt ty in
         modify_def empty ty
         (List.fold (\<lambda>(name_attr, shall).
           case f_attr_ty name_attr of
             Some (OclTy_object ty_obj, _, _) \<Rightarrow>
               modify_def ([], ty_obj) name_attr
               (\<lambda>(l, accu). case let find_map = \<lambda> ShallB_str s \<Rightarrow> map_username s | ShallB_self s \<Rightarrow> map_self s in
                                 case shall of
                                   Shall_base shall \<Rightarrow> Option.map (\<lambda>x. [x]) (find_map shall)
                                 | Shall_list l \<Rightarrow> Some (List_map (\<lambda>shall. case find_map shall of Some cpt \<Rightarrow> cpt) l) of
                      None \<Rightarrow> (l, accu)
                    | Some oid \<Rightarrow> (List_map (List_map oidGetInh) [[cpt], oid] # l, accu))
           | _ \<Rightarrow> id) l_attr)) ocli) l_assoc empty in
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
        ; mk_ty = \<lambda>l. (flatten o flatten) (List_map (\<lambda>x. ['' '', x, '' '']) l) in
      Expr_lambdas
        [var_oid_class, var_to_from, var_oid]
        (Expr_annot (Expr_case
          (Expr_apply var_deref_assocs_list
            [ Expr_annot (b var_to_from) (mk_ty
                                            [ const_oid, const_oid_list, const_oid_list
                                            , unicode_Rightarrow
                                            , const_oid, const_oid_list
                                            , unicode_times
                                            , const_oid, const_oid_list])
            , Expr_annot (b var_oid) const_oid
            , a ''drop''
              (Expr_applys (print_examp_def_st_assoc rbt map_self map_username
                             (flatten (fst (fold_list (\<lambda>ocli cpt. (case ocli of None \<Rightarrow> [] | Some ocli \<Rightarrow> [(ocli, cpt)], oidSucInh cpt)) l_ocli (D_oid_start ocl)))))
                           [Expr_annot (b var_oid_class) const_oid])])
          [ (b ''Nil'', b ''None'')
          , let b_l = b ''l'' in
            (b_l, a ''Some'' b_l)] ) (mk_ty [const_oid, const_oid_list, ''option''])))))])"

definition "print_examp_instance_defassoc = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res.
    ( print_examp_instance_oid (List_map Some l) ocl
      @@ List_map Thy_definition_hol l_res
    , ocl))
  (print_examp_instance_defassoc_gen
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
     ; a = \<lambda>f x. Expr_apply f [x]
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
  "(ocl_class
    \<Rightarrow> unit ocl_deep_embed_input_scheme
       \<Rightarrow> hol_thy list \<times>
          unit ocl_deep_embed_input_scheme) list" where "thy_class =
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
                           , print_examp_instance ]"
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
definition "thy_flush_all = []"

definition "ocl_deep_embed_input_empty disable_thy_output file_out_path_dep oid_start design_analysis =
  ocl_deep_embed_input.make
    disable_thy_output
    file_out_path_dep
    oid_start
    (0, 0)
    design_analysis
    None [] [] []"

definition "ocl_deep_embed_input_reset_no_env ocl =
  ocl_deep_embed_input_empty
    (D_disable_thy_output ocl)
    (D_file_out_path_dep ocl)
    (oidReinitAll (D_oid_start ocl))
    (D_design_analysis ocl)
    \<lparr> D_ocl_env := D_ocl_env ocl \<rparr>"

definition "ocl_deep_embed_input_reset_all ocl =
  (let ocl = ocl_deep_embed_input_reset_no_env ocl in
   ( ocl \<lparr> D_ocl_env := [] \<rparr>
   , let (l_class, l_ocl) = List.partition (\<lambda> OclAstClassFlat _ \<Rightarrow> True
                                            | OclAstAssociation _ \<Rightarrow> True
                                            | _ \<Rightarrow> False) (rev (D_ocl_env ocl)) in
     flatten
       [ l_class
       , List.filter (\<lambda> OclAstFlushAll _ \<Rightarrow> False | _ \<Rightarrow> True) l_ocl
       , [OclAstFlushAll OclFlushAll] ] ))"

definition "fold_thy0 univ thy_object0 f =
  List.fold (\<lambda>x (acc1, acc2).
    let (l, acc1) = x univ acc1 in
    (acc1, f l acc2)) thy_object0"

definition "ocl_env_class_spec_rm f_fold f ocl_accu =
  (let (ocl, accu) = f_fold f ocl_accu in
   (ocl \<lparr> D_class_spec := None \<rparr>, accu))"

definition "ocl_env_class_spec_mk f_try f_accu_reset f_fold f = 
  (\<lambda> (ocl, accu).
    f_fold f
      (case D_class_spec ocl of Some _ \<Rightarrow> (ocl, accu) | None \<Rightarrow>
       let (l_class, l_ocl) = List.partition (\<lambda> OclAstClassFlat _ \<Rightarrow> True 
                                              | OclAstAssociation _ \<Rightarrow> True
                                              | _ \<Rightarrow> False) (rev (D_ocl_env ocl)) in
       (f_try (\<lambda> () \<Rightarrow> List.fold
           (\<lambda>ast. (case ast of 
               OclAstInstance univ \<Rightarrow> fold_thy0 univ thy_instance
             | OclAstDefInt univ \<Rightarrow> fold_thy0 univ thy_def_int
             | OclAstDefState univ \<Rightarrow> fold_thy0 univ thy_def_state
             | OclAstDefPrePost univ \<Rightarrow> fold_thy0 univ thy_def_pre_post
             | OclAstFlushAll univ \<Rightarrow> fold_thy0 univ thy_flush_all)
                  f)
           l_ocl
           (let univ = class_unflat l_class
              ; (ocl, accu) = fold_thy0 univ thy_class f (let ocl = ocl_deep_embed_input_reset_no_env ocl in
                                                          (ocl, f_accu_reset ocl accu)) in
            (ocl \<lparr> D_class_spec := Some univ \<rparr>, accu))))))"

definition "ocl_env_save ast f_fold f ocl_accu =
  (let (ocl, accu) = f_fold f ocl_accu in
   (ocl \<lparr> D_ocl_env := ast # D_ocl_env ocl \<rparr>, accu))"

definition "fold_thy' f_try f_accu_reset f =
 (let ocl_env_class_spec_mk = ocl_env_class_spec_mk f_try f_accu_reset in
  List.fold (\<lambda> ast.
    ocl_env_save ast (case ast of
     OclAstClassFlat univ \<Rightarrow> ocl_env_class_spec_rm (fold_thy0 univ thy_class_flat)
   | OclAstAssociation univ \<Rightarrow> ocl_env_class_spec_rm (fold_thy0 univ thy_association)
   | OclAstInstance univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_instance)
   | OclAstDefInt univ \<Rightarrow> fold_thy0 univ thy_def_int
   | OclAstDefState univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_def_state)
   | OclAstDefPrePost univ \<Rightarrow> fold_thy0 univ thy_def_pre_post
   | OclAstFlushAll univ \<Rightarrow> ocl_env_class_spec_mk (fold_thy0 univ thy_flush_all)) f))"
definition "fold_thy_shallow f_try f_accu_reset = fold_thy' f_try f_accu_reset o List.fold"
definition "fold_thy_deep obj ocl =
  (case fold_thy'
          (\<lambda>f. f ())
          (\<lambda>ocl _. D_output_position ocl)
          (\<lambda>l (i, cpt). (Succ i, natural_of_nat (List.length l) + cpt))
          obj
          (ocl, D_output_position ocl) of
    (ocl, output_position) \<Rightarrow> ocl \<lparr> D_output_position := output_position \<rparr>)"

section{* Generation to both Form (setup part) *}

definition "ocl_ty_object_node_rec0 f ocl = f
  (TyObjN_ass_switch ocl)
  (TyObjN_role_multip ocl)
  (TyObjN_role_name ocl)
  (TyObjN_role_ty ocl)"

definition "ocl_ty_object_node_rec f ocl = ocl_ty_object_node_rec0 f ocl
  (ocl_ty_object_node.more ocl)"

definition "ocl_ty_object_rec0 f ocl = f
  (TyObj_name ocl)
  (TyObj_ass_id ocl)
  (TyObj_ass_arity ocl)
  (TyObj_from ocl)
  (TyObj_to ocl)"

definition "ocl_ty_object_rec f ocl = ocl_ty_object_rec0 f ocl
  (ocl_ty_object.more ocl)"

definition "ocl_class_flat_rec0 f ocl = f
  (Cflat_name ocl)
  (Cflat_own ocl)
  (Cflat_inh ocl)"

definition "ocl_class_flat_rec f ocl = ocl_class_flat_rec0 f ocl
  (ocl_class_flat.more ocl)"

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

definition "ocl_deep_embed_input_rec0 f ocl = f
  (D_disable_thy_output ocl)
  (D_file_out_path_dep ocl)
  (D_oid_start ocl)
  (D_output_position ocl)
  (D_design_analysis ocl)
  (D_class_spec ocl)
  (D_ocl_env ocl)
  (D_instance_rbt ocl)
  (D_state_rbt ocl)"

definition "ocl_deep_embed_input_rec f ocl = ocl_deep_embed_input_rec0 f ocl
  (ocl_deep_embed_input.more ocl)"

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

definition "ap1 a v0 f1 v1 = a v0 (f1 v1)"
definition "ap2 a v0 f1 f2 v1 v2 = a (a v0 (f1 v1)) (f2 v2)"
definition "ap3 a v0 f1 f2 f3 v1 v2 v3 = a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)"
definition "ap4 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)"
definition "ap5 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)"
definition "ap6 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)"
definition "ap7 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 = a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)"
definition "ap8 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 = a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)) (f8 v8)"
definition "ap9 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v1 v2 v3 v4 v5 v6 v7 v8 v9 = a (a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)) (f8 v8)) (f9 v9)"
definition "ap10 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 = a (a (a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)) (f8 v8)) (f9 v9)) (f10 v10)"

definition "ar1 a v0 = a v0"
definition "ar2 a v0 f1 v1 = a (a v0 (f1 v1))"
definition "ar3 a v0 f1 f2 v1 v2 = a (a (a v0 (f1 v1)) (f2 v2))"
definition "ar4 a v0 f1 f2 f3 v1 v2 v3 = a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3))"
definition "ar5 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4))"
definition "ar6 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5))"
definition "ar7 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6))"
definition "ar8 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 = a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7))"
definition "ar9 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 = a (a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)) (f8 v8))"
definition "ar10 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 v1 v2 v3 v4 v5 v6 v7 v8 v9 = a (a (a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)) (f8 v8)) (f9 v9))"

(* *)

lemma [code]: "ocl_class_flat.extend = (\<lambda>ocl v. ocl_class_flat_rec0 (co3 (\<lambda>f. f v) ocl_class_flat_ext) ocl)"
by(intro ext, simp add: ocl_class_flat_rec0_def
                        ocl_class_flat.extend_def
                        co3_def K_def)
lemma [code]: "ocl_class_flat.make = co3 (\<lambda>f. f ()) ocl_class_flat_ext"
by(intro ext, simp add: ocl_class_flat.make_def
                        co3_def)
lemma [code]: "ocl_class_flat.truncate = ocl_class_flat_rec (co3 K ocl_class_flat.make)"
by(intro ext, simp add: ocl_class_flat_rec0_def
                        ocl_class_flat_rec_def
                        ocl_class_flat.truncate_def
                        ocl_class_flat.make_def
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

lemma [code]: "ocl_deep_embed_input.extend = (\<lambda>ocl v. ocl_deep_embed_input_rec0 (co9 (\<lambda>f. f v) ocl_deep_embed_input_ext) ocl)"
by(intro ext, simp add: ocl_deep_embed_input_rec0_def
                        ocl_deep_embed_input.extend_def
                        co9_def K_def)
lemma [code]: "ocl_deep_embed_input.make = co9 (\<lambda>f. f ()) ocl_deep_embed_input_ext"
by(intro ext, simp add: ocl_deep_embed_input.make_def
                        co9_def)
lemma [code]: "ocl_deep_embed_input.truncate = ocl_deep_embed_input_rec (co9 K ocl_deep_embed_input.make)"
by(intro ext, simp add: ocl_deep_embed_input_rec0_def
                        ocl_deep_embed_input_rec_def
                        ocl_deep_embed_input.truncate_def
                        ocl_deep_embed_input.make_def
                        co9_def K_def)

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
end
*}

subsection{* beginning *}

lazy_code_printing code_module "" \<rightharpoonup> (OCaml) {*

module To = struct
  let nat big_int x = Big_int.int_of_big_int (big_int x)
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

  let outStand1 f =
    f (Printf.fprintf stdout)

  module Sys = struct open Sys
    let isDirectory2 s = try is_directory s with _ -> false
    let argv = Array.to_list argv
  end

  module Printf = Printf
  module String = String
  module To = To
end

*}

subsection{* ML type *}

type_synonym ml_string = String.literal
datatype ml_int = ML_int

code_printing type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.int"
            | type_constructor ml_int \<rightharpoonup> (SML) "string"

subsection{* ML code const *}

text{* ... *}

(*consts out_file0 :: "((ml_string \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"*)
consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
code_printing constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> unit"
code_printing constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"

text{* module To *}

consts ToNat :: "(nat \<Rightarrow> integer) \<Rightarrow>
                 nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"

text{* module Printf *}

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
consts sprintf6 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> '\<alpha>6 \<Rightarrow> ml_string"

code_printing constant sprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf1 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
            | constant sprintf1 \<rightharpoonup> (SML) "OCL'_boot.sprintf1"
code_printing constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
            | constant sprintf2 \<rightharpoonup> (SML) "OCL'_boot.sprintf2"
code_printing constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
            | constant sprintf3 \<rightharpoonup> (SML) "OCL'_boot.sprintf3"
code_printing constant sprintf4 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf5 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf6 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"

consts eprintf0 :: "ml_string \<Rightarrow> unit"
code_printing constant eprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.eprintf"

(* Monomorph *)

consts sprintf1s :: "ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string"
code_printing constant sprintf1s \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
consts sprintf2ss :: "ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string"
code_printing constant sprintf2ss \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"

text{* module String *}

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_printing constant String_concat \<rightharpoonup> (OCaml) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (SML) "String.concatWith"

text{* module Sys *}

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool"
code_printing constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"

consts Sys_argv :: "ml_string list"
code_printing constant Sys_argv \<rightharpoonup> (OCaml) "CodeConst.Sys.argv"

subsection{* ... *}

locale s_of = 
  fixes To_string :: "string \<Rightarrow> ml_string"
  fixes To_nat :: "nat \<Rightarrow> ml_int"

  fixes s_of_expr :: "hol_expr \<Rightarrow> String.literal"
  fixes s_of_ntheorem_aux :: "(String.literal \<times> String.literal) list \<Rightarrow> hol_ntheorem \<Rightarrow> String.literal"
  fixes s_of_tactic :: "hol_tactic \<Rightarrow> String.literal"
  fixes s_of_rawty :: "hol_raw_ty \<Rightarrow> String.literal"
  fixes s_of_sexpr :: "sml_expr \<Rightarrow> String.literal"
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

definition "flat_s_of_rawty = (\<lambda>
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (List.map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name))"

definition "s_of_ty_synonym _ = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

definition "flat_s_of_expr = (\<lambda>
    Expr_case e l \<Rightarrow> sprintf2 (STR ''(case %s of %s)'') (s_of_expr e) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  | Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Expr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Expr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (To_string s)
  | Expr_bind symb l e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (String_concat (STR '' '') (List_map To_string l)) (s_of_expr e)
  | Expr_bind0 symb e1 e2 \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (s_of_expr e1) (s_of_expr e2)
  | Expr_function l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string unicode_lambda) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) (To_string unicode_Rightarrow) (s_of_expr s2)) l))
  (*| Expr_apply s [e] \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (s_of_expr e)*)
  | Expr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_applys e l \<Rightarrow> sprintf2 (STR ''((%s) %s)'') (s_of_expr e) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_postunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_preunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_expr e) (To_string p_right))"

definition "flat_s_of_sexpr = (\<lambda>
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
  | Sexpr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_sexpr e) (To_string p_right))"

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

definition "s_of_consts_class _ = (\<lambda> Consts_raw n ty_out1 ty_out2 symb \<Rightarrow>
    sprintf5 (STR ''consts %s :: \"%s %s %s\" (\"(_) %s\")'') (To_string n) (s_of_rawty ty_out1) (To_string unicode_Rightarrow) (s_of_rawty ty_out2) (To_string symb))"

definition "s_of_definition_hol _ = (\<lambda>
    Definition e \<Rightarrow> sprintf1 (STR ''definition \"%s\"'') (s_of_expr e)
  | Definition_abbrev name (abbrev, prio) e \<Rightarrow> sprintf4 (STR ''definition %s (\"(1%s)\" %d)
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (To_nat prio) (s_of_expr e)
  | Definition_abbrev0 name abbrev e \<Rightarrow> sprintf3 (STR ''definition %s (\"%s\")
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (s_of_expr e))"

definition "flat_s_of_ntheorem_aux lacc =
  (let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l)))
     ; f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l)))
     ; f_symmetric = (STR ''symmetric'', STR '''')
     ; s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
   \<lambda> Thm_str s \<Rightarrow> To_string s
   | Thm_THEN (Thm_str s) e2 \<Rightarrow> s_base s ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_THEN e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_simplified (Thm_str s) e2 \<Rightarrow> s_base s ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_simplified e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_symmetric (Thm_str s) \<Rightarrow> s_base s (f_symmetric # lacc)
   | Thm_symmetric e1 \<Rightarrow> s_of_ntheorem_aux (f_symmetric # lacc) e1
   | Thm_where (Thm_str s) l \<Rightarrow> s_base s (f_where l # lacc)
   | Thm_where e1 l \<Rightarrow> s_of_ntheorem_aux (f_where l # lacc) e1
   | Thm_of (Thm_str s) l \<Rightarrow> s_base s (f_of l # lacc)
   | Thm_of e1 l \<Rightarrow> s_of_ntheorem_aux (f_of l # lacc) e1
   | Thm_OF (Thm_str s) e2 \<Rightarrow> s_base s ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_OF e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc) e1)"

definition "s_of_ntheorem = s_of_ntheorem_aux []"

definition "s_of_lemmas_simp _ = (\<lambda> Lemmas_simp s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map s_of_ntheorem l))
                                  | Lemmas_simps s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map To_string l)))"

definition "flat_s_of_tactic expr = (\<lambda>
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

definition "s_of_thy ocl =
            (\<lambda> Thy_dataty dataty \<Rightarrow> s_of_dataty ocl dataty
             | Thy_ty_synonym ty_synonym \<Rightarrow> s_of_ty_synonym ocl ty_synonym
             | Thy_instantiation_class instantiation_class \<Rightarrow> s_of_instantiation_class ocl instantiation_class
             | Thy_defs_overloaded defs_overloaded \<Rightarrow> s_of_defs_overloaded ocl defs_overloaded
             | Thy_consts_class consts_class \<Rightarrow> s_of_consts_class ocl consts_class
             | Thy_definition_hol definition_hol \<Rightarrow> s_of_definition_hol ocl definition_hol
             | Thy_lemmas_simp lemmas_simp \<Rightarrow> s_of_lemmas_simp ocl lemmas_simp
             | Thy_lemma_by lemma_by \<Rightarrow> s_of_lemma_by ocl lemma_by
             | Thy_section_title section_title \<Rightarrow> s_of_section_title ocl section_title
             | Thy_text text \<Rightarrow> s_of_text ocl text
             | Thy_ml ml \<Rightarrow> s_of_ml ocl ml)"

definition "s_of_thy_list ocl l_thy =
  (let (th_beg, th_end) = case D_file_out_path_dep ocl of None \<Rightarrow> ([], [])
   | Some (name, fic_import) \<Rightarrow>
       ( [ sprintf2 (STR ''theory %s imports %s begin'') (To_string name) (s_of_expr (expr_binop '' '' (List_map Expr_string fic_import))) ]
       , [ STR '''', STR ''end'' ]) in
  flatten
        [ th_beg
        , flatten (fst (fold_list (\<lambda>l (i, cpt).
            let (l_thy, lg) = fold_list (\<lambda>l n. (s_of_thy ocl l, Succ n)) l 0 in
            (( STR ''''
             # sprintf4 (STR ''%s(* %d ************************************ %d + %d *)'')
                 (To_string (if ocl_deep_embed_input.more ocl then '''' else [char_escape])) (To_nat (Succ i)) (To_nat cpt) (To_nat lg)
             # l_thy), Succ i, cpt + lg)) l_thy (D_output_position ocl)))
        , th_end ])"
end

subsection{* conclusion *}

context s_of
begin
definition "write_file ocl = (
  let (is_file, f_output) = case (D_file_out_path_dep ocl, Sys_argv)
     of (Some (file_out, _), _ # dir # _) \<Rightarrow> (True, \<lambda>f. out_file1 f (if Sys_is_directory2 dir then sprintf2 (STR ''%s/%s.thy'') dir (To_string file_out) else dir))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iter (fprintf1 (STR ''%s
''                                 ))
        (bug_ocaml_extraction (let (ocl, l) =
           fold_thy'
             (\<lambda>f. f ())
             (\<lambda>_ _. [])
             Cons
             (ocl_deep_embed_input.more ocl)
             (ocl_deep_embed_input.truncate ocl, []) in
         s_of_thy_list (ocl_deep_embed_input_more_map (\<lambda>_. is_file) ocl) (rev l)))))"
end

fun_sorry s_of_rawty where "s_of_rawty To_string e = s_of.flat_s_of_rawty To_string (s_of_rawty To_string) e"
fun_sorry s_of_expr where "s_of_expr To_string To_nat e = s_of.flat_s_of_expr To_string To_nat (s_of_expr To_string To_nat) e"
fun_sorry s_of_ntheorem_aux where "s_of_ntheorem_aux To_string To_nat e = s_of.flat_s_of_ntheorem_aux To_string (s_of_expr To_string To_nat) (s_of_ntheorem_aux To_string To_nat) e"
fun_sorry s_of_tactic where "s_of_tactic To_string To_nat e = s_of.flat_s_of_tactic To_string To_nat (s_of_expr To_string To_nat) (s_of_ntheorem_aux To_string To_nat) (s_of_tactic To_string To_nat) e"
fun_sorry s_of_sexpr where "s_of_sexpr To_string To_nat e = s_of.flat_s_of_sexpr To_string To_nat (s_of_sexpr To_string To_nat) e"

definition "write_file = 
 (let To_string = implode
    ; To_nat = ToNat integer_of_natural in
  s_of.write_file To_string To_nat (s_of_expr To_string To_nat) (s_of_ntheorem_aux To_string To_nat) (s_of_tactic To_string To_nat) (s_of_rawty To_string) (s_of_sexpr To_string To_nat))"

lemmas [code] =
  s_of.To_oid_def

  s_of.s_of_dataty_def
  s_of.flat_s_of_rawty_def
  s_of.s_of_ty_synonym_def
  s_of.flat_s_of_expr_def
  s_of.flat_s_of_sexpr_def
  s_of.s_of_instantiation_class_def
  s_of.s_of_defs_overloaded_def
  s_of.s_of_consts_class_def
  s_of.s_of_definition_hol_def
  s_of.flat_s_of_ntheorem_aux_def
  s_of.s_of_ntheorem_def
  s_of.s_of_lemmas_simp_def
  s_of.flat_s_of_tactic_def
  s_of.s_of_tactic_last_def
  s_of.s_of_tac_apply_def
  s_of.s_of_lemma_by_def
  s_of.s_of_section_title_def
  s_of.s_of_text_def
  s_of.s_of_ml_def
  s_of.s_of_thy_def
  s_of.s_of_thy_list_def

  s_of.write_file_def 

subsection{* Deep (without reflection) *}

definition "Employee_DesignModel_UMLPart =
  [ ocl_class_flat.make ''Galaxy'' [(''sound'', OclTy_base ''unit''), (''moving'', OclTy_base ''bool'')] None
  , ocl_class_flat.make ''Planet'' [(''weight'', OclTy_base ''nat'')] (Some ''Galaxy'')
  , ocl_class_flat.make ''Person'' [(''salary'', OclTy_base ''int'')] (Some ''Planet'') ]"

definition "main = write_file
 (ocl_deep_embed_input.extend
   (ocl_deep_embed_input_empty True None (oidInit (Oid 0)) Gen_design
      \<lparr> D_disable_thy_output := False
      , D_file_out_path_dep := Some (''Employee_DesignModel_UMLPart_generated''
                                    ,[''../src/OCL_main'', ''../src/OCL_class_diagram_static'']) \<rparr>)
   (List_map OclAstClassFlat Employee_DesignModel_UMLPart
    @@ [ OclAstAssociation (ocl_association.make OclAssTy_association
           [ (''Person'', OclMult [(Mult_star, None)], None)
           , (''Person'', OclMult [(Mult_nat 0, Some (Mult_nat 1))], Some ''boss'')])
       , OclAstFlushAll OclFlushAll]))"
(*
apply_code_printing ()
export_code main
  in OCaml module_name M
  (no_signatures)
*)
end
