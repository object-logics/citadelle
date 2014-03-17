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
imports "~~/src/HOL/Library/RBT"
        "~~/src/HOL/Library/Char_ord"
        "~~/src/HOL/Library/List_lexord"
  keywords (* ocl *)
           "attribute" (*"object"*) "inherit"
           "skip" "self"

           (* hol syntax *)
           "output_directory"
           "THEORY" "IMPORTS" "SECTION"
           "deep" "shallow" "syntax_print"
           "generation_semantics"
           "flush_all"

           (* hol semantics *)
           "design" "analysis" "oid_start"

       and (* ocl *)
           "Class" "Class.end" "Instance" "Define_int" "Define_state"

           (* hol syntax *)
           "generation_syntax" "lazy_code_printing" "apply_code_printing" "fun_sorry" "fun_quick"

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

datatype internal_oid = Oid nat
datatype internal_oids =
  Oids nat (* start *)
       nat (* oid for assoc (incremented from start) *)
       nat (* oid for inh (incremented from start) *)

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Suc n2) (Suc n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Suc n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"

section{* AST Definition: OCL *}
subsection{* type definition *}

datatype ocl_collection = Set | Sequence

datatype ocl_ty = OclTy_base string
                | OclTy_object string
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
    "ocl_class option" (* link to subclasses *)

datatype ocl_class_flat =
  OclClassFlat
    "( string (* name of the class *)
    \<times> (string (* name *) \<times> ocl_ty) list (* attribute *)
    (* \<times> (string (* name *) \<times> ocl_operation) list (* contract *)
    \<times> (string (* name *) \<times> string) list (* invariant *) *)
    \<times> string option (* inherits *)) list"
    string (* name class root *)

datatype ocl_data_shallow = Shall_str string
                          | Shall_self internal_oid

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

datatype ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                            | OclDefCoreSkip
                            | OclDefCoreBinding string (* name *)

datatype ocl_def_state = OclDefSt
                           string (* name *)
                           "ocl_def_state_core list"

datatype ocl_deep_embed_ast0 = OclAstClassFlat ocl_class_flat
                             | OclAstInstance ocl_instance
                             | OclAstDefInt ocl_def_int
                             | OclAstDefState ocl_def_state

datatype ocl_deep_embed_ast = OclDeepEmbed "ocl_deep_embed_ast0 list"

definition "ocl_deep_embed_ast_map f = (\<lambda> OclDeepEmbed l \<Rightarrow> OclDeepEmbed (f l))"

record ocl_deep_embed_input =
  D_disable_thy_output :: bool
  D_file_out_path_dep :: "(string \<times> string) option"
  D_oid_start :: internal_oids
  D_output_position :: "nat \<times> nat"
  D_design_analysis :: "nat option" (* None : activate design,
                                       Some n : activate analysis (with n + 1 assocs) *)
  D_class_spec :: "ocl_class option" (* last class considered for the generation *)
  D_instance_rbt :: "(string (* name (as key for rbt) *) \<times> ocl_instance_single \<times> internal_oid) list" (* instance namespace environment *)

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

fun_sorry class_unflat_aux where
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case (lookup rbt r, lookup rbt_cycle r) of (Some (l, _), None (* cycle detection *)) \<Rightarrow>
      OclClass r l (Option.map (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle)) (lookup rbt_inv r)))"

definition "class_unflat = (\<lambda> OclClassFlat l root \<Rightarrow>
  class_unflat_aux
    (List.fold (\<lambda> (k, v). insert k v) l empty)
    (List.fold (\<lambda> (v, _, Some k) \<Rightarrow> insert k v | _ \<Rightarrow> id) l empty)
    empty
    root)"

definition "str_of_ty = (\<lambda> OclTy_base x \<Rightarrow> x | OclTy_object x \<Rightarrow> x)"

fun_quick get_class_hierarchy_aux where
   "get_class_hierarchy_aux l_res (OclClass name l_attr dataty) =
   (let l_res = (name, l_attr) # l_res in
    case dataty of None \<Rightarrow> rev l_res
                 | Some dataty \<Rightarrow> get_class_hierarchy_aux l_res dataty)"
definition "get_class_hierarchy = get_class_hierarchy_aux []"

datatype position = EQ | LT | GT

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

definition "List_map f l = rev (foldl (\<lambda>l x. f x # l) [] l)"
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
                      | Thm_strs string nat (* nth to select *)
                      | Thm_THEN hol_ntheorem hol_ntheorem
                      | Thm_simplified hol_ntheorem hol_ntheorem
                      | Thm_symmetric hol_ntheorem
                      | Thm_where hol_ntheorem "(string \<times> hol_expr) list"
                      | Thm_of hol_ntheorem "hol_expr list"
                      | Thm_OF hol_ntheorem hol_ntheorem

datatype hol_lemmas_simp = Lemmas_simp string (* name *)
                                       "hol_ntheorem list"

datatype hol_tactic = Tac_rule hol_ntheorem
                    | Tac_drule hol_ntheorem
                    | Tac_erule hol_ntheorem
                    | Tac_intro "hol_ntheorem list"
                    | Tac_elim hol_ntheorem
                    | Tac_subst_l "string (* nat *) list" (* pos *) hol_ntheorem
                    | Tac_insert "hol_ntheorem list"
                    | Tac_plus "hol_tactic list"
                    | Tac_simp | Tac_simp_add "string list" | Tac_simp_add_del "string list" "string list" | Tac_simp_only "hol_ntheorem list"
                    | Tac_simp_all | Tac_simp_all_add string
                    | Tac_auto_simp_add "string list"
                    | Tac_auto_simp_add_split "hol_ntheorem list" "string list"
                    | Tac_rename_tac "string list"
                    | Tac_case_tac hol_expr

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

subsection{* ... *}

definition "wildcard = ''_''"

definition "escape_unicode c = flatten [[Char Nibble5 NibbleC], ''<'', c, ''>'']"

definition "isub_of_str = flatten o List_map (\<lambda>c. escape_unicode ''^sub'' @@ [c])"
definition "isup_of_str = flatten o List_map (\<lambda>c. escape_unicode [char_of_nat (nat_of_char c - 32)])"
definition "lowercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "number_of_str = flatten o List_map (\<lambda>c. escape_unicode ([''zero'', ''one'', ''two'', ''three'', ''four'', ''five'', ''six'', ''seven'', ''eight'', ''nine''] ! (nat_of_char c - 48)))"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, ''_'', isub_of_str x])"
definition "mk_dot = (\<lambda>s1 s2. flatten [''.'', s1, s2])"
definition "mk_dot_par = (\<lambda>dot s. flatten [dot, ''('', s, '')''])"

definition "hol_definition s = flatten [s, ''_def'']"
definition "hol_split s = flatten [s, ''.split'']"

subsection{* ... *}

definition "object = OclTy_object ''oid''"

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

definition "datatype_ext_name = ''type''"
definition "datatype_name = datatype_ext_name @@ str_of_ty object"
definition "datatype_ext_constr_name = ''mk''"
definition "datatype_constr_name = datatype_ext_constr_name @@ str_of_ty object"
definition "datatype_in = ''in''"

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "const_mixfix dot_ocl name = (let t = \<lambda>s. Char Nibble2 Nibble7 # s in
                                         flatten [dot_ocl, t ''('', name, t '')''])"
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
definition "var_select = ''select''"
definition "var_select_object = ''select_object''"
definition "var_choose = ''choose''"
definition "var_switch = ''switch''"
definition "var_assocs = ''assocs''"
definition "var_at_when_hol_post = ''''"
definition "var_at_when_hol_pre = ''at_pre''"
definition "var_at_when_ocl_post = ''''"
definition "var_at_when_ocl_pre = ''@pre''"
definition "var_OclInt = ''OclInt''"

section{* Translation of AST *}

fun_quick fold_class_gen_aux where
   "fold_class_gen_aux l_inherited l_res l_cons f accu (OclClass name l_attr dataty) = (
      let l_cons = tl l_cons
        ; (r, accu) = f (\<lambda>s. s @@ isub_of_str name) name l_attr l_inherited l_cons dataty accu in
      let l_res = r # l_res in
      case dataty
      of None \<Rightarrow> (flatten l_res, accu)
       | Some dataty \<Rightarrow> fold_class_gen_aux ((name, l_attr) # l_inherited) l_res l_cons f accu dataty)"
definition "fold_class_gen f accu expr = fold_class_gen_aux [] [] (List_map fst (get_class_hierarchy expr)) f accu expr"

definition "map_class_gen f = fst o fold_class_gen
  (\<lambda> isub_name name l_attr l_inh l_cons last_d. \<lambda> () \<Rightarrow>
    (f isub_name name l_attr l_inh l_cons last_d, ())) ()"

definition "add_hierarchy f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (List_map fst (get_class_hierarchy x)))"
definition "add_hierarchy' f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (get_class_hierarchy x))"
definition "add_hierarchy'' f x = (\<lambda>isub_name name l_attr _ _ _. f isub_name name (get_class_hierarchy x) l_attr)"
definition "add_hierarchy''' f x = (\<lambda>isub_name name l_attr l_inh _ next_dataty. f isub_name name (get_class_hierarchy x) l_attr (List_map snd l_inh) next_dataty)"
definition "add_hierarchy'''' f x = (\<lambda>isub_name name l_attr l_inh l_cons _. f isub_name name (get_class_hierarchy x) l_attr (List_map snd l_inh) l_cons)"
definition "map_class f = map_class_gen (\<lambda>isub_name name l_attr l_inh l_cons next_dataty. [f isub_name name l_attr l_inh l_cons next_dataty])"
definition "fold_class f = fold_class_gen (\<lambda>isub_name name l_attr l_inh l_cons next_dataty accu. let (x, accu) = f isub_name name l_attr l_inh l_cons next_dataty accu in ([x], accu))"
definition "map_class_gen_h f x = map_class_gen (add_hierarchy f x) x"
definition "map_class_gen_h' f x = map_class_gen (add_hierarchy' f x) x"
definition "map_class_gen_h'' f x = map_class_gen (add_hierarchy'' f x) x"
definition "map_class_gen_h''' f x = map_class_gen (add_hierarchy''' f x) x"
definition "map_class_gen_h'''' f x = map_class_gen (add_hierarchy'''' f x) x"
definition "map_class_h f x = map_class (add_hierarchy f x) x"
definition "map_class_h' f x = map_class (add_hierarchy' f x) x"
definition "map_class_h'' f x = map_class (add_hierarchy'' f x) x"
definition "map_class_h'''' f x = map_class (add_hierarchy'''' f x) x"
definition "map_class_arg_only f = map_class_gen (\<lambda> isub_name name l_attr _ _ _. case l_attr of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name l)"
definition "map_class_arg_only' f = map_class_gen (\<lambda> isub_name name l_attr l_inh l_cons _. case filter (\<lambda> (_, []) \<Rightarrow> False | _ \<Rightarrow> True) l_inh of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name (l_attr, l, l_cons))"
definition "map_class_arg_only0 f1 f2 u = map_class_arg_only f1 u @@ map_class_arg_only' f2 u"
definition "map_class_arg_only_var0 = (\<lambda>f_app f_lattr isub_name name l_attr.
    flatten (flatten (
    List_map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      flatten (List_map (\<lambda> (attr_orig, l_attr). List_map (\<lambda>(attr_name, attr_ty).
                  f_app
                    isub_name
                    name
                    (var_in_when_state, dot_at_when)
                    attr_orig
                    attr_ty
                    (\<lambda>s. s @@ isup_of_str attr_name)
                    (\<lambda>s. Expr_postunary s (Expr_basic [mk_dot attr_name attr_when]))) l_attr)
               (f_lattr l_attr)))
             [ (var_in_post_state, var_at_when_hol_post, var_at_when_ocl_post)
             , (var_in_pre_state, var_at_when_hol_pre, var_at_when_ocl_pre)])))"
definition "map_class_arg_only_var f1 f2 = map_class_arg_only0 (map_class_arg_only_var0 f1 (\<lambda>l. [(None :: string option, l)])) (map_class_arg_only_var0 f2 (\<lambda>(_, l, _). List_map (\<lambda>(s, l). (Some s, l)) l))"
definition "map_class_arg_only_var' f = map_class_arg_only0 (map_class_arg_only_var0 f (\<lambda>l. [(None, l)])) (map_class_arg_only_var0 f (\<lambda>(_, l, _). List_map (\<lambda>(s, l). (Some s, l)) l))"
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
  (case f_l (fst (fold_class (\<lambda>isub_name name l_attr l_inh l_cons next_dataty _. ((isub_name, name, l_attr, l_inh, l_cons, next_dataty), ())) () expr)) of
     (isub_name, name, l_attr, l_inh, l_cons, next_dataty) # _ \<Rightarrow>
     f isub_name name l_attr l_inh l_cons next_dataty)"
definition "map_class_top = map_class_one rev"
definition "map_class_bot = map_class_one id"
definition "get_hierarchy_fold f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  let (_, l) = foldl (\<lambda> (name1_last, l1) name1. (Some name1, List_map (\<lambda>name2. List_map (
  f (name1_last, name1) name2) l3) l2 # l1)) (None, []) l1 in rev l))"
definition "get_hierarchy_map f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  List_map (\<lambda>name1. List_map (\<lambda>name2. List_map (f name1 name2) l3) l2) l1))"
definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"
definition "thm_OF s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "thm_simplified s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
definition "Expr_lambdas = Expr_bind unicode_lambda"
definition "Expr_lambda x = Expr_lambdas [x]"
definition "Expr_lambdas0 = Expr_bind0 unicode_lambda"
definition "Expr_some = Expr_paren unicode_lfloor unicode_rfloor"
definition "Expr_parenthesis (* mandatory parenthesis *) = Expr_paren ''('' '')''"
definition "Expr_warning_parenthesis (* optional parenthesis that can be removed but a warning will be raised *) = Expr_parenthesis"
definition "Expr_pat b = Expr_basic [Char Nibble3 NibbleF # b]"
definition "Expr_And x f = Expr_bind0 unicode_And (Expr_basic [x]) (f x)"
definition "Expr_exists x f = Expr_bind0 unicode_exists (Expr_basic [x]) (f x)"
definition "expr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Expr_binop x s) xs x)"
definition "Consts s ty_out mix = Consts_raw s (Ty_base (Char Nibble2 Nibble7 # unicode_alpha)) ty_out mix"
definition "Tac_subst = Tac_subst_l [''0'']"
definition "Tac_auto = Tac_auto_simp_add []"
definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl.
  let design_analysis = D_design_analysis ocl
    ; base_attr = (if design_analysis = None then id else List_filter (\<lambda> (_, OclTy_object _) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, List_map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') ocl)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> ocl. start_map f (fl (D_design_analysis ocl)) ocl)"

subsection{* ... *}

definition "activate_simp_optimization = True"
definition "assoc_max = 3"

definition "print_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, l_inherited) in
    [ Datatype
        (isub_name datatype_ext_name)
        (  (rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ isub_of_str x)])) l_cons)
        @@ [(isub_name datatype_ext_constr_name, Raw (str_of_ty object) # flatten ( List_map (List_map (\<lambda>(_, x). Opt (str_of_ty x))) l_inherited))])
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

definition "print_infra_instantiation_class = start_map'' Thy_instantiation_class o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, l_inherited) in
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
                                         , Expr_apply oid_of [Expr_basic [var_oid]])) l_cons))]))
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

definition "print_astype_class = start_map'' Thy_defs_overloaded o (\<lambda>expr base_attr _ _.
  map_class_gen_h'' (\<lambda>isub_name name l_hierarchy nl_attr.
    let nl_attr = base_attr nl_attr in
    List_map
      (let l_hierarchy = List_map fst l_hierarchy in (\<lambda> (h_name, hl_attr).
        let hl_attr = base_attr hl_attr in
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
      l_hierarchy) expr)"

definition "print_astype_from_universe = start_map Thy_definition_hol o
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

definition "print_astype_from_universe' = start_map'' Thy_definition_hol o (\<lambda>expr base_attr _ _.
  map_class_h'' (\<lambda>isub_name name l_hierarchy nl_attr.
    let nl_attr = base_attr nl_attr in
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_astype]) ''=''
   (let ((finish_with_some1, finish_with_some2), last_case_none) =
     if (fst o hd) l_hierarchy = name then
       ((id, Expr_binop (Expr_basic [''Some'']) ''o''), [])
     else
       ((Expr_some, id), [(Expr_basic [wildcard], Expr_basic [''None''])]) in
   finish_with_some2
   (Expr_function (flatten (List_map
   (let l_hierarchy = List_map fst l_hierarchy in (\<lambda>(h_name, hl_attr).
     let hl_attr = base_attr hl_attr in
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
   # [last_case_none])))))) expr)"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclastype, ''_'', name])) name_set) ]))"

definition "print_astype_lemma_cp expr = (start_map Thy_lemma_by o get_hierarchy_map (
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

definition "print_astype_defined = start_map Thy_lemma_by o (\<lambda>expr. flatten (map_class_gen_h''' (\<lambda>isub_name name l_hierarchy _ _ _.
     (let l_hierarchy = List_map fst l_hierarchy
        ; var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
    List_map (\<lambda>h_name.
      case compare_hierarchy l_hierarchy h_name name of LT \<Rightarrow>
        [ Lemma_by_assum
          (flatten [isub_name const_oclastype, ''_'', h_name, ''_defined''])
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_astype name])))
          [App_using [Thm_str var_isdef]]
          (Tacl_by [Tac_auto_simp_add (flatten [isub_name const_oclastype, ''_'', h_name]
                                        # ''foundation16''
                                        # List_map hol_definition [''null_option'', ''bot_option'' ])]) ]
      | _ \<Rightarrow> [])
      l_hierarchy)) expr))"

definition "print_astype_up_d_cast0_name name_any name_pers = flatten [''up'', isub_of_str name_any, ''_down'', isub_of_str name_pers, ''_cast0'']"
definition "print_astype_up_d_cast0 = start_map Thy_lemma_by o
  map_class_nupl2' (\<lambda>name_pers name_any.
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
  map_class_nupl2' (\<lambda>name_pers name_any.
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

definition "print_istypeof_class = start_map'' Thy_defs_overloaded o (\<lambda>expr base_attr _ _.
  map_class_gen_h''' (\<lambda>isub_name name l_hierarchy _ l_inh _.
    let l_inh = List_map base_attr l_inh in
    List_map
      (let l_hierarchy = List_map fst l_hierarchy in
      (\<lambda> (h_name, hl_attr).
        let hl_attr = base_attr hl_attr in
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
      l_hierarchy) expr)"

definition "print_istypeof_from_universe = start_map Thy_definition_hol o
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

definition "print_istypeof_from_universe' = start_map Thy_definition_hol o
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
      (bug_ocaml_extraction (let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
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
definition "print_istypeof_defined = start_map Thy_lemma_by o flatten o map_class_h (\<lambda>isub_name name l_hierarchy.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_istypeof_defined_name isub_name h_name)
          [(var_isdef, False, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          [App [Tac_insert [Thm_simplified (Thm_str var_isdef) (Thm_str (''foundation18'' @@ [Char Nibble2 Nibble7])) ]
               ,Tac_simp_only [Thm_str (hol_definition ''OclValid'')]
               ,Tac_subst (Thm_str ''cp_defined'')]]
          (Tacl_by [Tac_auto_simp_add_split ( Thm_symmetric (Thm_str ''cp_defined'')
                                            # List_map Thm_str ( hol_definition ''bot_option''
                                                          # [ flatten [isub_name const_oclistypeof, ''_'', h_name] ]))
                                            (''option.split'' # split_ty h_name) ]) )
        l_hierarchy))"

definition "print_istypeof_defined'_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'',  [Char Nibble2 Nibble7]]"
definition "print_istypeof_defined' = start_map Thy_lemma_by o flatten o map_class_h (\<lambda>isub_name name l_hierarchy.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_istypeof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_istypeof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str ''foundation20'')))]) )
        l_hierarchy))"

definition "print_istypeof_up_larger_name name_pers name_any = flatten [''actualType'', isub_of_str name_pers, ''_larger_staticType'', isub_of_str name_any]"
definition "print_istypeof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2' (\<lambda>name_pers name_any.
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
  map_class_nupl3'_GE (\<lambda>name_pers name_mid name_any.
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
definition "print_iskindof_class = start_map Thy_defs_overloaded o map_class_gen_h''''
  (\<lambda>isub_name name l_hierarchy l_attr l_inherited l_cons. List_map (\<lambda> (h_name, _).
    Defs_overloaded
          (print_iskindof_class_name isub_name h_name)
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_iskindof name]))
             unicode_equiv
             (let isof = (\<lambda>f name. Expr_warning_parenthesis (Expr_postunary (Expr_basic [var_x]) (Expr_basic [f name]))) in
              case l_cons of [] \<Rightarrow> isof dot_istypeof name
                           | name_past # _ \<Rightarrow> Expr_binop (isof dot_istypeof name) ''or'' (isof dot_iskindof name_past))))
     l_hierarchy)"

definition "print_iskindof_from_universe = start_map Thy_definition_hol o
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

definition "print_iskindof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_iskindof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_ocliskindof, ''_'', name] )) name_set) ]))"

definition "print_iskindof_lemma_cp expr = (start_map Thy_lemma_by o
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
      ; lem_simp1 = Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name1, ''_'', name2])]
      ; lem_simp2 = Tac_simp_only [Thm_str (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])] in
    let (tac1, tac2) = case name1_previous
    of None \<Rightarrow> ([], Tacl_by [ lem_simp1 , lem_simp2 ])
     | Some name1_previous \<Rightarrow>
      ( [ [ lem_simp1 ]
        , [ Tac_rule (Thm_where (Thm_str ''cpI2'') [(''f'', Expr_preunary (Expr_basic [''op'']) (Expr_basic [''or'']))])
          , Tac_plus [Tac_rule (Thm_str ''allI'')]
          , Tac_rule (Thm_str ''cp_OclOr'') ] ]
      , Tacl_by [ lem_simp2 , Tac_simp_only [Thm_str (flatten [''cp_'', const_ocliskindof, isub_of_str name1_previous, ''_'', name3, ''_'', name2])] ])
    in Lemma_by lemma_name lemma_spec tac1 tac2
  ) (\<lambda>x. let rev_x = rev x in (rev_x, rev_x, x))) expr"

definition "print_iskindof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp ''''
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
  ) (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_lemma_strict expr = (start_map Thy_lemma_by o
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
      (Tacl_by
        (Tac_simp_only
           (List_map Thm_str (flatten
              [ [flatten [const_ocliskindof, isub_of_str name1, ''_'', name3]]
              , [flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]]
              , case name1_previous
                of None \<Rightarrow> []
                 | Some name1_previous \<Rightarrow> [flatten [const_ocliskindof, isub_of_str name1_previous, ''_'', name3, ''_'', name2]] ]))
        # (if name1_previous = None then [] else [Tac_simp])) )
  ) (\<lambda>x. (rev x, [(''invalid'',''invalid''),(''null'',''true'')], x))) expr"

definition "print_iskindof_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp '''' (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
  ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_defined_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name, ''_defined'']"
definition "print_iskindof_defined = start_map Thy_lemma_by o flatten o map_class_h'''' (\<lambda>isub_name name l_hierarchy _ _ l_cons.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_iskindof_defined_name isub_name h_name)
          [(var_isdef, False, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [ Tac_simp_only [Thm_str (flatten [isub_name const_ocliskindof, ''_'', h_name])]
                   , Tac_rule
                      (let mk_OF = \<lambda>f. Thm_OF (Thm_str (f h_name)) (Thm_str var_isdef) in
                       case l_cons of
                         n # _ \<Rightarrow>
                             thm_OF
                               (Thm_str ''defined_or_I'')
                               (List_map mk_OF
                                  [ print_istypeof_defined_name isub_name
                                  , print_iskindof_defined_name (\<lambda>name. name @@ isub_of_str n)])
                       | [] \<Rightarrow> mk_OF (print_istypeof_defined_name isub_name)) ]))
        (List_map fst l_hierarchy)))"

definition "print_iskindof_defined'_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name, ''_defined'', [Char Nibble2 Nibble7]]"
definition "print_iskindof_defined' = start_map Thy_lemma_by o flatten o map_class_h'''' (\<lambda>isub_name name l_hierarchy _ _ l_cons.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_iskindof_defined'_name isub_name h_name)
          [(var_isdef, False, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_iskindof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str ''foundation20'')))]) )
        (List_map fst l_hierarchy)))"

definition "print_iskindof_up_eq_asty_name name = (flatten [''actual_eq_static'', isub_of_str name])"
definition "print_iskindof_up_eq_asty = start_map Thy_lemma_by o map_class_gen_h''''
  (\<lambda> isub_name name _ _ _ l_cons.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    [Lemma_by_assum
        (print_iskindof_up_eq_asty_name name)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name)
               (Expr_basic [dot_iskindof name]))))
        [App [Tac_simp_only (List_map Thm_str [flatten [const_ocliskindof, isub_of_str name, ''_'', name], hol_definition ''OclValid''])
             ,Tac_insert [Thm_str var_isdef]]]
        (Tacl_by (let l = let l =
                           [Tac_auto_simp_add_split (bug_ocaml_extraction (let l =
                                                      List_map Thm_str (flatten ([''foundation16'', hol_definition ''bot_option'']
                                                    # List_map (\<lambda>n. flatten [const_ocliskindof, isub_of_str n, ''_'', name]
                                                             # flatten [const_oclistypeof, isub_of_str n, ''_'', name]
                                                             # []) l_cons)) in
                                                     if l_cons = [] then l else Thm_symmetric (Thm_str ''cp_OclOr'') # l))
                                                    (''option.split'' # flatten (split_ty name # List_map split_ty l_cons))] in
                            if l_cons = [] then l else Tac_subst (Thm_str ''cp_OclOr'') # l in
                  if l_cons = [] (* FIXME remove this condition if possible *) then l else [Tac_plus l]))])"

definition "print_iskindof_up_larger_name name_pers name_any = flatten [''actualKind'', isub_of_str name_pers, ''_larger_staticKind'', isub_of_str name_any]"
definition "print_iskindof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2'' (\<lambda>name_pers name_any name_pred.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_iskindof_up_larger_name name_pers name_any)
        [(var_isdef, False, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_pers)
               (Expr_basic [dot_iskindof name_any]))))
        (List_map (\<lambda>s. App [s]) [ Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name_any, ''_'', name_pers])]
                           , Tac_insert (List_map (\<lambda>s. Thm_OF (Thm_str s) (Thm_str var_isdef))
                                           [ case name_pred of None => print_iskindof_up_eq_asty_name name_pers
                                                             | Some name_pred => print_iskindof_up_larger_name name_pers name_pred
                                           , print_istypeof_up_larger_name name_pers name_any])
                           , Tac_rule (Thm_THEN (Thm_str ''foundation11'') (Thm_str ''iffD2''))])
        (Tacl_by [Tac_plus [Tac_simp_add [''OclNot_defargs'', ''foundation6'', ''foundation14'']]]))"

definition "print_iskindof_up_istypeof_name name_pers name_any = flatten [''not_'', const_ocliskindof, isub_of_str name_pers, ''_then_'', name_any, ''_'', const_oclistypeof, ''_others'']"
definition "print_iskindof_up_istypeof = start_map Thy_lemma_by o
  map_class_nupl2l' (\<lambda>name_pers name_any name_pred.
    let var_X = ''X''
      ; var_iskin = ''iskin''
      ; var_isdef = ''isdef''
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_iskindof_up_istypeof_name name_pers name_any)
        [(var_iskin, False, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_pers]))))
        ,(var_isdef, False, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (expr_binop unicode_or (List_map (\<lambda>name_pred. f id (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_istypeof name_pred])))) (name_any # name_pred)))
        (bug_ocaml_extraction (let f_app = \<lambda>name_pred name_pred_pred.
            App [Tac_simp_only [Thm_str (print_iskindof_class_name (\<lambda>s. s @@ isub_of_str name_pred) name_any)
                               ,thm_OF (Thm_str ''foundation11'')
                                       (List_map (\<lambda>(pr, n). Thm_OF (Thm_str (pr (\<lambda>name. name @@ isub_of_str n) name_any)) (Thm_str var_isdef))
                                          [ (print_istypeof_defined'_name, name_pred)
                                          , (print_iskindof_defined'_name, name_pred_pred)])]] in
            App_using [Thm_OF (Thm_str (print_iskindof_up_eq_asty_name name_any)) (Thm_str var_isdef)]
          # f_app name_any (case name_pred of name_pers # _ \<Rightarrow> name_pers | [] \<Rightarrow> name_pers)
          # flatten (let map_pred = \<lambda>f l init. let (l, _) = List.fold (\<lambda> x (acc, pred). (f x pred # acc, x)) (rev l) ([], init) in l in
                     map_pred (\<lambda>name_pred name_pred_pred.
                       [App [Tac_erule (Thm_str ''disjE''), Tac_simp, Tac_rule (Thm_str ''disjI2'')]
                       ,f_app name_pred name_pred_pred ]) name_pred name_pers)))
        (Tacl_by [Tac_simp_add [var_iskin]]))"

definition "print_iskindof_up_d_cast expr = (start_map Thy_lemma_by o
  map_class_nupl3'_LE' (\<lambda>name_pers name_mid name_any name_pred.
    let var_X = ''X''
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
        (List_map App
          ( let f = \<lambda>name_pred. [Tac_rule (Thm_str (print_istypeof_up_d_cast_name name_pred name_any name_pers))
                                ,Tac_simp_only [] (* FIXME use wildcard *)
                                ,Tac_simp_only [Thm_str var_isdef]] in
            ( Tac_insert [thm_OF (Thm_str (print_iskindof_up_istypeof_name name_mid name_any)) (List_map Thm_str [var_iskin, var_isdef])]
            # (case name_pred of [] \<Rightarrow> [] | _ \<Rightarrow> [ Tac_elim (Thm_str ''disjE'') ]))
          # List_map f (name_any # name_pred)))
        Tacl_done)) expr"

subsection{* allInstances *}

definition "print_allinst_def_id = start_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
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
     ; s_generic = ''generic''
     ; lem_gen = f_tit s_generic
     ; mk_pre_post = \<lambda>pre_post at_when.
         let s_allinst = f_allinst at_when in
         Lemma_by_assum
           (f_tit at_when)
           []
           (spec (Expr_apply s_allinst) pre_post)
           [App_unfolding [Thm_str (d s_allinst)]]
           (Tacl_by (Tac_rule (Thm_str lem_gen) # tac_last)) in
  [ f_lemma lem_gen (spec (\<lambda>l. Expr_apply (f_allinst s_generic) (b var_pre_post # l)) var_pre_post) var_pre_post
  , mk_pre_post ''snd'' ''at_post''
  , mk_pre_post ''fst'' ''at_pre'' ])"

definition "print_allinst_exec = start_map Thy_lemma_by o map_class_top (\<lambda>isub_name name _ _ _ _.
  let b = \<lambda>s. Expr_basic [s]
    ; a = \<lambda>f x. Expr_apply f [x]
    ; d = hol_definition
    ; f = Expr_paren unicode_lfloor unicode_rfloor
    ; f_img = \<lambda>e1. Expr_binop (b e1) ''`''
    ; ran_heap = \<lambda>var_pre_post var_tau. f_img name (a ''ran'' (a ''heap'' (Expr_apply var_pre_post [b var_tau])))
    ; Expr_lambd = \<lambda>x f. Expr_lambda x (f x)
    ; f_incl = \<lambda>v1 v2.
        let var_tau = unicode_tau in
        Expr_bind0 unicode_And (b var_tau) (Expr_binop (Expr_applys (Expr_pat v1) [b var_tau]) unicode_subseteq (Expr_applys (Expr_pat v2) [b var_tau]))
    ; var_B = ''B''
    ; var_C = ''C'' in
  gen_pre_post
    (\<lambda>s. flatten [isub_name s, ''_exec''])
    (\<lambda>f_expr var_pre_post.
      Expr_rewrite
       (f_expr [b name])
       ''=''
       (Expr_lambd unicode_tau (\<lambda>var_tau. Expr_apply ''Abs_Set_0'' [f (f (f_img ''Some'' (ran_heap var_pre_post var_tau))) ])))
    (\<lambda>lem_tit lem_spec var_pre_post.
      Lemma_by_assum
        lem_tit
        []
        lem_spec
        (bug_ocaml_extraction (let var_S1 = ''S1''
           ; var_S2 = ''S2'' in
         [ App_let (Expr_pat var_S1) (Expr_lambd unicode_tau (ran_heap var_pre_post))
         , App_let (Expr_pat var_S2) (Expr_lambd unicode_tau (\<lambda>var_tau. Expr_binop (Expr_applys (Expr_pat var_S1) [b var_tau]) ''-'' (Expr_paren ''{'' ''}'' (b ''None''))))
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

definition "print_allinst_istypeof_single isub_name name const_oclisof dot_isof f_simp1 f_simp2 =
  (let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [''1'',''2'',''3'']
    ; var_tau = unicode_tau in
  gen_pre_post
    (\<lambda>s. flatten [name, ''_'', s, ''_'', isub_name const_oclisof])
    (\<lambda>f_expr _. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply ''OclForall'' [f_expr [b name], b (isub_name const_oclisof) ]))
    (\<lambda>lem_tit lem_spec _. Lemma_by
      lem_tit
      [lem_spec]
      [ [Tac_simp_add_del [d ''OclValid''] (d ''OclAllInstances_generic'' # f_simp1 [flatten [isub_name const_oclisof, ''_'', name]])]
      , [Tac_simp_only (flatten [List_map Thm_str [ d ''OclForall'', ''refl'', ''if_True'' ], [Thm_simplified (Thm_str ''OclAllInstances_generic_defined'') (Thm_str (d ''OclValid''))]])]
      , [Tac_simp_only [Thm_str (d ''OclAllInstances_generic'')]]
      , [s (Thm_str ''Abs_Set_0_inverse''), Tac_simp_add [d ''bot_option'']]
      , [s (Thm_where
             (Thm_str print_allinst_istypeof_pre_name1)
             [ (''s'', let var_x = ''x'' in (Expr_lambda var_x (Expr_applys (Expr_postunary (Expr_lambda wildcard (b var_x)) (b (dot_isof name))) [b var_tau])))
             , (''t'', Expr_lambda wildcard (Expr_apply ''true'' [b var_tau]))])]
      , [Tac_intro [Thm_str ''ballI'', thm_simplified (Thm_str (print_iskindof_up_eq_asty_name name)) (List_map Thm_str (d ''OclValid'' # f_simp2 [flatten [isub_name const_ocliskindof, ''_'', name]]))]]
      , [Tac_drule (Thm_str print_allinst_istypeof_pre_name2), Tac_erule (Thm_str (''exE'')), Tac_simp]]
      (Tacl_by [Tac_simp]))
      [])"

definition "print_allinst_istypeof = start_map'' Thy_lemma_by o (\<lambda>expr base_attr _ _. map_class_gen (\<lambda>isub_name name l_attr _ _ next_dataty.
  let l_attr = base_attr l_attr in
  let b = \<lambda>s. Expr_basic [s]
    ; d = hol_definition
    ; s = Tac_subst_l [''1'',''2'',''3'']
    ; var_tau = unicode_tau in
  case next_dataty of None \<Rightarrow>
    print_allinst_istypeof_single isub_name name const_oclistypeof dot_istypeof (\<lambda>_. []) id
  | Some (OclClass name_next _ _) \<Rightarrow>
    flatten 
    [ gen_pre_post
        (\<lambda>s. flatten [name, ''_'', s, ''_'', isub_name const_oclistypeof, ''1''])
        (\<lambda>f_expr _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply ''OclForall'' [f_expr [b name], b (isub_name const_oclistypeof) ])))
        (\<lambda>lem_tit lem_spec var_pre_post. Lemma_by_assum
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
        (\<lambda>f_expr _.
           Expr_exists
             unicode_tau
             (\<lambda>var_tau. Expr_binop (b var_tau) unicode_Turnstile (Expr_apply ''not'' [Expr_apply ''OclForall'' [f_expr [b name], b (isub_name const_oclistypeof) ]])))
        (\<lambda>lem_tit lem_spec var_pre_post. Lemma_by_assum
           lem_tit
           [('''', True, Expr_And ''x'' (\<lambda>var_x. Expr_rewrite (Expr_apply var_pre_post [Expr_parenthesis (Expr_binop (b var_x) '','' (b var_x))]) ''='' (b var_x)) )]
           lem_spec
           (bug_ocaml_extraction (let var_oid = ''oid''
              ; var_a = ''a''
              ; var_t0 = ''t0''
              ; s_empty = ''Map.empty'' in
            [ App_fix [var_oid, var_a]
            , App_let (Expr_pat var_t0) (Expr_apply ''state.make''
                ( Expr_apply s_empty [Expr_binop (b var_oid) unicode_mapsto (Expr_apply (isub_name datatype_in) [Expr_apply (isub_name datatype_constr_name) (Expr_apply (datatype_ext_constr_name @@ mk_constr_name name name_next) [b var_a] # List_map (\<lambda>_. b ''None'') l_attr)])]
                # List_map (\<lambda>_. b s_empty) (List.upt 1 assoc_max)))
            , App [Tac_rule (Thm_where (Thm_str ''exI'') [(''x'', Expr_parenthesis (Expr_binop (Expr_pat var_t0) '','' (Expr_pat var_t0)))]), Tac_simp_add_del [d ''OclValid''] [d ''OclAllInstances_generic'']]
            , App [Tac_simp_only (flatten [List_map Thm_str [ d ''OclForall'', ''refl'', ''if_True'' ], [Thm_simplified (Thm_str ''OclAllInstances_generic_defined'') (Thm_str (d ''OclValid''))]])]
            , App [Tac_simp_only (List_map (\<lambda>x. Thm_str (d x)) [''OclAllInstances_generic'', flatten [isub_name const_oclastype, ''_'', unicode_AA]])]
            , App [s (Thm_str ''Abs_Set_0_inverse''), Tac_simp_add [d ''bot_option'']] ] ))
           (Tacl_by [Tac_simp_add [d ''state.make'', d ''OclNot'']]))
        [Tac_simp]]) expr)"

definition "print_allinst_iskindof = start_map Thy_lemma_by o map_class_gen (\<lambda>isub_name name _ _ _ _.
  print_allinst_istypeof_single isub_name name const_ocliskindof dot_iskindof id (\<lambda>_. []))"

subsection{* accessors *}

definition "print_access_oid_uniq_name isub_name attr = isub_name var_oid_uniq @@ isup_of_str attr"
definition "print_access_oid_uniq =
  (\<lambda>expr ocl.
    if D_design_analysis ocl = None then ([], ocl) else
      (\<lambda>(l, oid_start). (List_map Thy_definition_hol l, ocl \<lparr> D_oid_start := oid_start \<rparr>))
      (let (l, acc) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = List_map snd l_inh in
         let (l, cpt) = fold_list (fold_list
           (\<lambda> (attr, OclTy_object _) \<Rightarrow> \<lambda>cpt.
             ([Definition (Expr_rewrite
                   (Expr_basic [print_access_oid_uniq_name isub_name attr])
                   ''=''
                   (Expr_oid '''' (oidGetAssoc cpt)))], oidSucAssoc cpt)
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (flatten (flatten l), cpt)) (D_oid_start ocl) expr in
       (flatten l, acc)))"

definition "print_access_eval_extract _ = start_map Thy_definition_hol
  (let lets = \<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_basic [def])) in
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

definition "print_access_choose = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (let lets = \<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_basic [def]))
     ; lets' = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' exp) in
  if design_analysis = None then \<lambda>_. [] else
  if design_analysis = Some 1 then (\<lambda>_.
  let mk_n = \<lambda>s. s @@ isub_of_str ''2'' in
  ( lets (flatten [mk_n var_choose, ''_1'']) ''fst''
  # lets (flatten [mk_n var_choose, ''_2'']) ''snd''
  # lets' (flatten [mk_n var_switch, ''_1'']) (Expr_basic [''id''])
  # lets' (flatten [mk_n var_switch, ''_2'']) (let cpl = \<lambda>x y. Expr_parenthesis (Expr_binop (Expr_basic [x]) '','' (Expr_basic [y]))
                                                 ; var_x = ''x''
                                                 ; var_y = ''y'' in
                                               Expr_lambdas0 (cpl var_x var_y) (cpl var_y var_x))
  # [ let var_pre_post = ''pre_post''
        ; var_to_from = ''to_from''
        ; var_assoc_oid = ''assoc_oid''
        ; var_f = ''f''
        ; var_oid = ''oid''
        ; var_tau = unicode_tau in
      Definition (Expr_rewrite
        (Expr_basic [mk_n var_deref_assocs, var_pre_post, var_to_from, var_assoc_oid, var_f, var_oid ])
        ''=''
        (Expr_lambda var_tau (Expr_case (Expr_apply (mk_n var_assocs) [Expr_apply var_pre_post [Expr_basic [var_tau]]
                                                                      ,Expr_basic [var_assoc_oid]])
                                        [ bug_ocaml_extraction (let var_S = ''S'' in
                                          ( Expr_some (Expr_basic [var_S])
                                          , Expr_apply var_f
                                              [ Expr_apply ''List.map''
                                                 [ Expr_binop
                                                     (Expr_basic [flatten [mk_n var_choose, ''_2'']])
                                                     unicode_circ
                                                     (Expr_basic [var_to_from])
                                                 , Expr_apply ''filter'' [ bug_ocaml_extraction (let var_p = ''p'' in Expr_lambda var_p (Expr_rewrite (Expr_applys (Expr_basic [flatten [mk_n var_choose, ''_1'']]) [Expr_apply var_to_from [Expr_basic [var_p]]]) ''='' (Expr_basic [var_oid])))
                                                                         , Expr_basic [var_S]]]
                                              , Expr_basic [var_oid]
                                              , Expr_basic [var_tau]]))
                                        , ( Expr_basic[wildcard], Expr_apply ''invalid'' [Expr_basic [var_tau]]) ]))) ] )) else (\<lambda>_. []) (* TO DO *)) expr)"

definition "print_access_deref_oid = start_map Thy_definition_hol o
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

definition "print_access_deref_assocs_name isub_name = flatten [var_deref, ''_'', isub_name var_assocs]"
definition "print_access_deref_assocs = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (if design_analysis = None then \<lambda>_. [] else (\<lambda>expr. flatten (flatten (map_class (\<lambda>isub_name name l_attr l_inherited _ _.
  let l_inherited = List_map snd l_inherited in
  let mk_n = \<lambda>s. s @@ isub_of_str ''2''
    ; var_fst_snd = ''fst_snd''
    ; var_f = ''f''
    ; b = \<lambda>s. Expr_basic [s] in
    flatten (List_map (List_map
      (\<lambda> (attr, OclTy_object _) \<Rightarrow>
           [Definition (Expr_rewrite
                  (Expr_basic [(print_access_deref_assocs_name isub_name @@ isup_of_str attr), var_fst_snd, var_f])
                  ''=''
                  (Expr_binop
                    (Expr_apply
                      (mk_n var_deref_assocs)
                        (List_map b [ var_fst_snd
                               , flatten [mk_n var_switch, ''_1'']
                               , print_access_oid_uniq_name isub_name attr
                               , var_f ]))
                    unicode_circ
                    (b ''oid_of'')))]
       | _ \<Rightarrow> []))
      (l_attr # l_inherited))) expr)))) expr)"

definition "print_access_select_object = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (if design_analysis = None then \<lambda>_. [] else (\<lambda>_. [
   (let var_mt = ''mt''
      ; var_incl = ''incl''
      ; var_smash = ''smash''
      ; var_deref = ''deref''
      ; var_l = ''l''
      ; var_oid = ''oid''
      ; b = \<lambda>s. Expr_basic [s] in
    Definition (Expr_rewrite
                  (Expr_basic [var_select_object, var_mt, var_incl, var_smash, var_deref, var_l, var_oid])
                  ''=''
                  (Expr_apply var_smash
                     [ Expr_apply ''foldl''
                         [ b var_incl
                         , b var_mt
                         , Expr_apply ''List.map''
                             [ b var_deref
                             , b var_l ] ]]))) ])) expr)"

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
    let l_inherited = flatten (List_map snd l_inherited) in
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
                            # (List_map (\<lambda>x. let var_x = lowercase_of_str x in
                                             (Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x)
                                                             [Expr_basic [var_x]]
                                                         # List_map (\<lambda>_. wildc) l_attr), (Expr_apply (isup_attr (var_select @@ isub_of_str x))
                                                                                                     (List_map (\<lambda>x. Expr_basic [x]) [var_f, var_x]) ))) l_cons)
                            # [])))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_inherited), [])
      l_inherited) in
    rev l) expr)"

definition "print_access_select_obj = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (if design_analysis = None then \<lambda>_. [] else (\<lambda>expr. flatten (flatten (map_class (\<lambda>isub_name name l_attr l_inh _ _.
    let l_inh = List_map snd l_inh in
    flatten (List_map (List_map
      (\<lambda> (attr, OclTy_object _) \<Rightarrow>
           [Definition (let var_f = ''f''
                          ; b = \<lambda>s. Expr_basic [s] in
              Expr_rewrite
                  (Expr_basic [isub_name var_select @@ isup_of_str attr, var_f])
                  ''=''
                  (Expr_apply var_select_object [b ''mtSet'', b ''OclIncluding'', b ''OclANY'', Expr_apply var_f [let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x])))]]))]
       | _ \<Rightarrow> []))
      (l_attr # l_inh))) expr)))) expr)"

definition "print_access_dot_consts = start_map Thy_consts_class o
  flatten o flatten o map_class (\<lambda>isub_name name l_attr _ _ _.
    List_map (\<lambda>(attr_n, attr_ty).
      List_map
        (\<lambda>(var_at_when_hol, var_at_when_ocl).
          Consts_raw
            (flatten [''dot'', isup_of_str attr_n, var_at_when_hol])
            (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA, Ty_base (Char Nibble2 Nibble7 # unicode_alpha)])
            (case attr_ty of
                OclTy_base attr_ty \<Rightarrow> Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
                  let option = \<lambda>x. Ty_apply (Ty_base ''option'') [x] in
                  option (option (Ty_base attr_ty))]
              | OclTy_object _ \<Rightarrow> Ty_base name)
            (mk_dot attr_n var_at_when_ocl))
        [ (var_at_when_hol_post, var_at_when_ocl_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre)]) l_attr)"

definition "print_access_dot = start_map'''' Thy_defs_overloaded o (\<lambda>expr design_analysis.
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_orig attr_ty isup_attr dot_attr.
            [ Defs_overloaded
                (flatten [isup_attr (isub_name ''dot''), dot_at_when])
                (let var_x = ''x'' in
                 Expr_rewrite
                   (dot_attr (Expr_annot (Expr_basic [var_x]) name))
                   unicode_equiv
                   (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = \<lambda>attr_orig l. Expr_apply (case attr_orig of None \<Rightarrow> isub_name var_deref_oid
                                                                              | Some orig_n \<Rightarrow> var_deref_oid @@ isub_of_str orig_n) (Expr_basic [var_in_when_state] # l) in
                    deref_oid None [ (case (design_analysis, attr_ty) of
                                   (Some _, OclTy_object _) \<Rightarrow>
                                     \<lambda>l. Expr_apply (isup_attr (print_access_deref_assocs_name isub_name)) (Expr_basic [var_in_when_state] # [l])
                                 | _ \<Rightarrow> id) (Expr_apply (isup_attr (isub_name var_select))
                          [case attr_ty of OclTy_base _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                         | OclTy_object _ \<Rightarrow> deref_oid attr_orig [] ]) ] ])) ]) expr)"

definition "print_access_dot_lemmas_id_set =
  (if activate_simp_optimization then
     map_class_arg_only_var'
       (\<lambda>isub_name _ (_, dot_at_when) _ _ isup_attr _. [flatten [isup_attr (isub_name ''dot''), dot_at_when]])
   else (\<lambda>_. []))"

definition "print_access_dot_lemmas_id = start_map' (\<lambda>expr.
       (let name_set = print_access_dot_lemmas_id_set expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map Thm_str name_set) ]))"

definition "print_access_dot_cp_lemmas_set =
  (if activate_simp_optimization then [hol_definition var_eval_extract] else [])"

definition "print_access_dot_cp_lemmas = start_map' (\<lambda>_.
  List_map (\<lambda>x. Thy_lemmas_simp (Lemmas_simp '''' [Thm_str x])) print_access_dot_cp_lemmas_set)"

definition "print_access_dot_lemma_cp = start_map Thy_lemma_by o
  map_class_arg_only_var
    (\<lambda>isub_name name (_, dot_at_when) _ _ isup_attr dot_attr.
            [ Lemma_by
                (flatten [''cp_'', isup_attr (isub_name ''dot''), dot_at_when])
                (bug_ocaml_extraction
                (let var_x = ''X'' in
                 [Expr_apply ''cp'' [Expr_lambda var_x (dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]))
                []
                (Tacl_by [if print_access_dot_cp_lemmas_set = [] then
                            Tac_auto_simp_add (List_map hol_definition [''cp'', var_eval_extract, flatten [isup_attr (isub_name ''dot''), dot_at_when]])
                          else
                            Tac_auto_simp_add (List_map hol_definition [''cp''])]) ])
    (\<lambda>isub_name name (_, dot_at_when) _ _ isup_attr dot_attr.
            [ Lemma_by
                (flatten [''cp_'', isup_attr (isub_name ''dot''), dot_at_when])
                (bug_ocaml_extraction
                (let var_x = ''X'' in
                 [Expr_apply ''cp'' [Expr_lambda var_x (dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]))
                []
                (if print_access_dot_cp_lemmas_set = [] then Tacl_sorry (* fold l_hierarchy, take only subclass, unfold the corresponding definition *)
                 else Tacl_by [Tac_auto_simp_add (List_map hol_definition [''cp''])]) ])"

definition "print_access_dot_lemmas_cp = start_map Thy_lemmas_simp o (\<lambda>expr. [Lemmas_simp ''''
  (map_class_arg_only_var'
    (\<lambda>isub_name _ (_, dot_at_when) _ _ isup_attr _.
      [Thm_str (flatten [''cp_'', isup_attr (isub_name ''dot''), dot_at_when]) ])
    expr)])"

definition "print_access_lemma_strict expr = (start_map Thy_lemma_by o
  map_class_arg_only_var' (\<lambda>isub_name name (_, dot_at_when) _ _ isup_attr dot_attr.
            List_map (\<lambda>(name_invalid, tac_invalid). Lemma_by
                  (flatten [isup_attr (isub_name ''dot''), dot_at_when, ''_'', name_invalid])
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

definition "print_examp_instance_draw_list_attr map_self map_username =
  (let b = \<lambda>s. Expr_basic [s]
     ; f_get = \<lambda> None \<Rightarrow> b ''None''
               | Some cpt \<Rightarrow> Expr_some (Expr_oid var_oid_uniq (oidGetInh cpt)) in
   List_map (\<lambda> None \<Rightarrow> b ''None''
             | Some (ty, ocl) \<Rightarrow>
     case ocl of Shall_str s \<Rightarrow> (case ty of OclTy_object _ \<Rightarrow> f_get (map_username s) | _ \<Rightarrow> Expr_some (b s))
               | Shall_self cpt1 \<Rightarrow> f_get (map_self cpt1)))"

definition "print_examp_instance_app_constr_notmp map_self map_username = (\<lambda>isub_name app_x l_attr.
  Expr_apply
    (isub_name datatype_constr_name)
    ( app_x
    # print_examp_instance_draw_list_attr map_self map_username l_attr))"

definition "rbt_of_class ocl =
  (let rbt = (snd o fold_class_gen (\<lambda>_ name l_attr l_inh _ _ rbt.
     ( [()]
     , modify_def (empty, []) name
         (let fold = \<lambda>tag l rbt.
            let (rbt, _, n) = List.fold
                                   (\<lambda> (name_attr, ty) \<Rightarrow> \<lambda>(rbt, cpt, l_obj).
                                     (insert name_attr (ty, tag, OptIdent cpt) rbt, Suc cpt, (case ty of OclTy_object _ \<Rightarrow> True | _ \<Rightarrow> False) # l_obj))
                                   l
                                   (rbt, 0, []) in
            (rbt, (tag, n)) in
          (\<lambda>(rbt, _).
           let (rbt, info_own) = fold OptOwn l_attr rbt in
           let (rbt, info_inh) = fold OptInh (flatten (List_map snd l_inh)) rbt in
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
              (let f_fold = \<lambda>(n, accu). (Suc n, f n accu) in
               if D_design_analysis ocl = None then
                 (\<lambda>_ . f_fold)
               else
                 \<lambda> True \<Rightarrow> (\<lambda>(n, accu). (Suc n, accu))
                 | False \<Rightarrow> f_fold) (rev l) (0, accu) in
          accu) (List_assoc v l)) rbt)))"

definition "fill_blank f_blank =
  List_map (\<lambda> (attr_ty, l).
    case f_blank attr_ty of Some f_fold \<Rightarrow>
    let rbt = List.fold (\<lambda> ((ty, _, ident), shallow) \<Rightarrow> insert ident (ty, shallow)) l empty in
    (attr_ty, case f_fold (\<lambda>n l. lookup rbt (OptIdent n) # l) [] of l \<Rightarrow> rev l))"

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
   "print_examp_instance_app_constr2_notmp (map_self, map_username) ty l_attr isub_name cpt =
  (let (l_inh, l_own) =
     let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt) in
     case l_attr of
       OclAttrNoCast [(OptOwn, l_own), (OptInh, l_inh)] \<Rightarrow> (Expr_apply (isub_name datatype_ext_constr_name) (var_oid # print_examp_instance_draw_list_attr map_self map_username l_inh), l_own)
     | OclAttrCast x l_attr [(OptOwn, l_own)] \<Rightarrow>
                      (Expr_apply
                        (datatype_ext_constr_name @@ mk_constr_name ty x)
                        [ let isub_name = \<lambda>s. s @@ isub_of_str x in
                          print_examp_instance_app_constr2_notmp (map_self, map_username) ty l_attr isub_name cpt ], l_own) in
   print_examp_instance_app_constr_notmp map_self map_username isub_name l_inh l_own)"

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
         , Suc accu))
       l
       (empty, empty, D_oid_start ocl, 0) in
   (rbt_of_class ocl, lookup rbt_nat, lookup rbt_str))"

definition "print_examp_instance_app_constr2_notmp_norec = (\<lambda>(rbt, self_username) ocl ocli.
  print_examp_instance_app_constr2_notmp self_username (Inst_ty ocli) (split_inh_own rbt (Inst_ty ocli) (Inst_attr ocli)))"

definition "print_examp_instance_name = id"
definition "print_examp_instance = (\<lambda> OclInstance l \<Rightarrow> \<lambda> ocl.
  (\<lambda>((l, oid_start), instance_rbt). ((List_map Thy_definition_hol o flatten) l, ocl \<lparr> D_oid_start := oid_start, D_instance_rbt := instance_rbt \<rparr>))
    (let (rbt, (map_self, map_username)) = init_map_class ocl l in ((fold_list
      (\<lambda> (f1, f2) _.
        fold_list (\<lambda> ocli cpt.
          let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
            ; isub_name = \<lambda>s. s @@ isub_of_str (Inst_ty ocli) in
          ( Definition (Expr_rewrite (f1 var_oid isub_name ocli) ''='' (f2 ocli isub_name cpt))
          , oidSucInh cpt)) l (D_oid_start ocl))
      (let b = \<lambda>s. Expr_basic [s] in
       [ (\<lambda> var_oid _ _. var_oid,
          \<lambda> _ _ cpt. Expr_oid '''' (oidGetInh cpt))
       , (\<lambda> _ isub_name ocli. b (print_examp_instance_name isub_name (Inst_name ocli)),
          print_examp_instance_app_constr2_notmp_norec (rbt, (map_self, map_username)) ocl)
       , (\<lambda> _ _ ocli. Expr_annot (b (Inst_name ocli)) (Inst_ty ocli),
          \<lambda> ocli isub_name _. Expr_lambda wildcard (Expr_some (Expr_some (b (print_examp_instance_name isub_name (Inst_name ocli)))))) ])
      (D_oid_start ocl)
    , List.fold (\<lambda>ocli instance_rbt.
        let n = Inst_name ocli in
        (n, ocli, case map_username n of Some oid \<Rightarrow> oidGetInh oid) # instance_rbt) l (D_instance_rbt ocl)))))"

definition "print_examp_def_st_assoc rbt map_self map_username l_assoc s_empty =
  (let b = \<lambda>s. Expr_basic [s]
     ; rbt = List.fold
     (\<lambda> (ocli, cpt). fold_instance_single
       (\<lambda> ty l_attr.
         let (f_attr_ty, _) = rbt ty in
         modify_def empty ty
         (List.fold (\<lambda>(name_attr, shall).
           case f_attr_ty name_attr of
             Some (OclTy_object _, _, _) \<Rightarrow>
               modify_def [] name_attr
               (\<lambda>l. case case shall of Shall_str s \<Rightarrow> map_username s | Shall_self s \<Rightarrow> map_self s of
                      None \<Rightarrow> l
                    | Some oid \<Rightarrow> (oidGetInh cpt, oidGetInh oid) # l)
           | _ \<Rightarrow> id) l_attr)) ocli) l_assoc empty in
   [ Expr_apply s_empty
       (fold (\<lambda>name. fold (\<lambda>name_attr l_attr l_cons.
         Expr_binop
           (Expr_basic [print_access_oid_uniq_name (\<lambda>s. s @@ isub_of_str name) name_attr])
           unicode_mapsto
           (list_rec
             (b ''Nil'')
             (\<lambda>(x1, x2) _ xs. Expr_apply ''Cons'' [Expr_apply ''Pair'' (List_map (Expr_oid var_oid_uniq) [x1, x2]), xs])
             l_attr) # l_cons) ) rbt []), b s_empty])"

definition "print_examp_def_st = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 (\<lambda>(l, _). (List_map Thy_definition_hol l, ocl))
  (let ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>
     ; b = \<lambda>s. Expr_basic [s]
     ; (rbt, (map_self, map_username)) =
         init_map_class ocl (List_map (\<lambda> OclDefCoreAdd ocli \<Rightarrow> ocli
                                       | OclDefCoreBinding name \<Rightarrow>
                                           (case List_assoc name (D_instance_rbt ocl) of Some (ocli, _) \<Rightarrow> ocli)
                                       | _ \<Rightarrow> \<lparr> Inst_name = [], Inst_ty = [], Inst_attr = OclAttrNoCast [] \<rparr>) l)
     ; (expr_app, cpt, l_assoc) = fold_list (\<lambda> ocore (cpt, l_assoc).
         let f = \<lambda>ocli exp. ([Expr_binop (Expr_oid var_oid_uniq (oidGetInh cpt)) unicode_mapsto (Expr_apply (datatype_in @@ isub_of_str (Inst_ty ocli)) [exp])], Some ocli)
           ; (def, o_ocli) = case ocore of OclDefCoreSkip \<Rightarrow> ([], None)
                       | OclDefCoreBinding name \<Rightarrow>
                           case List_assoc name (D_instance_rbt ocl) of Some (ocli, cpt_registered) \<Rightarrow>
                           if oidGetInh cpt = cpt_registered then
                             f ocli (b (print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) name))
                           else
                             ([], None) (* TODO
                                   check that all oid appearing in this expression-alias
                                   all appear in this defining state *)
                       | OclDefCoreAdd ocli \<Rightarrow>
                           f ocli (print_examp_instance_app_constr2_notmp_norec (rbt, (map_self, map_username)) ocl ocli (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) cpt) in
         (def, oidSucInh cpt, case o_ocli of None \<Rightarrow> l_assoc | Some ocli \<Rightarrow> (ocli, cpt) # l_assoc)) l (D_oid_start ocl, []) in

   ([ let s_empty = ''Map.empty'' in
      Definition (Expr_rewrite (b name) ''='' (Expr_apply ''state.make''
       ( Expr_apply s_empty (flatten expr_app)
       # (case D_design_analysis ocl of
            Some (Suc 0) \<Rightarrow> print_examp_def_st_assoc rbt map_self map_username l_assoc s_empty
          | _ \<Rightarrow> List_map (\<lambda>_. b s_empty) (List.upt 1 assoc_max))))) ], cpt)))"

definition "print_examp_def_st_defs = (\<lambda> _ \<Rightarrow> start_map Thy_lemmas_simp
  ([ Lemmas_simp '''' [Thm_strs ''state.defs'' 0] ]))"

subsection{* Conclusion *}

definition "section_aux n s = start_map' (\<lambda>_. [ Thy_section_title (Section_title n s) ])"
definition "section = section_aux 0"
definition "subsection = section_aux 1"
definition "subsubsection = section_aux 2"
definition "txt f = start_map'''' Thy_text o (\<lambda>_ design_analysis. [Text (f design_analysis)])"
definition "txt' s = txt (\<lambda>_. s)"
definition "txt'' = txt' o flatten"
definition "txt''d s = txt (\<lambda> None \<Rightarrow> flatten s | _ \<Rightarrow> [])"
definition "txt''a s = txt (\<lambda> Some _ \<Rightarrow> flatten s | _ \<Rightarrow> [])"

definition thy_object ::
  (* polymorphism weakening needed by code_reflect *)
  "(ocl_class
    \<Rightarrow> unit ocl_deep_embed_input_scheme
       \<Rightarrow> hol_thy list \<times>
          unit ocl_deep_embed_input_scheme) list" where "thy_object =
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
            (*, print_astype_from_universe*), print_astype_from_universe'
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
            , print_istypeof_from_universe(*, print_istypeof_from_universe'*)
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
            , print_iskindof_from_universe(*, print_iskindof_from_universe'*)
            , print_iskindof_lemmas_id ]
            , [ print_iskindof_lemma_cp
            , print_iskindof_lemmas_cp ]
            , [ print_iskindof_lemma_strict
            , print_iskindof_lemmas_strict ]
            , [ print_iskindof_defined
            , print_iskindof_defined' ]
            , [ print_iskindof_up_eq_asty
            , print_iskindof_up_larger
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
            , print_allinst_iskindof

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
            , print_examp_def_st_defs ] ])"

definition "thy_object' = [ print_examp_oclint ]"
definition "thy_object'' = [ print_examp_instance ]"
definition "thy_object''' = [ print_examp_def_st ]"

definition "fold_thy0 univ thy_object0 f =
  List.fold (\<lambda>x (acc1, acc2).
    let (l, acc1) = x univ acc1 in
    (acc1, f l acc2)) thy_object0"
definition "fold_thy' f ast =
  (case ast of OclDeepEmbed l \<Rightarrow> List.fold (\<lambda> ast.
    (case ast of
     OclAstClassFlat univ \<Rightarrow> let univ = class_unflat univ in (\<lambda>f ((ocl :: unit ocl_deep_embed_input_scheme), accu).
       fold_thy0 univ thy_object f (ocl \<lparr> D_class_spec := Some univ \<rparr>, accu))
   | OclAstInstance univ \<Rightarrow> fold_thy0 univ thy_object''
   | OclAstDefInt univ \<Rightarrow> fold_thy0 univ thy_object'
   | OclAstDefState univ \<Rightarrow> fold_thy0 univ thy_object''') f) l)"
definition "fold_thy = fold_thy' o List.fold"
definition "fold_thy_deep obj ocl =
  (case fold_thy' (\<lambda>l (i, cpt). (Suc i, List.length l + cpt)) obj (ocl, D_output_position ocl) of
    (ocl, output_position) \<Rightarrow> ocl \<lparr> D_output_position := output_position \<rparr>)"

definition "ocl_deep_embed_input_empty oid_start design_analysis = ocl_deep_embed_input.make True None oid_start (0, 0) design_analysis None []"

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

  let oid oid_rec nat_rec oid =
    oid_rec (nat nat_rec) oid
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
datatype ml_nat = ML_nat
datatype ml_nibble = ML_nibble
datatype ml_char = ML_char
datatype ml_int = ML_int
datatype ml_oid = ML_oid

code_printing type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.int"

subsection{* ML code const *}

text{* ... *}

consts out_file0 :: "((ml_string \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
code_printing constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> unit"
code_printing constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"

text{* module To *}

consts ToString :: "(ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> nibble \<Rightarrow> ml_nibble) \<Rightarrow>
                    ((nibble \<Rightarrow> nibble \<Rightarrow> ml_char) \<Rightarrow> char \<Rightarrow> ml_char) \<Rightarrow>
                    string \<Rightarrow> ml_string"
code_printing constant ToString \<rightharpoonup> (OCaml) "CodeConst.To.string"
definition "To_string = ToString nibble_rec char_rec"

consts ToNat :: "(ml_nat \<Rightarrow> (nat \<Rightarrow> ml_nat \<Rightarrow> ml_nat) \<Rightarrow> nat \<Rightarrow> ml_nat) \<Rightarrow>
                 nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"
definition "To_nat = ToNat nat_rec"

consts ToOid :: "((nat \<Rightarrow> ml_oid) \<Rightarrow> internal_oid \<Rightarrow> ml_oid) \<Rightarrow>
                  (ml_nat \<Rightarrow> (nat \<Rightarrow> ml_nat \<Rightarrow> ml_nat) \<Rightarrow> nat \<Rightarrow> ml_nat) \<Rightarrow>
                 internal_oid \<Rightarrow> ml_int"
code_printing constant ToOid \<rightharpoonup> (OCaml) "CodeConst.To.oid"
definition "To_oid = ToOid internal_oid_rec nat_rec"

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
code_printing constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
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

text{* module List *}

definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "List_mapi f l = (let (l, _) = foldl (\<lambda>(acc, n) x. (f n x # acc, Suc n)) ([], 0) l in rev l)"

text{* module Sys *}

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool"
code_printing constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"

consts Sys_argv :: "ml_string list"
code_printing constant Sys_argv \<rightharpoonup> (OCaml) "CodeConst.Sys.argv"

text{* module Unicode *}

definition "Unicode_mk_u = sprintf1s (STR (Char Nibble5 NibbleC # ''<%s>''))"
definition "Unicode_u_Rightarrow = Unicode_mk_u (STR ''Rightarrow'')"
definition "Unicode_u_Longrightarrow = Unicode_mk_u (STR ''Longrightarrow'')"

subsection{* s of ... *} (* s_of *)

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

fun_quick s_of_rawty where "s_of_rawty rawty = (case rawty of
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (List.map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name))"

definition "s_of_ty_synonym _ = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

fun_quick s_of_expr where "s_of_expr expr = (
  case expr of
    Expr_case e l \<Rightarrow> sprintf2 (STR ''(case %s of %s)'') (s_of_expr e) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l))
  | Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Expr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Expr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (To_string s)
  | Expr_bind symb l e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (String_concat (STR '' '') (List_map To_string l)) (s_of_expr e)
  | Expr_bind0 symb e1 e2 \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') (To_string symb) (s_of_expr e1) (s_of_expr e2)
  | Expr_function l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string unicode_lambda) (String_concat (STR ''
    | '') (List.map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l))
  (*| Expr_apply s [e] \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (s_of_expr e)*)
  | Expr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_applys e l \<Rightarrow> sprintf2 (STR ''((%s) %s)'') (s_of_expr e) (String_concat (STR '' '') (List.map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_postunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_preunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_paren p_left p_right e \<Rightarrow> sprintf3 (STR ''%s%s%s'') (To_string p_left) (s_of_expr e) (To_string p_right))"

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
    sprintf5 (STR ''consts %s :: \"%s %s %s\" (\"(_) %s\")'') (To_string n) (s_of_rawty ty_out1) Unicode_u_Rightarrow (s_of_rawty ty_out2) (To_string symb))"

definition "s_of_definition_hol _ = (\<lambda>
    Definition e \<Rightarrow> sprintf1 (STR ''definition \"%s\"'') (s_of_expr e)
  | Definition_abbrev name (abbrev, prio) e \<Rightarrow> sprintf4 (STR ''definition %s (\"(1%s)\" %d)
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (To_nat prio) (s_of_expr e)
  | Definition_abbrev0 name abbrev e \<Rightarrow> sprintf3 (STR ''definition %s (\"%s\")
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (s_of_expr e))"

fun_quick s_of_ntheorem_aux where "s_of_ntheorem_aux lacc expr =
  (let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l)))
     ; f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l)))
     ; f_symmetric = (STR ''symmetric'', STR '''')
     ; s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
  (\<lambda> Thm_str s \<Rightarrow> To_string s
   | Thm_strs s _ \<Rightarrow> To_string s
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
   | Thm_OF e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc) e1) expr)"

definition "s_of_ntheorem = s_of_ntheorem_aux []"

definition "s_of_lemmas_simp _ = (\<lambda> Lemmas_simp s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map s_of_ntheorem l)))"

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
  | Tac_simp \<Rightarrow> sprintf0 (STR ''simp'')
  | Tac_simp_add l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map To_string l))
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
      (String_concat (sprintf1 (STR '' %s '') Unicode_u_Longrightarrow) (List_map s_of_expr l_spec))
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
      (To_string ((case n of 0 \<Rightarrow> ''''
                     | Suc 0 \<Rightarrow> ''sub''
                     | Suc (Suc _) \<Rightarrow> ''subsub'') @@ ''section''))
      (To_string section_title))"

definition "s_of_text _ = (\<lambda> Text s \<Rightarrow> sprintf1 (STR ''text{* %s *}'') (To_string s))"

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
             | Thy_text text \<Rightarrow> s_of_text ocl text)"

definition "s_of_thy_list ocl l_thy =
  (let (th_beg, th_end) = case D_file_out_path_dep ocl of None \<Rightarrow> ([], [])
   | Some (name, fic_import) \<Rightarrow>
       ( [ sprintf2 (STR ''theory %s imports \"%s\" begin'') (To_string name) (To_string fic_import) ]
       , [ STR '''', STR ''end'' ]) in
  flatten
        [ th_beg
        , flatten (fst (fold_list (\<lambda>l (i, cpt).
            let (l_thy, lg) = fold_list (\<lambda>l n. (s_of_thy ocl l, Suc n)) l 0 in
            (( STR ''''
             # sprintf4 (STR ''%s(* %d ************************************ %d + %d *)'')
                 (To_string (if ocl_deep_embed_input.more ocl then '''' else [char_escape])) (To_nat (Suc i)) (To_nat cpt) (To_nat lg)
             # l_thy), Suc i, cpt + lg)) l_thy (D_output_position ocl)))
        , th_end ])"

subsection{* conclusion *}

definition "write_file ocl = (
  let (is_file, f_output) = case (D_file_out_path_dep ocl, Sys_argv)
     of (Some (file_out, _), _ # dir # _) \<Rightarrow> (True, \<lambda>f. out_file1 f (if Sys_is_directory2 dir then sprintf2 (STR ''%s/%s.thy'') dir (To_string file_out) else dir))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iter (fprintf1 (STR ''%s
''                                 ))
        (s_of_thy_list (ocl_deep_embed_input_more_map (\<lambda>_. is_file) ocl)
          ((rev o snd o fold_thy' Cons (ocl_deep_embed_input.more ocl))
             (ocl_deep_embed_input.truncate ocl, [])))))"

subsection{* Deep (without reflection) *}

definition "Employee_DesignModel_UMLPart =
  OclClassFlat
    [ (''OclAny'', [], None)
    , (''Galaxy'', [(''sound'', OclTy_base ''unit''), (''moving'', OclTy_base ''bool'')], Some ''OclAny'')
    , (''Planet'', [(''weight'', OclTy_base ''nat'')], Some ''Galaxy'')
    , (''Person'', [(''salary'', OclTy_base ''int''), (''boss'', object)], Some ''Planet'') ]
    ''OclAny''"

definition "main = write_file (ocl_deep_embed_input.extend
                                (ocl_deep_embed_input_empty (oidInit (Oid 0)) None
                                   \<lparr> D_disable_thy_output := False
                                   , D_file_out_path_dep := Some (''Employee_DesignModel_UMLPart_generated''
                                                                 ,''../src/OCL_main'') \<rparr>)
                                (OclDeepEmbed [OclAstClassFlat Employee_DesignModel_UMLPart]))"
(*
apply_code_printing ()
export_code main
  in OCaml module_name M
  (no_signatures)
*)
section{* Generation to Shallow Form: SML *}

subsection{* i of ... *} (* i_of *)

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
  (D_instance_rbt ocl)"

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

definition "ap1 a v0 f1 v1 = a v0 (f1 v1)"
definition "ap2 a v0 f1 f2 v1 v2 = a (a v0 (f1 v1)) (f2 v2)"
definition "ap3 a v0 f1 f2 f3 v1 v2 v3 = a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)"
definition "ap4 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)"
definition "ap5 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)"
definition "ap6 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)"
definition "ap7 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 = a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)"
definition "ap8 a v0 f1 f2 f3 f4 f5 f6 f7 f8 v1 v2 v3 v4 v5 v6 v7 v8 = a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7)) (f8 v8)"

definition "ar1 a v0 = a v0"
definition "ar2 a v0 f1 v1 = a (a v0 (f1 v1))"
definition "ar3 a v0 f1 f2 v1 v2 = a (a (a v0 (f1 v1)) (f2 v2))"
definition "ar4 a v0 f1 f2 f3 v1 v2 v3 = a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3))"
definition "ar5 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4))"
definition "ar6 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5))"
definition "ar7 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6))"
definition "ar8 a v0 f1 f2 f3 f4 f5 f6 f7 v1 v2 v3 v4 v5 v6 v7 = a (a (a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)) (f7 v7))"

(* *)

definition "i_of_unit b = unit_rec
  (b ''()'')"

definition "i_of_bool b = bool_rec
  (b ''True'')
  (b ''False'')"

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b ''Pair'') f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b ''Nil'')
  (ar2 a (b ''Cons'') f)"

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

definition "i_of_option a b f = option_rec
  (b ''None'')
  (ap1 a (b ''Some'') f)"

definition "i_of_nat a b = (\<lambda>f0. nat_rec f0 o K)
  (b ''0'')
  (ar1 a (b ''Suc''))"

(* *)

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

definition "i_of_ocl_ty a b = (\<lambda>f1 f2. ocl_ty_rec f1 f2 o co1 K)
  (ap1 a (b ''OclTy_base'') (i_of_string a b))
  (ap1 a (b ''OclTy_object'') (i_of_string a b))
  (ar2 a (b ''OclTy_collection'') (i_of_ocl_collection b))
  (ap1 a (b ''OclTy_base_raw'') (i_of_string a b))"

definition "i_of_ocl_class a b = (\<lambda>f0 f1 f2 f3. ocl_class_rec_1 (co2 K (ar3 a f0 f1 f2)) (f3 None) (K (f3 o Some)))
  (b ''OclClass'')
    (i_of_string a b)
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
    (i_of_option a b id)"

definition "i_of_ocl_class_flat a b = ocl_class_flat_rec
  (ap2 a (b ''OclClassFlat'')
    (i_of_list a b (i_of_pair a b
      (i_of_string a b) (i_of_pair a b
      (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_ty a b)))
      (i_of_option a b (i_of_string a b)))))
    (i_of_string a b))"

definition "i_of_ocl_data_shallow a b = ocl_data_shallow_rec
  (ap1 a (b ''Shall_str'') (i_of_string a b))
  (ap1 a (b ''Shall_self'') (i_of_internal_oid a b))"

definition "i_of_ocl_list_attr a b f = (\<lambda>f0. co4 (\<lambda>f1. ocl_list_attr_rec f0 (\<lambda>s _ a rec. f1 s rec a)) (ap3 a))
  (ap1 a (b ''OclAttrNoCast'') f)
  (b ''OclAttrCast'')
    (i_of_string a b)
    id
    f"

definition "i_of_ocl_instance_single a b f = ocl_instance_single_rec
  (ap4 a (b ''ocl_instance_single_ext'')
    (i_of_string a b)
    (i_of_string a b)
    (i_of_ocl_list_attr a b (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_ocl_data_shallow a b))))
    (f a b))"

definition "i_of_ocl_instance a b = ocl_instance_rec
  (ap1 a (b ''OclInstance'')
    (i_of_list a b (i_of_ocl_instance_single a b (K i_of_unit))))"

definition "i_of_ocl_def_int a b = ocl_def_int_rec
  (ap1 a (b ''OclDefI'') (i_of_list a b (i_of_string a b)))"

definition "i_of_ocl_def_state_core a b = ocl_def_state_core_rec
  (ap1 a (b ''OclDefCoreAdd'') (i_of_ocl_instance_single a b (K i_of_unit)))
  (b ''OclDefCoreSkip'')
  (ap1 a (b ''OclDefCoreBinding'') (i_of_string a b))"

definition "i_of_ocl_def_state a b = ocl_def_state_rec
  (ap2 a (b ''OclDefSt'') (i_of_string a b) (i_of_list a b (i_of_ocl_def_state_core a b)))"

definition "i_of_ocl_deep_embed_ast0 a b = ocl_deep_embed_ast0_rec
  (ap1 a (b ''OclAstClassFlat'') (i_of_ocl_class_flat a b))
  (ap1 a (b ''OclAstInstance'') (i_of_ocl_instance a b))
  (ap1 a (b ''OclAstDefInt'') (i_of_ocl_def_int a b))
  (ap1 a (b ''OclAstDefState'') (i_of_ocl_def_state a b))"

definition "i_of_ocl_deep_embed_ast a b = ocl_deep_embed_ast_rec
  (ap1 a (b ''OclDeepEmbed'') (i_of_list a b (i_of_ocl_deep_embed_ast0 a b)))"

definition "i_of_ocl_deep_embed_input a b f = ocl_deep_embed_input_rec
  (ap8 a (b ''ocl_deep_embed_input_ext'')
    (i_of_bool b)
    (i_of_option a b (i_of_pair a b (i_of_string a b) (i_of_string a b)))
    (i_of_internal_oids a b)
    (i_of_pair a b (i_of_nat a b) (i_of_nat a b))
    (i_of_option a b (i_of_nat a b))
    (i_of_option a b (i_of_ocl_class a b))
    (i_of_list a b (i_of_pair a b (i_of_string a b) (i_of_pair a b (i_of_ocl_instance_single a b (K i_of_unit)) (i_of_internal_oid a b))))
    (f a b))"

(* *)

definition "i_apply l1 l2 = flatten [l1, '' ('', l2, '')'']"

(* *)

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

lemma [code]: "ocl_deep_embed_input.extend = (\<lambda>ocl v. ocl_deep_embed_input_rec0 (co7 (\<lambda>f. f v) ocl_deep_embed_input_ext) ocl)"
by(intro ext, simp add: ocl_deep_embed_input_rec0_def
                        ocl_deep_embed_input.extend_def
                        co7_def K_def)
lemma [code]: "ocl_deep_embed_input.make = co7 (\<lambda>f. f ()) ocl_deep_embed_input_ext"
by(intro ext, simp add: ocl_deep_embed_input.make_def
                        co7_def)
lemma [code]: "ocl_deep_embed_input.truncate = ocl_deep_embed_input_rec (co7 K ocl_deep_embed_input.make)"
by(intro ext, simp add: ocl_deep_embed_input_rec0_def
                        ocl_deep_embed_input_rec_def
                        ocl_deep_embed_input.truncate_def
                        ocl_deep_embed_input.make_def
                        co7_def K_def)

subsection{* global *}

code_reflect OCL
   functions nibble_rec char_rec
             char_escape
             fold_thy fold_thy_deep
             ocl_deep_embed_input_empty ocl_deep_embed_input_more_map ocl_deep_embed_ast_map oidInit
             D_file_out_path_dep_update
             i_apply i_of_ocl_deep_embed_input i_of_ocl_deep_embed_ast

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
                    , name : binding }

structure Data = Theory_Data
  (type T = class_inline list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

structure From = struct
 open OCL
 val from_nibble = fn
       0x0 => Nibble0 | 0x1 => Nibble1 | 0x2 => Nibble2 | 0x3 => Nibble3 | 0x4 => Nibble4 | 0x5 => Nibble5 |
        0x6 => Nibble6 | 0x7 => Nibble7 | 0x8 => Nibble8 | 0x9 => Nibble9 | 0xA => NibbleA | 0xB => NibbleB | 0xC => NibbleC | 0xD => NibbleD
       | 0xE => NibbleE | 0xF => NibbleF
 fun from_char c = let val c = Char.ord c in OCL.Char (from_nibble (c div 16), from_nibble (c mod 16)) end
 fun from_string n = List.map from_char (String.explode n)
 val from_binding = from_string o Binding.name_of
 fun from_term ctxt s = from_string (XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt s)))
 val from_nat =
   let fun from_nat accu = fn 0 => accu | x => from_nat (Suc accu) (x - 1) in
   from_nat Zero_nat
   end
 val from_internal_oid = Oid
 val from_bool = I
 val from_unit = I
 val from_option = Option.map
 val from_list = List.map
 fun from_pair f1 f2 (x, y) = (f1 x, f2 y)

 val mk_univ =
   map (fn { attr_base = attr_base, attr_object = attr_object, child = child, name = name } =>
     ( from_binding name
     , ( List.concat [ List.map (fn (b, ty) => (from_binding b, OclTy_base (from_binding ty))) attr_base
                     , List.map (fn b => (from_binding b, object)) attr_object]
       , case child of [] => NONE | [x] => SOME (from_binding x))))
end

val class_empty = ""

val () =
  Outer_Syntax.command @{command_spec "Class"} "Class definition"
    (((Parse.binding --| Parse.$$$ "=") --
      Scan.repeat (@{keyword "inherit"} |-- Parse.!!! Parse.binding) --
      Scan.repeat (@{keyword "attribute"} |-- Parse.!!! (Parse.binding -- Scan.optional (Parse.$$$ ":" |-- Parse.!!! Parse.binding >> SOME) NONE)))
        >> (fn ((binding, child), attribute) =>
            let val (attr_base, attr_object) = fold (fn (b, o_b) => fn (attr_base, attr_object) => case o_b of NONE => (attr_base, b :: attr_object) | SOME bb => ((b, bb) :: attr_base, attr_object)) attribute ([], [])
                val (attr_base, attr_object) = (rev attr_base, rev attr_object) in
            fn x =>
              x |> Toplevel.theory (fn thy => thy |> Data.map (fn t =>
                                                     Symtab.map_default (class_empty, []) (fn l => { attr_base = attr_base
                                                                                                   , attr_object = attr_object
                                                                                                   , child = child
                                                                                                   , name = binding } :: l) t))
            end))
*}

ML{*
fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global
*}

subsection{* Deep (with reflection) *}

ML{*
structure Deep = struct

fun prep_destination "" = NONE
  | prep_destination "-" = (legacy_feature "drop \"file\" argument entirely instead of \"-\""; NONE)
  | prep_destination s = SOME (Path.explode s)

fun produce_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs in
    map (fn (((target, module_name), some_path), args) =>
      (some_path, Code_Target.produce_code_for thy (*some_path*) target NONE module_name args naming program names_cs)) seris
  end

fun absolute_path filename thy = Path.implode (Path.append (Thy_Load.master_directory thy) (Path.explode filename))

fun export_code_cmd_gen with_tmp_file bash_output f_err raw_cs filename_thy thy =
  with_tmp_file (fn seris =>
    let val _ = Code_Target.export_code
                  thy
                  (Code_Target.read_const_exprs thy raw_cs)
                  ((map o apfst o apsnd) prep_destination (map fst seris))
        val (out, err) = bash_output (snd (hd seris)) (case filename_thy of NONE => ""
                                                                          | SOME filename_thy => " " ^ absolute_path filename_thy thy)
        val _ = f_err (snd (hd seris)) err in
    out end)

fun export_code_cmd' raw_cs seris filename_thy f f_err thy =
  export_code_cmd_gen
    (case seris of
        [] =>
        (fn f =>
          Isabelle_System.with_tmp_file "OCL_class_diagram_generator" "ml" (fn filename =>
          let val filename = Path.implode filename in
          (* export_code
               in OCaml module_name M (* file "" *) *)
          f [(((("OCaml", "M"), filename), []), filename)]
          end))
      | _ =>
        (fn f => f (map (fn x => (x, case x of (((_, _), filename), _) => absolute_path filename thy)) seris)))
    f
    f_err
    raw_cs filename_thy thy

fun msg_err msg err = if err <> 0 then error msg else ()

fun export_code_cmd raw_cs seris filename_thy =
  export_code_cmd' raw_cs seris filename_thy
    (fn tmp_file => fn arg => Isabelle_System.bash_output ("ocaml -w '-8' " ^ tmp_file ^ arg))
    msg_err

fun mk_term ctxt s = fst (Scan.pass (Context.Proof ctxt) Args.term (Outer_Syntax.scan Position.none s))

fun mk_free ctxt s l =
  let val t_s = mk_term ctxt s in
  if Term.is_Free t_s then s else
    let val l = (s, "") :: l in
    mk_free ctxt (fst (hd (Term.variant_frees t_s l))) l
    end
  end

end
*}

subsection{* ... *}

ML{*
fun parse_l f = Parse.$$$ "[" |-- Parse.!!! (Parse.list f --| Parse.$$$ "]")
fun parse_l' f = Parse.$$$ "[" |-- Parse.list f --| Parse.$$$ "]"
fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
*}

ML{*
structure Generation_mode = struct
datatype generation_mode = Gen_deep of unit OCL.ocl_deep_embed_input_ext
                                     * (((bstring * bstring) * bstring) * Token.T list) list (* seri_args *)
                                     * bstring option (* filename_thy *)
                                     * Path.T (* tmp dir export_code *)
                                     * (unit OCL.ocl_deep_embed_input_ext * OCL.ocl_deep_embed_ast) (* environment of commands entered *)
                         | Gen_shallow of unit OCL.ocl_deep_embed_input_ext
                         | Gen_syntax_print

structure Data_gen = Theory_Data
  (type T = generation_mode list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Args.parse --| @{keyword ")"}) []

val parse_scheme = @{keyword "design"} >> K NONE || @{keyword "analysis"} >> K (SOME 1)

val parse_deep =
     Scan.optional (((Parse.$$$ "(" -- @{keyword "THEORY"}) |-- Parse.name -- ((Parse.$$$ ")" -- Parse.$$$ "(" -- @{keyword "IMPORTS"}) |-- Parse.name) --| Parse.$$$ ")") >> SOME) NONE
  -- Scan.optional (@{keyword "SECTION"} >> K true) false
  -- (* code_expr_inP *) Scan.repeat (@{keyword "in"} |-- Parse.!!! (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- Scan.optional (@{keyword "file"} |-- Parse.name) ""
        -- code_expr_argsP))
  -- Scan.optional ((Parse.$$$ "(" -- @{keyword "output_directory"}) |-- Parse.name --| Parse.$$$ ")" >> SOME) NONE

val parse_sem_ocl =
      (Parse.$$$ "(" -- @{keyword "generation_semantics"} -- Parse.$$$ "[")
  |-- parse_scheme -- Scan.optional ((Parse.$$$ "," -- @{keyword "oid_start"}) |-- Parse.nat) 0
  --| (Parse.$$$ "]" -- Parse.$$$ ")")

val mode =
     @{keyword "deep"} |-- parse_sem_ocl -- parse_deep >> (fn ((design_analysis, oid_start), (((file_out_path_dep, disable_thy_output), seri_args), filename_thy)) =>
       let val _ = case (seri_args, filename_thy, file_out_path_dep) of
            ([_], _, NONE) => warning ("Unknown filename, generating to stdout and ignoring " ^ (@{make_string} seri_args))
          | (_, SOME t, NONE) => warning ("Unknown filename, generating to stdout and ignoring " ^ (@{make_string} t))
          | _ => ()
           val ocl = OCL.Ocl_deep_embed_input_ext
                  ( From.from_bool (not disable_thy_output)
                  , From.from_option (From.from_pair From.from_string From.from_string) file_out_path_dep
                  , OCL.oidInit (From.from_internal_oid (From.from_nat oid_start))
                  , From.from_pair From.from_nat From.from_nat (0, 0)
                  , From.from_option From.from_nat design_analysis
                  , From.from_option I NONE
                  , From.from_list I []
                  , () ) in
       Gen_deep (ocl, seri_args, filename_thy, Isabelle_System.create_tmp_path "deep_export_code" ""
                  , (ocl, OCL.OclDeepEmbed [])) end)
  || @{keyword "shallow"} |-- parse_sem_ocl >> (fn (design_analysis, oid_start) =>
       Gen_shallow
         (OCL.ocl_deep_embed_input_empty
           (OCL.oidInit (From.from_internal_oid (From.from_nat oid_start)))
           (From.from_option From.from_nat design_analysis)))
  || @{keyword "syntax_print"} >> K Gen_syntax_print

val gen_empty = ""
val ocamlfile_function = "function.ml"
val ocamlfile_argument = "argument.ml"
val ocamlfile_main = "main.ml"
val ocamlfile_ocp = "write"
val argument_main = "main"

fun f_command l_mode =
      Toplevel.theory (fn thy =>
        let val (l_mode, thy) = OCL.fold_list
          (fn Gen_shallow ocl => (fn thy => (Gen_shallow ocl, thy))
            | Gen_syntax_print => (fn thy => (Gen_syntax_print, thy))
            | Gen_deep (ocl, seri_args, filename_thy, tmp_export_code, l_ast) => fn thy =>
                let fun mk_fic s = Path.append tmp_export_code (Path.make [s])
                    val _ = warning ("remove the directory (at the end): " ^ Path.implode tmp_export_code)
                    val () = Isabelle_System.mkdir tmp_export_code
                    val _ = Deep.export_code_cmd_gen
                              (fn f => let val filename = Path.implode (mk_fic ocamlfile_function) in
                                f [(((("OCaml", "M"), filename), []), filename)] end)
                              (fn _ => fn _ => ("", ()))
                              (fn _ => fn _ => ())
                              ["write_file"] filename_thy (Code_printing.apply_code_printing thy)
                    val () = File.write (mk_fic (ocamlfile_ocp ^ ".ocp"))
                              (String.concat [ "comp += \"-g\" link += \"-g\" begin program \"", ocamlfile_ocp, "\" sort = true files = [ \"", ocamlfile_function
                                             , "\" \"", ocamlfile_argument
                                             , "\" \"", ocamlfile_main
                                             , "\" ] end" ])
                    val () = File.write (mk_fic ocamlfile_main) ("let _ = Function.M.write_file (Obj.magic (Argument.M." ^
                      Deep.mk_free (Proof_Context.init_global thy) argument_main [] ^ "))") in
                (Gen_deep (ocl, seri_args, filename_thy, tmp_export_code, l_ast), thy) end) l_mode thy in
        Data_gen.map (Symtab.map_default (gen_empty, l_mode) (fn _ => l_mode)) thy
        end)
end
*}

subsection{* Shallow *}

ML{*
structure Shallow_conv = struct
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
val Unicode_u_Longrightarrow = Unicode_mk_u (STR "Longrightarrow")

fun s_of_expr expr = let open OCL in
  case expr of
    Expr_case (e, l) => let val s1 =
 (s_of_expr e)
val s2 = (String.concatWith (STR "\n    | ") (List.map (fn (s1, s2) => String.concatWith (STR " ")
 [(s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) in
(STR "(case " ^ s1 ^ " of " ^ s2 ^ ")") end
  | Expr_rewrite (e1, symb, e2) => String.concatWith (STR " ") [(s_of_expr e1), (To_string symb), (s_of_expr e2)]
  | Expr_basic l =>  (String.concatWith (STR " ") (List.map To_string l))
  | Expr_oid (tit, s) => To_string tit ^ Int.toString (case s of Oid s => To_nat s)
  | Expr_binop (e1, s, e2) => String.concatWith (STR " ") [(s_of_expr e1), (s_of_expr (Expr_basic [s])), (s_of_expr e2)]
  | Expr_annot (e, s) => (STR "(" ^ (s_of_expr e)  ^ "::" ^ (To_string s) ^ ")")
  | Expr_bind (symb, l, e) => (STR "(" ^ To_string symb ^ "" ^ (String.concatWith (STR " ") (List.map To_string l)) ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_bind0 (symb, e1, e2) => (STR "(" ^ To_string symb ^ "" ^ (s_of_expr e1) ^ ". " ^ (s_of_expr e2) ^ ")")
  | Expr_function l =>  (STR "(" ^ (To_string unicode_lambda)  ^ " " ^ (String.concatWith (STR "\n    | ") (List.map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1),Unicode_u_Rightarrow, (s_of_expr s2)]) l)) ^ ")")
  (*| Expr_apply s [e] => sprintf2 (STR "(" ^ s ^ " " ^ s ^ ")") (To_string s) (s_of_expr e)*)
  | Expr_apply (s, l) =>  let val s1 = (To_string s) val s2 = (String.concatWith (STR " ") (List.map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
(STR "(" ^ s1 ^ " " ^ s2 ^ ")") end
  | Expr_applys (e, l) => let val s1 = (s_of_expr e) val s2 = (String.concatWith (STR " ") (List.map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
 (STR "((" ^ s1 ^ ") " ^ s2 ^ ")") end
  | Expr_postunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_preunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_paren (p_left, p_right, e) => (STR ((To_string p_left) ^ (s_of_expr e) ^ (To_string p_right)))
end

fun simp_tac f = Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac (f ctxt) 1))

fun m_of_ntheorem ctxt s = let open OCL in case s of
    Thm_str s => Proof_Context.get_thm ctxt (To_string s)
  | Thm_strs (s, n) => List.nth (Proof_Context.get_thms ctxt (To_string s), To_nat n)
  | Thm_THEN (e1, e2) => m_of_ntheorem ctxt e1 RSN (1, m_of_ntheorem ctxt e2)
  | Thm_simplified (e1, e2) => asm_full_simplify (clear_simpset ctxt addsimps [m_of_ntheorem ctxt e2]) (m_of_ntheorem ctxt e1)
  | Thm_OF (e1, e2) => [m_of_ntheorem ctxt e2] MRS m_of_ntheorem ctxt e1
  | Thm_where (nth, l) => read_instantiate ctxt (List.map (fn (var, expr) => ((To_string var, 0), s_of_expr expr)) l) (m_of_ntheorem ctxt nth)
  | Thm_symmetric s => m_of_ntheorem ctxt (Thm_THEN (s, Thm_str (From.from_string "sym")))
  | Thm_of (nth, l) =>
      let val thm = m_of_ntheorem ctxt nth
          fun zip_vars _ [] = []
            | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
            | zip_vars ((x, _) :: xs) (SOME t :: rest) = (x, t) :: zip_vars xs rest
            | zip_vars [] _ = error "More instantiations than variables in theorem" in
      read_instantiate ctxt (List.map (fn (v, expr) => (v, s_of_expr expr))
                                 (zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) []))
                                           (List.map SOME l))) thm
      end
end

fun m_of_tactic expr = let val f_fold = fold open OCL open Method in case expr of
    Tac_rule s => Basic (fn ctxt => rule [m_of_ntheorem ctxt s])
  | Tac_drule s => Basic (fn ctxt => drule 0 [m_of_ntheorem ctxt s])
  | Tac_erule s => Basic (fn ctxt => erule 0 [m_of_ntheorem ctxt s])
  | Tac_elim s => Basic (fn ctxt => elim [m_of_ntheorem ctxt s])
  | Tac_intro l => Basic (fn ctxt => intro (map (m_of_ntheorem ctxt) l))
  | Tac_subst_l (l, s) => Basic (fn ctxt => SIMPLE_METHOD' (EqSubst.eqsubst_tac ctxt (map (fn s => case Int.fromString (To_string s) of SOME i => i) l) [m_of_ntheorem ctxt s]))
  | Tac_insert l => Basic (fn ctxt => insert (List.map (m_of_ntheorem ctxt) l))
  | Tac_plus t => Repeat1 (Then (List.map m_of_tactic t))
  | Tac_simp => simp_tac I
  | Tac_simp_add l => simp_tac (fn ctxt => ctxt addsimps (List.map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_add_del (l_add, l_del) => simp_tac (fn ctxt => ctxt addsimps (List.map (Proof_Context.get_thm ctxt o To_string) l_add)
                                                                 delsimps (List.map (Proof_Context.get_thm ctxt o To_string) l_del))
  | Tac_simp_only l => simp_tac (fn ctxt => clear_simpset ctxt addsimps (List.map (m_of_ntheorem ctxt) l))
  | Tac_simp_all => m_of_tactic (Tac_plus [Tac_simp])
  | Tac_simp_all_add s => m_of_tactic (Tac_plus [Tac_simp_add [s]])
  | Tac_auto_simp_add l => Basic (fn ctxt => SIMPLE_METHOD (auto_tac (ctxt addsimps (List.map (Proof_Context.get_thm ctxt o To_string) l))))
  | Tac_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (f_fold (fn (f, l) => f_fold f l)
              [(Simplifier.add_simp, List.map (m_of_ntheorem ctxt) l_simp)
              ,(Splitter.add_split, List.map (Proof_Context.get_thm ctxt o To_string) l_split)]
              ctxt)))
  | Tac_rename_tac l => Basic (K (SIMPLE_METHOD' (rename_tac (List.map To_string l))))
  | Tac_case_tac e => Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (s_of_expr e)))
end

end

structure Shallow_ml = struct open Shallow_conv
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

fun local_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.local_done_proof
 | Tacl_sorry => Proof.local_skip_proof true
 | Tacl_by l_apply => Proof.local_terminal_proof (s_of_tactic l_apply, NONE)
end

fun global_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.global_done_proof
 | Tacl_sorry => Proof.global_skip_proof true
 | Tacl_by l_apply => Proof.global_terminal_proof (s_of_tactic l_apply, NONE)
end

fun proof_show f st = st
  |> Proof.enter_forward
  |> f
  |> Isar_Cmd.show [((@{binding ""}, []), [("?thesis", [])])] true

val apply_results = fn OCL.App l => (fn st => st |> (Proof.apply_results (s_of_tactic l)) |> Seq.the_result "")
                     | OCL.App_using l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.using [map (fn s => ([m_of_ntheorem ctxt s], [])) l] st
                         end)
                     | OCL.App_unfolding l => (fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.unfolding [map (fn s => ([m_of_ntheorem ctxt s], [])) l] st
                         end)
                     | OCL.App_let (e1, e2) => proof_show (Proof.let_bind_cmd [([s_of_expr e1], s_of_expr e2)])
                     | OCL.App_have (n, e, e_pr) => proof_show (fn st => st
                         |> Isar_Cmd.have [((To_sbinding n, []), [(s_of_expr e, [])])] true
                         |> local_terminal_proof e_pr)
                     | OCL.App_fix l => proof_show (Proof.fix_cmd (List.map (fn i => (To_sbinding i, NONE, NoSyn)) l))

end

structure Shallow_main = struct open Shallow_conv open Shallow_ml
val OCL_main = let val f_fold = fold open OCL in (*let val f = *)fn
  Thy_dataty (Datatype (n, l)) =>
    (snd oo Datatype.add_datatype_cmd Datatype_Aux.default_config)
      [((To_sbinding n, [], NoSyn),
       List.map (fn (n, l) => (To_sbinding n, List.map (fn OCL.Opt o_ => To_string o_ ^ " option"
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
| Thy_consts_class (Consts_raw (n, ty_out1, ty_out2, symb)) =>
    Sign.add_consts [( To_sbinding n
                     , String.concatWith " " [ (s_of_rawty ty_out1), Unicode_u_Rightarrow, (s_of_rawty ty_out2) ]
                     , Mixfix ("(_) " ^ To_string symb, [], 1000))]
| Thy_definition_hol def =>
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_abbrev (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e)
      | Definition_abbrev0 (name, abbrev, e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(" ^ s_of_expr abbrev ^ ")", [], 1000)), e) in
    in_local (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Thy_lemmas_simp (Lemmas_simp (s, l)) =>
    in_local (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, List.map (Attrib.intern_src (Proof_Context.theory_of lthy))
                          [Args.src (("simp", []), Position.none), Args.src (("code_unfold", []), Position.none)]),
        List.map (fn x => ([m_of_ntheorem lthy x], [])) l)]
      []
      false) lthy)
| Thy_lemma_by (Lemma_by (n, l_spec, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, [])
                                                       ,[((String.concatWith (STR " " ^ Unicode_u_Longrightarrow ^ " ")
                                                             (List.map s_of_expr l_spec)), [])])])
             false lthy
        |> f_fold (apply_results o OCL.App) l_apply
        |> global_terminal_proof o_by)
| Thy_lemma_by (Lemma_by_assum (n, l_spec, concl, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (To_sbinding n, [])
             []
             (List.map (fn (n, (b, e)) => Element.Assumes [((To_sbinding n, if b then [Args.src (("simp", []), Position.none)] else []), [(s_of_expr e, [])])]) l_spec)
             (Element.Shows [((@{binding ""}, []),[(s_of_expr concl, [])])])
             false lthy
        |> f_fold apply_results l_apply
        |> (case filter (fn OCL.App_let _ => true | OCL.App_have _ => true | OCL.App_fix _ => true | _ => false) l_apply of
              [] => global_terminal_proof o_by
            | _ :: l => let val arg = (NONE, true) in fn st => st
              |> local_terminal_proof o_by
              |> f_fold (K (Proof.local_qed arg)) l
              |> Proof.global_qed arg end))
| Thy_section_title _ => I
| Thy_text _ => I
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end
end
(*val _ = print_depth 100*)
*}

subsection{* ... *}

ML{*

fun exec_deep (ocl, seri_args, filename_thy, tmp_export_code, l_obj) thy0 =
  let open Generation_mode in
  let val i_of_arg =
    let val a = OCL.i_apply
      ; val b = I in
    OCL.i_of_ocl_deep_embed_input a b OCL.i_of_ocl_deep_embed_ast
    end in
              let fun def s = in_local (snd o Specification.definition_cmd (NONE, ((@{binding ""}, []), s)) false) in
                let val name_main = Deep.mk_free (Proof_Context.init_global thy0) argument_main [] in
                thy0 |> def (String.concatWith " " (  name_main
                                                  :: "="
                                                  :: To_string (i_of_arg (OCL.ocl_deep_embed_input_more_map (fn () => l_obj) ocl))
                                                  :: []))
                     |> Deep.export_code_cmd' [name_main] seri_args filename_thy (fn tmp_file => fn arg =>
                          let val out = Isabelle_System.bash_output
                                        ("cp " ^ tmp_file ^ " " ^ Path.implode (Path.append tmp_export_code (Path.make [ocamlfile_argument])) ^
                                         " && cd " ^ Path.implode tmp_export_code ^
                                         " && bash -c 'ocp-build -init -scan -no-bytecode 2>&1' 2>&1 > /dev/null" ^
                                         " && ./_obuild/" ^ ocamlfile_ocp ^ "/" ^ ocamlfile_ocp ^ ".asm " ^ arg) in
                          out end)
                          Deep.msg_err

end end end end

fun outer_syntax_command mk_string cmd_spec cmd_descr parser get_oclclass =
  let open Generation_mode in
  Outer_Syntax.command cmd_spec cmd_descr
    (parser >> (fn name =>
      Toplevel.theory (fn thy =>
        let val (ocl, thy) =
        OCL.fold_list

          let val get_oclclass = get_oclclass name in
          fn Gen_syntax_print => (fn thy => let val _ = writeln (mk_string name) in (Gen_syntax_print, thy) end)
           | Gen_deep (ocl, seri_args, filename_thy, tmp_export_code, (ocl_init, l_ast)) =>
              (fn thy0 =>
                let val obj = get_oclclass thy0
                  ; val l_obj = OCL.OclDeepEmbed [obj] in
                thy0 |> exec_deep (OCL.d_file_out_path_dep_update (fn _ => NONE) ocl, seri_args, NONE, tmp_export_code, l_obj)
                     |> (fn s =>
                          let val _ = writeln
                                (case seri_args of [] =>
                                  String.concat (map ((fn s => s ^ "\n") o Active.sendback_markup [Markup.padding_command] o trim_line)
                                    (String.tokens (fn c => From.from_char c = OCL.char_escape) s))
                                | _ => s) in
                          (Gen_deep (OCL.fold_thy_deep l_obj ocl, seri_args, filename_thy, tmp_export_code, (ocl_init, OCL.ocl_deep_embed_ast_map (fn l => obj :: l) l_ast)), thy0) end)
                end)
           | Gen_shallow ocl => fn thy =>
             let val (ocl, thy) = OCL.fold_thy Shallow_main.OCL_main (OCL.OclDeepEmbed [get_oclclass thy]) (ocl, thy) in
             (Gen_shallow ocl, thy)
             end
          end

          (case Symtab.lookup (Data_gen.get thy) gen_empty of SOME l => l | _ => [Gen_syntax_print])
          thy
        in
        Data_gen.map (Symtab.update (gen_empty, ocl)) thy end)))
end
*}

subsection{* ... *}

ML{*
val () = let open Generation_mode in
  Outer_Syntax.command @{command_spec "generation_syntax"} "set the generating list"
    ((   parse_l' mode >> SOME
     || @{keyword "deep"} -- @{keyword "flush_all"} >> K NONE) >>
    (fn SOME x => f_command x
      | NONE =>
      Toplevel.theory (fn thy =>
        let val l = case Symtab.lookup (Data_gen.get thy) gen_empty of SOME l => l | _ => []
            val l = List.concat (List.map (fn Gen_deep x => [x] | _ => []) l)
            val _ = case l of [] => warning "Nothing to perform." | _ => ()
            val thy =
        fold
          (fn (_, seri_args, filename_thy, tmp_export_code, (ocl_init, l_ast)) => fn thy0 =>
                thy0 |> exec_deep (ocl_init, seri_args, filename_thy, tmp_export_code, OCL.ocl_deep_embed_ast_map rev l_ast)
                     |> (fn s =>
                          let val _ = writeln
                                (case seri_args of [] =>
                                  String.concat (map ((fn s => s ^ "\n") o Active.sendback_markup [Markup.padding_command] o trim_line)
                                    (String.tokens (fn c => From.from_char c = OCL.char_escape) s))
                                | _ => s) in
                          thy0 end))
          l
          thy
        in
        thy end)))
end
*}

subsection{* Outer Syntax: Class.end *}

ML{*
val () =
  outer_syntax_command @{make_string} @{command_spec "Class.end"} "Class generation"
    Parse.binding
    (fn name => fn thy =>
       let val SOME l = Symtab.lookup (Data.get thy) class_empty in
       OCL.OclAstClassFlat (OCL.OclClassFlat (From.mk_univ l, From.from_binding name)) end)
*}

subsection{* Outer Syntax: Instance *}

ML{*

datatype ocl_term = OclTerm of binding
                  | OclOid of int
(*
datatype 'a ocl_l_attr = Ocl_l_attr of 'a
                    | Ocl_l_attr_cast of 'a ocl_prop * binding

and 'a ocl_prop = Ocl_prop of 'a ocl_l_attr (* l_inh *) * 'a (* l_attr *)

datatype ocl_prop_main = Ocl_prop_main of ((binding * ocl_term) list) ocl_prop
*)

val list_attr0 = Parse.binding -- (Parse.$$$ "=" |--
  (Parse.binding >> OclTerm
  || @{keyword "self"} |-- Parse.nat >> OclOid))
val list_attr00 = parse_l list_attr0
val list_attr = list_attr00 >> (fn res => (res, NONE : binding option))
val list_attr_cast00 = annot_ty list_attr00
val list_attr_cast = list_attr_cast00 >> (fn (res, ty) => (res, SOME ty))

val () =
  outer_syntax_command @{make_string} @{command_spec "Define_int"} ""
    (parse_l' Parse.number)
    (fn l_int => fn _ =>
      OCL.OclAstDefInt (OCL.OclDefI (map From.from_string l_int)))

datatype state_content = ST_l_attr of (binding * ocl_term) list * binding (* ty *)
                       | ST_skip
                       | ST_binding of binding

val state_parse =
  (@{keyword "defines"} |-- parse_l' (list_attr_cast00 >> ST_l_attr
                                     || Parse.binding >> ST_binding))
  || @{keyword "skip"} >> K [ST_skip]

local
  fun get_oclinst l _ =
    OCL.OclInstance (map (fn ((name,typ), (l_attr, is_cast)) =>
        let val f = map (fn (attr, ocl) => (From.from_binding attr,
                      case ocl of OclTerm s => OCL.Shall_str (From.from_binding s)
                                | OclOid n => OCL.Shall_self (From.from_internal_oid (From.from_nat n))))
            val l_attr = case is_cast of NONE => OCL.OclAttrNoCast (f l_attr)
                                       | SOME b => OCL.OclAttrCast (From.from_binding b, OCL.OclAttrNoCast (f l_attr), []) in
        OCL.Ocl_instance_single_ext
          (From.from_binding name, From.from_binding typ, l_attr, From.from_unit ()) end) l)
in
val () =
  outer_syntax_command @{make_string} @{command_spec "Instance"} ""
    (Parse.and_list1 (Parse.binding --| @{keyword "::"}
                      -- Parse.binding --| @{keyword "="}
                      -- (list_attr || list_attr_cast)))
    (OCL.OclAstInstance oo get_oclinst)

val () =
  outer_syntax_command @{make_string} @{command_spec "Define_state"} ""
    (Parse.binding --| @{keyword "="}
     -- parse_l' state_parse)
     (fn (name, l) => fn thy =>
      OCL.OclAstDefState (OCL.OclDefSt (From.from_binding name,
        map (fn ST_l_attr (l, ty) => OCL.OclDefCoreAdd (case get_oclinst [((@{binding ""}, ty), (l, NONE))] thy of OCL.OclInstance [x] => x)
              | ST_skip => OCL.OclDefCoreSkip
              | ST_binding b => OCL.OclDefCoreBinding (From.from_binding b)) (List.concat l))))
end

(*val _ = print_depth 100*)
*}

end
