(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_access.thy ---
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

theory  OCL_compiler_floor1_access
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* accessors *}

definition "print_access_oid_uniq_gen Thy_def D_oid_start_upd def_rewrite =
  (\<lambda>expr ocl.
      (\<lambda>(l, oid_start). (List_map Thy_def l, D_oid_start_upd ocl oid_start))
      (let (l, (acc, _)) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inh) in
         let (l, cpt) = fold_list (fold_list
           (\<lambda> (attr, OclTy_class ty_obj) \<Rightarrow> (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l obj_oid = TyObj_ass_id ty_obj
                                               ; obj_name_from_nat = TyObjN_ass_switch (TyObj_from ty_obj) in \<lambda>(cpt, rbt) \<Rightarrow>
             let (cpt_obj, cpt_rbt) =
               case RBT.lookup rbt obj_oid of
                 None \<Rightarrow> (cpt, oidSucAssoc cpt, RBT.insert obj_oid cpt rbt)
               | Some cpt_obj \<Rightarrow> (cpt_obj, cpt, rbt) in
             ( [def_rewrite obj_name_from_nat name isub_name attr (oidGetAssoc cpt_obj)]
             , cpt_rbt))
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (List_flatten (List_flatten l), cpt)) (D_oid_start ocl, RBT.empty) expr in
       (List_flatten l, acc)))"
definition "print_access_oid_uniq_ml =
  print_access_oid_uniq_gen
    Thy_ml
    (\<lambda>x _. x)
    (\<lambda>obj_name_from_nat name _ attr cpt_obj.
      Ml (Sexpr_rewrite_val
                   (Sexpr_basic [print_access_oid_uniq_mlname obj_name_from_nat name attr])
                   \<open>=\<close>
                   (Sexpr_oid \<open>\<close> cpt_obj)))"
definition "print_access_oid_uniq =
  print_access_oid_uniq_gen
    Thy_definition_hol
    (\<lambda>ocl oid_start. ocl \<lparr> D_oid_start := oid_start \<rparr>)
    (\<lambda>obj_name_from_nat _ isub_name attr cpt_obj.
      Definition (Expr_rewrite
                   (Expr_basic [print_access_oid_uniq_name obj_name_from_nat isub_name attr])
                   \<open>=\<close>
                   (Expr_oid \<open>\<close> cpt_obj)))"

definition "print_access_eval_extract _ = start_map Thy_definition_hol
  (let lets = \<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) \<open>=\<close> def)
     ; a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s] in
  [ let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<open>x\<close>
      ; var_f = \<open>f\<close>
      ; some_some = (\<lambda>x. Expr_some (Expr_some x))
      ; var_obj = \<open>obj\<close> in
    Definition (Expr_rewrite
                  (Expr_basic [var_eval_extract, var_x, var_f])
                  \<open>=\<close>
                  (Expr_lam unicode_tau
                     (\<lambda>var_tau. Expr_case (Expr_basic [var_x, var_tau])
                     [ (some_some (Expr_basic [var_obj]), Expr_apply var_f [Expr_apply \<open>oid_of\<close> [Expr_basic [var_obj]], Expr_basic [var_tau]])
                     , (Expr_basic [wildcard], Expr_basic [\<open>invalid\<close>, var_tau])])))
  , lets var_in_pre_state (b \<open>fst\<close>)
  , lets var_in_post_state (b \<open>snd\<close>)
  , lets var_reconst_basetype Expr_basety
  , let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<open>x\<close> in
     Definition (Expr_rewrite (Expr_basic [var_reconst_basetype_void, var_x])
                              \<open>=\<close>
                              (Expr_binop (Expr_basic [var_Abs_Void]) \<open>o\<close> (a var_reconst_basetype (b var_x)))) ])"


definition "print_access_choose_switch
              lets mk_var expr
              print_access_choose_n
              sexpr_list sexpr_function sexpr_pair =
  List_flatten
       (List_map
          (\<lambda>n.
           let l = List_upto 0 (n - 1) in
           List_map (let l = sexpr_list (List_map mk_var l) in (\<lambda>(i,j).
             (lets
                (print_access_choose_n n i j)
                (sexpr_function [(l, (sexpr_pair (mk_var i) (mk_var j)))]))))
             ((List_flatten o List_flatten) (List_map (\<lambda>i. List_map (\<lambda>j. if i = j then [] else [(i, j)]) l) l)))
          (class_arity expr))"
definition "print_access_choose_ml = start_map'''' Thy_ml o (\<lambda>expr _.
  (let a = \<lambda>f x. Sexpr_apply f [x]
     ; b = \<lambda>s. Sexpr_basic [s]
     ; lets = \<lambda>var exp. Ml (Sexpr_rewrite_val (Sexpr_basic [var]) \<open>=\<close> exp)
     ; mk_var = \<lambda>i. b (flatten [\<open>x\<close>, natural_of_str i]) in
   List_flatten
   [ print_access_choose_switch
       lets mk_var expr
       print_access_choose_mlname
       Sexpr_list Sexpr_function Sexpr_pair ]))"
definition "print_access_choose = start_map'''' Thy_definition_hol o (\<lambda>expr _.
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; lets = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) \<open>=\<close> exp)
     ; lets' = \<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>avar exp. Definition (Expr_rewrite (Expr_basic [var]) \<open>=\<close> (b exp))
     ; lets'' = \<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>avar exp. Definition (Expr_rewrite (Expr_basic [var]) \<open>=\<close> (Expr_lam \<open>l\<close> (\<lambda>var_l. Expr_binop (b var_l) \<open>!\<close> (b exp))))
     ; _(* ignored *) = 
        let l_flatten = \<open>List_flatten\<close> in
        [ lets l_flatten (let fun_foldl = \<lambda>f base.
                             Expr_lam \<open>l\<close> (\<lambda>var_l. Expr_apply \<open>foldl\<close> [Expr_lam \<open>acc\<close> f, base, a \<open>rev\<close> (b var_l)]) in
                           fun_foldl (\<lambda>var_acc.
                             fun_foldl (\<lambda>var_acc.
                               Expr_lam \<open>l\<close> (\<lambda>var_l. Expr_apply \<open>Cons\<close> (List_map b [var_l, var_acc]))) (b var_acc)) (b \<open>Nil\<close>))
        , lets var_map_of_list (Expr_apply \<open>foldl\<close>
            [ Expr_lam \<open>map\<close> (\<lambda>var_map.
                let var_x = \<open>x\<close>
                  ; var_l0 = \<open>l0\<close>
                  ; var_l1 = \<open>l1\<close>
                  ; f_map = a var_map in
                Expr_lambdas0 (Expr_pair (b var_x) (b var_l1))
                  (Expr_case (f_map (b var_x))
                    (List_map (\<lambda>(pat, e). (pat, f_map (Expr_binop (b var_x) unicode_mapsto e)))
                      [ (b \<open>None\<close>, b var_l1)
                      , (Expr_some (b var_l0), a l_flatten (Expr_list (List_map b [var_l0, var_l1])))])))
            , b \<open>Map.empty\<close>])] in
  List_flatten
  [ let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l a = \<lambda>f x. Expr_apply f [x]
      ; b = \<lambda>s. Expr_basic [s]
      ; lets = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) \<open>=\<close> exp)
      ; mk_var = \<lambda>i. b (flatten [\<open>x\<close>, natural_of_str i]) in
    print_access_choose_switch
      lets mk_var expr
      print_access_choose_name
      Expr_list Expr_function Expr_pair
  , [ let var_pre_post = \<open>pre_post\<close>
        ; var_to_from = \<open>to_from\<close>
        ; var_assoc_oid = \<open>assoc_oid\<close>
        ; var_f = \<open>f\<close>
        ; var_oid = \<open>oid\<close> in
      Definition (Expr_rewrite
        (Expr_basic [var_deref_assocs, var_pre_post, var_to_from, var_assoc_oid, var_f, var_oid ])
        \<open>=\<close>
        (Expr_lam
           unicode_tau
           (\<lambda>var_tau.
           Expr_case (Expr_apply var_assocs [Expr_apply var_pre_post [Expr_basic [var_tau]]
                                                                      ,Expr_basic [var_assoc_oid]])
             [ let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_S = \<open>S\<close> in
               ( Expr_some (Expr_basic [var_S])
               , Expr_apply var_f
                   [ Expr_apply var_deref_assocs_list (List_map b [var_to_from, var_oid, var_S])
                   , Expr_basic [var_tau]])
             , (Expr_basic[wildcard], Expr_apply \<open>invalid\<close> [Expr_basic [var_tau]]) ]))) ]] ))"

definition "print_access_deref_oid_name isub_name = isub_name var_deref_oid"
definition "print_access_deref_oid = start_map Thy_definition_hol o
  map_class (\<lambda>isub_name _ _ _ _ _.
    let var_fs = \<open>fst_snd\<close>
      ; var_f = \<open>f\<close>
      ; var_oid = \<open>oid\<close>
      ; var_obj = \<open>obj\<close> in
    Definition (Expr_rewrite
                  (Expr_basic [print_access_deref_oid_name isub_name, var_fs, var_f, var_oid])
                  \<open>=\<close>
                  (Expr_lam unicode_tau
                     (\<lambda>var_tau. Expr_case (Expr_apply \<open>heap\<close> [Expr_basic [var_fs, var_tau], Expr_basic [var_oid]])
                     [ (Expr_some (Expr_basic [isub_name datatype_in, var_obj]), Expr_basic [var_f, var_obj, var_tau])
                     , (Expr_basic [wildcard], Expr_basic [\<open>invalid\<close>, var_tau]) ]))))"

definition "print_access_deref_assocs_name' name_from isub_name isup_attr =
  flatten [var_deref, \<open>_\<close>, isub_name var_assocs, \<open>_\<close>, natural_of_str name_from, isup_attr \<open>_\<close>]"
definition "print_access_deref_assocs_name name_from isub_name attr =
  print_access_deref_assocs_name' name_from isub_name (\<lambda>s. s @@ isup_of_str attr)"
definition "print_access_deref_assocs = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (if design_analysis = Gen_only_design then \<lambda>_. [] else (\<lambda>expr. List_flatten (List_flatten (map_class (\<lambda>isub_name name l_attr l_inherited _ _.
  let l_inherited = map_class_inh l_inherited in
  let var_fst_snd = \<open>fst_snd\<close>
    ; var_f = \<open>f\<close>
    ; b = \<lambda>s. Expr_basic [s] in
    List_flatten (List_map (List_map
      (\<lambda> (attr, OclTy_class ty_obj) \<Rightarrow>
           let name_from = TyObjN_ass_switch (TyObj_from ty_obj) in
           [Definition (Expr_rewrite
                  (Expr_basic [print_access_deref_assocs_name name_from isub_name attr, var_fst_snd, var_f])
                  \<open>=\<close>
                  (Expr_binop
                    (Expr_apply
                      var_deref_assocs
                        (List_map b [ var_fst_snd
                               , print_access_choose_name (TyObj_ass_arity ty_obj) name_from (TyObjN_ass_switch (TyObj_to ty_obj))
                               , print_access_oid_uniq_name name_from isub_name attr
                               , var_f ]))
                    unicode_circ
                    (b \<open>oid_of\<close>)))]
       | _ \<Rightarrow> []))
      (l_attr # l_inherited))) expr)))) expr)"

definition "print_access_select_name isup_attr isub_name = isup_attr (isub_name var_select)"
definition "print_access_select = start_map'' Thy_definition_hol o (\<lambda>expr base_attr _ base_attr''.
  let b = \<lambda>s. Expr_basic [s] in
  map_class_arg_only0 (\<lambda>isub_name name l_attr.
    let l_attr = base_attr l_attr in
    let var_f = \<open>f\<close>
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [print_access_select_name isup_attr isub_name, var_f])
                       \<open>=\<close>
                       (let var_attr = b (isup_of_str attr) in
                        Expr_function
                          (List_map (\<lambda>(lhs,rhs). ( Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( wildc
                                                         # List_flatten [l_wildl, [lhs], l_wildr])
                                                     , rhs))
                            [ ( Expr_basic [unicode_bottom], Expr_basic [\<open>null\<close>] )
                            , ( Expr_some var_attr
                              , Expr_apply var_f [var_attr]) ]))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_attr), [])
      l_attr) in
    rev l)
  (\<lambda>isub_name name (l_attr, l_inherited, l_cons).
    let l_inherited = List_flatten (List_map (\<lambda> OclClass _ l _ \<Rightarrow> l) (of_inh l_inherited)) in
    let (l_attr, l_inherited) = base_attr'' (l_attr, l_inherited) in
    let var_f = \<open>f\<close>
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [isup_attr (isub_name var_select), var_f])
                       \<open>=\<close>
                       (let var_attr = b (isup_of_str attr) in
                        Expr_function
                          (List_flatten (List_map (\<lambda>(lhs,rhs). ( Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (isub_name datatype_ext_constr_name)
                                                             (wildc # List_flatten [l_wildl, [lhs], l_wildr])
                                                         # List_map (\<lambda>_. wildc) l_attr)
                                                     , rhs))
                            [ ( Expr_basic [unicode_bottom], Expr_basic [\<open>null\<close>] )
                            , ( Expr_some var_attr
                              , Expr_apply var_f [var_attr]) ]
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
  (if design_analysis = Gen_only_design then \<lambda>_. [] else (\<lambda>expr. List_flatten (List_flatten (map_class (\<lambda>isub_name name l_attr l_inh _ _.
    let l_inh = map_class_inh l_inh in
    List_flatten (fst (fold_list (fold_list
      (\<lambda> (attr, OclTy_class ty_obj) \<Rightarrow> \<lambda>rbt.
          if lookup2 rbt (name, attr) = None then
           ([Definition (let var_f = \<open>f\<close>
                          ; b = \<lambda>s. Expr_basic [s] in
              Expr_rewrite
                  (Expr_basic [isub_name var_select @@ isup_of_str attr, var_f])
                  \<open>=\<close>
                  (Expr_apply var_select_object
                   (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l obj_mult = TyObjN_role_multip (TyObj_to ty_obj)
                      ; (var_mt, var_OclIncluding, var_ANY) =
                          case obj_mult of OclMult _ Set \<Rightarrow> (var_mt_set, var_OclIncluding_set, var_ANY_set)
                                         | _ \<Rightarrow> (var_mt_sequence, var_OclIncluding_sequence, var_ANY_sequence) in
                    List_map b [ var_mt
                               , var_OclIncluding
                               , if single_multip obj_mult then var_ANY else \<open>id\<close>
                               , var_f])))], insert2 (name, attr) () rbt)
         else ([], rbt)
       | _ \<Rightarrow> Pair []))
      (l_attr # l_inh) RBT.empty))) expr)))) expr)"

definition "print_access_dot_consts =
 (fold_list (\<lambda>(f_update, x) ocl. (Thy_consts_class x, ocl \<lparr> D_accessor_rbt := f_update (D_accessor_rbt ocl) \<rparr> ))) o
  (List_flatten o List_flatten o map_class (\<lambda>isub_name name l_attr _ _ _.
    List_map (\<lambda>(attr_n, attr_ty).
      List_map
        (\<lambda>(var_at_when_hol, var_at_when_ocl, f_update_ocl).
          let name =
             flatten [ \<open>dot\<close>
                     , case attr_ty of
                         OclTy_class ty_obj \<Rightarrow> flatten [\<open>_\<close>, natural_of_str (TyObjN_ass_switch (TyObj_from ty_obj)), \<open>_\<close>]
                       | _ \<Rightarrow> \<open>\<close>
                     , isup_of_str attr_n, var_at_when_hol] in
          ( f_update_ocl (\<lambda> l. String_to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e name # l)
          , Consts_raw0
            name
            (Ty_arrow
              (Ty_apply (Ty_base \<open>val\<close>) [Ty_base unicode_AA, Ty_base (\<degree>Char Nibble2 Nibble7\<degree> @@ unicode_alpha)])

              (let ty_base = \<lambda>attr_ty.
                 Ty_apply (Ty_base \<open>val\<close>) [Ty_base unicode_AA,
                    let option = \<lambda>x. Ty_apply (Ty_base \<open>option\<close>) [x] in
                    option (option (Ty_base attr_ty))] in
               case attr_ty of
                  OclTy_raw attr_ty \<Rightarrow> ty_base attr_ty
                | OclTy_class ty_obj \<Rightarrow>
                    let ty_obj = TyObj_to ty_obj
                      ; name = TyObjN_role_ty ty_obj
                      ; obj_mult = TyObjN_role_multip ty_obj in
                    Ty_base (if single_multip obj_mult then
                               name
                             else
                               case obj_mult of OclMult _ Set \<Rightarrow> print_infra_type_synonym_class_set_name name
                                              | _ \<Rightarrow> print_infra_type_synonym_class_sequence_name name)
                | OclTy_base_unlimitednatural \<Rightarrow> str_hol_of_ty_all Ty_apply ty_base attr_ty
                   (* REMARK Dependencies to UnlimitedNatural.thy can be detected and added
                             so that this pattern clause would be merged with the default case *)
                | OclTy_collection _ _ \<Rightarrow> Raw (fst (print_infra_type_synonym_class_rec_aux attr_ty))
                | OclTy_pair _ _ \<Rightarrow> Raw (fst (print_infra_type_synonym_class_rec_aux attr_ty))
                | _ \<Rightarrow> Raw (str_of_ty attr_ty)))
            (let dot_name = mk_dot attr_n var_at_when_ocl
               ; mk_par =
                   let esc = \<lambda>s. \<degree>Char Nibble2 Nibble7\<degree> @@ s in
                   (\<lambda>s1 s2. flatten [s1, \<open> \<close>, esc \<open>/\<close>, \<open>* \<close>, s2, \<open> *\<close>, esc \<open>/\<close>]) in
             case attr_ty of OclTy_class ty_obj \<Rightarrow>
               (case apply_optim_ass_arity
                       ty_obj
                       (mk_par
                          dot_name
                          (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l ty_obj = TyObj_from ty_obj in
                           case TyObjN_role_name ty_obj of
                                None => natural_of_str (TyObjN_ass_switch ty_obj)
                              | Some s => s)) of
                  None \<Rightarrow> dot_name
                | Some dot_name \<Rightarrow> dot_name)
                           | _ \<Rightarrow> dot_name)
            None))
        [ (var_at_when_hol_post, var_at_when_ocl_post, update_D_accessor_rbt_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre, update_D_accessor_rbt_pre)]) l_attr))"

definition "print_access_dot_name isub_name dot_at_when attr_ty isup_attr =
  flatten [ isup_attr (let dot_name = isub_name \<open>dot\<close> in
                       case attr_ty of
                         OclTy_class ty_obj \<Rightarrow> flatten [dot_name, \<open>_\<close>, natural_of_str (TyObjN_ass_switch (TyObj_from ty_obj)), \<open>_\<close>]
                       | _ \<Rightarrow> dot_name)
          , dot_at_when]"

fun_quick print_access_dot_aux where
   "print_access_dot_aux deref_oid x =
    (\<lambda> OclTy_collection (OclMult _ Set) ty \<Rightarrow> Expr_apply var_select_object_set [print_access_dot_aux deref_oid ty]
     | OclTy_collection (OclMult _ Sequence) ty \<Rightarrow> Expr_apply var_select_object_sequence [print_access_dot_aux deref_oid ty]
     | OclTy_pair ty1 ty2 \<Rightarrow> Expr_apply var_select_object_pair [print_access_dot_aux deref_oid ty1, print_access_dot_aux deref_oid ty2]
     | OclTy_class_pre s \<Rightarrow> deref_oid (Some s) [Expr_basic [var_reconst_basetype]]
     | OclTy_base_void \<Rightarrow> Expr_basic [var_reconst_basetype_void]
     | _ \<Rightarrow> Expr_basic [var_reconst_basetype]) x"

definition "print_access_dot = start_map'''' Thy_defs_overloaded o (\<lambda>expr design_analysis.
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_ty isup_attr dot_attr.
            [ Defs_overloaded
                (print_access_dot_name isub_name dot_at_when attr_ty isup_attr)
                (let var_x = \<open>x\<close> in
                 Expr_rewrite
                   (dot_attr (Expr_annot (Expr_basic [var_x]) name))
                   unicode_equiv
                   (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = \<lambda>attr_orig l. Expr_apply (case attr_orig of None \<Rightarrow> isub_name var_deref_oid
                                                                              | Some orig_n \<Rightarrow> var_deref_oid @@ isub_of_str orig_n) (Expr_basic [var_in_when_state] # l) in
                    deref_oid None
                      [ ( case attr_ty of
                            OclTy_class ty_obj \<Rightarrow>
                              if design_analysis = Gen_only_design then id else
                                (\<lambda>l. Expr_apply (print_access_deref_assocs_name' (TyObjN_ass_switch (TyObj_from ty_obj)) isub_name isup_attr) (Expr_basic [var_in_when_state] # [l]))
                          | _ \<Rightarrow> id)
                          (Expr_apply (isup_attr (isub_name var_select))
                            [case attr_ty of
                               OclTy_raw _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                             | OclTy_class ty_obj \<Rightarrow>
                                 let ty_obj = TyObj_to ty_obj
                                   ; der_name = deref_oid (Some (TyObjN_role_ty ty_obj)) [Expr_basic [var_reconst_basetype]] in
                                 if design_analysis = Gen_only_design then
                                   let obj_mult = TyObjN_role_multip ty_obj
                                     ; (var_select_object_name_any, var_select_object_name) =
                                         case obj_mult of OclMult _ Set \<Rightarrow> (var_select_object_set_any, var_select_object_set)
                                                        | _ \<Rightarrow> (var_select_object_sequence_any, var_select_object_sequence) in
                                   Expr_apply (if single_multip obj_mult then
                                                 var_select_object_name_any
                                               else
                                                 var_select_object_name) [der_name]
                                 else
                                   der_name
                             | x \<Rightarrow> print_access_dot_aux deref_oid x ]) ] ])) ]) expr)"

definition "print_access_dot_lemmas_id_set =
  (if activate_simp_optimization then
     map_class_arg_only_var'
       (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _. [print_access_dot_name isub_name dot_at_when attr_ty isup_attr])
   else (\<lambda>_. []))"

definition "print_access_dot_lemmas_id_name = \<open>dot_accessor\<close>"
definition "print_access_dot_lemmas_id = start_map' (\<lambda>expr.
       (let name_set = print_access_dot_lemmas_id_set expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_nosimp print_access_dot_lemmas_id_name (List_map Thm_str name_set) ]))"

definition "print_access_dot_cp_lemmas_set =
  (if activate_simp_optimization then [hol_definition var_eval_extract] else [])"

definition "print_access_dot_cp_lemmas = start_map' (\<lambda>_.
  List_map (\<lambda>x. Thy_lemmas_simp (Lemmas_simp \<open>\<close> [Thm_str x])) print_access_dot_cp_lemmas_set)"

definition "print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr = flatten [\<open>cp_\<close>, print_access_dot_name isub_name dot_at_when attr_ty isup_attr]"
definition "print_access_dot_lemma_cp = start_map Thy_lemma_by o
 (let auto = \<lambda>l. Tac_auto_simp_add2 [print_access_dot_lemmas_id_name] (List_map hol_definition (\<open>cp\<close> # l)) in
  map_class_arg_only_var
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            [ Lemma_by
                (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr)
                [Expr_apply \<open>cp\<close> [Expr_lam \<open>X\<close> (\<lambda>var_x. dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]
                []
                (Tacl_by [auto (if print_access_dot_cp_lemmas_set = [] then
                                  [var_eval_extract, flatten [isup_attr (isub_name \<open>dot\<close>), dot_at_when]]
                                else
                                  [])]) ])
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            [ Lemma_by
                (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr)
                [Expr_apply \<open>cp\<close> [Expr_lam \<open>X\<close> (\<lambda>var_x. dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]
                []
                (if print_access_dot_cp_lemmas_set = [] then Tacl_sorry (* fold l_hierarchy, take only subclass, unfold the corresponding definition *)
                 else Tacl_by [auto []]) ]))"

definition "print_access_dot_lemmas_cp = start_map Thy_lemmas_simp o (\<lambda>expr.
  case map_class_arg_only_var'
    (\<lambda>isub_name _ (_, dot_at_when) attr_ty isup_attr _.
      [Thm_str (print_access_dot_lemma_cp_name isub_name dot_at_when attr_ty isup_attr) ])
    expr
  of [] \<Rightarrow> []
   | l \<Rightarrow> [Lemmas_simp \<open>\<close> l])"

definition "print_access_lemma_strict_name isub_name dot_at_when attr_ty isup_attr name_invalid = flatten [print_access_dot_name isub_name dot_at_when attr_ty isup_attr, \<open>_\<close>, name_invalid]"
definition "print_access_lemma_strict expr = (start_map Thy_lemma_by o
  map_class_arg_only_var' (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
            List_map (\<lambda>(name_invalid, tac_invalid). Lemma_by
                  (print_access_lemma_strict_name isub_name dot_at_when attr_ty isup_attr name_invalid)
                  [Expr_rewrite
                     (dot_attr (Expr_annot (Expr_basic [name_invalid]) name))
                     \<open>=\<close>
                     (Expr_basic [\<open>invalid\<close>])]
                  []
                  (if print_access_dot_lemmas_id_set expr = [] | print_access_dot_cp_lemmas_set = [] then
                     Tacl_sorry else
                   Tacl_by [ Tac_rule (Thm_str \<open>ext\<close>),
                             Tac_simp_add2 [print_access_dot_lemmas_id_name]
                                           (List_map hol_definition
                                             (let l = (let l = (\<open>bot_option\<close> # tac_invalid) in
                                              if print_access_dot_lemmas_id_set expr = [] then
                                                flatten [isup_attr (isub_name \<open>dot\<close>), dot_at_when] # l
                                              else l) in
                                              if print_access_dot_cp_lemmas_set = []
                                              then
                                                \<open>eval_extract\<close> # l
                                              else l))]) )
                [(\<open>invalid\<close>, [\<open>invalid\<close>]), (\<open>null\<close>, [\<open>null_fun\<close>, \<open>null_option\<close>])])) expr"

definition "print_access_def_mono_name isub_name dot_at_when attr_ty isup_attr =
  flatten [ \<open>defined_mono_\<close>, print_access_dot_name isub_name dot_at_when attr_ty isup_attr ]"
definition "print_access_def_mono = start_map'''' Thy_lemma_by o (\<lambda>expr _.
  map_class_arg_only_var'
    (\<lambda>isub_name name (_, dot_at_when) attr_ty isup_attr dot_attr.
      let var_X = \<open>X\<close>
        ; var_tau = unicode_tau
        ; a = \<lambda>f x. Expr_apply f [x]
        ; b = \<lambda>s. Expr_basic [s]
        ; f0 = \<lambda>e. Expr_binop (Expr_basic [var_tau]) unicode_Turnstile e
        ; f = \<lambda>e. f0 (Expr_apply unicode_delta [e]) in
            [ Lemma_by
                (print_access_def_mono_name isub_name dot_at_when attr_ty isup_attr)
                (List_map f [ dot_attr (Expr_annot (b var_X) name)
                            , b var_X ])
                (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f_tac = \<lambda>s.
                   [ Tac_case_tac (f0 (Expr_warning_parenthesis (Expr_rewrite (b var_X) unicode_triangleq (b s))))
                   , Tac_insert [Thm_where (Thm_str \<open>StrongEq_L_subst2\<close>)
                                           [ (\<open>P\<close>, Expr_lam \<open>x\<close> (\<lambda>var_X. a unicode_delta (dot_attr (b var_X))))
                                           , (unicode_tau, b unicode_tau)
                                           , (\<open>x\<close>, b var_X)
                                           , (\<open>y\<close>, b s)]]
                   , Tac_simp_add [ \<open>foundation16\<close> @@ \<degree>Char Nibble2 Nibble7\<degree>
                                  , print_access_lemma_strict_name isub_name dot_at_when attr_ty isup_attr s] ] in
                 [ f_tac \<open>invalid\<close>
                 , f_tac \<open>null\<close> ])
                (Tacl_by [Tac_simp_add [\<open>defined_split\<close>]]) ]) expr)"

definition "print_access_is_repr_name isub_name dot_at_when attr_ty isup_attr =
  flatten [ \<open>is_repr_\<close>, print_access_dot_name isub_name dot_at_when attr_ty isup_attr ]"
definition "print_access_is_repr = start_map'''' Thy_lemma_by o (\<lambda>expr design_analysis.
  (case design_analysis of Gen_only_analysis \<Rightarrow> \<lambda>_. [] | Gen_default \<Rightarrow> \<lambda>_. [] | Gen_only_design \<Rightarrow>
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_ty isup_attr dot_attr.
      case attr_ty of OclTy_class ty_obj \<Rightarrow>
      let var_X = \<open>X\<close>
        ; var_tau = unicode_tau
        ; var_def_dot = \<open>def_dot\<close>
        ; a = \<lambda>f x. Expr_apply f [x]
        ; ap = \<lambda>f x. Expr_applys (Expr_pat f) [x]
        ; ap' = \<lambda>f x. Expr_applys (Expr_pat f) x
        ; b = \<lambda>s. Expr_basic [s]
        ; f0 = \<lambda>e. Expr_binop (Expr_basic [var_tau]) unicode_Turnstile e
        ; f = \<lambda>e. f0 (Expr_apply unicode_delta [e])
        ; attr_ty' = case TyObjN_role_multip (TyObj_to ty_obj) of OclMult _ x \<Rightarrow> x in
            [ Lemma_by_assum
                (print_access_is_repr_name isub_name dot_at_when attr_ty isup_attr)
                [ (var_def_dot, False, f (dot_attr (Expr_annot (b var_X) name))) ]
                (Expr_apply \<open>is_represented_in_state\<close> [b var_in_when_state, dot_attr (Expr_basic [var_X]), b name, b var_tau])
(let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l (* existential variables *)
     v_a0 = \<open>a0\<close>
   ; v_a = \<open>a\<close>
   ; v_b = \<open>b\<close>
   ; v_r = \<open>r\<close>
   ; v_typeoid = \<open>typeoid\<close>
   ; v_opt = \<open>opt\<close>
   ; v_aa = \<open>aa\<close>
   ; v_e = \<open>e\<close>
   ; v_aaa = \<open>aaa\<close>

     (* schematic variables *)
   ; vs_t = \<open>t\<close>
   ; vs_sel_any = \<open>sel_any\<close>

     (* *)
   ; l_thes = \<lambda>l. Some (l @@@@ [Expr_pat \<open>thesis\<close>])
   ; l_thes0 = \<lambda>l. Some (l @@@@ [Expr_pat \<open>t\<close>])
   ; hol_d = List_map hol_definition
   ; thol_d = List_map (Thm_str o hol_definition)
   ; App_f = \<lambda>l e. App_fix_let l [] e []
   ; App_f' = \<lambda>l. App_fix_let l []
   ; f_ss = \<lambda>v. a \<open>Some\<close> (a \<open>Some\<close> (b v)) in
 [ App [Tac_insert [Thm_simplified (Thm_OF (Thm_str (print_access_def_mono_name isub_name dot_at_when attr_ty isup_attr))
                                           (Thm_str var_def_dot))
                                   (Thm_str \<open>foundation16\<close>)]]
 , App [Tac_case_tac (a var_X (b var_tau)), Tac_simp_add [hol_definition \<open>bot_option\<close>]]
 (* *)
 , App_f' [v_a0]
          (l_thes [ Expr_binop (a var_X (b var_tau)) unicode_noteq (b \<open>null\<close>)
                  , Expr_binop (a var_X (b var_tau)) \<open>=\<close> (a \<open>Some\<close> (b v_a0)) ])
          [AppE [Tac_simp_all]]
 , App [Tac_case_tac (b v_a0), Tac_simp_add (List_map hol_definition [\<open>null_option\<close>, \<open>bot_option\<close>]), Tac_clarify]
 (* *)
 , App_f [v_a] (l_thes [ Expr_binop (a var_X (b var_tau)) \<open>=\<close> (f_ss v_a) ])
 , App [Tac_case_tac (Expr_apply \<open>heap\<close> [ a var_in_when_state (b var_tau)
                                          , a \<open>oid_of\<close> (b v_a)]), Tac_simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>])]
 , App [ Tac_insert [Thm_str \<open>def_dot\<close>]
       , Tac_simp_add_split ( Thm_str (print_access_dot_name isub_name dot_at_when attr_ty isup_attr)
                            # thol_d [ \<open>is_represented_in_state\<close>
                                     , print_access_select_name isup_attr isub_name
                                     , print_access_deref_oid_name isub_name
                                     , var_in_when_state
                                     , \<open>defined\<close>, \<open>OclValid\<close>, \<open>false\<close>, \<open>true\<close>, \<open>invalid\<close>, \<open>bot_fun\<close>])
                            [Thm_str \<open>split_if_asm\<close>]]
 (* *)
 , App_f [v_b] (l_thes [ Expr_binop (a var_X (b var_tau)) \<open>=\<close> (f_ss v_a)
                       , Expr_rewrite (Expr_apply \<open>heap\<close> [ a var_in_when_state (b var_tau)
                                                           , a \<open>oid_of\<close> (b v_a)])
                                      \<open>=\<close>
                                      (a \<open>Some\<close> (b v_b)) ])
 , App [ Tac_insert [Thm_simplified (Thm_str \<open>def_dot\<close>) (Thm_str \<open>foundation16\<close>)]
       , Tac_auto_simp_add ( print_access_dot_name isub_name dot_at_when attr_ty isup_attr
                           # hol_d [ \<open>is_represented_in_state\<close>
                                   , print_access_deref_oid_name isub_name
                                   , \<open>bot_option\<close>, \<open>null_option\<close>])]
 , App [ Tac_case_tac (b v_b), Tac_simp_all_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>]) ]
 (* *)
 , App_fix_let
     [v_r, v_typeoid]
     [ ( Expr_pat vs_t
       , Expr_rewrite (f_ss v_r) unicode_in (Expr_binop
                                              (Expr_parenthesis
                                                (Expr_binop (b \<open>Some\<close>) \<open>o\<close> (b (print_astype_from_universe_name name))))
                                              \<open>`\<close>
                                              (a \<open>ran\<close> (a \<open>heap\<close> (a var_in_when_state (b var_tau))))))
     , ( Expr_pat vs_sel_any
       , Expr_apply (case attr_ty' of Set \<Rightarrow> var_select_object_set_any | Sequence \<Rightarrow> var_select_object_sequence_any)
                    [ Expr_apply (print_access_deref_oid_name isub_name) [b var_in_when_state, b var_reconst_basetype] ])]
     (Some [ Expr_rewrite (Expr_apply (print_access_select_name isup_attr isub_name)
                                      [ Expr_pat vs_sel_any
                                      , b v_typeoid
                                      , b var_tau ]) \<open>=\<close> (f_ss v_r)
           , Expr_pat vs_t ])
     []
 , App [ Tac_case_tac (b v_typeoid), Tac_simp_add (hol_d [print_access_select_name isup_attr isub_name]) ]
 (* *)
 , App_f [v_opt]
     (l_thes0
       [ Expr_rewrite (Expr_applys (Expr_case (b v_opt)
                                              [ (b \<open>None\<close>, b \<open>null\<close>)
                                              , let var_x = \<open>x\<close> in
                                                (a \<open>Some\<close> (b var_x), ap vs_sel_any (b var_x)) ])
                                   [ b var_tau ])
                      \<open>=\<close>
                      (f_ss v_r) ])
 , App [ Tac_case_tac (b v_opt), Tac_auto_simp_add (hol_d [\<open>null_fun\<close>, \<open>null_option\<close>, \<open>bot_option\<close>]) ]
 (* *)
 , App_f' [v_aa]
     (l_thes0
       [ Expr_binop (b var_tau) unicode_Turnstile (a unicode_delta (ap vs_sel_any (b v_aa)))
       , Expr_rewrite (ap' vs_sel_any [ b v_aa, b var_tau ]) \<open>=\<close> (f_ss v_r) ])
     [ AppE [ Tac_simp_all_only [] ]
     , AppE [ Tac_simp_add (\<open>foundation16\<close> # hol_d [\<open>bot_option\<close>, \<open>null_option\<close>]) ] ]
 , App [ Tac_drule (Thm_simplified (Thm_str (case attr_ty' of Set \<Rightarrow> var_select_object_set_any_exec
                                                            | Sequence \<Rightarrow> var_select_object_sequence_any_exec))
                                   (Thm_str \<open>foundation22\<close>)), Tac_erule (Thm_str \<open>exE\<close>) ]
 (* *)
 , App_f' [v_e]
     (l_thes0
       [ Expr_rewrite (ap' vs_sel_any [ b v_aa, b var_tau ]) \<open>=\<close> (f_ss v_r)
       , Expr_rewrite (ap' vs_sel_any [ b v_aa, b var_tau ])
                      \<open>=\<close>
                      (Expr_apply (print_access_deref_oid_name isub_name)
                                  (List_map b [ var_in_when_state
                                              , var_reconst_basetype
                                              , v_e
                                              , var_tau ])) ])
     [ AppE [ Tac_plus [Tac_blast None] ] ]
 , App [ Tac_simp_add (hol_d [print_access_deref_oid_name isub_name]) ]
 , App [ Tac_case_tac (Expr_apply \<open>heap\<close> [ a var_in_when_state (b var_tau), b v_e ])
       , Tac_simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>]), Tac_simp ]
 (* *)
 , App_f [v_aaa]
     (l_thes0
       [ Expr_rewrite (Expr_case (b v_aaa)
                                 [ let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_obj = \<open>obj\<close> in
                                   (a (isub_name datatype_in) (b var_obj), Expr_apply var_reconst_basetype [b var_obj, b var_tau])
                                 , (b wildcard, a \<open>invalid\<close> (b var_tau)) ])
                      \<open>=\<close>
                      (f_ss v_r)
       , Expr_rewrite (Expr_apply \<open>heap\<close> [ a var_in_when_state (b var_tau), b v_e ])
                      \<open>=\<close>
                      (a \<open>Some\<close> (b v_aaa)) ])
 , App [ Tac_case_tac (b v_aaa), Tac_auto_simp_add (hol_d [\<open>invalid\<close>, \<open>bot_option\<close>, \<open>image\<close>, \<open>ran\<close>]) ]
 , App [ Tac_rule (Thm_where (Thm_str \<open>exI\<close>) [(\<open>x\<close>, a (isub_name datatype_in) (b v_r))])
       , Tac_simp_add_split (thol_d [print_astype_from_universe_name name, \<open>Let\<close>, var_reconst_basetype])
                            [Thm_str \<open>split_if_asm\<close>] ] ])
                (Tacl_by [ Tac_rule' ]) ]
      | _ \<Rightarrow> [])) expr)"

end
