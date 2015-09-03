(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor2_ctxt.thy ---
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

theory  OCL_compiler_floor2_ctxt
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* context2 *}

(* (* ERROR this lambda term type-checks expensively *)
definition "print_ctxt_is_accessor =
  (\<lambda> Pure_Type \<lless>''fun''\<ggreater>
               [Pure_Type \<lless>''fun''\<ggreater>
                       [Pure_Type \<lless>''Product_Type.prod''\<ggreater>
                               [Pure_Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Pure_Type _ (* AA *) [], Pure_Type \<lless>''Product_Type.unit''\<ggreater> []],
                                Pure_Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Pure_Type _ (* AA *) [], Pure_Type \<lless>''Product_Type.unit''\<ggreater> []]],
                        Pure_TFree _ (* 'a *) (Pure_Sort [Pure_Class \<lless>''HOL.type''\<ggreater>])],
                Pure_Type \<lless>''fun''\<ggreater>
                       [Pure_Type \<lless>''Product_Type.prod''\<ggreater>
                               [Pure_Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Pure_Type _ (* AA *) [], Pure_Type \<lless>''Product_Type.unit''\<ggreater> []],
                                Pure_Type \<lless>''OCL_core.state.state_ext''\<ggreater>
                                       [Pure_Type _ (* AA *) [], Pure_Type \<lless>''Product_Type.unit''\<ggreater> []]],
                        Pure_Type \<lless>''Option.option''\<ggreater>
                               [Pure_Type \<lless>''Option.option''\<ggreater>
                                       [Pure_Type _ (* class name *) []]]]]
       \<Rightarrow> True
   | _ \<Rightarrow> False)"
*)
definition "print_ctxt_is_name_at_gen var s =
 (let var = String_to_list var
    ; s = String_to_list s in
  case var of _ # _ \<Rightarrow>
    let lg_var = length var in
    if (* TODO use 'String_equal' *) List_take_last lg_var s = var then
      Some \<lless>List_take_first (length s - lg_var) s\<ggreater>
    else
      None)"

definition "print_ctxt_is_name_at_pre = print_ctxt_is_name_at_gen var_at_when_hol_pre"
definition "print_ctxt_is_name_at_post = (case String_to_list var_at_when_hol_post of [] \<Rightarrow>
  \<lambda>s. case print_ctxt_is_name_at_pre s of None \<Rightarrow> Some s
                                        | _ \<Rightarrow> None)"

definition "print_ctxt_to_ocl_gen_split s = 
 (case List_split_at (\<lambda> s. s = Char Nibble2 NibbleE) (String_to_list s) of
    (_, Some _, s) \<Rightarrow> Some s
  | _ \<Rightarrow> None)"
definition "print_ctxt_to_ocl_gen l_access f var = (\<lambda> T_pure t \<Rightarrow>
  T_pure (P.map_Const (\<lambda> s ty.
    if (*print_ctxt2_is_accessor ty*)
       list_ex (case print_ctxt_to_ocl_gen_split s of
                  Some s \<Rightarrow> \<lambda>n. String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_list n = s
                | _ \<Rightarrow> \<lambda>_. False) l_access then
      case f s of
        Some s \<Rightarrow> s @@ var
      | _ \<Rightarrow> s
    else
      s) t))"

definition "print_ctxt_to_ocl_pre ocl = print_ctxt_to_ocl_gen (snd (D_ocl_accessor ocl)) print_ctxt_is_name_at_post var_at_when_hol_pre"
definition "print_ctxt_to_ocl_post ocl = print_ctxt_to_ocl_gen (fst (D_ocl_accessor ocl)) print_ctxt_is_name_at_pre var_at_when_hol_post"

definition "raise_ml_unbound f_msg ctxt =
        [ (\<lambda>_. [O.ml (raise_ml (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l l = List_flatten (List_mapi (\<lambda> n. \<lambda>(msg, T_pure t) \<Rightarrow>
                                            let l =
                                              rev (P.fold_Free (\<lambda>l s.
                                                (Error, flatten [f_msg n msg, \<open>: unbound value \<close>, s]) # l) [] t) in
                                            if l = [] then [(Writeln, f_msg n msg)] else l) ctxt) in
                                 if list_ex (\<lambda>(Error, _) \<Rightarrow> True | _ \<Rightarrow> False) l then l else [])
                                \<open> error(s)\<close>)]) ]"

definition "print_ctxt_pre_post_interp = (\<lambda>(sorry, dirty) name ctxt e_name e_pre e_post.
  let a = \<lambda>f x. Expr_app f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; f = \<lambda>(pref, e). List.foldr Expr_lambda (make_ctxt_free_var pref ctxt) e
    ; lg = length (Ctxt_fun_ty_arg ctxt) in
  if (sorry = Some Gen_sorry | sorry = None & dirty) & lg \<le> 3 then
    Some (O.interpretation
      (Interpretation
        name
        (\<open>contract\<close> @@ nat_of_str lg)
        [ e_name
        , f e_pre
        , f e_post ]
        (*apply(unfold_locales, simp only: dot__aaa_Person Let_def, auto)*)
        C.sorry))
  else
    None (* not yet implemented *))"

definition "print_ctxt_pre_post = (\<lambda>f. map_prod List_flatten id o f) o fold_list (\<lambda>x ocl. (x ocl, ocl)) o (\<lambda> ctxt. 
 let ty_name = ty_obj_to_string (Ctxt_ty ctxt) in
 List_flatten (List_map (\<lambda> (l_ctxt, ctxt).
  let (l_pre, l_post) = List.partition (\<lambda> (OclCtxtPre, _) \<Rightarrow> True | _ \<Rightarrow> False) l_ctxt
    ; attr_n = Ctxt_fun_name ctxt
    ; a = \<lambda>f x. Expr_app f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; var_tau = \<open>\<tau>\<close>
    ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) \<open>\<Turnstile>\<close> (Expr_warning_parenthesis s))
    ; expr_binop0 = \<lambda>base u_and. \<lambda> [] \<Rightarrow> b base | l \<Rightarrow> Expr_parenthesis (expr_binop u_and l)
    ; to_s = \<lambda>pref f_to l_pre.
        Expr_parenthesis (expr_binop0 \<open>true\<close> \<open>and\<close>
          (List_map
             (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l nb_var = length (make_ctxt_free_var pref ctxt) in
              (\<lambda>(_, expr) \<Rightarrow>
                 cross_abs (\<lambda>_. id) nb_var (case f_to expr of T_pure expr \<Rightarrow> expr))) l_pre))
    ; f = \<lambda> (var_at_when_hol, var_at_when_ocl).
        let dot_expr = \<lambda>e f_escape. Expr_postunary e (b (mk_dot_par_gen (flatten [\<open>.\<close>, attr_n, var_at_when_ocl]) (List_map (f_escape o fst) (Ctxt_fun_ty_arg ctxt)))) in
        (\<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>aocl.
            let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_r = var_result
              ; expr = 
              Expr_rewrite
                (dot_expr (Expr_annot_ocl (b var_self) ty_name) id)
                \<open>\<equiv>\<close>
                (Expr_lambda var_tau
                  (a \<open>Eps\<close> (Expr_lambda var_r
                                        (Expr_app \<open>Let\<close>
                                          [ Expr_lambda \<open>_\<close> (b var_r)
                                          , Expr_lambda var_result
                                                        (Expr_parenthesis (Expr_if_then_else (expr_binop0 \<open>True\<close> \<open>\<and>\<close> (f_tau (a \<open>\<delta>\<close> (b var_self)) # List_map (\<lambda>s. f_tau (a \<open>\<upsilon>\<close> (b (fst s)))) (Ctxt_fun_ty_arg ctxt)))
                                                                                             (Expr_binop
                                                                                               (f_tau (to_s OclCtxtPre (print_ctxt_to_ocl_pre ocl) l_pre))
                                                                                               \<open>\<and>\<close>
                                                                                               (f_tau (to_s OclCtxtPost (print_ctxt_to_ocl_post ocl) l_post)))
                                                                                             (f_tau (Expr_rewrite (b var_result) \<open>\<triangleq>\<close> (b \<open>invalid\<close>)))))]))))
              ; (name0, def) =
                 (if 
                    List.fold (\<lambda> (_, T_pure t) \<Rightarrow> \<lambda> b \<Rightarrow>
                                 b | P.fold_Const (\<lambda> b s. b | (case print_ctxt_to_ocl_gen_split s of
                                                               None \<Rightarrow> False
                                                             | Some s \<Rightarrow> 
                                                                 let f_eq = \<lambda>a. String_to_list (print_ctxt_const_name attr_n a None) = s in
                                                                 f_eq var_at_when_hol_post | f_eq var_at_when_hol_pre))
                                                False
                                                t)
                              l_ctxt
                              False
                  then
                    ( print_ctxt_pre_post_name attr_n var_at_when_hol
                    , O.axiom (Axiomatization (print_ctxt_pre_post_name attr_n var_at_when_hol (Some ty_name)) expr))
                  else
                    ( print_ctxt_const_name attr_n var_at_when_hol
                    , O.defs_overloaded (Defs_overloaded (print_ctxt_const_name attr_n var_at_when_hol (Some ty_name)) expr)))
              ; name = name0 (Some ty_name) in
            def
            # O.thm (Thm [T.thm name])
            # (case let name = name0 None in
                    print_ctxt_pre_post_interp
                      (D_output_sorry_dirty ocl)
                      name
                      ctxt
                      (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l v = b var_self in
                       Expr_lambdas0 (Expr_annot_ocl v ty_name) (a name v))
                      (OclCtxtPre, to_s OclCtxtPre (print_ctxt_to_ocl_pre ocl) l_pre)
                      (OclCtxtPost, to_s OclCtxtPost (print_ctxt_to_ocl_post ocl) l_post) of
                 None \<Rightarrow> []
               | Some x \<Rightarrow> [x]))
        # (\<lambda>\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>aocl. 
            List_flatten (fst (fold_class (\<lambda>_ name _ _ _ _.
              Pair (if String_equal ty_name name then
                      []
                    else
                      let var_x = \<open>x\<close>
                        ; f_escape = \<lambda>s. var_x @@ isub_of_str s in
                      [ O.defs_overloaded
                          (Defs_overloaded (flatten [ \<open>dot\<close>, isup_of_str attr_n, var_at_when_hol, \<open>_\<close>, name])
                                           (Expr_rewrite
                                             (dot_expr (Expr_annot_ocl (b var_x) name) f_escape)
                                             \<open>\<equiv>\<close>
                                             (dot_expr (Expr_postunary (b var_x) (b (dot_astype ty_name))) f_escape))) ]))
                  ()
                  (case D_input_class ocl of Some class_spec \<Rightarrow> class_spec))))
        # raise_ml_unbound
          (\<lambda>n pref. flatten [\<open>(\<close>, natural_of_str (n + 1), \<open>) \<close>, if pref = OclCtxtPre then \<open>pre\<close> else \<open>post\<close>])
          l_ctxt in
  f (var_at_when_hol_post, var_at_when_ocl_post))
  (rev (fold_pre_post (\<lambda> l c. Cons (List_map (map_prod id snd) l, c)) ctxt []))))"

definition "print_ctxt_inv = (\<lambda>f. map_prod List_flatten id o f) o fold_list (\<lambda>x ocl. (x ocl, ocl)) o List_flatten o List_flatten o (\<lambda> ctxt.
  let a = \<lambda>f x. Expr_app f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; f_tau = \<lambda>s. Expr_lam \<open>\<tau>\<close> (\<lambda>var_tau. Expr_warning_parenthesis (Expr_binop (b var_tau) \<open>\<Turnstile>\<close> s))
    ; nb_var = length (Ctxt_param ctxt)
    ; Ctxt_ty_n = ty_obj_to_string (Ctxt_ty ctxt)
    ; l = fold_invariant' ctxt in

 List_map (\<lambda> (tit, T_pure t) \<Rightarrow>
    (List_map
      (\<lambda> (allinst_at_when, var_at_when, e) \<Rightarrow>
        [ (\<lambda>ocl. [ O.definition_hol
                     (Definition (Expr_rewrite
                                   (b (print_ctxt_inv_name Ctxt_ty_n tit var_at_when))
                                   \<open>=\<close>
                                   (f_tau (cross_abs (\<lambda>s x. Expr_app var_OclForall_set
                                                              [ a allinst_at_when (b Ctxt_ty_n)
                                                              , Expr_lambda s x])
                                                     (Suc nb_var (* nb_var + \<open>self\<close> *))
                                                     (case e ocl of T_pure e \<Rightarrow> e)) )))]) ])
      [(\<open>OclAllInstances_at_pre\<close>, var_at_when_hol_pre, \<lambda>ocl. print_ctxt_to_ocl_pre ocl (T_pure t))
      ,(\<open>OclAllInstances_at_post\<close>, var_at_when_hol_post, \<lambda>ocl. print_ctxt_to_ocl_post ocl (T_pure t))])
  @@@@ [raise_ml_unbound (\<lambda>_ pref. flatten [\<open>inv \<close>, pref]) l])
    l)"

definition "print_ctxt_thm ctxt = Pair
 (case List_flatten (List_map (\<lambda>(tit, _). List_map (hol_definition o print_ctxt_inv_name (ty_obj_to_string (Ctxt_ty ctxt)) tit)
                                                   [ var_at_when_hol_pre
                                                   , var_at_when_hol_post ])
                              (fold_invariant' ctxt)) of 
    [] \<Rightarrow> []
  | l \<Rightarrow> [ O.thm (Thm (List_map T.thm l)) ])"

end
