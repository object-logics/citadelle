(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor2_ctxt.thy ---
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

theory  OCL_compiler_floor2_ctxt
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* context2 *}

(* (* ERROR this lambda term type-checks expensively *)
definition "print_ctxt_is_accessor =
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
definition "print_ctxt_is_name_at_gen var s =
 (case var of _ # _ \<Rightarrow>
    let lg_var = length var in
    if List_take_last lg_var s = var then
      Some (List_take_first (length s - lg_var) s)
    else
      None)"

definition "print_ctxt_is_name_at_pre = print_ctxt_is_name_at_gen var_at_when_hol_pre"
definition "print_ctxt_is_name_at_post = (case var_at_when_hol_post of [] \<Rightarrow>
  \<lambda>s. case print_ctxt_is_name_at_pre s of None \<Rightarrow> Some s
                                        | _ \<Rightarrow> None)"

definition "print_ctxt_to_ocl_gen l_access f var = (\<lambda> T_pure t \<Rightarrow>
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

definition "print_ctxt_to_ocl_pre ocl = print_ctxt_to_ocl_gen (snd (D_accessor_rbt ocl)) print_ctxt_is_name_at_post var_at_when_hol_pre"
definition "print_ctxt_to_ocl_post ocl = print_ctxt_to_ocl_gen (fst (D_accessor_rbt ocl)) print_ctxt_is_name_at_pre var_at_when_hol_post"

definition "axiom_unbound ax_name ax_body f_msg ctxt = 
        [ (\<lambda>ocl. Thy_axiom (Axiom ax_name (ax_body ocl)))
        , (\<lambda>_. Thy_ml (raise_ml (bug_ocaml_extraction
                                (let l = flatten (List_mapi (\<lambda> n. \<lambda>(msg, T_pure t) \<Rightarrow> 
                                            let l = 
                                              rev (fold_Free (\<lambda>l s. 
                                                (Error, flatten [f_msg n msg, '': unbound value '', s]) # l) [] t) in
                                            if l = [] then [(Writeln, f_msg n msg)] else l) ctxt) in
                                 if list_ex (\<lambda>(Error, _) \<Rightarrow> True | _ \<Rightarrow> False) l then l else []))
                                '' error(s)'')) ]"

definition "print_ctxt_pre_post = fold_list (\<lambda>x ocl. (x ocl, ocl)) o (\<lambda> ctxt.
  let (l_pre, l_post) = List.partition (\<lambda> (OclCtxtPre, _) \<Rightarrow> True | _ \<Rightarrow> False) (Ctxt_expr ctxt)
    ; attr_n = Ctxt_fun_name ctxt
    ; a = \<lambda>f x. Expr_apply f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; var_tau = unicode_tau
    ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) unicode_Turnstile (Expr_warning_parenthesis s))
    ; expr_binop = \<lambda>s_op. \<lambda> [] \<Rightarrow> b ''True'' | l \<Rightarrow> Expr_parenthesis (expr_binop s_op l)
    ; to_s = \<lambda>pref f_to l_pre. 
        expr_binop unicode_and
          (bug_ocaml_extraction
          (List_map
             (bug_ocaml_extraction
             (let nb_var = length (make_ctxt_free_var pref ctxt) in
              (\<lambda>(_, expr) \<Rightarrow> 
               f_tau (bug_ocaml_extraction
                     (let (l, expr) = cross_abs nb_var (case f_to expr of T_pure expr \<Rightarrow> expr) in
                      Expr_inner0 l expr))))) l_pre))
    ; f = \<lambda> (var_at_when_hol, var_at_when_ocl).
        axiom_unbound (print_ctxt_pre_post_name attr_n var_at_when_hol)
          (\<lambda>ocl. Expr_rewrite
              (Expr_parenthesis (f_tau (Expr_rewrite
                  (Expr_postunary (b var_self) (b (mk_dot_par_gen (flatten [''.'', attr_n, var_at_when_ocl]) (List_map fst (Ctxt_fun_ty_arg ctxt)))))
                  unicode_triangleq
                  (b var_result))))
              ''=''
              (Expr_parenthesis (Expr_if_then_else
                (f_tau (a unicode_delta (b var_self)))
                (Expr_warning_parenthesis (Expr_binop
                  (to_s OclCtxtPre (print_ctxt_to_ocl_pre ocl) l_pre)
                  unicode_longrightarrow
                  (to_s OclCtxtPost (print_ctxt_to_ocl_post ocl) l_post)))
                (f_tau (Expr_rewrite (b var_result) unicode_triangleq (b ''invalid''))))))
          (\<lambda>n pref. flatten [''('', natural_of_str (n + 1), '') '', if pref = OclCtxtPre then ''pre'' else ''post''])
          (Ctxt_expr ctxt) in
  f (var_at_when_hol_post, var_at_when_ocl_post))"

definition "print_ctxt_inv = fold_list (\<lambda>x ocl. (x ocl, ocl)) o flatten o flatten o (\<lambda> ctxt.
  let a = \<lambda>f x. Expr_apply f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; var_tau = unicode_tau
    ; f_tau = \<lambda>s. Expr_warning_parenthesis (Expr_binop (b var_tau) unicode_Turnstile s) in
  List_map (\<lambda> (tit, e) \<Rightarrow>
    List_map (\<lambda> (allinst_at_when, var_at_when, e) \<Rightarrow>
        axiom_unbound (print_ctxt_inv_name (Ctxt_inv_ty ctxt) tit var_at_when)
          (\<lambda>ocl. f_tau (Expr_apply var_OclForall_set
              [ a allinst_at_when (b (Ctxt_inv_ty ctxt))
              , Expr_inner (case e ocl of T_pure e \<Rightarrow> e)]))
          (\<lambda>_ pref. flatten [''inv '', pref])
          (Ctxt_inv_expr ctxt))
      [(''OclAllInstances_at_pre'', var_at_when_hol_pre, \<lambda>ocl. print_ctxt_to_ocl_pre ocl e)
      ,(''OclAllInstances_at_post'', var_at_when_hol_post, \<lambda>ocl. print_ctxt_to_ocl_post ocl e)])
    (Ctxt_inv_expr ctxt))"

end
