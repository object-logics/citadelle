(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Floor1_enum.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ Paris Sud, France
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

theory  Floor1_enum
imports Core_init
begin

section{* Translation of AST *}

definition "print_enum = (\<lambda> OclEnum name_ty l \<Rightarrow> Pair
 (let a = \<lambda>f x. Expr_app f [x]
    ; b = \<lambda>s. Expr_basic [s]
    ; option = Ty_apply_paren \<open>\<langle>\<close> \<open>\<rangle>\<^sub>\<bottom>\<close>
    ; name_ty_base = name_ty @@ String.isub \<open>base\<close>
    ; name_ty_base' = pref_generic_enum name_ty
    ; uu = \<open>'\<AA>\<close> in
  L.flatten
  [ [ O.datatype (Datatype (pref_ty_enum name_ty) (L.map (\<lambda>constr. (pref_constr_enum constr, [])) l))
    , O.type_synonym (Type_synonym' name_ty_base (option (option (Ty_base (pref_ty_enum name_ty)))))
    , O.type_synonym (Type_synonym'' name_ty_base' [uu] (\<lambda> [u] \<Rightarrow> Ty_apply (Ty_base \<open>val\<close>) [Ty_base u, Ty_base name_ty_base]))
    , O.defs
        (Defs_overloaded
          (\<open>StrictRefEq\<close> @@ String.isub name_ty)
          (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l var_x = \<open>x\<close>
             ; var_y = \<open>y\<close> in
           Expr_rewrite
            (Expr_rewrite (Expr_annot (b var_x) (Ty_apply (Ty_base name_ty_base') [Ty_base uu])) \<open>\<doteq>\<close> (b var_y))
            \<open>\<equiv>\<close>
            (Expr_lam \<open>\<tau>\<close>
              (\<lambda>var_tau.
                Expr_if_then_else
                  (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l f = \<lambda>v. Expr_rewrite (Expr_applys (a \<open>\<upsilon>\<close> (b v)) [b var_tau]) \<open>=\<close> (a \<open>true\<close> (b var_tau)) in
                   Expr_binop (f var_x) \<open>\<and>\<close> (f var_y))
                  (Expr_applys (Expr_rewrite (b var_x) \<open>\<triangleq>\<close> (b var_y)) [b var_tau])
                  (a \<open>invalid\<close> (b var_tau)))))) ]
  , L.map
      (\<lambda>constr.
        O.definition
          (Definition (Expr_rewrite (b constr)
                                    \<open>=\<close>
                                    (Expr_lam \<open>_\<close> (\<lambda>_. Expr_some (Expr_some (Expr_annot' (b (pref_constr_enum constr)) (pref_ty_enum name_ty)))))))) l ]))"

end
