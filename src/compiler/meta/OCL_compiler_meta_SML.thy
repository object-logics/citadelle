(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_SML.thy ---
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

theory  OCL_compiler_meta_SML
imports OCL_compiler_meta_oid
begin

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

section{* ... *}

definition "Sexpr_none = Sexpr_basic [''NONE'']"
definition "Sexpr_some s = Sexpr_apply ''SOME'' [s]"
definition "Sexpr_option' f l = (case Option.map f l of None \<Rightarrow> Sexpr_none | Some s \<Rightarrow> Sexpr_some s)"
definition "Sexpr_option = Sexpr_option' id"
definition "Sexpr_parenthesis (* mandatory parenthesis *) = Sexpr_paren ''('' '')''"
definition "sexpr_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Sexpr_binop x s) xs x)"
definition "Sexpr_list l = (case l of [] \<Rightarrow> Sexpr_basic [''[]''] | _ \<Rightarrow> Sexpr_paren ''['' '']'' (sexpr_binop '','' l))"
definition "Sexpr_list' f l = Sexpr_list (List_map f l)"
definition "Sexpr_pair e1 e2 = Sexpr_parenthesis (Sexpr_binop e1 '','' e2)"
definition "Sexpr_pair' f1 f2 = (\<lambda> (e1, e2) \<Rightarrow> Sexpr_parenthesis (Sexpr_binop (f1 e1) '','' (f2 e2)))"

end
