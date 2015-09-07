(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Meta_Pure.thy ---
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

section{* \text{Lambda\_pure} Meta-Model aka. AST definition of \text{Lambda\_pure} *}

theory  Meta_Pure
imports "../Init"
begin

subsection{* Type Definition *}

datatype pure_indexname = Pure_Indexname string nat
datatype pure_class = Pure_Class string
datatype pure_sort = Pure_Sort "pure_class list"
datatype pure_typ =
  Pure_Type string "pure_typ list" |
  Pure_TFree string pure_sort |
  Pure_TVar pure_indexname pure_sort
datatype pure_term =
  Pure_Const string pure_typ |
  Pure_Free string pure_typ |
  Pure_Var pure_indexname pure_typ |
  Pure_Bound nat |
  Pure_Abs string pure_typ pure_term |
  Pure_App pure_term pure_term (infixl "$" 200)

subsection{* Fold, Map, etc. on Pure Terms.*}

locale P
begin (* TODO move datatypes in the locale (when terminations will not be needed to be proved by hand anymore) *)
definition "Const = Pure_Const"
definition "Free = Pure_Free"
definition "Var = Pure_Var"
definition "Bound = Pure_Bound"
definition "Abs = Pure_Abs"
definition "App = Pure_App"

fun map_Const where
   "map_Const f expr = (\<lambda> Pure_Const s ty \<Rightarrow> Const (f s ty) ty
                        | Pure_Free s ty \<Rightarrow> Free s ty
                        | Pure_Var i ty \<Rightarrow> Var i ty
                        | Pure_Bound n \<Rightarrow> Bound n
                        | Pure_Abs s ty term \<Rightarrow> Abs s ty (map_Const f term)
                        | Pure_App term1 term2 \<Rightarrow> App (map_Const f term1)
                                                         (map_Const f term2))
                        expr"

fun fold_Const where
   "fold_Const f accu expr = (\<lambda> Pure_Const s _ \<Rightarrow> f accu s 
                              | Pure_Abs _ _ term \<Rightarrow> fold_Const f accu term
                              | Pure_App term1 term2 \<Rightarrow> fold_Const f (fold_Const f accu term1) term2
                              | _ \<Rightarrow> accu)
                               expr"

fun fold_Free where
   "fold_Free f accu expr = (\<lambda> Pure_Free s _ \<Rightarrow> f accu s 
                             | Pure_Abs _ _ term \<Rightarrow> fold_Free f accu term
                             | Pure_App term1 term2 \<Rightarrow> fold_Free f (fold_Free f accu term1) term2
                             | _ \<Rightarrow> accu)
                              expr"
end

lemmas [code] =
  (*def*)
  P.Const_def
  P.Free_def
  P.Var_def
  P.Bound_def
  P.Abs_def
  P.App_def

  (*fun*)
  P.map_Const.simps
  P.fold_Const.simps
  P.fold_Free.simps

end
