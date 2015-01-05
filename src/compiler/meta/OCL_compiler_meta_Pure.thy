(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_meta_Pure.thy ---
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

theory  OCL_compiler_meta_Pure
imports "../OCL_compiler_init"
begin

section{* \text{Lambda\_pure} Meta-Model aka. AST definition of \text{Lambda\_pure} *}

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

fun_quick fold_Free where
   "fold_Free f accu expr = (\<lambda> PureFree s ty \<Rightarrow> f accu s 
                        | PureAbs _ _ term \<Rightarrow> fold_Free f accu term
                        | PureApp term1 term2 \<Rightarrow> fold_Free f (fold_Free f accu term1) term2
                        | _ \<Rightarrow> accu)
                        expr"

fun_quick cross_abs_aux where
   "cross_abs_aux l x = (\<lambda> (Suc n, PureAbs s _ t) \<Rightarrow> cross_abs_aux (s # l) (n, t)
                         | (_, e) \<Rightarrow> (l, e))
                         x"

definition "cross_abs n l = cross_abs_aux [] (n, l)"

end
