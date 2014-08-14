(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_parser_init.thy ---
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

theory  OCL_compiler_parser_init
imports OCL_compiler_init
begin

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
definition "co13 f g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 = f (g x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)"

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
definition "ap13 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, f12 v12, f13 v13]"

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
definition "ar13 a v0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 z = a v0 [f1 v1, f2 v2, f3 v3, f4 v4, f5 v5, f6 v6, f7 v7, f8 v8, f9 v9, f10 v10, f11 v11, f12 v12, z]"

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

definition "i_of_internal_oid a b = internal_oid_rec
  (ap1 a (b ''Oid'') (i_of_nat a b))"

definition "i_of_internal_oids a b = internal_oids_rec
  (ap3 a (b ''Oids'')
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_nat a b))"

end

lemmas [code] =
  i_of.i_of_pair_def
  i_of.i_of_list_def
  i_of.i_of_option_def
  (* *)
  i_of.i_of_internal_oid_def
  i_of.i_of_internal_oids_def

end
