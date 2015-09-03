(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer_SML.thy ---
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

theory  OCL_compiler_printer_SML
imports OCL_compiler_meta_SML
        OCL_compiler_printer_oid
begin


subsection{* s of ... *} (* s_of *)

context s_of
begin

definition "s_of_val_fun = (\<lambda> Sval \<Rightarrow> \<open>val\<close>
                            | Sfun \<Rightarrow> \<open>fun\<close>)"

fun' s_of_sexpr where \<open>s_of_sexpr e = (\<lambda>
    SML_string s \<Rightarrow> sprint1 \<open>"%s"\<close>\<acute> (To_string (escape_sml s))
  | SML_rewrite val_fun e1 symb e2 \<Rightarrow> sprint4 \<open>%s %s %s %s\<close>\<acute> (s_of_val_fun val_fun) (s_of_sexpr e1) (To_string symb) (s_of_sexpr e2)
  | SML_basic l \<Rightarrow> sprint1 \<open>%s\<close>\<acute> (String_concat \<open> \<close> (L.map To_string l))
  | SML_oid tit s \<Rightarrow> sprint2 \<open>%s%d\<close>\<acute> (To_string tit) (To_oid s)
  | SML_binop e1 s e2 \<Rightarrow> sprint3 \<open>%s %s %s\<close>\<acute> (s_of_sexpr e1) (s_of_sexpr (SML_basic [s])) (s_of_sexpr e2)
  | SML_annot e s \<Rightarrow> sprint2 \<open>(%s:%s)\<close>\<acute> (s_of_sexpr e) (To_string s)
  | SML_function l \<Rightarrow> sprint1 \<open>(fn %s)\<close>\<acute> (String_concat \<open>
    | \<close> (List.map (\<lambda> (s1, s2) \<Rightarrow> sprint2 \<open>%s => %s\<close>\<acute> (s_of_sexpr s1) (s_of_sexpr s2)) l))
  | SML_apply s l \<Rightarrow> sprint2 \<open>(%s %s)\<close>\<acute> (To_string s) (String_concat \<open> \<close> (List.map (\<lambda> e \<Rightarrow> sprint1 \<open>(%s)\<close>\<acute> (s_of_sexpr e)) l))
  | SML_paren p_left p_right e \<Rightarrow> sprint3 \<open>%s%s%s\<close>\<acute> (To_string p_left) (s_of_sexpr e) (To_string p_right)
  | SML_let_open s e \<Rightarrow> sprint2 \<open>let open %s in %s end\<close>\<acute> (To_string s) (s_of_sexpr e)) e\<close>

end

lemmas [code] =
  (* def *)
  s_of.s_of_val_fun_def
  (* fun *)
  s_of.s_of_sexpr.simps

end
