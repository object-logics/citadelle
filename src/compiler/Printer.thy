(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Printer.thy ---
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

theory  Printer
imports Core
        "meta/Printer_META"
begin

section{* Generation to Deep Form: OCaml *}

subsection{* conclusion *}

definition "List_iterM f l =
  List.fold (\<lambda>x m. bind m (\<lambda> () \<Rightarrow> f x)) l (return ())"

context Print
begin
definition "write_file ocl = (
  let (l_thy, Sys_argv) = compiler_env_config.more ocl
    ; (is_file, f_output) = case (D_output_header_thy ocl, Sys_argv)
     of (Some (file_out, _), Some dir) \<Rightarrow>
          let dir = To_string dir in
          (True, \<lambda>f. bind (Sys_is_directory2 dir) (\<lambda> Sys_is_directory2_dir.
                     out_file1 f (if Sys_is_directory2_dir then sprint2 \<open>%s/%s.thy\<close>\<acute> dir (To_string file_out) else dir)))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iterM (fprintf1 \<open>%s
\<close>                             )
        (let\<^sub>O\<^sub>C\<^sub>a\<^sub>m\<^sub>l (ocl, l) =
           fold_thy'
             (\<lambda>f. f ())
             (\<lambda>_ _. [])
             (\<lambda>x acc1 acc2. (acc1, Cons x acc2))
             l_thy
             (compiler_env_config.truncate ocl, []) in
         s_of_thy_list (compiler_env_config_more_map (\<lambda>_. is_file) ocl) (rev l))))"
end

definition "write_file = Print.write_file (String.implode o String.to_list) (ToNat integer_of_natural)"

lemmas [code] =
  (* def *)
  Print.write_file_def

  (* fun *)

section{* ... *}  (* garbage collection of aliases *)

no_type_notation natural ("nat")
no_type_notation abr_string ("string")

end
