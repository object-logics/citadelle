(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_printer.thy ---
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

theory  OCL_compiler_printer
imports OCL_compiler_core
        "meta/OCL_compiler_printer_META"
begin

section{* Generation to Deep Form: OCaml *}

subsection{* conclusion *}

definition "List_iterM f l =
  List.fold (\<lambda>x m. bind m (\<lambda> () \<Rightarrow> f x)) l (return ())"

context s_of
begin
definition "write_file ocl = (
  let (l_thy, Sys_argv) = ocl_compiler_config.more ocl
    ; (is_file, f_output) = case (D_file_out_path_dep ocl, Sys_argv)
     of (Some (file_out, _), Some dir) \<Rightarrow>
          let dir = To_string dir in
          (True, \<lambda>f. bind (Sys_is_directory2 dir) (\<lambda> Sys_is_directory2_dir.
                     out_file1 f (if Sys_is_directory2_dir then sprintf2 (STR ''%s/%s.thy'') dir (To_string file_out) else dir)))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iterM (fprintf1 (STR ''%s
''                                 ))
        (bug_ocaml_extraction (let (ocl, l) =
           fold_thy'
             (\<lambda>f. f ())
             (\<lambda>_ _. [])
             (\<lambda>x acc1 acc2. (acc1, Cons x acc2))
             l_thy
             (ocl_compiler_config.truncate ocl, []) in
         s_of_thy_list (ocl_compiler_config_more_map (\<lambda>_. is_file) ocl) (rev l)))))"
end

definition "write_file = s_of.write_file implode (ToNat integer_of_natural)"

lemmas [code] =
  (* def *)
  s_of.write_file_def

  (* fun *)

end
