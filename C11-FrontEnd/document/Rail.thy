(******************************************************************************
 * Generation of Language.C Grammar with ML Interface Binding
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

(*<*)
theory Rail
  imports "../src/C_Command"
          "~~/src/Doc/Isar_Ref/Base"
begin
(*>*)

section \<open>Incorporating C code\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "C_file"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C_export_boot"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    @{command_def "C_prf"} & : & \<open>proof \<rightarrow> proof\<close> \\
    @{command_def "C_val"} & : & \<open>any \<rightarrow>\<close> \\
    @{command_def "C_export_file"} & : & \<open>any \<rightarrow>\<close> \\
  \end{matharray}
  \begin{tabular}{rcll}
    @{attribute_def C_lexer_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def C_parser_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def C_ML_verbose} & : & \<open>attribute\<close> & default \<open>true\<close> \\
    @{attribute_def C_propagate_env} & : & \<open>attribute\<close> & default \<open>false\<close> \\
  \end{tabular}

  @{rail \<open>
    @@{command C_file} @{syntax name} ';'?
    ;
    (@@{command C} | @@{command C_export_boot} | @@{command C_prf} |
      @@{command C_val} | @@{command C_export_file}) @{syntax text}
    ;
  \<close>}

  \<^descr> \<^theory_text>\<open>C_file name\<close> resembles to
  \<^theory_text>\<open>ML_file name\<close>: it reads the given C
  file, and let any attached semantic back-ends to proceed for further
  subsequent evaluation. Top-level C bindings are stored within the
  (global or local) theory context; the initial environment is set by
  default to be an empty one, or the one returned by a previous
  \<^theory_text>\<open>C_file\<close> (depending on @{attribute_def
    C_propagate_env}). Multiple \<^theory_text>\<open>C_file\<close>
  commands may be used to build larger C projects if they are all
  written in a single theory file (existing parent theories are
  ignored, and not affecting the current working theory).

  \<^descr> \<^theory_text>\<open>C\<close> is similar to
  \<^theory_text>\<open>C_file\<close>, but evaluates directly the
  given \<open>text\<close>. Top-level resulting bindings are stored
  within the (global or local) theory context.

  \<^descr> \<^theory_text>\<open>C_export_boot\<close> is similar to
  \<^theory_text>\<open>ML_export\<close>, except that the code in
  input is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_prf\<close> is similar to
  \<^theory_text>\<open>ML_prf\<close>, except that the code in input
  is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_val\<close> is similar to
  \<^theory_text>\<open>ML_val\<close>, except that the code in input
  is understood as being processed by
  \<^theory_text>\<open>C\<close> instead of \<^theory_text>\<open>ML\<close>.

  \<^descr> \<^theory_text>\<open>C_export_file\<close> dumps all
  existing previous C code to \<open>T.c\<close>, where
  \<open>T.thy\<close> is the name of the current working theory. The
  dump is actually restricted to \<open>T\<close> (parent theories are
  ignored).
\<close>

text \<open>

  \<^descr> @{attribute C_lexer_trace} indicates whether the list of C
  tokens associated to the source text should be output (that list is
  computed during the lexing phase).

  \<^descr> @{attribute C_parser_trace} indicates whether the stack
  forest of Shift-Reduce node should be output (it is the final stack
  which is printed, i.e., the one taken as soon as the parsing
  terminates).

  \<^descr> @{attribute C_ML_verbose} indicates whether nested
  \<^theory_text>\<open>ML\<close> commands are acting similarly as
  their default verbose configuration in top-level.

  \<^descr> @{attribute_def C_propagate_env} makes the start of a C
  command (e.g., \<^theory_text>\<open>C_file\<close>,
  \<^theory_text>\<open>C\<close>) initialized with the environment of
  the previous C command if existing.
\<close>

(*<*)
end
(*>*)
