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

theory C_Command
  imports C_Annotation
  keywords "C" :: thy_decl % "ML"
       and "C_file" :: thy_load % "ML"
       and "C_export" :: thy_decl % "ML"
       and "C_prf" :: prf_decl % "proof"  (* FIXME % "ML" ?? *)
       and "C_val" "C_dump" :: diag % "ML"
begin

section \<open>The Global C11-Module State\<close>

ML\<open>
structure C_Context' = struct

fun accept env_lang (_, (res, _, _)) =
  (fn context =>
    ( Context.theory_name (Context.theory_of context)
    , (res, #stream_ignored env_lang |> rev))
    |> Symtab.update_list (op =)
    |> C11_core.map_tab
    |> (fn map_tab => C11_core.Data.map map_tab context))
  |> C_Env.map_context

val eval_source =
  C_Context.eval_source
    C_Env.empty_env_lang
    (fn _ => fn _ => fn pos => fn _ =>
      error ("Parser: No matching grammar rule" ^ Position.here pos))
    accept
end
\<close>

section \<open>The Isar Binding to the C11 Interface.\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Pure.thy
    Author:     Makarius

The Pure theory, with definitions of Isar commands and some lemmas.
*)

subsection \<open>\<close>

ML\<open>
structure C_Outer_Parse =
struct
  val C_source = Parse.input (Parse.group (fn () => "C source") Parse.text)
end
\<close>

ML\<open>
structure C_Outer_Syntax =
struct

fun C_prf source =
  Proof.map_context (Context.proof_map (ML_Context.exec (fn () => C_Context'.eval_source source)))
  #> Proof.propagate_ml_env

fun C_export source context =
  context
  |> ML_Env.set_bootstrap true
  |> ML_Context.exec (fn () => C_Context'.eval_source source)
  |> ML_Env.restore_bootstrap context
  |> Local_Theory.propagate_ml_env

fun C source =
  ML_Context.exec (fn () => C_Context'.eval_source source)
  #> Local_Theory.propagate_ml_env

fun C' err env_lang src =
  C_Env.empty_env_tree
  #> C_Context.eval_source'
       env_lang
       err
       C_Context'.accept
       src
  #> (fn {context, reports_text} => Stack_Data_Tree.map (append reports_text) context)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C\<close> ""
    (C_Outer_Parse.C_source >> (Toplevel.generic_theory o C));

end
\<close>

ML\<open>
structure C_Outer_Isar_Cmd =
struct
(* diagnostic ML evaluation *)

structure Diag_State = Proof_Data
(
  type T = Toplevel.state;
  fun init _ = Toplevel.toplevel;
);

fun C_diag source state =
  let
    val opt_ctxt =
      try Toplevel.generic_theory_of state
      |> Option.map (Context.proof_of #> Diag_State.put state);
  in Context.setmp_generic_context (Option.map Context.Proof opt_ctxt)
    (fn () => C_Context'.eval_source source) () end;

val diag_state = Diag_State.get;
val diag_goal = Proof.goal o Toplevel.proof_of o diag_state;

val _ = Theory.setup
  (ML_Antiquotation.value (Binding.qualify true "Isar" \<^binding>\<open>C_state\<close>)
    (Scan.succeed "C_Outer_Isar_Cmd.diag_state ML_context") #>
   ML_Antiquotation.value (Binding.qualify true "Isar" \<^binding>\<open>C_goal\<close>)
    (Scan.succeed "C_Outer_Isar_Cmd.diag_goal ML_context"));

end
\<close>

ML\<open>
structure C_Outer_File =
struct

fun command0 ({src_path, lines, digest, pos}: Token.file) =
  let
    val provide = Resources.provide (src_path, digest);
  in I
    #> C_Outer_Syntax.C (Input.source true (cat_lines lines) (pos, pos))
    #> Context.mapping provide (Local_Theory.background_theory provide)
  end;

fun command files gthy =
  command0 (hd (files (Context.theory_of gthy))) gthy;

end;
\<close>

subsection \<open>Reading and Writing C-Files\<close>

ML\<open>
local

val semi = Scan.option \<^keyword>\<open>;\<close>;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_file\<close> "read and evaluate Isabelle/C file"
    (Resources.parse_files "C_file" --| semi >> (Toplevel.generic_theory o C_Outer_File.command));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_export\<close>
    "C text within theory or local theory, and export to bootstrap environment"
    (C_Outer_Parse.C_source >> (Toplevel.generic_theory o C_Outer_Syntax.C_export));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_prf\<close> "C text within proof"
    (C_Outer_Parse.C_source >> (Toplevel.proof o C_Outer_Syntax.C_prf));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_val\<close> "diagnostic C text"
    (C_Outer_Parse.C_source >> (Toplevel.keep o C_Outer_Isar_Cmd.C_diag));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_dump\<close> "diagnostic C text"
    (C_Outer_Parse.C_source >> (Toplevel.keep o C_Outer_Isar_Cmd.C_diag));   (* HACK: TO BE DONE *)

in end\<close>

end
