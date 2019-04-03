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

theory "C_Main"
  imports "src/C_Annotation"
  keywords "C" :: thy_decl
       and "C_import" :: thy_load % "ML"
       and "C_export" :: thy_load % "ML"
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

ML\<open>

structure C_Outer_Syntax =
struct

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
  Outer_Syntax.command @{command_keyword C} ""
    (Parse.input (Parse.group (fn () => "C source") Parse.text)
     >> (Toplevel.generic_theory o C));
end
\<close>

section \<open>The Command @{command C_import}\<close>

ML\<open>

structure C_File =
struct

fun command0 ({src_path, lines, digest, pos}: Token.file) =
  let
    val provide = Resources.provide (src_path, digest);
  in I
    #> C_Outer_Syntax.C (Input.source true (cat_lines lines) (pos, pos))
    #> Context.mapping provide (Local_Theory.background_theory provide)
  end;

fun command files =
  Toplevel.generic_theory
    (fn gthy => command0 (hd (files (Context.theory_of gthy))) gthy);

end;
\<close>

section \<open>Reading and Writing C-Files\<close>

ML\<open>
local

val semi = Scan.option @{keyword ";"};

val _ =
  Outer_Syntax.command @{command_keyword C_import} "read and evaluate C file"
    (Resources.parse_files "C_file" --| semi >> C_File.command);

val _ =
  Outer_Syntax.command @{command_keyword C_export} "read and evaluate C file"
    (Resources.parse_files "C_file" --| semi >> C_File.command);   (* HACK: TO BE DONE *)


in end
\<close>

section \<open>ML-Antiquotations for Debugging\<close>

ML\<open>
fun print_top make_string f _ (_, (value, pos1, pos2)) _ thy =
  let
    val () = writeln (make_string value)
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
  in f thy end

fun print_top' _ f _ (_, (_, pos1, pos2)) env thy =
  let
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
    val () = writeln ("ENV " ^ C_Env.string_of env)
  in f thy end

fun print_stack s make_string stack _ _ thy =
  let
    val () = warning ("SHIFT  " ^ (case s of NONE => "" | SOME s => "\"" ^ s ^ "\" ") ^ Int.toString (length stack - 1) ^ "    +1 ")
    val () = stack
          |> split_list
          |> #2
          |> map_index I
          |> app (fn (i, (value, pos1, pos2)) => writeln ("   " ^ Int.toString (length stack - i) ^ " " ^ make_string value ^ " " ^ Position.here pos1 ^ " " ^ Position.here pos2))
  in thy end

fun print_stack' s _ stack _ env thy =
  let
    val () = warning ("SHIFT  " ^ (case s of NONE => "" | SOME s => "\"" ^ s ^ "\" ") ^ Int.toString (length stack - 1) ^ "    +1 ")
    val () = writeln ("ENV " ^ C_Env.string_of env)
  in thy end
\<close>

setup \<open>ML_Antiquotation.inline @{binding print_top}
                               (Args.context >> K ("print_top " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_top'}
                               (Args.context >> K ("print_top' " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_stack}
                               (Scan.peek (fn _ => Scan.option Args.text) >> (fn name => ("print_stack " ^ (case name of NONE => "NONE" | SOME s => "(SOME \"" ^ s ^ "\")") ^ " " ^ ML_Pretty.make_string_fn)))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_stack'}
                               (Scan.peek (fn _ => Scan.option Args.text) >> (fn name => ("print_stack' " ^ (case name of NONE => "NONE" | SOME s => "(SOME \"" ^ s ^ "\")") ^ " " ^ ML_Pretty.make_string_fn)))\<close>

end
