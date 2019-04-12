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
  imports C_Eval
  keywords "C" :: thy_decl % "ML"
       and "C_file" :: thy_load % "ML"
       and "C_export" :: thy_decl % "ML"
       and "C_prf" :: prf_decl % "proof"  (* FIXME % "ML" ?? *)
       and "C_val" "C_dump" :: diag % "ML"
begin

section \<open>The Global C11-Module State\<close>

ML\<open>
structure C_Module =
struct

structure Data = Generic_Data
  (type T = ((C_Ast.CTranslUnit * C_Antiquote.antiq C_Env.stream) list * C_Env.env_lang) Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K false))

val get_global = Data.get o Context.Theory
val dest_list = Symtab.dest o get_global
fun get_module thy = the (Symtab.lookup (get_global thy) (Context.theory_name thy))
fun get_module'' context = Symtab.lookup (Data.get context)
                                         (Context.theory_name (Context.theory_of context))
val get_module' = the o get_module''

fun accept env_lang (_, (res, _, _)) =
  C_Env.map_context
    (fn context =>
      Data.map (Symtab.map_default
                 (Context.theory_name (Context.theory_of context), ([], env_lang))
                 (fn (xs, _) => (cons (res, #stream_ignored env_lang |> rev) xs, C_Env.map_stream_ignored (K []) env_lang)))
               context)

val eval_source =
  C_Context.eval_source
    (fn context => case (Config.get (Context.proof_of context) C_Options.propagate_env, get_module'' context)
                     of (true, SOME (_, env_lang)) => env_lang
                      | _ => C_Env.empty_env_lang)
    (fn _ => fn _ => fn pos => fn _ =>
      error ("Parser: No matching grammar rule" ^ Position.here pos))
    accept

fun C_prf source =
  Proof.map_context (Context.proof_map (ML_Context.exec (fn () => eval_source source)))
  #> Proof.propagate_ml_env

fun C_export source context =
  context
  |> ML_Env.set_bootstrap true
  |> ML_Context.exec (fn () => eval_source source)
  |> ML_Env.restore_bootstrap context
  |> Local_Theory.propagate_ml_env

fun C source =
  ML_Context.exec (fn () => eval_source source)
  #> Local_Theory.propagate_ml_env

fun C' err env_lang src =
  C_Env.empty_env_tree
  #> C_Context.eval_source'
       env_lang
       err
       accept
       src
  #> (fn {context, reports_text} => C_Stack.Data_Tree.map (append reports_text) context)
end
\<close>

section \<open>Definitions of Inner Directive Commands\<close>

ML\<open>
local
val _ =
  Theory.setup
  (Context.theory_map
    (C_Context.Directives.map
      (C_Context.directive_update ("define", \<^here>)
        (fn C_Lex.Define (_, C_Lex.Group1 ([], [tok3]), NONE, C_Lex.Group1 ([], toks)) =>
              (fn (env_dir, env_tree) =>
                ( NONE
                , []
                , let val name = C_Lex.content_of tok3
                      val id = serial ()
                      val pos = [C_Lex.pos_of tok3]
                  in
                    ( Symtab.update (name, (pos, id, toks)) env_dir
                    , C_Env.map_reports_text (C_Grammar_Rule_Lib.report pos (C_Context.markup_directive_define true false pos) (name, id))
                                             env_tree)
                  end))
          | C_Lex.Define (_, C_Lex.Group1 ([], [tok3]), SOME (C_Lex.Group1 (_ :: toks_bl, _)), _) =>
              tap (fn _ => (* not yet implemented *)
                           warning ("Ignored functional macro directive" ^ Position.here (Position.range_position (C_Lex.pos_of tok3, C_Lex.end_pos_of (List.last toks_bl)))))
              #> (fn env => (NONE, [], env))
          | _ => fn env => (NONE, [], env))
       #>
       C_Context.directive_update ("undef", \<^here>)
        (fn C_Lex.Undef (C_Lex.Group2 (_, _, [tok])) =>
              (fn (env_dir, env_tree) =>
                ( NONE
                , []
                , let val name = C_Lex.content_of tok
                      val pos1 = C_Lex.pos_of tok
                  in case Symtab.lookup env_dir name of
                       NONE => (env_dir, C_Env.map_reports_text (cons ((pos1, Markup.intensify), "")) env_tree)
                     | SOME (pos0, id, _) =>
                         ( Symtab.delete name env_dir
                         , C_Env.map_reports_text (C_Grammar_Rule_Lib.report [pos1] (C_Context.markup_directive_define false true pos0) (name, id))
                                                  env_tree)
                  end))
          | _ => fn env => (NONE, [], env)))))
in end
\<close>

section \<open>Definitions of Inner Annotation Commands\<close>
subsection \<open>\<close>

ML\<open>
structure C_Inner_Toplevel =
struct
val theory = Context.map_theory
val generic_theory = I
end
\<close>

ML\<open>
structure C_Inner_Isar_Cmd = 
struct
fun setup0 f_typ f_val src =
 fn NONE =>
    let val setup = "setup"
    in C_Context.expression
        "C_Ast"
        (Input.range_of src)
        setup
        (f_typ "C_Stack.stack_data" "C_Stack.stack_data_elem -> C_Env.env_lang -> Context.generic -> Context.generic")
        ("fn context => \
           \let val (stack, env_lang) = C_Stack.Data_Lang.get context \
           \in " ^ f_val setup "stack" ^ " (stack |> hd) env_lang end context")
        (ML_Lex.read_source false src) end
  | SOME rule => 
    let val hook = "hook"
    in C_Context.expression
        "C_Ast"
        (Input.range_of src)
        hook
        (f_typ "C_Stack.stack_data" (C_Grammar_Rule.type_reduce rule ^ " C_Stack.stack_elem -> C_Env.env_lang -> Context.generic -> Context.generic"))
        ("fn context => \
           \let val (stack, env_lang) = C_Stack.Data_Lang.get context \
           \in " ^ f_val hook "stack" ^ " (stack |> hd |> C_Stack.map_svalue0 C_Grammar_Rule.reduce" ^ Int.toString rule ^ ") env_lang end context")
        (ML_Lex.read_source false src)
    end
val setup = setup0 (fn a => fn b => a ^ " -> " ^ b) (fn a => fn b => a ^ " " ^ b)
val setup' = setup0 (K I) K
end
\<close>

ML\<open>
structure C_Inner_Syntax =
struct
fun command f dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          C_Transition.Parsing ((stack1, stack2), (range, dir, Symtab.empty, to_delay, f src))))

fun command0 f = command (K o f)
end
\<close>

subsection \<open>\<close>

ML\<open>
local
structure C_Isar_Cmd = 
struct
fun ML source = ML_Context.exec (fn () =>
                   ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
                 Local_Theory.propagate_ml_env
end
val _ = Theory.setup (   C_Inner_Syntax.command (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup) C_Transition.Bottom_up ("\<approx>setup", \<^here>)
                      #> C_Inner_Syntax.command (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup) C_Transition.Top_down ("\<approx>setup\<Down>", \<^here>)
                      #> C_Inner_Syntax.command0 (C_Inner_Toplevel.theory o Isar_Cmd.setup) C_Transition.Bottom_up ("setup", \<^here>)
                      #> C_Inner_Syntax.command0 (C_Inner_Toplevel.theory o Isar_Cmd.setup) C_Transition.Top_down ("setup\<Down>", \<^here>)
                      #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Isar_Cmd.ML) C_Transition.Bottom_up ("ML", \<^here>)
                      #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Isar_Cmd.ML) C_Transition.Top_down ("ML\<Down>", \<^here>)
                      #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Module.C) C_Transition.Bottom_up ("C", \<^here>)
                      #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Module.C) C_Transition.Top_down ("C\<Down>", \<^here>))
in end
\<close>

section \<open>Definitions of Outer Commands\<close>
subsection \<open>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/Pure.thy
    Author:     Makarius

The Pure theory, with definitions of Isar commands and some lemmas.
*)

ML\<open>
structure C_Outer_Parse =
struct
  val C_source = Parse.input (Parse.group (fn () => "C source") Parse.text)
end
\<close>

ML\<open>
structure C_Outer_Syntax =
struct
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C\<close> ""
    (C_Outer_Parse.C_source >> (Toplevel.generic_theory o C_Module.C));
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
    (fn () => C_Module.eval_source source) () end;

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
    #> C_Module.C (Input.source true (cat_lines lines) (pos, pos))
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
    (C_Outer_Parse.C_source >> (Toplevel.generic_theory o C_Module.C_export));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_prf\<close> "C text within proof"
    (C_Outer_Parse.C_source >> (Toplevel.proof o C_Module.C_prf));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_val\<close> "diagnostic C text"
    (C_Outer_Parse.C_source >> (Toplevel.keep o C_Outer_Isar_Cmd.C_diag));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_dump\<close> "diagnostic C text"
    (C_Outer_Parse.C_source >> (Toplevel.keep o C_Outer_Isar_Cmd.C_diag));   (* HACK: TO BE DONE *)

in end\<close>

end
