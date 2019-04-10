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

section \<open>Definitions of Directive Commands\<close>

ML\<open>
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
                  , C_Env.map_reports_text (Hsk_c_parser.report pos (C_Context.markup_directive_define true false pos) (name, id))
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
                       , C_Env.map_reports_text (Hsk_c_parser.report [pos1] (C_Context.markup_directive_define false true pos0) (name, id))
                                                env_tree)
                end))
         | _ => fn env => (NONE, [], env)))))
\<close>

section \<open>Definitions of Annotation Commands\<close>

ML\<open>
local
fun expression range name constraint body ants context = context |>
  ML_Context.exec let val verbose = Config.get (Context.proof_of context) C_Options.ML_verbose
                  in fn () =>
    ML_Context.eval (ML_Compiler.verbose verbose ML_Compiler.flags) (#1 range)
     (ML_Lex.read "Context.put_generic_context (SOME (let val " @ ML_Lex.read_set_range range name @
      ML_Lex.read (": " ^ constraint ^ " =") @ ants @
      ML_Lex.read ("in " ^ body ^ " end (Context.the_generic_context ())));")) end;

structure C_Inner_Toplevel =
struct
val theory = Context.map_theory
val generic_theory = I
end

structure Isar_Cmd0 = 
struct
fun ML source =  ML_Context.exec (fn () =>
                    ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
                  Local_Theory.propagate_ml_env
end

structure C_Inner_Isar_Cmd = 
struct
fun setup src =
 fn NONE =>
    let val setup = "setup"
    in expression
        (Input.range_of src)
        setup
        "stack_data -> stack_data_elem -> C_Env.env_lang -> Context.generic -> Context.generic"
        ("fn context => \
           \let val (stack, env_lang) = Stack_Data_Lang.get context \
           \in " ^ setup ^ " stack (stack |> hd) env_lang end context")
        (ML_Lex.read_source false src) end
  | SOME rule => 
    let val hook = "hook"
    in expression
        (Input.range_of src)
        hook
        ("stack_data -> " ^ MlyValue.type_reduce rule ^ " stack_elem -> C_Env.env_lang -> Context.generic -> Context.generic")
        ("fn context => \
           \let val (stack, env_lang) = Stack_Data_Lang.get context \
           \in " ^ hook ^ " stack (stack |> hd |> map_svalue0 MlyValue.reduce" ^ Int.toString rule ^ ") env_lang end context")
        (ML_Lex.read_source false src)
    end

end

fun command0 f dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          Parsing ((stack1, stack2), (range, dir, Symtab.empty, to_delay, K (f src)))))

fun command f dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          Parsing ((stack1, stack2), (range, dir, Symtab.empty, to_delay, f src))))

in
val _ = Theory.setup (   command (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup) Bottom_up ("\<approx>setup", \<^here>)
                      #> command (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup) Top_down ("\<approx>setup\<Down>", \<^here>)
                      #> command0 (C_Inner_Toplevel.theory o Isar_Cmd.setup) Bottom_up ("setup", \<^here>)
                      #> command0 (C_Inner_Toplevel.theory o Isar_Cmd.setup) Top_down ("setup\<Down>", \<^here>)
                      #> command0 (C_Inner_Toplevel.generic_theory o Isar_Cmd0.ML) Bottom_up ("ML", \<^here>)
                      #> command0 (C_Inner_Toplevel.generic_theory o Isar_Cmd0.ML) Top_down ("ML\<Down>", \<^here>))
end
\<close>

section \<open>Definitions of Outer Commands\<close>
subsection \<open>The Global C11-Module State\<close>

ML\<open>
structure C11_core = (*Old C11 Env - deprecated?*)
struct
  datatype id_kind = cpp_id        of Position.T * serial
                   | cpp_macro     of Position.T * serial
                   | builtin_id  
                   | builtin_func 
                   | imported_id   of Position.T * serial
                   | imported_func of Position.T * serial 
                   | global_id     of Position.T * serial
                   | local_id      of Position.T * serial
                   | global_func   of Position.T * serial


  type new_env_type  = { 
                        cpp_id       :  unit Name_Space.table,
                        cpp_macro    :  unit Name_Space.table,
                        builtin_id   : unit Name_Space.table,
                        builtin_func : unit Name_Space.table,
                        global_var   : (NodeInfo C_ast_simple.cTypeSpecifier) Name_Space.table,
                        local_var    : (NodeInfo C_ast_simple.cTypeSpecifier) Name_Space.table,
                        global_func  : (NodeInfo C_ast_simple.cTypeSpecifier) Name_Space.table
  }

  val mt_env = {cpp_id       = Name_Space.empty_table "cpp_id",
                cpp_macro    = Name_Space.empty_table "cpp_macro", 
                builtin_id   = Name_Space.empty_table "builtin_id",
                builtin_func = Name_Space.empty_table "builtin_func",
                global_var   = Name_Space.empty_table "global_var",
                local_var    = Name_Space.empty_table "local_var",
                global_func  = Name_Space.empty_table "global_func"
  }


  type c_file_name      = string
  type C11_struct       = { tab  : (CTranslUnit * C_Antiquote.antiq C_Env.stream) list Symtab.table,
                            env  : id_kind list Symtab.table }
  val  C11_struct_empty = { tab  = Symtab.empty, env = Symtab.empty}

  fun map_tab f {tab, env} = {tab = f tab, env=env}
  fun map_env f {tab, env} = {tab = tab, env=f env}

  (* registrating data of the Isa_DOF component *)
  structure Data = Generic_Data
  (
    type T =     C11_struct
    val empty = C11_struct_empty
    val extend =  I
    fun merge(t1,t2) = { tab = Symtab.merge (op =) (#tab t1, #tab t2),
                         env = Symtab.merge (op =) (#env t1, #env t2)}
  );

  val get_global      = Data.get o Context.Theory
  fun put_global x    = Data.put x;
  val map_data        = Context.theory_map o Data.map;
  val map_data_global = Context.theory_map o Data.map
  
  val trans_tab_of    = #tab o get_global
  val dest_list       = Symtab.dest_list o trans_tab_of

  fun push_env(k,a) tab = case Symtab.lookup tab k of
                        NONE => Symtab.update(k,[a])(tab)
                     |  SOME S => Symtab.update(k,a::S)(tab)
  fun pop_env(k) tab = case Symtab.lookup tab k of
                       SOME (a::S) => Symtab.update(k,S)(tab)
                     | _ => error("internal error - illegal break of scoping rules")
  
  fun push_global (k,a) =  (map_data_global o map_env) (push_env (k,a)) 
  fun push (k,a)        =  (map_data        o map_env) (push_env (k,a)) 
  fun pop_global (k)    =  (map_data_global o map_env) (pop_env k) 
  fun pop (k)           =  (map_data        o map_env) (pop_env k) 

end
\<close>

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

subsubsection \<open>Reading and Writing C-Files\<close>

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
