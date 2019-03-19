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

theory "C11-Interface"
  imports "src/C_Isar"
  keywords "C" :: thy_decl
       and "C_file" :: thy_load % "ML"
begin

section\<open>The Global C11-Module State\<close>
ML\<open>
structure C11_core = 
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
  type C11_struct       = { tab  : (CTranslUnit * C_Env.stream) list Symtab.table,
                            env  : id_kind list Symtab.table }
  val  C11_struct_empty = { tab  = Symtab.empty, env = Symtab.empty}

  fun map_tab f {tab, env} = {tab = f tab, env=env}
  fun map_env f {tab, env} = {tab = tab, env=f env}

  fun cmp_either (x1, x2) = fst x1 = fst x2
  fun cmp_tab (x1, x2) = map #1 x1 = map #1 x2

  (* registrating data of the Isa_DOF component *)
  structure Data = Generic_Data
  (
    type T =     C11_struct
    val empty = C11_struct_empty
    val extend =  I
    fun merge(t1,t2) = { tab = Symtab.merge cmp_tab (#tab t1, #tab t2),
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
    |> Symtab.update_list C11_core.cmp_either
    |> C11_core.map_tab
    |> (fn map_tab => C11_core.Data.map map_tab context))
  |> C_Env.map_context

val eval_source =
  C_Context.eval_source
    C_Env.empty_env_lang
    (fn _ => fn _ => fn pos =>
      Scan.error (Symbol_Pos.!!! (K "Syntax error") Scan.fail)
                 [("", pos)])
    accept
end
\<close>

section \<open>The Isar Binding to the C11 Interface.\<close>

ML\<open>

structure C_Outer_Syntax =
struct

val C = C_Context'.eval_source (ML_Compiler.verbose true ML_Compiler.flags)
fun C' err env_lang src context =
  {context = context, reports = Stack_Data_Tree.get context}
  |> C_Context.eval_source'
       env_lang
       err
       C_Context'.accept
       (ML_Compiler.verbose true ML_Compiler.flags)
       src
  |> (fn {context, reports} => Stack_Data_Tree.put reports context)

val _ =
  Outer_Syntax.command @{command_keyword C} ""
    (Parse.input (Parse.group (fn () => "C source") Parse.text) >> (fn source =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () =>
            C source) #>
          Local_Theory.propagate_ml_env)));
end
\<close>

section\<open>Definition of the Command "C_file"\<close>

ML\<open>
(*  Title:      Pure/ML/ml_file.ML
    Author:     Makarius

Commands to load ML files.
*)

structure C_File =
struct

fun command SML debug files = Toplevel.generic_theory (fn gthy =>
  let
    val [{src_path, lines, digest, pos}: Token.file] = files (Context.theory_of gthy);
    val provide = Resources.provide (src_path, digest);
    val source = Input.source true (cat_lines lines) (pos, pos);
    val flags =
      {SML = SML, exchange = false, redirect = true, verbose = true,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => C_Context'.eval_source flags source)
    |> Local_Theory.propagate_ml_env
    |> Context.mapping provide (Local_Theory.background_theory provide)
  end);

val C : bool option ->
      (theory -> Token.file list) ->
        Toplevel.transition -> Toplevel.transition = command false;

end;
\<close>

section \<open>Pure\<close>

ML\<open>
local

val semi = Scan.option @{keyword ";"};

val _ =
  Outer_Syntax.command @{command_keyword C_file} "read and evaluate C file"
    (Resources.parse_files "C_file" --| semi >> C_File.C NONE);

in end
\<close>

section \<open>\<close>

ML\<open>
fun reduce make_string f (_, (value, pos1, pos2)) _ thy =
  let
    val () = writeln (make_string value)
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
  in f thy end

fun reduce' _ f (_, (_, pos1, pos2)) env thy =
  let
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
    val () = writeln ("ENV " ^ C_Env.string_of env)
  in f thy end

fun shift s make_string (stack, _) thy =
  let
    val () = warning ("SHIFT  " ^ (case s of NONE => "" | SOME s => "\"" ^ s ^ "\" ") ^ Int.toString (length stack - 1) ^ "    +1 ")
    val () = stack
          |> split_list
          |> #2
          |> map_index I
          |> app (fn (i, (value, pos1, pos2)) => writeln ("   " ^ Int.toString (length stack - i) ^ " " ^ make_string value ^ " " ^ Position.here pos1 ^ " " ^ Position.here pos2))
  in thy end

fun shift' s _ (stack, env) thy =
  let
    val () = warning ("SHIFT  " ^ (case s of NONE => "" | SOME s => "\"" ^ s ^ "\" ") ^ Int.toString (length stack - 1) ^ "    +1 ")
    val () = writeln ("ENV " ^ C_Env.string_of env)
  in thy end
\<close>

setup \<open>ML_Antiquotation.inline @{binding reduce}
                               (Args.context >> K ("reduce " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding reduce'}
                               (Args.context >> K ("reduce' " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding shift}
                               (Scan.peek (fn _ => Scan.option Args.text) >> (fn name => ("shift " ^ (case name of NONE => "NONE" | SOME s => "(SOME \"" ^ s ^ "\")") ^ " " ^ ML_Pretty.make_string_fn)))\<close>
setup \<open>ML_Antiquotation.inline @{binding shift'}
                               (Scan.peek (fn _ => Scan.option Args.text) >> (fn name => ("shift' " ^ (case name of NONE => "NONE" | SOME s => "(SOME \"" ^ s ^ "\")") ^ " " ^ ML_Pretty.make_string_fn)))\<close>

end
