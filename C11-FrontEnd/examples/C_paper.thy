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

theory C_paper
  imports "../C_Main"
begin

ML\<open>
local
fun expression range name constraint body ants context = context |>
  ML_Context.exec let val verbose = Config.get (Context.proof_of context) C_Options.ML_verbose
                  in fn () =>
    ML_Context.eval (ML_Compiler.verbose verbose ML_Compiler.flags) (#1 range)
     (ML_Lex.read "Context.put_generic_context (SOME (let val " @ ML_Lex.read_set_range range name @
      ML_Lex.read (": " ^ constraint ^ " =") @ ants @
      ML_Lex.read ("in " ^ body ^ " end (Context.the_generic_context ())));")) end;

fun command0 dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          (fn f => Once ((stack1, stack2), (range, dir, to_delay, f)))
            (fn NONE =>
                let val setup = "setup"
                in expression
                    (Input.range_of src)
                    setup
                    "stack_data_elem -> C_Env.env_lang -> Context.generic -> Context.generic"
                    ("fn context => \
                       \let val (stack, env_lang) = Stack_Data_Lang.get context \
                       \in " ^ setup ^ " (stack |> hd) env_lang end context")
                    (ML_Lex.read_source false src) end
              | SOME rule => 
                let val hook = "hook"
                in expression
                    (Input.range_of src)
                    hook
                    (MlyValue.type_reduce rule ^ " stack_elem -> C_Env.env_lang -> Context.generic -> Context.generic")
                    ("fn context => \
                       \let val (stack, env_lang) = Stack_Data_Lang.get context \
                       \in " ^ hook ^ " (stack |> hd |> map_svalue0 MlyValue.reduce" ^ Int.toString rule ^ ") env_lang end context")
                    (ML_Lex.read_source false src)
                end)))

fun command dir name =
  C_Annotation.command' name ""
    (fn (stack1, (to_delay, stack2)) =>
      C_Parse.range C_Parse.ML_source >>
        (fn (src, range) =>
          (fn f => Once ((stack1, stack2), (range, dir, to_delay, f)))
            (fn NONE =>
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
                end)))

in
val _ = Theory.setup (   command0 Bottom_up ("ML_setup", \<^here>)
                      #> command0 Top_down ("ML_setup\<Down>", \<^here>))
val _ = Theory.setup (   command Bottom_up ("ML\<Up>", \<^here>)
                      #> command Bottom_up ("setup1", \<^here>)
                      #> command Top_down ("setup1_rev", \<^here>)
                      #> command Top_down ("ML\<Down>", \<^here>))
end
\<close>

ML\<open>
fun show_env0 make_string f msg context =
  warning ("(" ^ msg ^ ") "
           ^ make_string (f (the (Symtab.lookup (#tab (C11_core.Data.get context))
                                                (Context.theory_name (Context.theory_of context))))))

val show_env = tap o show_env0 @{make_string} length

val C' = C_Outer_Syntax.C' (fn _ => fn _ => fn pos =>
                             tap (fn _ => warning ("Parser: No matching grammar rule " ^ Position.here pos)))
\<close>


ML\<open>
fun command_c' name _ _ =
  Context.map_theory 
    (C_Annotation.command' name ""
      (fn (stack1, (to_delay, stack2)) =>
        C_Parse.range C_Parse.ML_source >>
          (fn (src, range) =>
            (fn f => Once ((stack1, stack2), (range, Bottom_up, to_delay, f)))
              (fn _ => fn context => C' (Stack_Data_Lang.get context |> #2) src context))))

fun command_c'' name _ _ =
  Context.map_theory 
    (C_Annotation.command' name ""
      (fn (stack1, (to_delay, stack2)) =>
        C_Parse.range C_Parse.ML_source >>
          (fn (src, range) =>
            (fn f => Once ((stack1, stack2), (range, Top_down, to_delay, f)))
              (fn _ => fn context => C' (Stack_Data_Lang.get context |> #2) src context))))

fun fun_decl a v s ctxt =
  let
    val (b, ctxt') = ML_Context.variant a ctxt;
    val env = "fun " ^ b ^ " " ^ v ^ " = " ^ s ^ " " ^ v ^ ";\n";
    val body = ML_Context.struct_name ctxt ^ "." ^ b;
    fun decl (_: Proof.context) = (env, body);
  in (decl, ctxt') end;

val _ = Theory.setup
  (ML_Antiquotation.declaration (Binding.make ("C_define", \<^here>)) (Scan.lift (Parse.sym_ident
 -- Parse.position Parse.name))
    (fn _ => fn (top_down, (name, pos)) =>
      tap (fn ctxt => Context_Position.reports ctxt [(pos, Markup.keyword1)]) #>
      fun_decl "cmd" "x" ((case top_down of "\<Up>" => "command_c'" | "\<Down>" => "command_c''" | _ => error "Illegal symbol") ^ " (\"" ^ name ^ "\", " ^ ML_Syntax.print_position pos ^ ")")))

fun C opt = case opt of NONE => (fn src => tap (fn _ => C_Outer_Syntax.C src))
                      | SOME env => C' env
\<close>

ML\<open>
fun print_top make_string (_, (value, pos1, pos2)) thy =
  let
    val () = writeln (make_string value)
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
  in thy end

fun highlight (_, (_, pos1, pos2)) thy =
  let
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                    |> Position.range_position, Markup.intensify), "")]
  in thy end
\<close>

setup \<open>ML_Antiquotation.inline @{binding highlight}
                               (Args.context >> K ("highlight " ^ " "))\<close>

C (*NONE*) \<comment> \<open> the command starts with a default empty environment \<close>
\<open>int f (int a)
  //@ ++& ML_setup \<open>fn stack_top => fn env => highlight stack_top\<close>
  { /*@ @ ML_setup \<open>fn stack_top => fn env =>
                    C (SOME env) (* the command starts with some provided environment *)
                     \<open>int b = a + b; //@ C1 \<open>int c; //@ @ ML_setup\<Down> \<open>@{C_define \<Up> C2}\<close> \
                                                        @ C1  \<open>//* C2 \<open>int d;\<close>\<close>        \
                                                        @ C1\<Down> \<open>//* C2 \<open>int d;\<close>\<close>        \<close>
                      int b = a + b + c + d;\<close>\<close>
        @ ML_setup \<open>fn stack_top => fn env => C NONE \<open>int b = a + b; //* C2 \<open>int c = b;\<close>\<close>\<close>
          ML_setup \<open>@{C_define \<Up> (* bottom-up *)  C1  }\<close>
          ML_setup \<open>@{C_define \<Down> (* top-down  *) "C1\<Down>"}\<close>
     */
    return a + b + c + d; /* explicit highlighting */ }\<close>


declare [[C_parser_trace]]
C\<open>int f (int a) { return a + b + c + d; } \<close>

end
