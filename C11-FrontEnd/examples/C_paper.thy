(******************************************************************************
 * Isabelle/C
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

chapter \<open>Example\<close>

theory C_paper
  imports C.C_Main
begin

section \<open>\<close>

ML\<open>
local
val command = C_Inner_Syntax.command C_Inner_Isar_Cmd.setup' C_Parse.ML_source
in
val _ = Theory.setup (   command C_Transition.Bottom_up ("ML_setup", \<^here>)
                      #> command C_Transition.Top_down ("ML_setup\<Down>", \<^here>))
end

val C' = C_Module.C' (fn _ => fn _ => fn pos =>
                       tap (fn _ => warning ("Parser: No matching grammar rule " ^ Position.here pos)))

fun C_define dir name _ _ =
  Context.map_theory 
    (C_Inner_Syntax.command0
      (fn src => fn context => C' (C_Stack.Data_Lang.get context |> #2) src context)
      C_Parse.C_source
      dir
      name)

local
in
val _ = Theory.setup
  (ML_Antiquotation.declaration
    @{binding "C_define"}
    (Scan.lift (Parse.sym_ident -- Parse.position Parse.name))
    (fn _ => fn (top_down, (name, pos)) =>
      tap (fn ctxt => Context_Position.reports ctxt [(pos, Markup.keyword1)]) #>
      C_Context.fun_decl
               "cmd" "x" ( "C_define "
                         ^ (case top_down of "\<Up>" => "C_Transition.Bottom_up"
                                           | "\<Down>" => "C_Transition.Top_down"
                                           | _ => error "Illegal symbol")
                         ^ " (\"" ^ name ^ "\", " ^ ML_Syntax.print_position pos ^ ")")))
end

fun C opt = case opt of NONE => tap o C_Module.C
                      | SOME env => C' env

fun highlight (_, (_, pos1, pos2)) =
  tap (fn _ => Position.reports_text [((Position.range (pos1, pos2)
                                        |> Position.range_position, Markup.intensify), "")])
\<close>

section \<open>\<close>

C (*NONE*) \<comment> \<open> the command starts with a default empty environment \<close>
\<open>int f (int a)
  //@ ++& ML_setup \<open>fn stack_top => fn env => highlight stack_top\<close>
  { /*@ @ ML_setup \<open>fn stack_top => fn env =>
                    C (SOME env) (* the command starts with some provided environment *)
                     \<open>int b = a + b; //@ C1 \<open>int c; //@ @ ML_setup\<Down> \<open>@{C_define \<Up> C2}\<close> \
                                                        @ C1  \<open>//* C2 \<open>int d;\<close>\<close>        \
                                                        @ C1\<Down> \<open>//* C2 \<open>int d;\<close>\<close>        \<close>
                      int b = a + b + c + d;\<close>\<close>
        @ ML_setup \<open>fn stack_top => fn env => C NONE \<open>#define int int
                                                      int b = a + b; //* C2 \<open>int c = b;\<close>\<close>\<close>
          ML_setup \<open>@{C_define \<Up> (* bottom-up *)  C1  }\<close>
          ML_setup \<open>@{C_define \<Down> (* top-down  *) "C1\<Down>"}\<close>
     */
    return a + b + c + d; /* explicit highlighting */ }\<close>


declare [[C_parser_trace]]
C\<open>int f (int a) { return a + b + c + d; } \<close>

end
