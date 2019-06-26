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

chapter \<open>Example\<close>

theory C_autocorres
  imports "../../src/compiler/AC_Command"
begin

ML\<open>
fun print_top make_string f _ (_, (value, pos1, pos2)) _ thy =
  let
    val () = writeln (make_string value)
    val () = Position.reports_text [((Position.range (pos1, pos2) 
                                      |> Position.range_position, Markup.intensify), "")]
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
\<close>

setup \<open>ML_Antiquotation.inline @{binding print_top}
                               (Args.context >> K ("print_top " ^ ML_Pretty.make_string_fn ^ " I"))\<close>
setup \<open>ML_Antiquotation.inline @{binding print_stack}
                               (Scan.peek (fn _ => Scan.option Args.text) >> (fn name => ("print_stack " ^ (case name of NONE => "NONE" | SOME s => "(SOME \"" ^ s ^ "\")") ^ " " ^ ML_Pretty.make_string_fn)))\<close>

ML\<open>
structure Example_Data = Generic_Data (type T = string list
                                       val empty = [] val extend = K empty val merge = K empty)
fun add_ex s1 s2 =
  Example_Data.map (cons s2)
  #> (fn context => let val () = warning (s1 ^ s2)
                        val () = app (fn s => writeln ("  Data content: " ^ s)) (Example_Data.get context)
                    in context end)
\<close>

setup \<open>Context.theory_map (Example_Data.put [])\<close>

declare[[ML_source_trace]]
declare[[C_parser_trace]]

C \<comment> \<open>Arbitrary interleaving of effects\<close> \<open>
int x /** OWNED_BY foo */, hh /*@
  MODIFIES: [*] x
  \<approx>setup \<open>@{print_stack "evaluation of 2_print_stack"}\<close>
  +++++@@ \<approx>setup \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "2_print_top"\<close>
  OWNED_BY bar
  @\<approx>setup \<open>fn s => fn x => fn env => @{print_top} s x env #> add_ex "evaluation of " "1_print_top"\<close>
  \<approx>setup \<open>@{print_stack "evaluation of 1_print_stack"}\<close>
*/, z;

int b = 0;
\<close>

end
