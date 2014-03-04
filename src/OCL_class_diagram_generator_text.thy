(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator_text.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2014 Universite Paris-Sud, France
 *               2014 IRT SystemX, France
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

theory OCL_class_diagram_generator_text
imports Main
  keywords "lazy_text" :: thy_decl
       and "reset_text" :: thy_decl
       and "apply_text" :: thy_decl
begin

ML{*
datatype code_printing = Code_printing of string

structure Data_code = Theory_Data
  (type T = code_printing list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_empty = ""

val _ =
  Outer_Syntax.markup_command Thy_Output.MarkupEnv
    @{command_spec "lazy_text"} ""
    (Parse.opt_target -- Parse.document_source
     >> (fn (_, (code, _)) =>
       let val _ = writeln (@{make_string} code) in
            Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn l => Code_printing code :: l)))
       end))

fun of_text s = 
  let val s = String.substring (s, 2, String.size s - 4)
    ; fun esc n = "'', " ^ n ^ ", ''" in
  String.concat
    [ "txt'' [ ''", str #"\n"
    , "  ", translate_string
      (fn "\034" (* " *) => esc "a"
        | "\039" (* ' *) => esc "n"
        | "\092" (* \ *) => esc "e"
        | x => x) s
    , "'' ]", str #"\n" ]
  end

fun apply_code_printing thy =
  (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
  |> (fn l => 
    let val (thy, l) =
      fold (fn Code_printing s => fn (thy, l) => (thy, of_text s :: l)) l (thy, [])
      ; val _ = writeln (Active.sendback_markup [Markup.padding_command] ("definition \034t txt'' e n a = [\n              " ^ String.concatWith "            , " (rev l) ^ "]\034")) in
    thy
    end)

val () =
  Outer_Syntax.command @{command_spec "apply_text"} ""
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory apply_code_printing))

val () =
  Outer_Syntax.command @{command_spec "reset_text"} ""
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn _ => [])))))
*}

end
