(******************************************************************************
 * LICENSE
 *
 * Copyright (c) 2017-2018 Virginia Tech, USA
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

theory LICENSE0
  imports Main
  keywords "project" "country" "holder" "copyright" "license"
           "check_license" "insert_license" "map_license" :: thy_decl
begin

ML\<open>
functor Theory_Data' (N : sig type T val name : string end) : THEORY_DATA = Theory_Data
  (type T = N.T Name_Space.table
   val empty = Name_Space.empty_table N.name
   val extend = I
   val merge = Name_Space.merge_tables)

structure Project = Theory_Data' (type T = unit val name = "project")
structure Country = Theory_Data' (type T = unit val name = "country")
structure Holder = Theory_Data' (type T = unit val name = "holder")
structure Copyright = Theory_Data' (type T = unit val name = "copyright")
structure License = Theory_Data' (type T = unit val name = "license")

fun define key data_map n =
  ( key
  , Toplevel.theory
      (fn thy => data_map (#2 o Name_Space.define (Context.Theory thy) true (n, ()))
                          thy))

val _ =
  Outer_Syntax.commands @{command_keyword project} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.list1 (Parse.document_source --
                 (Parse.position Parse.name >> SOME || Parse.document_source >> K NONE)) >>
     (fn (n, l) =>
       define @{command_keyword project} Project.map n
       :: flat
            (map
              (fn (x, opt_n) =>
                let val l = [(@{command_keyword project}, Thy_Output.document_command {markdown = true} (NONE, x))] in
                  case opt_n of
                    NONE => l
                  | SOME n =>
                    ( @{command_keyword project}
                    , Toplevel.keep
                        (fn thy => 
                          let val thy = Toplevel.theory_of thy
                          in #2 (Name_Space.check (Context.Theory thy) (Copyright.get thy) n) end))
                    :: l
                end)
              l)));

val _ =
  Outer_Syntax.commands @{command_keyword country} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.document_source >>
      (fn (n, src) =>
        [ define @{command_keyword country} Country.map n
        , (@{command_keyword country}, Thy_Output.document_command {markdown = true} (NONE, src))]));

val _ =
  Outer_Syntax.commands @{command_keyword holder} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.list Parse.document_source >>
      (fn (n, l_src) =>
        define @{command_keyword holder} Holder.map n
        :: map (fn src =>
                 (@{command_keyword holder}, Thy_Output.document_command {markdown = true} (NONE, src)))
               l_src));

val _ =
  Outer_Syntax.commands @{command_keyword copyright} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.document_source >>
      (fn (n, src) =>
        [ define @{command_keyword copyright} Copyright.map n
        , (@{command_keyword copyright}, Thy_Output.document_command {markdown = true} (NONE, src))]));

val _ =
  Outer_Syntax.commands @{command_keyword license} "formal comment (primary style)"
    (Parse.binding --| Parse.where_ -- Parse.document_source >>
      (fn (n, src) =>
        [ define @{command_keyword license} License.map n
        , (@{command_keyword license}, Thy_Output.document_command {markdown = true} (NONE, src))]));

val _ =
  Outer_Syntax.command @{command_keyword check_license} "formal comment (primary style)"
    (Scan.option Parse.binding >>
      (fn _ => Toplevel.keep (fn _ => warning "to be implemented")))

val _ =
  Outer_Syntax.command @{command_keyword insert_license} "formal comment (primary style)"
    (Scan.option Parse.binding >>
      (fn _ => Toplevel.keep (fn _ => warning "to be implemented")))

val _ =
  Outer_Syntax.command @{command_keyword map_license} "formal comment (primary style)"
    (Scan.option Parse.binding >>
      (fn _ => Toplevel.keep (fn _ => warning "to be implemented")))
\<close>

end