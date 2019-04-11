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

theory AC_Command
  imports "../../C_Main"
begin

section \<open>User Defined Commands in the Semantic Verification Space\<close>

ML\<open>
local
type text_range = Symbol_Pos.text * Position.T

datatype antiq_hol = Invariant of string (* term *)
                   | Fnspec of text_range (* ident *) * string (* term *)
                   | Relspec of string (* term *)
                   | Modifies of (bool (* true: [*] *) * text_range) list
                   | Dont_translate
                   | Auxupd of string (* term *)
                   | Ghostupd of string (* term *)
                   | Spec of string (* term *)
                   | End_spec of string (* term *)
                   | Calls of text_range list
                   | Owned_by of text_range

val scan_ident = Scan.one C_Token.is_ident >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
val scan_sym_ident_not_stack = Scan.one (fn c => C_Token.is_sym_ident c andalso
                                                 not (C_Token.is_stack1 c) andalso
                                                 not (C_Token.is_stack2 c))
                               >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
fun command cmd scan f =
  C_Annotation.command' cmd "" (K (Scan.option (Scan.one C_Token.is_colon) -- (scan >> f)
                                      >> K C_Transition.Never))
in
val _ = Theory.setup ((* 1 '@' *)
                         command ("INVARIANT", \<^here>) C_Parse.term Invariant
                      #> command ("INV", \<^here>) C_Parse.term Invariant

                      (* '+' until being at the position of the first ident
                        then 2 '@' *)
                      #> command ("FNSPEC", \<^here>) (scan_ident --| Scan.option (Scan.one C_Token.is_colon) -- C_Parse.term) Fnspec
                      #> command ("RELSPEC", \<^here>) C_Parse.term Relspec
                      #> command ("MODIFIES", \<^here>) (Scan.repeat (   scan_sym_ident_not_stack >> pair true
                                                                || scan_ident >> pair false))
                                                  Modifies
                      #> command ("DONT_TRANSLATE", \<^here>) (Scan.succeed ()) (K Dont_translate)

                      (**)
                      #> command ("AUXUPD", \<^here>) C_Parse.term Auxupd
                      #> command ("GHOSTUPD", \<^here>) C_Parse.term Ghostupd
                      #> command ("SPEC", \<^here>) C_Parse.term Spec
                      #> command ("END-SPEC", \<^here>) C_Parse.term End_spec

                      (**)
                      #> command ("CALLS", \<^here>) (Scan.repeat scan_ident) Calls
                      #> command ("OWNED_BY", \<^here>) scan_ident Owned_by);
end
\<close>

end
