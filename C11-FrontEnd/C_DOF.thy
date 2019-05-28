(******************************************************************************
 * Isabelle/DOF
 *
 * Copyright (c) 2018-2019 The University of Sheffield
 *               2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

section \<open>Simulating Isabelle/DOF\<close>

theory C_DOF
  imports Main
  keywords "+=" ":=" "accepts" "rejects"

  and      "title*"     "subtitle*"
           "chapter*"  "section*"    "subsection*"   "subsubsection*" 
           "paragraph*"  "subparagraph*" 
           "text*"       
           "figure*"
           "side_by_side_figure*" 
           :: document_body
           
  and      "open_monitor*" "close_monitor*" "declare_reference*" 
           "update_instance*" :: thy_decl
 begin

ML\<open>
structure ODL_Command_Parser = 
struct

type meta_args_t = (((string * Position.T) *
                     (string * Position.T) option)
                    * ((string * Position.T) * string) list)

val semi = Scan.option (Parse.$$$ ";");
val is_improper = not o (Token.is_proper orf Token.is_begin_ignore orf Token.is_end_ignore);
val improper = Scan.many is_improper; (* parses white-space and comments *)

val attribute =
    Parse.position Parse.const
    --| improper 
    -- Scan.optional (Parse.$$$ "=" --| improper |-- Parse.!!! Parse.term --| improper) "True"
   : ((string * Position.T) * string) parser;

val attribute_upd  : (((string * Position.T) * string) * string) parser =
    Parse.position Parse.const 
    --| improper
    -- ((@{keyword "+="} --| improper) || (@{keyword ":="} --| improper))
    -- Parse.!!! Parse.term
    --| improper
    : (((string * Position.T) * string) * string) parser;

val reference =
    Parse.position Parse.name 
    --| improper
    -- Scan.option (Parse.$$$ "::" 
                    -- improper 
                    |-- (Parse.!!! (Parse.position Parse.name))
                    ) 
    --| improper;


val attributes =  
    ((Parse.$$$ "["
      -- improper 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," -- improper |-- (Parse.enum "," (improper |-- attribute)))) []))
     --| Parse.$$$ "]"
     --| improper)  : meta_args_t parser 

val attributes_upd =  
    ((Parse.$$$ "[" 
     -- improper 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," -- improper |-- (Parse.enum "," (improper |-- attribute_upd)))) []))
     --| Parse.$$$ "]")
     --| improper

fun enriched_document_command _ {markdown} ((_, opt), src) =
  Pure_Syn.document_command {markdown = markdown} (opt, src)
fun open_monitor_command _ = I
fun close_monitor_command _ = I
fun update_instance_command _ = I

end
\<close>

ML\<open>
structure DOF_core =
struct
val (strict_monitor_checking, strict_monitor_checking_setup) 
     = Attrib.config_bool @{binding strict_monitor_checking} (K false);
fun declare_object_global _ = I
end
\<close>

setup\<open>DOF_core.strict_monitor_checking_setup\<close>

ML\<open>
structure OntoLinkParser = 
struct
(* generic syntax for doc_class links. *) 

val defineN    = "define"
val uncheckedN = "unchecked" 

val docitem_modes = Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN)
                                   >> (fn str => if str = defineN 
                                                 then {unchecked = false, define= true}  
                                                 else {unchecked = true,  define= false})) 
                                   {unchecked = false, define= false} (* default *);

val docitem_antiquotation_parser : ({define: bool, unchecked: bool} * Input.source) context_parser = (Scan.lift (docitem_modes -- Args.text_input))
end
\<close>

ML\<open>
structure OntoParser =
struct
val _ = Theory.setup
 (Thy_Output.antiquotation_verbatim  @{binding figure}
   OntoLinkParser.docitem_antiquotation_parser (fn _ => fn _ => "") #>
  Thy_Output.antiquotation_verbatim  @{binding docitem}
   OntoLinkParser.docitem_antiquotation_parser (fn _ => fn _ => ""))
end\<close>

ML\<open>
local
open ODL_Command_Parser
in
(* *********************************************************************** *)
(* Textual Command Support                                                 *)
(* *********************************************************************** *)

(* {markdown = true} sets the parsing process such that in the text-core markdown elements are
   accepted. *)

val _ =
  Outer_Syntax.command ("title*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command NONE {markdown = false} ))) ;

val _ =
  Outer_Syntax.command ("subtitle*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command NONE {markdown = false} )));

val _ =
  Outer_Syntax.command ("chapter*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command (SOME(SOME 0)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("section*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command (SOME(SOME 1)) {markdown = false} )));


val _ =
  Outer_Syntax.command ("subsection*", @{here}) "subsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command (SOME(SOME 2)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("subsubsection*", @{here}) "subsubsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command (SOME(SOME 3)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("paragraph*", @{here}) "paragraph heading"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command (SOME(SOME 4)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("subparagraph*", @{here}) "subparagraph heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command (SOME(SOME 5)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("figure*", @{here}) "figure"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command NONE {markdown = false} )));

val _ =
  Outer_Syntax.command ("side_by_side_figure*", @{here}) "multiple figures"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> ((enriched_document_command NONE {markdown = false} )));


val _ =
  Outer_Syntax.command ("text*", @{here}) "formal comment (primary style)"
    (attributes -- Parse.opt_target -- Parse.document_source 
      >> ((enriched_document_command NONE {markdown = true} )));

val _ =
  Outer_Syntax.command @{command_keyword "declare_reference*"} 
                       "declare document reference"
                       (attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
                                      (Toplevel.theory (DOF_core.declare_object_global oid))));

val _ =
  Outer_Syntax.command @{command_keyword "open_monitor*"} 
                       "open a document reference monitor"
                       (attributes >> (Toplevel.theory o open_monitor_command));

val _ =
  Outer_Syntax.command @{command_keyword "close_monitor*"} 
                       "close a document reference monitor"
                       (attributes_upd >> (Toplevel.theory o close_monitor_command)); 


val _ =
  Outer_Syntax.command @{command_keyword "update_instance*"} 
                       "update meta-attributes of an instance of a document class"
                        (attributes_upd >> (Toplevel.theory o update_instance_command)); 
end
\<close>

end