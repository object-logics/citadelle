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

section \<open>Parsing Environment\<close>

theory C_Environment
  imports C_Lexer
begin

subsection \<open>Types Characterizing Command Actions (Outer and Inner Commands)\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/context.ML\<close>\<close> \<open>
structure C_Transition =
struct

datatype comment_style = Comment_directive
                       | Comment_language

datatype env_propagation = Bottom_up (*during parsing*) | Top_down (*after parsing*)

type env_directives = (Position.T list * serial * C_Lex.token list) Symtab.table

type eval_node = Position.range
                 * env_propagation
                 * env_directives
                 * bool (* true: skip vacuous reduce rules *)
                 * (int (*reduce rule number*) option (* NONE: shift action *)
                    -> Context.generic -> Context.generic)

datatype eval_time = Lexing of Position.range * (comment_style -> Context.generic -> Context.generic)
                   | Parsing of (Symbol_Pos.T list (* length = number of tokens to advance *) 
                                 * Symbol_Pos.T list (* length = number of steps back in stack *)) 
                                 * eval_node
                   | Never (* to be manually treated by the semantic back-end, and analyzed there *)

datatype antiq_language = Antiq_stack of C_Position.reports_text * eval_time
                        | Antiq_none of C_Lex.token
end;

\<close>

text \<open> The key element of \<^ML_structure>\<open>C_Transition\<close> is
\<^ML_type>\<open>C_Transition.eval_time\<close>, relevant for the generic annotation
module. \<close>

subsection \<open>Definition of the Environment\<close>

text \<open> The environment comes in two parts: a basic core structure, and a (thin) layer of
utilities. \<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/context.ML\<close>\<close> \<open>
structure C_Env = struct
datatype 'a parse_status = Parsed of 'a | Previous_in_stack

type markup_ident = { global : bool (*true: global*)
                    , params : C_Ast.CDerivedDeclr list
                    , ret : C_Ast.CDeclSpec list parse_status }

type var_table = { tyidents : (Position.T list * serial) Symtab.table
                 , idents : (Position.T list * serial * markup_ident) Symtab.table }

type 'antiq_language_list stream = ('antiq_language_list, C_Lex.token) C_Scan.either list

\<comment> \<open>Key entry point environment to the C language\<close>
type env_lang = { var_table : var_table \<comment> \<open>current active table in the scope\<close>
                , scopes : (C_Ast.ident option * var_table) list  \<comment> \<open>parent scope tables\<close>
                , namesupply : int
                , stream_ignored : C_Antiquote.antiq stream
                , env_directives : C_Transition.env_directives }
(* NOTE: The distinction between type variable or identifier can not be solely made
         during the lexing process.
         Another pass on the parsed tree is required. *)

type env_tree = { context : Context.generic
                , reports_text : C_Position.reports_text }

type rule_static = (env_tree -> env_lang * env_tree) option

(**)

type ('LrTable_state, 'a, 'Position_T) stack_elem0 = 'LrTable_state * ('a * 'Position_T * 'Position_T)
type ('LrTable_state, 'a, 'Position_T) stack0 = ('LrTable_state, 'a, 'Position_T) stack_elem0 list

type ('LrTable_state, 'svalue0, 'pos) rule_reduce0 = (('LrTable_state, 'svalue0, 'pos) stack0 * env_lang * C_Transition.eval_node) list
type ('LrTable_state, 'svalue0, 'pos) rule_reduce = int * ('LrTable_state, 'svalue0, 'pos) stack0 * C_Transition.eval_node list list
type ('LrTable_state, 'svalue0, 'pos) rule_reduce' = int * bool (*vacuous*) * ('LrTable_state, 'svalue0, 'pos) rule_reduce0

datatype ('LrTable_state, 'svalue0, 'pos) rule_type =
                     Void
                   | Shift
                   | Reduce of rule_static * ('LrTable_state, 'svalue0, 'pos) rule_reduce'

type ('LrTable_state, 'svalue0, 'pos) rule_ml =
  { rule_pos : 'pos * 'pos
  , rule_type : ('LrTable_state, 'svalue0, 'pos) rule_type }

(**)

type 'class_Pos rule_output0' = { output_pos : 'class_Pos option
                                , output_vacuous : bool
                                , output_env : rule_static }

type ('LrTable_state, 'svalue0, 'pos) rule_output0 =
                                 C_Transition.eval_node list list (* delayed *)
                               * ('LrTable_state, 'svalue0, 'pos) rule_reduce0 (* actual *)
                               * ('pos * 'pos) rule_output0'

type rule_output = C_Ast.class_Pos rule_output0'

(**)

type T = { env_lang : env_lang
         , env_tree : env_tree
         , rule_output : rule_output
         , rule_input : C_Ast.class_Pos list * int
         , stream_hook : (Symbol_Pos.T list * Symbol_Pos.T list * C_Transition.eval_node) list list
         , stream_lang : (C_Antiquote.antiq * C_Transition.antiq_language list) stream }

(**)

datatype 'a tree = Tree of 'a * 'a tree list

type ('LrTable_state, 'a, 'Position_T) stack' =
     ('LrTable_state, 'a, 'Position_T) stack0
   * C_Transition.eval_node list list
   * ('Position_T * 'Position_T) list
   * ('LrTable_state, 'a, 'Position_T) rule_ml tree list

(**)

fun map_env_lang f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                   {env_lang = f env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_env_tree f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                   {env_lang = env_lang, env_tree = f env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_rule_output f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                   {env_lang = env_lang, env_tree = env_tree, rule_output = f rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_rule_input f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                   {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = f rule_input, stream_hook = stream_hook, stream_lang = stream_lang}

fun map_stream_hook f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                   {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = f stream_hook, stream_lang = stream_lang}

fun map_stream_lang f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
                   {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
                    rule_input = rule_input, stream_hook = stream_hook, stream_lang = f stream_lang}

(**)

fun map_output_pos f {output_pos, output_vacuous, output_env} =
              {output_pos = f output_pos, output_vacuous = output_vacuous, output_env = output_env}

fun map_output_vacuous f {output_pos, output_vacuous, output_env} =
              {output_pos = output_pos, output_vacuous = f output_vacuous, output_env = output_env}

fun map_output_env f {output_pos, output_vacuous, output_env} =
              {output_pos = output_pos, output_vacuous = output_vacuous, output_env = f output_env}

(**)

fun map_tyidents f {tyidents, idents} =
                    {tyidents = f tyidents, idents = idents}

fun map_idents f {tyidents, idents} =
                    {tyidents = tyidents, idents = f idents}

(**)

fun map_var_table f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                    {var_table = f var_table, scopes = scopes, namesupply = namesupply, 
                     stream_ignored = stream_ignored, env_directives = env_directives}

fun map_scopes f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                    {var_table = var_table, scopes = f scopes, namesupply = namesupply, 
                     stream_ignored = stream_ignored, env_directives = env_directives}

fun map_namesupply f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                    {var_table = var_table, scopes = scopes, namesupply = f namesupply, 
                     stream_ignored = stream_ignored, env_directives = env_directives}

fun map_stream_ignored f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                    {var_table = var_table, scopes = scopes, namesupply = namesupply, 
                     stream_ignored = f stream_ignored, env_directives = env_directives}

fun map_env_directives f {var_table, scopes, namesupply, stream_ignored, env_directives} =
                    {var_table = var_table, scopes = scopes, namesupply = namesupply, 
                     stream_ignored = stream_ignored, env_directives = f env_directives}

(**)

fun map_context f {context, reports_text} =
                     {context = f context, reports_text = reports_text}

fun map_reports_text f {context, reports_text} =
                     {context = context, reports_text = f reports_text}

(**)

val empty_env_lang : env_lang = 
        {var_table = {tyidents = Symtab.make [], idents = Symtab.make []}, 
         scopes = [], namesupply = 0, stream_ignored = [],
         env_directives = Symtab.empty}
fun empty_env_tree context =
        {context = context, reports_text = []}
val empty_rule_output : rule_output = 
        {output_pos = NONE, output_vacuous = true, output_env = NONE}
fun make env_lang stream_lang env_tree =
         { env_lang = env_lang
         , env_tree = env_tree
         , rule_output = empty_rule_output
         , rule_input = ([], 0)
         , stream_hook = []
         , stream_lang = map_filter (fn C_Scan.Right (C_Lex.Token (_, (C_Lex.Space, _))) => NONE
                                      | C_Scan.Right (C_Lex.Token (_, (C_Lex.Comment _, _))) => NONE
                                      | C_Scan.Right tok => SOME (C_Scan.Right tok)
                                      | C_Scan.Left antiq => SOME (C_Scan.Left antiq))
                                    stream_lang }
fun string_of (env_lang : env_lang) = 
  let fun dest0 x f = x |> Symtab.dest |> map f
      fun dest {tyidents, idents} = (dest0 tyidents #1, dest0 idents (fn (i, (_,_,v)) => (i, if #global v then "global" else "local")))
  in \<^make_string> ( ("var_table", dest (#var_table env_lang))
                 , ("scopes", map (fn (id, i) => (Option.map (fn C_Ast.Ident0 (i, _, _) => (String.implode o C_Ast.to_list) i) id, dest i)) (#scopes env_lang))
                 , ("namesupply", #namesupply env_lang)
                 , ("stream_ignored", #stream_ignored env_lang)) end

(**)

val encode_positions =
     map (Position.dest
       #> (fn pos => ((#line pos, #offset pos, #end_offset pos), #props pos)))
  #> let open XML.Encode in list (pair (triple int int int) properties) end
  #> YXML.string_of_body
  
val decode_positions =
     YXML.parse_body
  #> let open XML.Decode in list (pair (triple int int int) properties) end
  #> map ((fn ((line, offset, end_offset), props) =>
           {line = line, offset = offset, end_offset = end_offset, props = props})
          #> Position.make)

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/context.ML\<close>\<close> \<open>
structure C_Env_Ext =
struct

fun map_tyidents f = C_Env.map_env_lang (C_Env.map_var_table (C_Env.map_tyidents f))
fun map_idents f = C_Env.map_env_lang (C_Env.map_var_table (C_Env.map_idents f))

(**)

fun map_var_table f = C_Env.map_env_lang (C_Env.map_var_table f)
fun map_scopes f = C_Env.map_env_lang (C_Env.map_scopes f)
fun map_namesupply f = C_Env.map_env_lang (C_Env.map_namesupply f)
fun map_stream_ignored f = C_Env.map_env_lang (C_Env.map_stream_ignored f)

(**)

fun get_tyidents (t:C_Env.T) = #env_lang t |> #var_table |> #tyidents

(**)

fun get_var_table (t:C_Env.T) = #env_lang t |> #var_table
fun get_scopes (t:C_Env.T) = #env_lang t |> #scopes
fun get_namesupply (t:C_Env.T) = #env_lang t |> #namesupply

(**)

fun map_output_pos f = C_Env.map_rule_output (C_Env.map_output_pos f)
fun map_output_vacuous f = C_Env.map_rule_output (C_Env.map_output_vacuous f)
fun map_output_env f = C_Env.map_rule_output (C_Env.map_output_env f)

(**)

fun get_output_pos (t : C_Env.T) = #rule_output t |> #output_pos

(**)

fun map_context f = C_Env.map_env_tree (C_Env.map_context f)
fun map_reports_text f = C_Env.map_env_tree (C_Env.map_reports_text f)

(**)

fun get_reports_text (t : C_Env.T) = #env_tree t |> #reports_text

(**)

fun map_env_directives' f {var_table, scopes, namesupply, stream_ignored, env_directives} =
  let val (res, env_directives) = f env_directives
  in (res, {var_table = var_table, scopes = scopes, namesupply = namesupply, 
                      stream_ignored = stream_ignored, env_directives = env_directives}) end

(**)

fun map_stream_lang' f {env_lang, env_tree, rule_output, rule_input, stream_hook, stream_lang} =
  let val (res, stream_lang) = f stream_lang
  in (res, {env_lang = env_lang, env_tree = env_tree, rule_output = rule_output, 
            rule_input = rule_input, stream_hook = stream_hook, stream_lang = stream_lang}) end

(**)

fun context_map (f : C_Env.env_tree -> C_Env.env_tree) =
  C_Env.empty_env_tree #> f #> #context


end 

\<close>

end
