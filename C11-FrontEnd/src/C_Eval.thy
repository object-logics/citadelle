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

theory C_Eval
  imports C_Parser
          C_Annotation
begin

ML\<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/ML/ml_context.ML
    Author:     Makarius

ML context and antiquotations.
*)

structure C_Context =
struct

(* theory data *)

type env_direct = env_directives * C_Env.env_tree

structure Directives = Generic_Data
  (type T = (Position.T list
             * serial
             * (C_Lex.token_kind_directive
                -> env_direct
                -> int option (* result path of conditional directive to choose *)
                   * antiq_language list (* nested annotations from the input *)
                   * env_direct (*NOTE: remove the possibility of returning a too modified env?*)))
            Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = #2);


(* parsing and evaluation *)

local

fun scan_antiq context syms =
  let val keywords = C_Thy_Header.get_keywords' (Context.proof_of context)
  in ( C_Token.read_antiq'
         keywords
         (C_Parse.!!! (Scan.trace (C_Annotation.parse_command (Context.theory_of context))
                       >> (I #>> Antiq_stack)))
         syms
     , C_Token.read_with_commands'0 keywords syms)
  end

fun print0 s =
  maps
    (fn C_Lex.Token (_, (t as C_Lex.Directive d, _)) =>
        (s ^ @{make_string} t) :: print0 (s ^ "  ") (C_Lex.token_list_of d)
      | C_Lex.Token (_, t) => 
        [case t of (C_Lex.Char _, _) => "Text Char"
                 | (C_Lex.String _, _) => "Text String"
                 | _ => let val t' = @{make_string} (#2 t)
                        in
                          if String.size t' <= 2 then @{make_string} (#1 t)
                          else
                            s ^ @{make_string} (#1 t) ^ " "
                              ^ (String.substring (t', 1, String.size t' - 2)
                                 |> Markup.markup Markup.intensify)
                        end])

val print = tracing o cat_lines o print0 ""

in

fun markup_directive_command def ps (name, id) =
  let 
    fun markup_elem name = (name, (name, []): Markup.T);
    val (varN, var) = markup_elem "directive command";
    val entity = Markup.entity varN name
  in
    var ::
    ((if def then I else cons (Markup.keyword_properties Markup.keyword1)))
      (map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps)
  end

fun directive_update (name, pos) f tab =
  let val pos = [pos]
      val id = serial ()
      val _ = markup_directive_command true pos (name, id)
  in Symtab.update (name, (pos, id, f)) tab end

fun markup_directive_define def in_direct ps (name, id) =
  let 
    fun markup_elem name = (name, (name, []): Markup.T);
    val (varN, var) = markup_elem "directive define";
    val entity = Markup.entity varN name
  in
    var ::
    (cons (Markup.keyword_properties (if def orelse in_direct then Markup.operator else Markup.antiquote)))
      (map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps)
  end

fun eval'0 env err accept ants {context, reports_text} =
  let fun scan_comment tag pos (antiq as {explicit, body, ...}) cts =
           let val (res, l_comm) = scan_antiq context body
           in 
             Left
                 ( tag
                 , antiq
                 , l_comm
                 , if forall (fn Right _ => true | _ => false) res then
                     let val (l_msg, res) = split_list (map_filter (fn Right (msg, l_report, l_tok) => SOME (msg, (l_report, l_tok)) | _ => NONE) res)
                         val (l_report, l_tok) = split_list res
                     in [(Antiq_none (C_Lex.Token (pos, ((C_Lex.Comment o Right o SOME) (explicit, cat_lines l_msg, if explicit then flat l_report else []), cts))), l_tok)] end
                   else
                     map (fn Left x => x
                           | Right (msg, l_report, tok) =>
                               (Antiq_none (C_Lex.Token (C_Token.range_of [tok], ((C_Lex.Comment o Right o SOME) (explicit, msg, l_report), C_Token.content_of tok))), [tok]))
                         res)
           end

      val ants = map (fn C_Lex.Token (pos, (C_Lex.Comment (Left antiq), cts)) =>
                          scan_comment Comment_language pos antiq cts
                       | tok => Right tok)
                     ants

      fun map_ants f1 f2 = maps (fn Left x => f1 x | Right tok => f2 tok)

      val ants_none = map_ants (fn (_, _, _, l) => maps (fn (Antiq_none x, _) => [x] | _ => []) l) (K []) ants

      val _ = Position.reports (maps (fn Left (_, _, _, [(Antiq_none _, _)]) => []
                                       | Left (_, {start, stop, range = (pos, _), ...}, _, _) =>
                                          (case stop of SOME stop => cons (stop, Markup.antiquote)
                                                      | NONE => I)
                                            [(start, Markup.antiquote),
                                             (pos, Markup.language_antiquotation)]
                                       | _ => [])
                                     ants);
      val _ = Position.reports_text (maps C_Lex.token_report ants_none
                                     @ maps (fn Left (_, _, _, [(Antiq_none _, _)]) => []
                                              | Left (_, _, l, ls) =>
                                                  maps (fn (Antiq_stack (pos, _), _) => pos | _ => []) ls
                                                  @ maps (maps (C_Token.reports ())) (l :: map #2 ls)
                                              | _ => [])
                                            ants);
      val _ = C_Lex.check ants_none;

      val ((ants, {context, reports_text}), env) =
        C_Env_Ext.map_env_directives'
          (fn env_dir =>
            let val (ants, (env_dir, env_tree)) =
              fold_map
                let
                  fun subst_directive tok (range1 as (pos1, _)) name (env_dir, env_tree) =
                    case Symtab.lookup env_dir name of
                      NONE => (Right (Left tok), (env_dir, env_tree))
                    | SOME (pos0, id, toks) =>
                        let val _ = Position.reports [(pos1, Markup.language_antiquotation)]
                        in
                          ( Right (Right (pos1, map (C_Lex.set_range range1) toks))
                          , (env_dir, C_Env.map_reports_text (Hsk_c_parser.report [pos1] (markup_directive_define false false pos0) (name, id)) env_tree))
                        end
                in
                 fn Left (tag, antiq, toks, l_antiq) =>
                      fold_map (fn antiq as (Antiq_stack (_, Lexing (_, exec)), _) =>
                                     apsnd (stack_exec0 (exec Comment_language)) #> pair antiq
                                 | (Antiq_stack (rep, Parsing (syms, (range, env1, _, skip, exec))), toks) =>
                                     (fn env as (env_dir, _) =>
                                       ((Antiq_stack (rep, Parsing (syms, (range, env1, env_dir, skip, exec))), toks), env))
                                 | antiq => pair antiq)
                               l_antiq
                      #> apfst (fn l_antiq => Left (tag, antiq, toks, l_antiq))
                  | Right tok =>
                  case tok of
                    C_Lex.Token (_, (C_Lex.Directive dir, _)) =>
                      (case C_Lex.directive_first_cmd_of dir of
                         NONE => I
                       | SOME dir_tok =>
                         apsnd (C_Env.map_reports_text (append (map (fn tok => ((C_Lex.pos_of tok, Markup.antiquote), "")) (C_Lex.directive_tail_cmds_of dir))))
                         #>
                         let val name = C_Lex.content_of dir_tok
                             val pos1 = C_Lex.pos_of dir_tok
                         in
                           case Symtab.lookup (Directives.get context) name of
                             NONE => apsnd (C_Env.map_reports_text (cons ((pos1, Markup.antiquote), "")))
                           | SOME (pos0, id, exec) =>
                               apsnd (C_Env.map_reports_text (Hsk_c_parser.report [pos1] (markup_directive_command false pos0) (name, id)))
                               #> exec dir
                               #> (fn (_, _, env) => env)
                         end)
                      #> tap
                           (fn _ =>
                             app (fn C_Lex.Token ((pos, _), (C_Lex.Comment (Left _), _)) =>
                                     (Position.reports_text [((pos, Markup.ML_comment), "")];
                                      (* not yet implemented *)
                                      warning ("Ignored annotation in directive" ^ Position.here pos))
                                   | _ => ())
                                 (C_Lex.token_list_of dir))
                      #> pair (Right (Left tok))
                  | C_Lex.Token (pos, (C_Lex.Keyword, cts)) => subst_directive tok pos cts
                  | C_Lex.Token (pos, (C_Lex.Ident, cts)) => subst_directive tok pos cts
                  | _ => pair (Right (Left tok))
                end
                ants
                (env_dir, {context = context, reports_text = reports_text})
            in ((ants, env_tree), env_dir) end)
          env

      val ants_stack =
        map_ants (single o Left o (fn (_, a, _, l) => (a, maps (single o #1) l)))
                 (map Right o (fn Left tok => [tok] | Right (_, toks) => toks))
                 ants
      val _ = Position.reports_text (maps (fn Right (Left tok) => C_Lex.token_report tok
                                            | Right (Right (pos, [])) => [((pos, Markup.intensify), "")]
                                            | _ => [])
                                          ants);
      val ctxt = Context.proof_of context
      val () = if Config.get ctxt C_Options.lexer_trace andalso Context_Position.is_visible ctxt
               then print (map_filter (fn Right x => SOME x | _ => NONE) ants_stack)
               else ()
  in P.parse env err accept ants_stack {context = context, reports_text = reports_text} end


(* derived versions *)

fun eval' env err accept ants =
  Context.>> (C_Env_Ext.context_map
               let val tap_report = tap (Position.reports_text o #reports_text)
                                    #> (C_Env.empty_env_tree o #context)
               in eval'0 env
                         (fn env_lang => fn stack => fn pos => tap_report #> err env_lang stack pos)
                         (fn env_lang => fn stack => accept env_lang stack #> tap_report)
                         ants
               end)
end;

fun eval_source env err accept source =
  eval' env err accept (C_Lex.read_source source);

fun eval_source' env err accept source =
  eval'0 env err accept (C_Lex.read_source source);

end
\<close>

end
