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
  imports C_Parser_Language
          C_Parser_Annotation
begin

section \<open>\<close> \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/thy_info.ML\<close>: \<^theory>\<open>C.C_Parser_Language\<close>\<close>

text\<open>The parser consists of a generic module @{file "../copied_from_git/mlton/lib/mlyacc-lib/base.sig"}, 
which interprets a automata-like format generated from smlyacc.\<close>

ML \<comment> \<open>\<^theory>\<open>C.C_Environment\<close>\<close> \<open>
structure C_Stack =
struct
type 'a stack_elem = (LALR_Table.state, 'a, Position.T) C_Env.stack_elem0
type stack_data = (LALR_Table.state, C_Grammar.Tokens.svalue0, Position.T) C_Env.stack0
type stack_data_elem = (LALR_Table.state, C_Grammar.Tokens.svalue0, Position.T) C_Env.stack_elem0

fun map_svalue0 f (st, (v, pos1, pos2)) = (st, (f v, pos1, pos2))

structure Data_Lang = Generic_Data
  (type T = stack_data * C_Env.env_lang
   val empty = ([], C_Env.empty_env_lang)
   val extend = K empty
   val merge = K empty)

structure Data_Tree_Args =
struct
  type T = C_Position.reports_text
  val empty = []
  val extend = I
  val merge = op @
end

structure Data_Tree = Generic_Data (Data_Tree_Args)

fun setmp_tree f context =
  let val x = Data_Tree.get context
      val context = f (Data_Tree.put [] context)
  in (Data_Tree.get context, Data_Tree.put x context) end

fun stack_exec0 f {context, reports_text} =
  let val (reports_text', context) = setmp_tree f context
  in {context = context, reports_text = append reports_text' reports_text} end

fun stack_exec env_dir data_put f =
  stack_exec0 (Data_Lang.put (apsnd (C_Env.map_env_directives (K env_dir)) data_put) #> f)
end
\<close>

ML \<comment> \<open>\<^theory>\<open>C.C_Lexer\<close>\<close> \<open>
structure C_Grammar_Lexer : ARG_LEXER1 =
struct
structure LALR_Lex_Instance =
struct
  type ('a,'b) token = ('a, 'b) C_Grammar.Tokens.token
  type pos = Position.T
  type arg = C_Grammar.Tokens.arg
  type svalue0 = C_Grammar.Tokens.svalue0
  type svalue = arg -> svalue0 * arg
  type state = C_Grammar.ParserData.LALR_Table.state
end

type stack = (LALR_Lex_Instance.state, LALR_Lex_Instance.svalue0, LALR_Lex_Instance.pos) C_Env.stack'

fun advance_hook stack = (fn f => fn (arg, stack_ml) => f (#stream_hook arg) (arg, stack_ml))
 (fn [] => I | l :: ls =>
  I
  #> fold_rev 
    (fn (_, syms, ml_exec) =>
      let
        val len = length syms
      in 
        if len = 0 then
          I #>>
          (case ml_exec of
             (_, C_Transition.Bottom_up, env_dir, _, exec) =>
              (fn arg => C_Env.map_env_tree (C_Stack.stack_exec env_dir (stack, #env_lang arg) (exec NONE))
                                            arg)
           | ((pos, _), _, _, _, _) =>
              C_Env_Ext.map_context (fn _ => error ("Style of evaluation not yet implemented" ^ Position.here pos)))
        else
          I ##>
          let
            val len = len - 1
          in
            tap (fn stack_ml =>
              if length stack_ml = 1 orelse length stack_ml - len = 1 then
                warning ("Unevaluated code as the hook is pointing to an internal initial value" ^ Position.here (ml_exec |> #1 |> Position.range_position))
              else ())
            #>
            tap (fn stack_ml =>
              if length stack_ml - len <= 0 then
                error ("Maximum depth reached (" ^ Int.toString (len - length stack_ml + 1) ^ " in excess)" ^ Position.here (Symbol_Pos.range syms |> Position.range_position))
              else ())
            #>
            nth_map len (cons ml_exec)
          end
      end)
    l
  #>> C_Env.map_stream_hook (K ls))

fun makeLexer ((stack, stack_ml, stack_pos, stack_tree), arg) =
  let val (token, arg) = C_Env_Ext.map_stream_lang' (fn [] => (NONE, []) | x :: xs => (SOME x, xs)) arg
      fun return0' f x =
        let val (arg, stack_ml) = f stack (arg, stack_ml)
        in (x, ((stack, stack_ml, stack_pos, stack_tree), arg)) end
      val return0 = return0' advance_hook
      open C_Ast
      open C_Scan
  in
    case token
    of NONE => 
        return0'
          (fn stack => 
            advance_hook stack
            #> tap (fn (arg, _) => 
              fold (uncurry
                     (fn pos => 
                       fold_rev (fn (syms, _, _) => fn () =>
                                  let val () = error ("Maximum depth reached (" ^ Int.toString (pos + 1) ^ " in excess)" ^ Position.here (Symbol_Pos.range syms |> Position.range_position))
                                  in () end)))
                   (map_index I (#stream_hook arg))
                   ()))
          (C_Grammar.Tokens.x25_eof (Position.none, Position.none))
     | SOME (Left (antiq_raw, l_antiq)) =>
        makeLexer
          ( (stack, stack_ml, stack_pos, stack_tree)
          , (arg, false)
             |> fold (fn C_Transition.Antiq_stack (_, C_Transition.Parsing ((syms_shift, syms), ml_exec)) =>
                         I #>>
                           (C_Env.map_stream_hook
                             (fn stream_hook => 
                              case
                                 fold (fn _ => fn (eval1, eval2) =>
                                     (case eval2 of e2 :: eval2 => (e2, eval2)
                                                  | [] => ([], []))
                                     |>> (fn e1 => e1 :: eval1))
                                   syms_shift
                                   ([], stream_hook)
                              of (eval1, eval2) => fold cons
                                                        eval1
                                                        (case eval2 of e :: es => ((syms_shift, syms, ml_exec) :: e) :: es
                                                                     | [] => [[(syms_shift, syms, ml_exec)]])))
                       | C_Transition.Antiq_stack (_, C_Transition.Never) => I ##> K true
                       | _ => I)
                     l_antiq
             |> (fn (arg, false) => arg
                  | (arg, true) => C_Env_Ext.map_stream_ignored (cons (Left antiq_raw)) arg))
     | SOME (Right (tok as C_Lex.Token (_, (C_Lex.Directive _, _)))) =>
        makeLexer ((stack, stack_ml, stack_pos, stack_tree), C_Env_Ext.map_stream_ignored (cons (Right tok)) arg)
     | SOME (Right (C_Lex.Token ((pos1, pos2), (tok, src)))) =>
       case tok of
         C_Lex.Char (b, [c]) =>
          return0 (C_Grammar.Tokens.cchar (CChar (String.sub (c,0)) b, pos1, pos2))
       | C_Lex.String (b, s) =>
          return0 (C_Grammar.Tokens.cstr (CString0 (From_string (implode s), b), pos1, pos2))
       | C_Lex.Integer (i, repr, flag) =>
          return0 (C_Grammar.Tokens.cint
                    ( CInteger i repr
                        (C_Lex.read_bin (fold (fn flag => map (fn (bit, flag0) => (if flag = flag0 then "1" else bit, flag0)))
                                              flag
                                              ([FlagUnsigned, FlagLong, FlagLongLong, FlagImag] |> rev |> map (pair "0"))
                                         |> map #1)
                         |> Flags)
                    , pos1
                    , pos2))
       | C_Lex.Ident => 
          let val (name, arg) = C_Grammar_Rule_Lib.getNewName arg
              val ident0 = C_Grammar_Rule_Lib.mkIdent (C_Grammar_Rule_Lib.posOf' false (pos1, pos2)) src name
          in return0
               (if C_Grammar_Rule_Lib.isTypeIdent src arg then
                  C_Grammar.Tokens.tyident (ident0, pos1, pos2)
                else
                  C_Grammar.Tokens.ident (ident0, pos1, pos2))
          end
       | _ => 
          C_Grammar_Tokens.token_of_string
                          (C_Grammar.Tokens.error (pos1, pos2))
                          (ClangCVersion0 (From_string src))
                          (CChar #"0" false)
                          (CFloat (From_string src))
                          (CInteger 0 DecRepr (Flags 0))
                          (CString0 (From_string src, false))
                          (Ident (From_string src, 0, OnlyPos NoPosition (NoPosition, 0)))
                          src
                          pos1
                          pos2
                          src
          |> return0
  end
end
\<close>

text\<open>This is where the instatiation of the Parser Functor with the Lexer actually happens ...\<close>

ML \<comment> \<open>\<^theory>\<open>C.C_Parser_Language\<close>\<close> \<open>
structure C_Grammar_Parser =
  LALR_Parser_Join (structure LrParser = LALR_Parser_Eval
                    structure ParserData = C_Grammar.ParserData
                    structure Lex = C_Grammar_Lexer)
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_compiler.ML\<close>\<close> \<open>
structure C_Language = struct

open C_Env

fun exec_tree write msg (Tree ({rule_pos, rule_type}, l_tree)) =
  case rule_type of
    Void => write msg rule_pos "VOID" NONE
  | Shift => write msg rule_pos "SHIFT" NONE
  | Reduce (rule_static, (rule0, vacuous, rule_antiq)) =>
      write msg rule_pos ("REDUCE " ^ Int.toString rule0 ^ " " ^ (if vacuous then "X" else "O")) (SOME (C_Grammar_Rule.string_reduce rule0 ^ " " ^ C_Grammar_Rule.type_reduce rule0))
      #> (case rule_static of SOME rule_static => rule_static #>> SOME | NONE => pair NONE)
      #-> (fn env_lang =>
            fold (fn (stack0, env_lang0, (_, C_Transition.Top_down, env_dir, _, exec)) =>
                     C_Stack.stack_exec env_dir (stack0, Option.getOpt (env_lang, env_lang0)) (exec (SOME rule0))
                   | _ => I)
                 rule_antiq)
      #> fold (exec_tree write (msg ^ " ")) l_tree

fun exec_tree' l env_tree = env_tree
  |> fold (exec_tree let val ctxt = Context.proof_of (#context env_tree)
                         val write =
                           if Config.get ctxt C_Options.parser_trace andalso Context_Position.is_visible ctxt
                              then fn f => tap (tracing o f) else K I
                     in fn msg => fn (p1, p2) => fn s1 => fn s2 =>
                       write (fn _ => msg ^ s1 ^ " " ^ Position.here p1 ^ " " ^ Position.here p2 ^ (case s2 of SOME s2 => " " ^ s2 | NONE => ""))
                     end
                     "")
          l

fun uncurry_context f pos = uncurry (fn x => fn arg => map_env_tree (f pos x (#env_lang arg)) arg)

fun eval env_lang err accept stream_lang =
 make env_lang stream_lang
 #> C_Grammar_Parser.makeLexer
 #> C_Grammar_Parser.parse
      ( 0
      , uncurry_context (fn (next_pos1, next_pos2) => fn (stack, _, _, stack_tree) => fn env_lang =>
          C_Env.map_reports_text
            (cons ( ( Position.range_position (case hd stack of (_, (_, pos1, pos2)) => (pos1, pos2))
                    , Markup.bad ())
                  , "")
            #> (case rev (tl stack) of
                  _ :: _ :: stack =>
                 append
                   (map_filter (fn (pos1, pos2) =>
                                if Position.offset_of pos1 = Position.offset_of pos2
                                then NONE
                                else SOME ((Position.range_position (pos1, pos2), Markup.intensify), ""))
                              ((next_pos1, next_pos2) :: map (fn (_, (_, pos1, pos2)) => (pos1, pos2)) stack))
                | _ => I))
          #> exec_tree' (rev stack_tree)
          #> err env_lang stack (Position.range_position (case hd stack_tree of Tree ({rule_pos = (rule_pos1, _), ...}, _) => (rule_pos1, next_pos2))))
      , Position.none
      , uncurry_context (fn _ => fn (stack, _, _, stack_tree) => fn env_lang =>
          exec_tree' stack_tree
          #> accept env_lang (stack |> hd |> C_Stack.map_svalue0 C_Grammar_Rule.reduce0))
      , fn (stack, arg) => arg |> map_rule_input (K stack)
                               |> map_rule_output (K empty_rule_output)
      , fn (rule0, stack0, pre_ml) => fn arg =>
          let val rule_output = #rule_output arg
              val env_lang = #env_lang arg
              val (delayed, actual) =
                if #output_vacuous rule_output
                then let fun f (_, _, _, to_delay, _) = to_delay
                     in (map (filter f) pre_ml, map (filter_out f) pre_ml) end
                else ([], pre_ml)
              val actual = flat (map rev actual)
          in
            ( (delayed, map (fn x => (stack0, env_lang, x)) actual, rule_output)
            , fold (fn (_, C_Transition.Bottom_up, env_dir, _, exec) =>
                       C_Env.map_env_tree (C_Stack.stack_exec env_dir (stack0, env_lang) (exec (SOME rule0)))
                     | _ => I)
                   actual
                   arg)
          end)
 #> snd
 #> #env_tree
end
\<close>

section \<open>\<close> \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/thy_info.ML\<close>: \<^theory>\<open>C.C_Parser_Language\<close>, \<^theory>\<open>C.C_Parser_Annotation\<close>\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_context.ML\<close>\<close> \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      Pure/ML/ml_context.ML
    Author:     Makarius

ML context and antiquotations.
*)

structure C_Context =
struct
fun fun_decl a v s ctxt =
  let
    val (b, ctxt') = ML_Context.variant a ctxt;
    val env = "fun " ^ b ^ " " ^ v ^ " = " ^ s ^ " " ^ v ^ ";\n";
    val body = ML_Context.struct_name ctxt ^ "." ^ b;
    fun decl (_: Proof.context) = (env, body);
  in (decl, ctxt') end;

(* theory data *)

type env_direct = C_Transition.env_directives * C_Env.env_tree

structure Directives = Generic_Data
  (type T = (Position.T list
             * serial
             * (C_Lex.token_kind_directive
                -> env_direct
                -> int option (* result path of conditional directive to choose *)
                   * C_Transition.antiq_language list (* nested annotations from the input *)
                   * env_direct (*NOTE: remove the possibility of returning a too modified env?*)))
            Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.join (K #2));


(* parsing and evaluation *)

local

fun scan_antiq context syms =
  let val keywords = C_Thy_Header.get_keywords' (Context.proof_of context)
  in ( C_Token.read_antiq'
         keywords
         (C_Parse.!!! (Scan.trace (C_Annotation.parse_command (Context.theory_of context))
                       >> (I #>> C_Transition.Antiq_stack)))
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

open C_Scan
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
  let val id = serial ()
      val _ = Position.reports (map (pair pos) (markup_directive_command true [pos] (name, id)))
  in Symtab.update (name, ([pos], id, f)) tab end

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

fun eval env err accept ants {context, reports_text} =
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
                     in [(C_Transition.Antiq_none (C_Lex.Token (pos, ((C_Lex.Comment o C_Lex.Comment_suspicious o SOME) (explicit, cat_lines l_msg, if explicit then flat l_report else []), cts))), l_tok)] end
                   else
                     map (fn Left x => x
                           | Right (msg, l_report, tok) =>
                               (C_Transition.Antiq_none (C_Lex.Token (C_Token.range_of [tok], ((C_Lex.Comment o C_Lex.Comment_suspicious o SOME) (explicit, msg, l_report), C_Token.content_of tok))), [tok]))
                         res)
           end

      val ants = map (fn C_Lex.Token (pos, (C_Lex.Comment (C_Lex.Comment_formal antiq), cts)) =>
                          scan_comment C_Transition.Comment_language pos antiq cts
                       | tok => Right tok)
                     ants

      fun map_ants f1 f2 = maps (fn Left x => f1 x | Right tok => f2 tok)

      val ants_none = map_ants (fn (_, _, _, l) => maps (fn (C_Transition.Antiq_none x, _) => [x] | _ => []) l) (K []) ants

      val _ = Position.reports (maps (fn Left (_, _, _, [(C_Transition.Antiq_none _, _)]) => []
                                       | Left (_, {start, stop, range = (pos, _), ...}, _, _) =>
                                          (case stop of SOME stop => cons (stop, Markup.antiquote)
                                                      | NONE => I)
                                            [(start, Markup.antiquote),
                                             (pos, Markup.language_antiquotation)]
                                       | _ => [])
                                     ants);
      val _ = Position.reports_text (maps C_Lex.token_report ants_none
                                     @ maps (fn Left (_, _, _, [(C_Transition.Antiq_none _, _)]) => []
                                              | Left (_, _, l, ls) =>
                                                  maps (fn (C_Transition.Antiq_stack (pos, _), _) => pos | _ => []) ls
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
                          , (env_dir, C_Env.map_reports_text (C_Grammar_Rule_Lib.report [pos1] (markup_directive_define false false pos0) (name, id)) env_tree))
                        end
                in
                 fn Left (tag, antiq, toks, l_antiq) =>
                      fold_map (fn antiq as (C_Transition.Antiq_stack (_, C_Transition.Lexing (_, exec)), _) =>
                                     apsnd (C_Stack.stack_exec0 (exec C_Transition.Comment_language)) #> pair antiq
                                 | (C_Transition.Antiq_stack (rep, C_Transition.Parsing (syms, (range, env1, _, skip, exec))), toks) =>
                                     (fn env as (env_dir, _) =>
                                       ((C_Transition.Antiq_stack (rep, C_Transition.Parsing (syms, (range, env1, env_dir, skip, exec))), toks), env))
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
                               apsnd (C_Env.map_reports_text (C_Grammar_Rule_Lib.report [pos1] (markup_directive_command false pos0) (name, id)))
                               #> exec dir
                               #> (fn (_, _, env) => env)
                         end)
                      #> tap
                           (fn _ =>
                             app (fn C_Lex.Token ((pos, _), (C_Lex.Comment (C_Lex.Comment_formal _), _)) =>
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
  in C_Language.eval env err accept ants_stack {context = context, reports_text = reports_text} end


(* derived versions *)

fun eval' env err accept ants =
  Context.>> (fn context =>
               C_Env_Ext.context_map
                 let val tap_report = tap (Position.reports_text o #reports_text)
                                      #> (C_Env.empty_env_tree o #context)
                 in eval (env context)
                         (fn env_lang => fn stack => fn pos => tap_report #> err env_lang stack pos)
                         (fn env_lang => fn stack => accept env_lang stack #> tap_report)
                         ants
                 end
                 context)
end;

fun eval_source env err accept source =
  eval' env err accept (C_Lex.read_source source);

fun eval_source' env err accept source =
  eval env err accept (C_Lex.read_source source);

fun expression struct_open range name constraint body ants context = context |>
  ML_Context.exec let val verbose = Config.get (Context.proof_of context) C_Options.ML_verbose
                  in fn () =>
    ML_Context.eval (ML_Compiler.verbose verbose ML_Compiler.flags) (#1 range)
     (ML_Lex.read ("Context.put_generic_context (SOME (let open " ^ struct_open ^ " val ") @ ML_Lex.read_set_range range name @
      ML_Lex.read (": " ^ constraint ^ " =") @ ants @
      ML_Lex.read ("in " ^ body ^ " end (Context.the_generic_context ())));")) end;
end
\<close>

end
