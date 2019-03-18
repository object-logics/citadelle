(* Modified by Frédéric Tuong
 * Generation of Language.C Grammar with ML Interface Binding
 * (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* drt (12/15/89) -- the functor should be used during development work,
   but it is wastes space in the release version.

functor ParserGen(structure LrTable : LR_TABLE
                  structure Stream : STREAM) : LR_PARSER =
*)

structure LrParser1 : LR_PARSER1 =
struct

structure LrTable = LrTable
structure Stream = Stream1

structure Token : TOKEN =
  struct
      structure LrTable = LrTable
      datatype ('a,'b) token = TOKEN of LrTable.term * ('a * 'b * 'b)
      val sameToken = fn (TOKEN (t,_),TOKEN(t',_)) => t=t'
  end


open LrTable
open Token

val DEBUG1 = false
exception ParseImpossible of int

type ('a,'b) stack0 = (state * ('a * 'b * 'b)) list

type ('_b, '_c) stack = (LrTable.state * ('_b * '_c * '_c)) list
                      * (Position.range * ML_Lex.token Antiquote.antiquote list) list list
                      * ('_c * '_c) list
                      * (LrTable.state, '_b, '_c) C_Env.rule_ml C_Env.tree list

type ('_b, '_c, 'arg) lexer = (('arg -> '_b * 'arg,'_c) Token.token, ('_b, '_c) stack * 'arg) Stream.stream * 'arg

val showState = fn (STATE s) => "STATE " ^ Int.toString s

fun printStack(stack: ('a,'b) stack0, n: int) =
   case stack
     of (state, _) :: rest =>
           (writeln ("          " ^ Int.toString n ^ ": " ^ showState state);
            printStack(rest, n+1)
           )
      | nil => ()

fun parse {table, saction, void, void_position, accept, reduce_init, reduce_get, get_env_lang, ec = {showTerminal, error, ...}, ...} =
  let fun empty_tree rule_pos rule_type arg =
        C_Env.Tree ({rule_pos = rule_pos, rule_type = rule_type, rule_env_lang = get_env_lang arg, rule_static = NONE, rule_antiq = []}, [])

      fun prAction(stack as (state, _) :: _, (TOKEN (term,_),_), action) =
             (writeln "Parse: state stack:";
              printStack(stack, 0);
              writeln( "       state="
                     ^ showState state
                     ^ " next="
                     ^ showTerminal term
                     ^ " action="
                     ^ (case action
                          of SHIFT state => "SHIFT " ^ (showState state)
                           | REDUCE i => "REDUCE " ^ (Int.toString i)
                           | ERROR => "ERROR"
                           | ACCEPT => "ACCEPT")))
        | prAction (_,_,_) = ()

      val action = LrTable.action table
      val goto = LrTable.goto table

      fun add_stack (value, stack_value) stack_ml (pos, stack_pos) (tree, stack_tree) =
        (value :: stack_value, [] :: stack_ml, pos :: stack_pos, tree :: stack_tree)

      fun parseStep ( (token as TOKEN (terminal, (f_val,leftPos,rightPos)))
                    , (lexer, (((stack as (state,_) :: _), stack_ml, stack_pos, stack_tree), arg))) =
          let val nextAction = action (state, terminal)
              val _ = if DEBUG1 then prAction(stack,(token, lexer),nextAction)
                      else ()
          in case nextAction
             of SHIFT s => (lexer, arg)
                           ||> (f_val #>> (fn value => add_stack ((s, (value, leftPos, rightPos)), stack)
                                                                 stack_ml
                                                                 ((leftPos, rightPos), stack_pos)
                                                                 (empty_tree (leftPos, rightPos) C_Env.Shift arg, stack_tree)))
                           |> Stream.get
                           |> parseStep
              | REDUCE i =>
                (case saction (i, leftPos, stack, arg)
                 of (nonterm, (reduce_exec, p1, p2), stack' as (state, _) :: _) =>
                   let val dist = length stack - length stack'
                       val arg = reduce_init ((stack_pos, dist), arg)
                       val (value, arg) = reduce_exec arg
                       val (goto0', arg) = reduce_get arg
                       val goto0 = (goto (state, nonterm), (value, p1, p2))
                       val ((l_ml, stack_ml), stack_pos, (l_tree, stack_tree)) =
                         ( chop dist stack_ml
                           |>> (fn st0 => fold (fold (cons o pair (i, goto0))) st0 [])
                         , drop dist stack_pos
                         , chop dist stack_tree)
                       val pos = case #output_pos goto0' of NONE => (p1, p2) | SOME pos => pos
                   in ( add_stack
                          (goto0, stack')
                          stack_ml
                          (pos, stack_pos)
                          ( C_Env.Tree ( { rule_pos = pos
                                         , rule_type = C_Env.Reduce i
                                         , rule_env_lang = get_env_lang arg
                                         , rule_static = #output_env goto0'
                                         , rule_antiq = l_ml }
                                       , rev l_tree )
                          , stack_tree)
                      , arg) end
                 | _ => raise (ParseImpossible 197))
                |> (fn stack_arg => parseStep (token, (lexer, stack_arg)))
              | ERROR => (lexer, ((stack, stack_ml, stack_pos, stack_tree), arg))
                         |> Stream.cons o pair token
                         ||> error
              | ACCEPT => (lexer, ((stack, stack_ml, stack_pos, stack_tree), arg))
                          |> Stream.cons o pair token
                          ||> accept
          end
        | parseStep _ = raise (ParseImpossible 204)
  in I
     ##> (fn arg => void arg
            |>> (fn void' => add_stack ((initialState table, (void', void_position, void_position)), [])
                                       []
                                       ((void_position, void_position), [])
                                       (empty_tree (void_position, void_position) C_Env.Void arg, [])))
     #> Stream.get 
     #> parseStep 
end

end;
