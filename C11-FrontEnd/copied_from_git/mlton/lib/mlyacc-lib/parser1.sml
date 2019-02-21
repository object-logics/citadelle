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
exception ParseError
exception ParseImpossible of int

type ('a,'b) stack = (state * ('a * 'b * 'b)) list

val showState = fn (STATE s) => "STATE " ^ Int.toString s

fun printStack(stack: ('a,'b) stack, n: int) =
   case stack
     of (state, _) :: rest =>
           (writeln ("          " ^ Int.toString n ^ ": " ^ showState state);
            printStack(rest, n+1)
           )
      | nil => ()

fun parse {table, saction, void, void_position, reduce, accept, position_init, position_get, ec = {showTerminal, error, ...}, ...} =
  let fun prAction(stack as (state, _) :: _, (TOKEN (term,_),_), action) =
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

      fun add_stack x stack stack_ml pos stack_pos = (x :: stack, [] :: stack_ml, pos :: stack_pos)

      fun parseStep ( (token as TOKEN (terminal, (f_val,leftPos,rightPos)))
                    , (lexer, (((stack as (state,_) :: _), stack_ml, stack_pos), arg))) =
          let val nextAction = action (state, terminal)
              val _ = if DEBUG1 then prAction(stack,(token, lexer),nextAction)
                      else ()
          in case nextAction
             of SHIFT s => (lexer, arg)
                           ||> (f_val #>> (fn value => add_stack (s, (value, leftPos, rightPos)) stack stack_ml (leftPos, rightPos) stack_pos))
                           |> Stream.get
                           |> parseStep
              | REDUCE i =>
                (case saction (i, leftPos, stack, arg)
                 of (nonterm, (f_val, p1, p2), stack' as (state, _) :: _) =>
                   let val len = length stack
                       val len' = length stack'
                       val arg = position_init ((stack_pos, len - len'), arg)
                       val (value, arg) = f_val arg
                       val (goto0_pos, arg) = position_get arg
                       val goto0 = (goto (state, nonterm), (value, p1, p2))
                       val ((arg, stack_ml), stack_pos) =
                         if len = len' then ((arg, stack_ml), stack_pos)
                         else
                           ( chop (len - len') stack_ml
                             |>> (fn st0 => fold_rev (fold_rev (curry (I #>> pair (i, goto0) #> reduce)))
                                                     st0
                                                     arg)
                           , drop (len - len') stack_pos)
                   in (add_stack goto0 stack' stack_ml (case goto0_pos of NONE => (p1, p2) | SOME pos => pos) stack_pos, arg) end
                 | _ => raise (ParseImpossible 197))
                |> (fn stack_arg => parseStep (token, (lexer, stack_arg)))
              | ERROR => (error (stack,leftPos,rightPos);
                          raise ParseError)
              | ACCEPT => (lexer, ((stack, stack_ml, stack_pos), arg))
                          |> Stream.cons o pair token
                          |> (fn (lexer, ((stack, stack_ml, stack_pos), arg)) =>
                              case stack
                              of (_,(topvalue,_,_)) :: _ => pair topvalue (lexer, accept ((stack, stack_ml, stack_pos), arg))
                               | _ => raise (ParseImpossible 202))
          end
        | parseStep _ = raise (ParseImpossible 204)
  in I
     ##> (void #>> (fn void' => add_stack (initialState table, (void', void_position, void_position)) [] [] (void_position, void_position) []))
     #> Stream.get 
     #> parseStep 
end

end;
