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

type ('a,'b) elem = (state * ('a * 'b * 'b))
type ('a,'b) stack = ('a,'b) elem list

val showState = fn (STATE s) => "STATE " ^ Int.toString s

fun printStack(stack: ('a,'b) elem list, n: int) =
   case stack
     of (state, _) :: rest =>
           (writeln ("          " ^ Int.toString n ^ ": " ^ showState state);
            printStack(rest, n+1)
           )
      | nil => ()

val parse = fn {table, saction, void, ec = {showTerminal, error, ...}, ...} =>
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

      fun parseStep (((token as TOKEN (terminal, (f_val,leftPos,rightPos))),
                    stack as (state,_) :: _), (lexer,arg)) =
          let val nextAction = action (state, terminal)
              val _ = if DEBUG1 then prAction(stack,(token, lexer),nextAction)
                      else ()
          in case nextAction
             of SHIFT s => (lexer, arg)
                           |> Scan.lift f_val -- Stream.get >> (fn (value, v) => (v, (s,(value, leftPos, rightPos)) :: stack))
                           |> parseStep
              | REDUCE i => (lexer, arg)
                           |> Scan.lift (fn arg =>
                                         case saction(i,leftPos,stack,arg)
                                         of (nonterm,(f_val, p1, p2),stack as (state,_) :: _ ) =>
                                             arg
                                             |> f_val >> (fn value => (token,(goto(state,nonterm),(value, p1, p2))::stack))
                                          | _ => raise (ParseImpossible 197))
                           |> parseStep
              | ERROR => (error("syntax error\n",leftPos,rightPos);
                          raise ParseError)
              | ACCEPT => (lexer, arg)
                          |> Stream.cons o pair token
                          |> (case stack
                              of (_,(topvalue,_,_)) :: _ => pair topvalue
                               | _ => raise (ParseImpossible 202))
          end
        | parseStep _ = raise (ParseImpossible 204)

  in Scan.lift void -- Stream.get >> (fn (void, p1 as TOKEN (_,(_,leftPos,_))) =>
                                      (p1,[(initialState table,(void,leftPos,leftPos))]))
     #> parseStep
  end
end;
