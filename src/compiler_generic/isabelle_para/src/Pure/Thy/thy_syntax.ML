(*  Title:      Pure/Thy/thy_syntax.ML
    Author:     Makarius

Theory syntax elements.
*)

signature THY_SYNTAX =
sig
  datatype 'a element = Element of 'a * ('a element list * 'a) option
  val atom: 'a -> 'a element
  val map_element: ('a -> 'b) -> 'a element -> 'b element
  val exists_element: ('a -> bool) -> 'a element -> bool
  val flat_element: 'a element -> 'a list
  val last_element: 'a element -> 'a
  val parse_elements: Keyword.keywords -> (Command_Span.kind -> 'a) -> ('a -> Command_Span.kind) -> 'a list -> 'a element list
end;

structure Thy_Syntax: THY_SYNTAX =
struct

(* datatype element: command with optional proof *)

datatype 'a element = Element of 'a * ('a element list * 'a) option;

fun element (a, b) = Element (a, SOME b);
fun atom a = Element (a, NONE);

fun map_element f (Element (a, NONE)) = Element (f a, NONE)
  | map_element f (Element (a, SOME (elems, b))) =
      Element (f a, SOME ((map o map_element) f elems, f b));

fun exists_element f (Element (a, NONE)) = f a
  | exists_element f (Element (a, SOME (elems, b))) =
      f a orelse (exists o exists_element) f elems orelse f b;

fun flat_element (Element (a, NONE)) = [a]
  | flat_element (Element (a, SOME (elems, b))) = a :: maps flat_element elems @ [b];

fun last_element (Element (a, NONE)) = a
  | last_element (Element (_, SOME (_, b))) = b;


(* scanning spans *)

fun eof f_mk = f_mk (Command_Span.Command_Span ("", Position.none));

fun is_eof f name = (case f name of Command_Span.Command_Span ("", _) => true | _ => false);

fun not_eof f = not o is_eof f;

fun stopper f_mk f = Scan.stopper (K (eof f_mk)) (is_eof f);


(* parse *)

local

fun command_with f pred =
  Scan.one
    (fn name => case f name of Command_Span.Command_Span (name, _) => pred name | _ => false);

fun parse_element keywords f =
  let
    val proof_atom =
      Scan.one
        (fn name =>
          case f name of Command_Span.Command_Span (name, _) => Keyword.is_proof_body keywords name
          | _ => true) >> atom;
    fun proof_element x =
      (command_with f (Keyword.is_proof_goal keywords) -- proof_rest >> element || proof_atom) x
    and proof_rest x =
      (Scan.repeat proof_element -- command_with f (Keyword.is_qed keywords)) x;
  in
    command_with f (Keyword.is_theory_goal keywords) -- proof_rest >> element ||
    Scan.one (not_eof f) >> atom
  end;

in

fun parse_elements keywords f_mk f =
  Source.of_list #>
  Source.source (stopper f_mk f) (Scan.bulk (parse_element keywords f)) #>
  Source.exhaust;

end;

end;
