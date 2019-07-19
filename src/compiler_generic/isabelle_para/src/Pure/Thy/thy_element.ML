(*  Title:      Pure/Thy/thy_element.ML
    Author:     Makarius

Theory elements: statements with optional proof.
*)

signature THY_ELEMENT =
sig
  datatype 'a element = Element of 'a * ('a element list * 'a) option
  val atom: 'a -> 'a element
  val map_element: ('a -> 'b) -> 'a element -> 'b element
  val exists_element: ('a -> bool) -> 'a element -> bool
  val flat_element: 'a element -> 'a list
  val last_element: 'a element -> 'a
  val parse_elements: Keyword.keywords -> (Command_Span.kind -> 'a) -> ('a -> Command_Span.kind) -> 'a list -> 'a element list
end;

structure Thy_Element: THY_ELEMENT =
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

fun parse_element keywords f =
  let
    fun category pred other =
      Scan.one
        (fn name => case f name of Command_Span.Command_Span (name, _) =>
            pred keywords name
          | _ => other);

    fun theory_element x =
      (category Keyword.is_theory_goal false -- proof >> element) x
    and proof_element x =
      (category Keyword.is_proof_goal false -- proof >> element ||
        category Keyword.is_proof_body true >> atom) x
    and proof x = (Scan.repeat proof_element -- category Keyword.is_qed false) x;

    val default_element = Scan.one (not_eof f) >> atom;
  in theory_element || default_element end;

in

fun parse_elements keywords f_mk f =
  Source.of_list #>
  Source.source (stopper f_mk f) (Scan.bulk (parse_element keywords f)) #>
  Source.exhaust;

end;

end;
