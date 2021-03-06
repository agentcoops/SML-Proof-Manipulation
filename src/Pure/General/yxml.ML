(*  Title:      Pure/General/yxml.ML
    Author:     Makarius

Efficient text representation of XML trees using extra characters X
and Y -- no escaping, may nest marked text verbatim.

Markup <elem att="val" ...>...body...</elem> is encoded as:

  X Y name Y att=val ... X
  ...
  body
  ...
  X Y X
*)

signature YXML =
sig
  val escape_controls: string -> string
  val output_markup: Markup.T -> string * string
  val element: string -> XML.attributes -> string list -> string
  val string_of: XML.tree -> string
  val parse_body: string -> XML.body
  val parse: string -> XML.tree
  val parse_file: (XML.tree -> 'a -> 'a) -> Path.T -> 'a -> 'a
end;

structure YXML: YXML =
struct

(** string representation **)

(* idempotent recoding of certain low ASCII control characters *)

fun pseudo_utf8 c =
  if Symbol.is_ascii_control c
  then chr 192 ^ chr (128 + ord c)
  else c;

fun escape_controls str =
  if exists_string Symbol.is_ascii_control str
  then translate_string pseudo_utf8 str
  else str;


(* markers *)

val X = Symbol.ENQ;
val Y = Symbol.ACK;
val XY = X ^ Y;
val XYX = XY ^ X;


(* output *)

fun output_markup (markup as (name, atts)) =
  if Markup.is_empty markup then Markup.no_output
  else (XY ^ name ^ implode (map (fn (a, x) => Y ^ a ^ "=" ^ x) atts) ^ X, XYX);

fun element name atts body =
  let val (pre, post) = output_markup (name, atts)
  in pre ^ implode body ^ post end;

fun string_of t =
  let
    fun attrib (a, x) =
      Buffer.add Y #>
      Buffer.add a #> Buffer.add "=" #> Buffer.add x;
    fun tree (XML.Elem ((name, atts), ts)) =
          Buffer.add XY #> Buffer.add name #> fold attrib atts #> Buffer.add X #>
          fold tree ts #>
          Buffer.add XYX
      | tree (XML.Text s) = Buffer.add s;
  in Buffer.empty |> tree t |> Buffer.content end;



(** efficient YXML parsing **)

local

(* splitting *)

fun is_char s c = ord s = Char.ord c;

val split_string =
  Substring.full #>
  Substring.tokens (is_char X) #>
  map (Substring.fields (is_char Y) #> map Substring.string);


(* structural errors *)

fun err msg = raise Fail ("Malformed YXML encoding: " ^ msg);
fun err_attribute () = err "bad attribute";
fun err_element () = err "bad element";
fun err_unbalanced "" = err "unbalanced element"
  | err_unbalanced name = err ("unbalanced element " ^ quote name);


(* stack operations *)

fun add x ((elem, body) :: pending) = (elem, x :: body) :: pending;

fun push "" _ _ = err_element ()
  | push name atts pending = ((name, atts), []) :: pending;

fun pop ((("", _), _) :: _) = err_unbalanced ""
  | pop ((markup, body) :: pending) = add (XML.Elem (markup, rev body)) pending;

val stack_init = [(("", []), [])];

(* parsing *)

fun parse_attrib s =
  (case first_field "=" s of
    NONE => err_attribute ()
  | SOME ("", _) => err_attribute ()
  | SOME att => att);

fun parse_chunk ["", ""] = pop
  | parse_chunk ("" :: name :: atts) = push name (map parse_attrib atts)
  | parse_chunk txts = fold (add o XML.Text) txts;

fun preparse_chunk _ "" x = x
  | preparse_chunk f str (pending, results) =
      (case parse_chunk (String.fields (is_char Y) str) pending of
        [(("", _), [result])] => (stack_init, f result results)
      | x => (x, results));

in

fun parse_body source =
  (case fold parse_chunk (split_string source) stack_init of
    [(("", _), result)] => rev result
  | ((name, _), _) :: _ => err_unbalanced name);

fun parse source =
  (case parse_body source of
    [result] => result
  | [] => XML.Text ""
  | _ => err "multiple results");

(*folds a function over each XML.Tree in the file*)
fun parse_file f path s =
  (case File.fold_fields (is_char X) (preparse_chunk f)
      path (stack_init, s) of
    ([(("", _), [])], result) => result
  | (((name, _), _) :: _, _) => err_unbalanced name);

end;

end;

