(*  Title:      Pure/Thy/thy_header.ML
    Author:     Markus Wenzel, TU Muenchen

Theory headers -- independent of outer syntax.
*)

signature THY_HEADER =
sig
  val args: Token.T list -> (string * string list * (string * bool) list) * Token.T list
  val read: Position.T -> string -> string * string list * (Path.T * bool) list
  val thy_path: string -> Path.T
  val split_thy_path: Path.T -> Path.T * string
  val consistent_name: string -> string -> unit
end;

structure Thy_Header: THY_HEADER =
struct

(* keywords *)

val headerN = "header";
val theoryN = "theory";
val importsN = "imports";
val usesN = "uses";
val beginN = "begin";

val header_lexicon = Scan.make_lexicon
  (map Symbol.explode ["%", "(", ")", ";", beginN, headerN, importsN, theoryN, usesN]);


(* header args *)

val file_name = Parse.group "file name" Parse.name;
val theory_name = Parse.group "theory name" Parse.name;

val file =
  Parse.$$$ "(" |-- Parse.!!! (file_name --| Parse.$$$ ")") >> rpair false ||
  file_name >> rpair true;

val uses = Scan.optional (Parse.$$$ usesN |-- Parse.!!! (Scan.repeat1 file)) [];

val args =
  theory_name -- (Parse.$$$ importsN |--
    Parse.!!! (Scan.repeat1 theory_name -- uses --| Parse.$$$ beginN))
  >> Parse.triple2;


(* read header *)

val header =
  (Parse.$$$ headerN -- Parse.tags) |--
    (Parse.!!! (Parse.doc_source -- Scan.repeat Parse.semicolon --
      (Parse.$$$ theoryN -- Parse.tags) |-- args)) ||
  (Parse.$$$ theoryN -- Parse.tags) |-- Parse.!!! args;

fun read pos str =
  let val res =
    str
    |> Source.of_string_limited 8000
    |> Symbol.source
    |> Token.source {do_recover = NONE} (fn () => (header_lexicon, Scan.empty_lexicon)) pos
    |> Token.source_proper
    |> Source.source Token.stopper (Scan.single (Scan.error (Parse.!!! header))) NONE
    |> Source.get_single;
  in
    (case res of
      SOME ((name, imports, uses), _) => (name, imports, map (apfst Path.explode) uses)
    | NONE => error ("Unexpected end of input" ^ Position.str_of pos))
  end;


(* file name *)

val thy_path = Path.ext "thy" o Path.basic;

fun split_thy_path path =
  (case Path.split_ext path of
    (path', "thy") => (Path.dir path', Path.implode (Path.base path'))
  | _ => error ("Bad theory file specification: " ^ Path.print path));

fun consistent_name name name' =
  if name = name' then ()
  else error ("Bad file name " ^ Path.print (thy_path name) ^ " for theory " ^ quote name');

end;
