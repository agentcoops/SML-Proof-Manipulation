(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

The global Isabelle/Isar outer syntax.

Note: the syntax for files is statically determined at the very
beginning; for interactive processing it may change dynamically.
*)

signature OUTER_SYNTAX =
sig
  val command: string -> string -> Keyword.T ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val markup_command: Thy_Output.markup -> string -> string -> Keyword.T ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val improper_command: string -> string -> Keyword.T ->
    (Toplevel.transition -> Toplevel.transition) parser -> unit
  val internal_command: string -> (Toplevel.transition -> Toplevel.transition) parser -> unit
  val local_theory': string -> string -> Keyword.T ->
    (bool -> local_theory -> local_theory) parser -> unit
  val local_theory: string -> string -> Keyword.T ->
    (local_theory -> local_theory) parser -> unit
  val local_theory_to_proof': string -> string -> Keyword.T ->
    (bool -> local_theory -> Proof.state) parser -> unit
  val local_theory_to_proof: string -> string -> Keyword.T ->
    (local_theory -> Proof.state) parser -> unit
  val print_outer_syntax: unit -> unit
  val scan: Position.T -> string -> Token.T list
  val parse: Position.T -> string -> Toplevel.transition list
  val process_file: Path.T -> theory -> theory
  type isar
  val isar: TextIO.instream -> bool -> isar
  val prepare_command: Position.T -> string -> Toplevel.transition
  val load_thy: string -> (Path.T option -> theory) -> Position.T -> string -> theory * unit future
end;

structure Outer_Syntax: OUTER_SYNTAX =
struct

(** outer syntax **)

(* command parsers *)

datatype command = Command of
 {comment: string,
  markup: Thy_Output.markup option,
  int_only: bool,
  parse: (Toplevel.transition -> Toplevel.transition) parser};

fun make_command comment markup int_only parse =
  Command {comment = comment, markup = markup, int_only = int_only, parse = parse};


(* parse command *)

local

fun terminate false = Scan.succeed ()
  | terminate true = Parse.group "end of input" (Scan.option Parse.sync -- Parse.semicolon >> K ());

fun body cmd (name, _) =
  (case cmd name of
    SOME (Command {int_only, parse, ...}) =>
      Parse.!!! (Scan.prompt (name ^ "# ") (Parse.tags |-- parse >> pair int_only))
  | NONE => raise Fail ("No parser for outer syntax command " ^ quote name));

in

fun parse_command do_terminate cmd =
  Parse.semicolon >> K NONE ||
  Parse.sync >> K NONE ||
  (Parse.position Parse.command :-- body cmd) --| terminate do_terminate
    >> (fn ((name, pos), (int_only, f)) =>
      SOME (Toplevel.empty |> Toplevel.name name |> Toplevel.position pos |>
        Toplevel.interactive int_only |> f));

end;



(** global outer syntax **)

local

val global_commands = Unsynchronized.ref (Symtab.empty: command Symtab.table);
val global_markups = Unsynchronized.ref ([]: (string * Thy_Output.markup) list);

fun change_commands f = CRITICAL (fn () =>
 (Unsynchronized.change global_commands f;
  global_markups :=
    Symtab.fold (fn (name, Command {markup = SOME m, ...}) => cons (name, m) | _ => I)
      (! global_commands) []));

in

(* access current syntax *)

fun get_commands () = ! global_commands;
fun get_markups () = ! global_markups;

fun get_command () = Symtab.lookup (get_commands ());
fun get_syntax () = CRITICAL (fn () => (Keyword.get_lexicons (), get_command ()));

fun is_markup kind name = AList.lookup (op =) (get_markups ()) name = SOME kind;


(* augment syntax *)

fun add_command name kind cmd = CRITICAL (fn () =>
 (Keyword.command name kind;
  if not (Symtab.defined (get_commands ()) name) then ()
  else warning ("Redefining outer syntax command " ^ quote name);
  change_commands (Symtab.update (name, cmd))));

fun command name comment kind parse =
  add_command name kind (make_command comment NONE false parse);

fun markup_command markup name comment kind parse =
  add_command name kind (make_command comment (SOME markup) false parse);

fun improper_command name comment kind parse =
  add_command name kind (make_command comment NONE true parse);

end;

fun internal_command name parse =
  command name "(internal)" Keyword.control (parse >> (fn tr => Toplevel.no_timing o tr));


(* local_theory commands *)

fun local_theory_command do_print trans name comment kind parse =
  command name comment kind (Parse.opt_target -- parse
    >> (fn (loc, f) => (if do_print then Toplevel.print else I) o trans loc f));

val local_theory' = local_theory_command false Toplevel.local_theory';
val local_theory = local_theory_command false Toplevel.local_theory;
val local_theory_to_proof' = local_theory_command true Toplevel.local_theory_to_proof';
val local_theory_to_proof = local_theory_command true Toplevel.local_theory_to_proof;


(* inspect syntax *)

fun dest_commands () =
  get_commands () |> Symtab.dest |> sort_wrt #1
  |> map (fn (name, Command {comment, int_only, ...}) => (name, comment, int_only));

fun print_outer_syntax () =
  let
    fun pretty_cmd (name, comment, _) =
      Pretty.block [Pretty.str (name ^ ":"), Pretty.brk 2, Pretty.str comment];
    val (int_cmds, cmds) = List.partition #3 (dest_commands ());
  in
    [Pretty.strs ("syntax keywords:" :: map quote (Keyword.dest_keywords ())),
      Pretty.big_list "commands:" (map pretty_cmd cmds),
      Pretty.big_list "interactive-only commands:" (map pretty_cmd int_cmds)]
    |> Pretty.chunks |> Pretty.writeln
  end;



(** toplevel parsing **)

(* basic sources *)

fun toplevel_source term do_recover cmd src =
  let
    val no_terminator =
      Scan.unless Parse.semicolon (Scan.one (Token.not_sync andf Token.not_eof));
    fun recover int =
      (int, fn _ => Scan.prompt "recover# " (Scan.repeat no_terminator) >> K [NONE]);
  in
    src
    |> Token.source_proper
    |> Source.source Token.stopper
      (Scan.bulk (Parse.$$$ "--" -- Parse.!!! Parse.doc_source >> K NONE || Parse.not_eof >> SOME))
        (Option.map recover do_recover)
    |> Source.map_filter I
    |> Source.source Token.stopper
        (Scan.bulk (fn xs => Parse.!!! (parse_command term (cmd ())) xs))
        (Option.map recover do_recover)
    |> Source.map_filter I
  end;


(* off-line scanning/parsing *)

fun scan pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source {do_recover = SOME false} Keyword.get_lexicons pos
  |> Source.exhaust;

fun parse pos str =
  Source.of_string str
  |> Symbol.source
  |> Token.source {do_recover = SOME false} Keyword.get_lexicons pos
  |> toplevel_source false NONE get_command
  |> Source.exhaust;


(* process file *)

fun process_file path thy =
  let
    val trs = parse (Path.position path) (File.read path);
    val init = Toplevel.init_theory NONE "" (K thy) Toplevel.empty;
    val result = fold Toplevel.command (init :: trs) Toplevel.toplevel;
  in
    (case (Toplevel.is_theory result, Toplevel.generic_theory_of result) of
      (true, Context.Theory thy') => thy'
    | _ => error "Bad result state: global theory expected")
  end;


(* interactive source of toplevel transformers *)

type isar =
  (Toplevel.transition, (Toplevel.transition option,
    (Token.T, (Token.T option, (Token.T, (Token.T,
      (Symbol_Pos.T, Position.T * (Symbol.symbol, (string, unit) Source.source)
  Source.source) Source.source) Source.source) Source.source)
  Source.source) Source.source) Source.source) Source.source;

fun isar in_stream term : isar =
  Source.tty in_stream
  |> Symbol.source
  |> Token.source {do_recover = SOME true} Keyword.get_lexicons Position.none
  |> toplevel_source term (SOME true) get_command;


(* prepare toplevel commands -- fail-safe *)

val not_singleton = "Exactly one command expected";

fun prepare_span commands span =
  let
    val range_pos = Position.set_range (Thy_Syntax.span_range span);
    val toks = Thy_Syntax.span_content span;
    val _ = List.app Thy_Syntax.report_token toks;
  in
    (case Source.exhaust (toplevel_source false NONE (K commands) (Source.of_list toks)) of
      [tr] =>
        if Keyword.is_control (Toplevel.name_of tr) then
          (Toplevel.malformed range_pos "Illegal control command", true)
        else (tr, true)
    | [] => (Toplevel.ignored range_pos, false)
    | _ => (Toplevel.malformed range_pos not_singleton, true))
    handle ERROR msg => (Toplevel.malformed range_pos msg, true)
  end;

fun prepare_atom commands init (cmd, proof, proper_proof) =
  let
    val (tr, proper_cmd) = prepare_span commands cmd |>> Toplevel.modify_init init;
    val proof_trs = map (prepare_span commands) proof |> filter #2 |> map #1;
  in
    if proper_cmd andalso proper_proof then [(tr, proof_trs)]
    else map (rpair []) (if proper_cmd then tr :: proof_trs else proof_trs)
  end;

fun prepare_command pos str =
  let val (lexs, commands) = get_syntax () in
    (case Thy_Syntax.parse_spans lexs pos str of
      [span] => #1 (prepare_span commands span)
    | _ => Toplevel.malformed pos not_singleton)
  end;


(* load_thy *)

fun load_thy name init pos text =
  let
    val (lexs, commands) = get_syntax ();
    val time = ! Toplevel.timing;

    val _ = Present.init_theory name;

    val toks = Source.exhausted (Thy_Syntax.token_source lexs pos (Source.of_string text));
    val spans = Source.exhaust (Thy_Syntax.span_source toks);
    val _ = List.app Thy_Syntax.report_span spans;  (* FIXME ?? *)
    val atoms = Source.exhaust (Thy_Syntax.atom_source (Source.of_list spans))
      |> Par_List.map_name "Outer_Syntax.prepare_atom" (prepare_atom commands init) |> flat;

    val _ = Present.theory_source name
      (fn () => HTML.html_mode (implode o map Thy_Syntax.present_span) spans);

    val _ = if time then writeln ("\n**** Starting theory " ^ quote name ^ " ****") else ();
    val (results, thy) = cond_timeit time "" (fn () => Toplevel.excursion atoms);
    val _ = if time then writeln ("**** Finished theory " ^ quote name ^ " ****\n") else ();

    val present =
      singleton (Future.cond_forks {name = "Outer_Syntax.present:" ^ name, group = NONE,
        deps = map Future.task_of results, pri = 0})
      (fn () =>
        Thy_Output.present_thy (#1 lexs) Keyword.command_tags is_markup
          (maps Future.join results) toks
        |> Buffer.content
        |> Present.theory_output name);

  in (thy, present) end;

end;

