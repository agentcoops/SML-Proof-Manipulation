(*  Title:      Pure/General/markup.ML
    Author:     Makarius

Common markup elements.
*)

signature MARKUP =
sig
  val parse_int: string -> int
  val print_int: int -> string
  type T = string * Properties.T
  val empty: T
  val is_empty: T -> bool
  val properties: Properties.T -> T -> T
  val nameN: string
  val name: string -> T -> T
  val kindN: string
  val bindingN: string val binding: string -> T
  val entityN: string val entity: string -> string -> T
  val defN: string
  val refN: string
  val lineN: string
  val columnN: string
  val offsetN: string
  val end_offsetN: string
  val fileN: string
  val idN: string
  val position_properties': string list
  val position_properties: string list
  val positionN: string val position: T
  val indentN: string
  val blockN: string val block: int -> T
  val widthN: string
  val breakN: string val break: int -> T
  val fbreakN: string val fbreak: T
  val hiddenN: string val hidden: T
  val tclassN: string val tclass: string -> T
  val tyconN: string val tycon: string -> T
  val fixedN: string val fixed: string -> T
  val constN: string val const: string -> T
  val dynamic_factN: string val dynamic_fact: string -> T
  val tfreeN: string val tfree: T
  val tvarN: string val tvar: T
  val freeN: string val free: T
  val skolemN: string val skolem: T
  val boundN: string val bound: T
  val varN: string val var: T
  val numeralN: string val numeral: T
  val literalN: string val literal: T
  val inner_stringN: string val inner_string: T
  val inner_commentN: string val inner_comment: T
  val token_rangeN: string val token_range: T
  val sortN: string val sort: T
  val typN: string val typ: T
  val termN: string val term: T
  val propN: string val prop: T
  val ML_keywordN: string val ML_keyword: T
  val ML_delimiterN: string val ML_delimiter: T
  val ML_identN: string val ML_ident: T
  val ML_tvarN: string val ML_tvar: T
  val ML_numeralN: string val ML_numeral: T
  val ML_charN: string val ML_char: T
  val ML_stringN: string val ML_string: T
  val ML_commentN: string val ML_comment: T
  val ML_malformedN: string val ML_malformed: T
  val ML_defN: string
  val ML_openN: string
  val ML_structN: string
  val ML_typingN: string val ML_typing: T
  val ML_sourceN: string val ML_source: T
  val doc_sourceN: string val doc_source: T
  val antiqN: string val antiq: T
  val ML_antiqN: string val ML_antiq: string -> T
  val doc_antiqN: string val doc_antiq: string -> T
  val keyword_declN: string val keyword_decl: string -> T
  val command_declN: string val command_decl: string -> string -> T
  val keywordN: string val keyword: T
  val operatorN: string val operator: T
  val commandN: string val command: T
  val identN: string val ident: T
  val stringN: string val string: T
  val altstringN: string val altstring: T
  val verbatimN: string val verbatim: T
  val commentN: string val comment: T
  val controlN: string val control: T
  val malformedN: string val malformed: T
  val tokenN: string val token: Properties.T -> T
  val command_spanN: string val command_span: string -> T
  val ignored_spanN: string val ignored_span: T
  val malformed_spanN: string val malformed_span: T
  val elapsedN: string
  val cpuN: string
  val gcN: string
  val timingN: string val timing: Timing.timing -> T
  val subgoalsN: string
  val proof_stateN: string val proof_state: int -> T
  val stateN: string val state: T
  val subgoalN: string val subgoal: T
  val sendbackN: string val sendback: T
  val hiliteN: string val hilite: T
  val taskN: string
  val forkedN: string val forked: T
  val joinedN: string val joined: T
  val failedN: string val failed: T
  val finishedN: string val finished: T
  val versionN: string
  val execN: string
  val assignN: string val assign: int -> T
  val editN: string val edit: int -> int -> T
  val serialN: string
  val promptN: string val prompt: T
  val readyN: string val ready: T
  val reportN: string val report: T
  val no_reportN: string val no_report: T
  val badN: string val bad: T
  val no_output: Output.output * Output.output
  val default_output: T -> Output.output * Output.output
  val add_mode: string -> (T -> Output.output * Output.output) -> unit
  val output: T -> Output.output * Output.output
  val enclose: T -> Output.output -> Output.output
  val markup: T -> string -> string
end;

structure Markup: MARKUP =
struct

(** markup elements **)

(* integers *)

fun parse_int s =
  (case Int.fromString s of
    SOME i => i
  | NONE => raise Fail ("Bad integer: " ^ quote s));

val print_int = signed_string_of_int;


(* basic markup *)

type T = string * Properties.T;

val empty = ("", []);

fun is_empty ("", _) = true
  | is_empty _ = false;


fun properties more_props ((elem, props): T) =
  (elem, fold_rev Properties.put more_props props);

fun markup_elem elem = (elem, (elem, []): T);
fun markup_string elem prop = (elem, fn s => (elem, [(prop, s)]): T);
fun markup_int elem prop = (elem, fn i => (elem, [(prop, print_int i)]): T);


(* misc properties *)

val nameN = "name";
fun name a = properties [(nameN, a)];

val kindN = "kind";


(* formal entities *)

val (bindingN, binding) = markup_string "binding" nameN;

val entityN = "entity";
fun entity kind name = (entityN, [(nameN, name), (kindN, kind)]);

val defN = "def";
val refN = "ref";


(* position *)

val lineN = "line";
val columnN = "column";
val offsetN = "offset";
val end_offsetN = "end_offset";
val fileN = "file";
val idN = "id";

val position_properties' = [fileN, idN];
val position_properties = [lineN, columnN, offsetN, end_offsetN] @ position_properties';

val (positionN, position) = markup_elem "position";


(* pretty printing *)

val indentN = "indent";
val (blockN, block) = markup_int "block" indentN;

val widthN = "width";
val (breakN, break) = markup_int "break" widthN;

val (fbreakN, fbreak) = markup_elem "fbreak";


(* hidden text *)

val (hiddenN, hidden) = markup_elem "hidden";


(* logical entities *)

val (tclassN, tclass) = markup_string "tclass" nameN;
val (tyconN, tycon) = markup_string "tycon" nameN;
val (fixedN, fixed) = markup_string "fixed" nameN;
val (constN, const) = markup_string "constant" nameN;
val (dynamic_factN, dynamic_fact) = markup_string "dynamic_fact" nameN;


(* inner syntax *)

val (tfreeN, tfree) = markup_elem "tfree";
val (tvarN, tvar) = markup_elem "tvar";
val (freeN, free) = markup_elem "free";
val (skolemN, skolem) = markup_elem "skolem";
val (boundN, bound) = markup_elem "bound";
val (varN, var) = markup_elem "var";
val (numeralN, numeral) = markup_elem "numeral";
val (literalN, literal) = markup_elem "literal";
val (inner_stringN, inner_string) = markup_elem "inner_string";
val (inner_commentN, inner_comment) = markup_elem "inner_comment";

val (token_rangeN, token_range) = markup_elem "token_range";

val (sortN, sort) = markup_elem "sort";
val (typN, typ) = markup_elem "typ";
val (termN, term) = markup_elem "term";
val (propN, prop) = markup_elem "prop";


(* ML syntax *)

val (ML_keywordN, ML_keyword) = markup_elem "ML_keyword";
val (ML_delimiterN, ML_delimiter) = markup_elem "ML_delimiter";
val (ML_identN, ML_ident) = markup_elem "ML_ident";
val (ML_tvarN, ML_tvar) = markup_elem "ML_tvar";
val (ML_numeralN, ML_numeral) = markup_elem "ML_numeral";
val (ML_charN, ML_char) = markup_elem "ML_char";
val (ML_stringN, ML_string) = markup_elem "ML_string";
val (ML_commentN, ML_comment) = markup_elem "ML_comment";
val (ML_malformedN, ML_malformed) = markup_elem "ML_malformed";

val ML_defN = "ML_def";
val ML_openN = "ML_open";
val ML_structN = "ML_struct";
val (ML_typingN, ML_typing) = markup_elem "ML_typing";


(* embedded source text *)

val (ML_sourceN, ML_source) = markup_elem "ML_source";
val (doc_sourceN, doc_source) = markup_elem "doc_source";

val (antiqN, antiq) = markup_elem "antiq";
val (ML_antiqN, ML_antiq) = markup_string "ML_antiq" nameN;
val (doc_antiqN, doc_antiq) = markup_string "doc_antiq" nameN;


(* outer syntax *)

val (keyword_declN, keyword_decl) = markup_string "keyword_decl" nameN;

val command_declN = "command_decl";
fun command_decl name kind : T = (command_declN, [(nameN, name), (kindN, kind)]);

val (keywordN, keyword) = markup_elem "keyword";
val (operatorN, operator) = markup_elem "operator";
val (commandN, command) = markup_elem "command";
val (identN, ident) = markup_elem "ident";
val (stringN, string) = markup_elem "string";
val (altstringN, altstring) = markup_elem "altstring";
val (verbatimN, verbatim) = markup_elem "verbatim";
val (commentN, comment) = markup_elem "comment";
val (controlN, control) = markup_elem "control";
val (malformedN, malformed) = markup_elem "malformed";

val tokenN = "token";
fun token props = (tokenN, props);

val (command_spanN, command_span) = markup_string "command_span" nameN;
val (ignored_spanN, ignored_span) = markup_elem "ignored_span";
val (malformed_spanN, malformed_span) = markup_elem "malformed_span";


(* timing *)

val timingN = "timing";
val elapsedN = "elapsed";
val cpuN = "cpu";
val gcN = "gc";

fun timing {elapsed, cpu, gc} =
  (timingN,
   [(elapsedN, Time.toString elapsed),
    (cpuN, Time.toString cpu),
    (gcN, Time.toString gc)]);


(* toplevel *)

val subgoalsN = "subgoals";
val (proof_stateN, proof_state) = markup_int "proof_state" subgoalsN;

val (stateN, state) = markup_elem "state";
val (subgoalN, subgoal) = markup_elem "subgoal";
val (sendbackN, sendback) = markup_elem "sendback";
val (hiliteN, hilite) = markup_elem "hilite";


(* command status *)

val taskN = "task";

val (forkedN, forked) = markup_elem "forked";
val (joinedN, joined) = markup_elem "joined";

val (failedN, failed) = markup_elem "failed";
val (finishedN, finished) = markup_elem "finished";


(* interactive documents *)

val versionN = "version";
val execN = "exec";
val (assignN, assign) = markup_int "assign" versionN;

val editN = "edit";
fun edit cmd_id exec_id : T = (editN, [(idN, print_int cmd_id), (execN, print_int exec_id)]);


(* messages *)

val serialN = "serial";

val (promptN, prompt) = markup_elem "prompt";
val (readyN, ready) = markup_elem "ready";

val (reportN, report) = markup_elem "report";
val (no_reportN, no_report) = markup_elem "no_report";

val (badN, bad) = markup_elem "bad";



(** print mode operations **)

val no_output = ("", "");
fun default_output (_: T) = no_output;

local
  val default = {output = default_output};
  val modes = Unsynchronized.ref (Symtab.make [("", default)]);
in
  fun add_mode name output = CRITICAL (fn () =>
    Unsynchronized.change modes (Symtab.update_new (name, {output = output})));
  fun get_mode () =
    the_default default (Library.get_first (Symtab.lookup (! modes)) (print_mode_value ()));
end;

fun output m = if is_empty m then no_output else #output (get_mode ()) m;

val enclose = output #-> Library.enclose;

fun markup m =
  let val (bg, en) = output m
  in Library.enclose (Output.escape bg) (Output.escape en) end;

end;
