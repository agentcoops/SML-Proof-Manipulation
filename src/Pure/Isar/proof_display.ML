(*  Title:      Pure/Isar/proof_display.ML
    Author:     Makarius

Printing of theorems, goals, results etc.
*)

signature PROOF_DISPLAY =
sig
  val pp_context: Proof.context -> Pretty.T
  val pp_thm: thm -> Pretty.T
  val pp_typ: theory -> typ -> Pretty.T
  val pp_term: theory -> term -> Pretty.T
  val pp_ctyp: ctyp -> Pretty.T
  val pp_cterm: cterm -> Pretty.T
  val print_theorems_diff: bool -> theory -> theory -> unit
  val print_theorems: bool -> theory -> unit
  val pretty_full_theory: bool -> theory -> Pretty.T
  val print_theory: theory -> unit
  val string_of_rule: Proof.context -> string -> thm -> string
  val print_results: bool -> Proof.context -> ((string * string) * (string * thm list) list) -> unit
  val pretty_consts: Proof.context -> (string * typ -> bool) -> (string * typ) list -> Pretty.T
end

structure Proof_Display: PROOF_DISPLAY =
struct

(* toplevel pretty printing *)

fun pp_context ctxt =
 (if Config.get ctxt Proof_Context.debug then
    Pretty.quote (Pretty.big_list "proof context:" (Proof_Context.pretty_context ctxt))
  else Pretty.str "<context>");

fun pp_thm th =
  let
    val thy = Thm.theory_of_thm th;
    val flags = {quote = true, show_hyps = false, show_status = true};
  in Display.pretty_thm_raw (Syntax.init_pretty_global thy) flags th end;

val pp_typ = Pretty.quote oo Syntax.pretty_typ_global;
val pp_term = Pretty.quote oo Syntax.pretty_term_global;

fun pp_ctyp cT = pp_typ (Thm.theory_of_ctyp cT) (Thm.typ_of cT);
fun pp_cterm ct = pp_term (Thm.theory_of_cterm ct) (Thm.term_of ct);


(* theorems and theory *)

fun pretty_theorems_diff verbose prev_thys thy =
  let
    val pretty_fact = Proof_Context.pretty_fact (Proof_Context.init_global thy);
    val facts = Global_Theory.facts_of thy;
    val thmss =
      Facts.dest_static (map Global_Theory.facts_of prev_thys) facts
      |> not verbose ? filter_out (Facts.is_concealed facts o #1);
  in Pretty.big_list "theorems:" (map #1 (sort_wrt (#1 o #2) (map (`pretty_fact) thmss))) end;

fun print_theorems_diff verbose prev_thy thy =
  Pretty.writeln (pretty_theorems_diff verbose [prev_thy] thy);

fun pretty_theorems verbose thy = pretty_theorems_diff verbose (Theory.parents_of thy) thy;
val print_theorems = Pretty.writeln oo pretty_theorems;

fun pretty_full_theory verbose thy =
  Pretty.chunks (Display.pretty_full_theory verbose thy @ [pretty_theorems verbose thy]);

val print_theory = Pretty.writeln o pretty_full_theory false;


(* refinement rule *)

fun pretty_rule ctxt s thm =
  Pretty.block [Pretty.str (s ^ " attempt to solve goal by exported rule:"),
    Pretty.fbrk, Display.pretty_thm_aux ctxt false thm];

val string_of_rule = Pretty.string_of ooo pretty_rule;


(* results *)

local

fun pretty_fact_name (kind, "") = Pretty.command kind
  | pretty_fact_name (kind, name) =
      Pretty.block [Pretty.command kind, Pretty.brk 1,
        Pretty.str (Long_Name.base_name name), Pretty.str ":"];

fun pretty_facts ctxt =
  flat o (separate [Pretty.fbrk, Pretty.keyword "and", Pretty.str " "]) o
    map (single o Proof_Context.pretty_fact_aux ctxt false);

in

fun print_results do_print ctxt ((kind, name), facts) =
  if not do_print orelse kind = "" then ()
  else if name = "" then
    Pretty.writeln (Pretty.block (Pretty.command kind :: Pretty.brk 1 :: pretty_facts ctxt facts))
  else Pretty.writeln
    (case facts of
      [fact] => Pretty.blk (1, [pretty_fact_name (kind, name), Pretty.fbrk,
        Proof_Context.pretty_fact_aux ctxt false fact])
    | _ => Pretty.blk (1, [pretty_fact_name (kind, name), Pretty.fbrk,
        Pretty.blk (1, Pretty.str "(" :: pretty_facts ctxt facts @ [Pretty.str ")"])]));

end;


(* consts *)

local

fun pretty_var ctxt (x, T) =
  Pretty.block [Pretty.str x, Pretty.str " ::", Pretty.brk 1,
    Pretty.quote (Syntax.pretty_typ ctxt T)];

fun pretty_vars ctxt kind vs = Pretty.big_list kind (map (pretty_var ctxt) vs);

in

fun pretty_consts ctxt pred cs =
  (case filter pred (#1 (Proof_Context.inferred_fixes ctxt)) of
    [] => pretty_vars ctxt "constants" cs
  | ps => Pretty.chunks [pretty_vars ctxt "parameters" ps, pretty_vars ctxt "constants" cs]);

end;

end;
