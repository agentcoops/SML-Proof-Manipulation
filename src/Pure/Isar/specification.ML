(*  Title:      Pure/Isar/specification.ML
    Author:     Makarius

Derived local theory specifications --- with type-inference and
toplevel polymorphism.
*)

signature SPECIFICATION =
sig
  val print_consts: local_theory -> (string * typ -> bool) -> (string * typ) list -> unit
  val check_spec:
    (binding * typ option * mixfix) list -> (Attrib.binding * term) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term) list) * Proof.context
  val read_spec:
    (binding * string option * mixfix) list -> (Attrib.binding * string) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term) list) * Proof.context
  val check_free_spec:
    (binding * typ option * mixfix) list -> (Attrib.binding * term) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term) list) * Proof.context
  val read_free_spec:
    (binding * string option * mixfix) list -> (Attrib.binding * string) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term) list) * Proof.context
  val check_specification: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val read_specification: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list -> Proof.context ->
    (((binding * typ) * mixfix) list * (Attrib.binding * term list) list) * Proof.context
  val axiomatization: (binding * typ option * mixfix) list ->
    (Attrib.binding * term list) list -> theory ->
    (term list * thm list list) * theory
  val axiomatization_cmd: (binding * string option * mixfix) list ->
    (Attrib.binding * string list) list -> theory ->
    (term list * thm list list) * theory
  val axiom: Attrib.binding * term -> theory -> thm * theory
  val axiom_cmd: Attrib.binding * string -> theory -> thm * theory
  val definition:
    (binding * typ option * mixfix) option * (Attrib.binding * term) ->
    local_theory -> (term * (string * thm)) * local_theory
  val definition_cmd:
    (binding * string option * mixfix) option * (Attrib.binding * string) ->
    local_theory -> (term * (string * thm)) * local_theory
  val abbreviation: Syntax.mode -> (binding * typ option * mixfix) option * term ->
    local_theory -> local_theory
  val abbreviation_cmd: Syntax.mode -> (binding * string option * mixfix) option * string ->
    local_theory -> local_theory
  val type_notation: bool -> Syntax.mode -> (typ * mixfix) list -> local_theory -> local_theory
  val type_notation_cmd: bool -> Syntax.mode -> (string * mixfix) list -> local_theory -> local_theory
  val notation: bool -> Syntax.mode -> (term * mixfix) list -> local_theory -> local_theory
  val notation_cmd: bool -> Syntax.mode -> (string * mixfix) list -> local_theory -> local_theory
  val theorems: string ->
    (Attrib.binding * (thm list * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val theorems_cmd: string ->
    (Attrib.binding * (Facts.ref * Attrib.src list) list) list ->
    local_theory -> (string * thm list) list * local_theory
  val theorem: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    Element.context_i list -> Element.statement_i ->
    bool -> local_theory -> Proof.state
  val theorem_cmd: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    Element.context list -> Element.statement ->
    bool -> local_theory -> Proof.state
  val schematic_theorem: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    Element.context_i list -> Element.statement_i ->
    bool -> local_theory -> Proof.state
  val schematic_theorem_cmd: string -> Method.text option ->
    (thm list list -> local_theory -> local_theory) -> Attrib.binding ->
    Element.context list -> Element.statement ->
    bool -> local_theory -> Proof.state
  val add_theorem_hook: (bool -> Proof.state -> Proof.state) -> Context.generic -> Context.generic
end;

structure Specification: SPECIFICATION =
struct

(* diagnostics *)

fun print_consts _ _ [] = ()
  | print_consts ctxt pred cs = Pretty.writeln (Proof_Display.pretty_consts ctxt pred cs);


(* prepare specification *)

local

fun close_forms ctxt i xs As =
  let
    val commons = map #1 xs;
    val _ =
      (case duplicates (op =) commons of [] => ()
      | dups => error ("Duplicate local variables " ^ commas_quote dups));
    val frees = rev (fold (Variable.add_free_names ctxt) As (rev commons));
    val types = map (Type_Infer.param i o rpair []) (Name.invents Name.context Name.aT (length frees));
    val uniform_typing = the o AList.lookup (op =) (frees ~~ types);

    fun abs_body lev y (Abs (x, T, b)) = Abs (x, T, abs_body (lev + 1) y b)
      | abs_body lev y (t $ u) = abs_body lev y t $ abs_body lev y u
      | abs_body lev y (t as Free (x, T)) =
          if x = y then Type.constraint (uniform_typing x) (Type.constraint T (Bound lev))
          else t
      | abs_body _ _ a = a;
    fun close (y, U) B =
      let val B' = abs_body 0 y (Term.incr_boundvars 1 B)
      in if Term.is_dependent B' then Term.all dummyT $ Abs (y, U, B') else B end;
    fun close_form A =
      let
        val occ_frees = rev (Variable.add_free_names ctxt A []);
        val bounds = xs @ map (rpair dummyT) (subtract (op =) commons occ_frees);
      in fold_rev close bounds A end;
  in map close_form As end;

fun prepare prep_vars parse_prop prep_att do_close raw_vars raw_specss ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;

    val (vars, vars_ctxt) = ctxt |> prep_vars raw_vars;
    val (xs, params_ctxt) = vars_ctxt |> Proof_Context.add_fixes vars;

    val Asss =
      (map o map) snd raw_specss
      |> (burrow o burrow) (Par_List.map_name "Specification.parse_prop" (parse_prop params_ctxt));
    val names = Variable.names_of (params_ctxt |> (fold o fold o fold) Variable.declare_term Asss)
      |> fold Name.declare xs;
    val Asss' = #1 ((fold_map o fold_map o fold_map) Term.free_dummy_patterns Asss names);
    val idx = (fold o fold o fold) Term.maxidx_term Asss' ~1 + 1;
    val specs =
      (if do_close then
        #1 (fold_map
            (fn Ass => fn i => (burrow (close_forms params_ctxt i []) Ass, i + 1)) Asss' idx)
      else Asss')
      |> flat |> burrow (Syntax.check_props params_ctxt);
    val specs_ctxt = params_ctxt |> (fold o fold) Variable.declare_term specs;

    val Ts = specs_ctxt |> fold_map Proof_Context.inferred_param xs |> fst;
    val params = map2 (fn (b, _, mx) => fn T => ((b, T), mx)) vars Ts;
    val name_atts = map (fn ((name, atts), _) => (name, map (prep_att thy) atts)) (flat raw_specss);
  in ((params, name_atts ~~ specs), specs_ctxt) end;


fun single_spec (a, prop) = [(a, [prop])];
fun the_spec (a, [prop]) = (a, prop);

fun prep_spec prep_vars parse_prop prep_att do_close vars specs =
  prepare prep_vars parse_prop prep_att do_close
    vars (map single_spec specs) #>> apsnd (map the_spec);

in

fun check_spec x = prep_spec Proof_Context.cert_vars (K I) (K I) true x;
fun read_spec x = prep_spec Proof_Context.read_vars Syntax.parse_prop Attrib.intern_src true x;

fun check_free_spec x = prep_spec Proof_Context.cert_vars (K I) (K I) false x;
fun read_free_spec x = prep_spec Proof_Context.read_vars Syntax.parse_prop Attrib.intern_src false x;

fun check_specification vars specs =
  prepare Proof_Context.cert_vars (K I) (K I) true vars [specs];

fun read_specification vars specs =
  prepare Proof_Context.read_vars Syntax.parse_prop Attrib.intern_src true vars [specs];

end;


(* axiomatization -- within global theory *)

fun gen_axioms do_print prep raw_vars raw_specs thy =
  let
    val ((vars, specs), _) = prep raw_vars raw_specs (Proof_Context.init_global thy);
    val xs = map (fn ((b, T), _) => (Variable.check_name b, T)) vars;

    (*consts*)
    val (consts, consts_thy) = thy |> fold_map Theory.specify_const vars;
    val subst = Term.subst_atomic (map Free xs ~~ consts);

    (*axioms*)
    val (axioms, axioms_thy) = (specs, consts_thy) |-> fold_map (fn ((b, atts), props) =>
        fold_map Thm.add_axiom_global
          (map (apfst (fn a => Binding.map_name (K a) b))
            (Global_Theory.name_multi (Variable.check_name b) (map subst props)))
        #>> (fn ths => ((b, atts), [(map #2 ths, [])])));

    (*facts*)
    val (facts, facts_lthy) = axioms_thy
      |> Named_Target.theory_init
      |> Spec_Rules.add Spec_Rules.Unknown (consts, maps (maps #1 o #2) axioms)
      |> Local_Theory.notes axioms;

    val _ =
      if not do_print then ()
      else print_consts facts_lthy (K false) xs;
  in ((consts, map #2 facts), Local_Theory.exit_global facts_lthy) end;

val axiomatization = gen_axioms false check_specification;
val axiomatization_cmd = gen_axioms true read_specification;

fun axiom (b, ax) = axiomatization [] [(b, [ax])] #>> (hd o hd o snd);
fun axiom_cmd (b, ax) = axiomatization_cmd [] [(b, [ax])] #>> (hd o hd o snd);


(* definition *)

fun gen_def do_print prep (raw_var, raw_spec) lthy =
  let
    val (vars, [((raw_name, atts), prop)]) = fst (prep (the_list raw_var) [raw_spec] lthy);
    val (((x, T), rhs), prove) = Local_Defs.derived_def lthy true prop;
    val var as (b, _) =
      (case vars of
        [] => (Binding.name x, NoSyn)
      | [((b, _), mx)] =>
          let
            val y = Variable.check_name b;
            val _ = x = y orelse
              error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote y ^
                Position.str_of (Binding.pos_of b));
          in (b, mx) end);
    val name = Thm.def_binding_optional b raw_name;
    val ((lhs, (_, raw_th)), lthy2) = lthy
      |> Local_Theory.define (var, ((Binding.suffix_name "_raw" name, []), rhs));

    val th = prove lthy2 raw_th;
    val lthy3 = lthy2 |> Spec_Rules.add Spec_Rules.Equational ([lhs], [th]);

    val ([(def_name, [th'])], lthy4) = lthy3
      |> Local_Theory.notes_kind ""
        [((name, Code.add_default_eqn_attrib :: atts), [([th], [])])];

    val lhs' = Morphism.term (Local_Theory.target_morphism lthy4) lhs;
    val _ =
      if not do_print then ()
      else print_consts lthy4 (member (op =) (Term.add_frees lhs' [])) [(x, T)];
  in ((lhs, (def_name, th')), lthy4) end;

val definition = gen_def false check_free_spec;
val definition_cmd = gen_def true read_free_spec;


(* abbreviation *)

fun gen_abbrev do_print prep mode (raw_var, raw_prop) lthy =
  let
    val ((vars, [(_, prop)]), _) =
      prep (the_list raw_var) [(Attrib.empty_binding, raw_prop)]
        (lthy |> Proof_Context.set_mode Proof_Context.mode_abbrev);
    val ((x, T), rhs) = Local_Defs.abs_def (#2 (Local_Defs.cert_def lthy prop));
    val var =
      (case vars of
        [] => (Binding.name x, NoSyn)
      | [((b, _), mx)] =>
          let
            val y = Variable.check_name b;
            val _ = x = y orelse
              error ("Head of abbreviation " ^ quote x ^ " differs from declaration " ^ quote y ^
                Position.str_of (Binding.pos_of b));
          in (b, mx) end);
    val lthy' = lthy
      |> Proof_Context.set_syntax_mode mode    (* FIXME ?!? *)
      |> Local_Theory.abbrev mode (var, rhs) |> snd
      |> Proof_Context.restore_syntax_mode lthy;

    val _ = if not do_print then () else print_consts lthy' (K false) [(x, T)];
  in lthy' end;

val abbreviation = gen_abbrev false check_free_spec;
val abbreviation_cmd = gen_abbrev true read_free_spec;


(* notation *)

local

fun gen_type_notation prep_type add mode args lthy =
  lthy |> Local_Theory.type_notation add mode (map (apfst (prep_type lthy)) args);

fun gen_notation prep_const add mode args lthy =
  lthy |> Local_Theory.notation add mode (map (apfst (prep_const lthy)) args);

in

val type_notation = gen_type_notation (K I);
val type_notation_cmd = gen_type_notation (fn ctxt => Proof_Context.read_type_name ctxt false);

val notation = gen_notation (K I);
val notation_cmd = gen_notation (fn ctxt => Proof_Context.read_const ctxt false dummyT);

end;


(* fact statements *)

fun gen_theorems prep_fact prep_att kind raw_facts lthy =
  let
    val attrib = prep_att (Proof_Context.theory_of lthy);
    val facts = raw_facts |> map (fn ((name, atts), bs) =>
      ((name, map attrib atts),
        bs |> map (fn (b, more_atts) => (prep_fact lthy b, map attrib more_atts))));
    val (res, lthy') = lthy |> Local_Theory.notes_kind kind facts;
    val _ = Proof_Display.print_results true lthy' ((kind, ""), res);
  in (res, lthy') end;

val theorems = gen_theorems (K I) (K I);
val theorems_cmd = gen_theorems Proof_Context.get_fact Attrib.intern_src;


(* complex goal statements *)

local

fun prep_statement prep_att prep_stmt elems concl ctxt =
  (case concl of
    Element.Shows shows =>
      let
        val (propp, elems_ctxt) = prep_stmt elems (map snd shows) ctxt;
        val prems = Assumption.local_prems_of elems_ctxt ctxt;
        val stmt = Attrib.map_specs prep_att (map fst shows ~~ propp);
        val goal_ctxt = fold (fold (Variable.auto_fixes o fst)) propp elems_ctxt;
      in ((prems, stmt, NONE), goal_ctxt) end
  | Element.Obtains obtains =>
      let
        val case_names = obtains |> map_index (fn (i, (b, _)) =>
          if Binding.is_empty b then string_of_int (i + 1) else Variable.check_name b);
        val constraints = obtains |> map (fn (_, (vars, _)) =>
          Element.Constrains
            (vars |> map_filter (fn (x, SOME T) => SOME (Variable.check_name x, T) | _ => NONE)));

        val raw_propp = obtains |> map (fn (_, (_, props)) => map (rpair []) props);
        val (propp, elems_ctxt) = prep_stmt (elems @ constraints) raw_propp ctxt;

        val thesis = Object_Logic.fixed_judgment (Proof_Context.theory_of ctxt) Auto_Bind.thesisN;

        fun assume_case ((name, (vars, _)), asms) ctxt' =
          let
            val bs = map fst vars;
            val xs = map Variable.check_name bs;
            val props = map fst asms;
            val (Ts, _) = ctxt'
              |> fold Variable.declare_term props
              |> fold_map Proof_Context.inferred_param xs;
            val asm = Term.list_all_free (xs ~~ Ts, Logic.list_implies (props, thesis));
          in
            ctxt' |> (snd o Proof_Context.add_fixes (map (fn b => (b, NONE, NoSyn)) bs));
            ctxt' |> Variable.auto_fixes asm
            |> Proof_Context.add_assms_i Assumption.assume_export
              [((name, [Context_Rules.intro_query NONE]), [(asm, [])])]
            |>> (fn [(_, [th])] => th)
          end;

        val atts = map (Attrib.internal o K)
          [Rule_Cases.consumes (~ (length obtains)), Rule_Cases.case_names case_names];
        val prems = Assumption.local_prems_of elems_ctxt ctxt;
        val stmt = [((Binding.empty, atts), [(thesis, [])])];

        val (facts, goal_ctxt) = elems_ctxt
          |> (snd o Proof_Context.add_fixes [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)])
          |> fold_map assume_case (obtains ~~ propp)
          |-> (fn ths =>
            Proof_Context.note_thmss "" [((Binding.name Obtain.thatN, []), [(ths, [])])] #>
            #2 #> pair ths);
      in ((prems, stmt, SOME facts), goal_ctxt) end);

structure Theorem_Hook = Generic_Data
(
  type T = ((bool -> Proof.state -> Proof.state) * stamp) list;
  val empty = [];
  val extend = I;
  fun merge data : T = Library.merge (eq_snd op =) data;
);

fun gen_theorem schematic prep_att prep_stmt
    kind before_qed after_qed (name, raw_atts) raw_elems raw_concl int lthy =
  let
    val _ = Local_Theory.affirm lthy;
    val thy = Proof_Context.theory_of lthy;

    val attrib = prep_att thy;
    val atts = map attrib raw_atts;
    val elems = raw_elems |> map (Element.map_ctxt_attrib attrib);
    val ((prems, stmt, facts), goal_ctxt) =
      prep_statement attrib prep_stmt elems raw_concl lthy;

    fun after_qed' results goal_ctxt' =
      let val results' =
        burrow (map Goal.norm_result o Proof_Context.export goal_ctxt' lthy) results
      in
        lthy
        |> Local_Theory.notes_kind kind
          (map2 (fn (a, _) => fn ths => (a, [(ths, [])])) stmt results')
        |> (fn (res, lthy') =>
          if Binding.is_empty name andalso null atts then
            (Proof_Display.print_results true lthy' ((kind, ""), res); lthy')
          else
            let
              val ([(res_name, _)], lthy'') = lthy'
                |> Local_Theory.notes_kind kind [((name, atts), [(maps #2 res, [])])];
              val _ = Proof_Display.print_results true lthy' ((kind, res_name), res);
            in lthy'' end)
        |> after_qed results'
      end;
  in
    goal_ctxt
    |> Proof_Context.note_thmss "" [((Binding.name Auto_Bind.assmsN, []), [(prems, [])])]
    |> snd
    |> Proof.theorem before_qed after_qed' (map snd stmt)
    |> (case facts of NONE => I | SOME ths => Proof.refine_insert ths)
    |> tap (fn state => not schematic andalso Proof.schematic_goal state andalso
        error "Illegal schematic goal statement")
    |> Library.apply (map (fn (f, _) => f int) (rev (Theorem_Hook.get (Context.Proof goal_ctxt))))
  end;

in

val theorem = gen_theorem false (K I) Expression.cert_statement;
val theorem_cmd = gen_theorem false Attrib.intern_src Expression.read_statement;

val schematic_theorem = gen_theorem true (K I) Expression.cert_statement;
val schematic_theorem_cmd = gen_theorem true Attrib.intern_src Expression.read_statement;

fun add_theorem_hook f = Theorem_Hook.map (cons (f, stamp ()));

end;

end;
