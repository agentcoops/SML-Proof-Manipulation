(*  Title:      Pure/Thy/thy_info.ML
    Author:     Markus Wenzel, TU Muenchen

Global theory info database, with auto-loading according to theory and
file dependencies.
*)

signature THY_INFO =
sig
  datatype action = Update | Remove
  val add_hook: (action -> string -> unit) -> unit
  val get_names: unit -> string list
  val lookup_theory: string -> theory option
  val get_theory: string -> theory
  val is_finished: string -> bool
  val master_directory: string -> Path.T
  val loaded_files: string -> Path.T list
  val remove_thy: string -> unit
  val kill_thy: string -> unit
  val use_thys_wrt: Path.T -> string list -> unit
  val use_thys: string list -> unit
  val use_thy: string -> unit
  val toplevel_begin_theory: Path.T option -> string ->
    string list -> (Path.T * bool) list -> theory
  val register_thy: theory -> unit
  val finish: unit -> unit
end;

structure Thy_Info: THY_INFO =
struct

(** theory loader actions and hooks **)

datatype action = Update | Remove;

local
  val hooks = Unsynchronized.ref ([]: (action -> string -> unit) list);
in
  fun add_hook f = NAMED_CRITICAL "Thy_Info" (fn () => Unsynchronized.change hooks (cons f));
  fun perform action name = List.app (fn f => (try (fn () => f action name) (); ())) (! hooks);
end;



(** thy database **)

(* messages *)

fun loader_msg txt [] = "Theory loader: " ^ txt
  | loader_msg txt names = "Theory loader: " ^ txt ^ " " ^ commas_quote names;

val show_path = space_implode " via " o map quote;
fun cycle_msg names = loader_msg ("cyclic dependency of " ^ show_path names) [];


(* derived graph operations *)

fun add_deps name parents G = Graph.add_deps_acyclic (name, parents) G
  handle Graph.CYCLES namess => error (cat_lines (map cycle_msg namess));

fun new_entry name parents entry =
  Graph.new_node (name, entry) #> add_deps name parents;


(* thy database *)

type deps =
 {master: (Path.T * SHA1.digest),  (*master dependencies for thy file*)
  imports: string list};  (*source specification of imports (partially qualified)*)

fun make_deps master imports : deps = {master = master, imports = imports};

fun master_dir (d: deps option) = the_default Path.current (Option.map (Path.dir o #1 o #master) d);
fun base_name s = Path.implode (Path.base (Path.explode s));

local
  val database = Unsynchronized.ref (Graph.empty: (deps option * theory option) Graph.T);
in
  fun get_thys () = ! database;
  fun change_thys f = NAMED_CRITICAL "Thy_Info" (fn () => Unsynchronized.change database f);
end;


(* access thy graph *)

fun thy_graph f x = f (get_thys ()) x;

fun get_names () = Graph.topological_order (get_thys ());


(* access thy *)

fun lookup_thy name =
  SOME (thy_graph Graph.get_node name) handle Graph.UNDEF _ => NONE;

val known_thy = is_some o lookup_thy;

fun get_thy name =
  (case lookup_thy name of
    SOME thy => thy
  | NONE => error (loader_msg "nothing known about theory" [name]));


(* access deps *)

val lookup_deps = Option.map #1 o lookup_thy;
val get_deps = #1 o get_thy;

val is_finished = is_none o get_deps;
val master_directory = master_dir o get_deps;

fun get_parents name =
  thy_graph Graph.imm_preds name handle Graph.UNDEF _ =>
    error (loader_msg "nothing known about theory" [name]);


(* access theory *)

fun lookup_theory name =
  (case lookup_thy name of
    SOME (_, SOME theory) => SOME theory
  | _ => NONE);

fun get_theory name =
  (case lookup_theory name of
    SOME theory => theory
  | _ => error (loader_msg "undefined theory entry for" [name]));

fun loaded_files name = NAMED_CRITICAL "Thy_Info" (fn () =>
  (case get_deps name of
    NONE => []
  | SOME {master = (thy_path, _), ...} => thy_path :: Thy_Load.loaded_files (get_theory name)));



(** thy operations **)

(* remove theory *)

fun remove_thy name = NAMED_CRITICAL "Thy_Info" (fn () =>
  if is_finished name then error (loader_msg "attempt to change finished theory" [name])
  else
    let
      val succs = thy_graph Graph.all_succs [name];
      val _ = Output.urgent_message (loader_msg "removing" succs);
      val _ = List.app (perform Remove) succs;
      val _ = change_thys (Graph.del_nodes succs);
    in () end);

fun kill_thy name = NAMED_CRITICAL "Thy_Info" (fn () =>
  if known_thy name then remove_thy name
  else ());


(* scheduling loader tasks *)

datatype task =
  Task of string list * (theory list -> (theory * unit future * (unit -> unit))) |
  Finished of theory;

fun task_finished (Task _) = false
  | task_finished (Finished _) = true;

local

fun schedule_seq task_graph =
  ((Graph.topological_order task_graph, Symtab.empty) |-> fold (fn name => fn tab =>
    (case Graph.get_node task_graph name of
      Task (parents, body) =>
        let
          val (thy, present, commit) = body (map (the o Symtab.lookup tab) parents);
          val _ = Future.join present;
          val _ = commit ();
        in Symtab.update (name, thy) tab end
    | Finished thy => Symtab.update (name, thy) tab))) |> ignore;

fun schedule_futures task_graph = uninterruptible (fn _ => fn () =>
  let
    val tasks = Graph.topological_order task_graph;
    val futures = (tasks, Symtab.empty) |-> fold (fn name => fn tab =>
      (case Graph.get_node task_graph name of
        Task (parents, body) =>
          let
            val get = the o Symtab.lookup tab;
            val deps = map (`get) (Graph.imm_preds task_graph name);
            val task_deps = map (Future.task_of o #1) deps;
            fun failed (future, parent) = if can Future.join future then NONE else SOME parent;

            val future =
              singleton
                (Future.forks {name = "theory:" ^ name, group = NONE, deps = task_deps, pri = 0})
                (fn () =>
                  (case map_filter failed deps of
                    [] => body (map (#1 o Future.join o get) parents)
                  | bad => error (loader_msg ("failed to load " ^ quote name ^
                      " (unresolved " ^ commas_quote bad ^ ")") [])));
          in Symtab.update (name, future) tab end
      | Finished thy => Symtab.update (name, Future.value (thy, Future.value (), I)) tab));
    val _ =
      tasks |> maps (fn name =>
        let
          val (thy, present, commit) = Future.join (the (Symtab.lookup futures name));
          val _ = Global_Theory.join_proofs thy;
          val _ = Future.join present;
          val _ = commit ();
        in [] end handle exn => [Exn.Exn exn])
      |> rev |> Exn.release_all;
  in () end) ();

in

fun schedule_tasks tasks =
  if not (Multithreading.enabled ()) then schedule_seq tasks
  else if Multithreading.self_critical () then
     (warning (loader_msg "no multithreading within critical section" []);
      schedule_seq tasks)
  else schedule_futures tasks;

end;


(* require_thy -- checking database entries wrt. the file-system *)

local

fun required_by _ [] = ""
  | required_by s initiators = s ^ "(required by " ^ show_path (rev initiators) ^ ")";

fun load_thy initiators update_time (deps: deps) text name parent_thys =
  let
    val _ = kill_thy name;
    val _ = Output.urgent_message ("Loading theory " ^ quote name ^ required_by " " initiators);

    val {master = (thy_path, _), imports} = deps;
    val dir = Path.dir thy_path;
    val pos = Path.position thy_path;
    val (_, _, uses) = Thy_Header.read pos text;
    fun init _ =
      Thy_Load.begin_theory dir name imports parent_thys uses
      |> Present.begin_theory update_time dir uses;

    val (theory, present) = Outer_Syntax.load_thy name init pos text;

    val parents = map Context.theory_name parent_thys;
    fun commit () =
      NAMED_CRITICAL "Thy_Info" (fn () =>
       (map get_theory parents;
        change_thys (new_entry name parents (SOME deps, SOME theory));
        perform Update name));
  in (theory, present, commit) end;

fun check_deps dir name =
  (case lookup_deps name of
    SOME NONE => (true, NONE, get_parents name)
  | NONE =>
      let val {master, text, imports, ...} = Thy_Load.check_thy dir name
      in (false, SOME (make_deps master imports, text), imports) end
  | SOME (SOME {master, ...}) =>
      let
        val {master = master', text = text', imports = imports', ...} = Thy_Load.check_thy dir name;
        val deps' = SOME (make_deps master' imports', text');
        val current =
          #2 master = #2 master' andalso
            (case lookup_theory name of
              NONE => false
            | SOME theory => Thy_Load.all_current theory);
      in (current, deps', imports') end);

in

fun require_thys initiators dir strs tasks =
      fold_map (require_thy initiators dir) strs tasks |>> forall I
and require_thy initiators dir str tasks =
  let
    val path = Path.expand (Path.explode str);
    val name = Path.implode (Path.base path);
    val dir' = Path.append dir (Path.dir path);
    val _ = member (op =) initiators name andalso error (cycle_msg initiators);
  in
    (case try (Graph.get_node tasks) name of
      SOME task => (task_finished task, tasks)
    | NONE =>
        let
          val (current, deps, imports) = check_deps dir' name
            handle ERROR msg => cat_error msg
              (loader_msg "the error(s) above occurred while examining theory" [name] ^
                required_by "\n" initiators);

          val parents = map base_name imports;
          val (parents_current, tasks') =
            require_thys (name :: initiators)
              (Path.append dir (master_dir (Option.map #1 deps))) imports tasks;

          val all_current = current andalso parents_current;
          val task =
            if all_current then Finished (get_theory name)
            else
              (case deps of
                NONE => raise Fail "Malformed deps"
              | SOME (dep, text) =>
                  let val update_time = serial ()
                  in Task (parents, load_thy initiators update_time dep text name) end);
        in (all_current, new_entry name parents task tasks') end)
  end;

end;


(* use_thy *)

fun use_thys_wrt dir arg =
  schedule_tasks (snd (require_thys [] dir arg Graph.empty));

val use_thys = use_thys_wrt Path.current;
val use_thy = use_thys o single;


(* toplevel begin theory -- without maintaining database *)

fun toplevel_begin_theory master name imports uses =
  let
    val dir = (case master of SOME dir => dir | NONE => Thy_Load.get_master_path ());
    val _ = kill_thy name;
    val _ = use_thys_wrt dir imports;
    val parent_thys = map (get_theory o base_name) imports;
  in Thy_Load.begin_theory dir name imports parent_thys uses end;


(* register theory *)

fun register_thy theory =
  let
    val name = Context.theory_name theory;
    val {master, ...} = Thy_Load.check_thy (Thy_Load.master_directory theory) name;
    val parents = map Context.theory_name (Theory.parents_of theory);
    val imports = Thy_Load.imports_of theory;
    val deps = make_deps master imports;
  in
    NAMED_CRITICAL "Thy_Info" (fn () =>
     (kill_thy name;
      Output.urgent_message ("Registering theory " ^ quote name);
      map get_theory parents;
      change_thys (new_entry name parents (SOME deps, SOME theory));
      perform Update name))
  end;


(* finish all theories *)

fun finish () = change_thys (Graph.map (fn _ => fn (_, entry) => (NONE, entry)));

end;
