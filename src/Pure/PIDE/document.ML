(*  Title:      Pure/PIDE/document.ML
    Author:     Makarius

Document as collection of named nodes, each consisting of an editable
list of commands, associated with asynchronous execution process.
*)

signature DOCUMENT =
sig
  type id = int
  type version_id = id
  type command_id = id
  type exec_id = id
  val no_id: id
  val new_id: unit -> id
  val parse_id: string -> id
  val print_id: id -> string
  type edit = string * ((command_id option * command_id option) list) option
  type state
  val init_state: state
  val cancel: state -> unit
  val define_command: command_id -> string -> state -> state
  val edit: version_id -> version_id -> edit list -> state -> (command_id * exec_id) list * state
  val execute: version_id -> state -> state
end;

structure Document: DOCUMENT =
struct

(* unique identifiers *)

type id = int;
type version_id = id;
type command_id = id;
type exec_id = id;

val no_id = 0;
val new_id = Synchronized.counter ();

val parse_id = Markup.parse_int;
val print_id = Markup.print_int;

fun err_dup kind id = error ("Duplicate " ^ kind ^ ": " ^ print_id id);
fun err_undef kind id = error ("Undefined " ^ kind ^ ": " ^ print_id id);



(** document structure **)

structure Entries = Linear_Set(type key = command_id val ord = int_ord);

abstype node = Node of exec_id option Entries.T  (*command entries with excecutions*)
  and version = Version of node Graph.T  (*development graph wrt. static imports*)
with

val empty_node = Node Entries.empty;
val empty_version = Version Graph.empty;

fun fold_entries start f (Node entries) = Entries.fold start f entries;
fun first_entry start P (Node entries) = Entries.get_first start P entries;


(* node edits and associated executions *)

type edit =
  string *
  (*NONE: remove node, SOME: insert/remove commands*)
  ((command_id option * command_id option) list) option;

fun the_entry (Node entries) id =
  (case Entries.lookup entries id of
    NONE => err_undef "command entry" id
  | SOME entry => entry);

fun update_entry (id, exec_id) (Node entries) =
  Node (Entries.update (id, SOME exec_id) entries);

fun reset_after id entries =
  (case Entries.get_after entries id of
    NONE => entries
  | SOME next => Entries.update (next, NONE) entries);

fun edit_node (hook, SOME id2) (Node entries) =
      Node (Entries.insert_after hook (id2, NONE) entries)
  | edit_node (hook, NONE) (Node entries) =
      Node (entries |> Entries.delete_after hook |> reset_after hook);


(* version operations *)

fun nodes_of (Version nodes) = nodes;
val node_names_of = Graph.keys o nodes_of;

fun get_node version name = Graph.get_node (nodes_of version) name
  handle Graph.UNDEF _ => empty_node;

fun edit_nodes (name, SOME edits) (Version nodes) =
      Version (nodes
        |> Graph.default_node (name, empty_node)
        |> Graph.map_node name (fold edit_node edits))
  | edit_nodes (name, NONE) (Version nodes) =
      Version (perhaps (try (Graph.del_node name)) nodes);

fun put_node name node (Version nodes) =
  Version (nodes
    |> Graph.default_node (name, empty_node)
    |> Graph.map_node name (K node));

end;



(** global state -- document structure and execution process **)

abstype state = State of
 {versions: version Inttab.table,  (*version_id -> document content*)
  commands: Toplevel.transition future Inttab.table,  (*command_id -> transition (future parsing)*)
  execs: (bool * Toplevel.state) lazy Inttab.table,  (*exec_id -> execution process*)
  execution: unit future list}  (*global execution process*)
with

fun make_state (versions, commands, execs, execution) =
  State {versions = versions, commands = commands, execs = execs, execution = execution};

fun map_state f (State {versions, commands, execs, execution}) =
  make_state (f (versions, commands, execs, execution));

val init_state =
  make_state (Inttab.make [(no_id, empty_version)],
    Inttab.make [(no_id, Future.value Toplevel.empty)],
    Inttab.make [(no_id, Lazy.value (true, Toplevel.toplevel))],
    []);


(* document versions *)

fun define_version (id: version_id) version =
  map_state (fn (versions, commands, execs, execution) =>
    let val versions' = Inttab.update_new (id, version) versions
      handle Inttab.DUP dup => err_dup "document version" dup
    in (versions', commands, execs, execution) end);

fun the_version (State {versions, ...}) (id: version_id) =
  (case Inttab.lookup versions id of
    NONE => err_undef "document version" id
  | SOME version => version);


(* commands *)

fun define_command (id: command_id) text =
  map_state (fn (versions, commands, execs, execution) =>
    let
      val id_string = print_id id;
      val tr = Future.fork_pri 2 (fn () =>
        Position.setmp_thread_data (Position.id_only id_string)
          (fn () => Outer_Syntax.prepare_command (Position.id id_string) text) ());
      val commands' =
        Inttab.update_new (id, tr) commands
          handle Inttab.DUP dup => err_dup "command" dup;
    in (versions, commands', execs, execution) end);

fun the_command (State {commands, ...}) (id: command_id) =
  (case Inttab.lookup commands id of
    NONE => err_undef "command" id
  | SOME tr => tr);

fun join_commands (State {commands, ...}) =
  Inttab.fold (fn (_, tr) => fn () => ignore (Future.join_result tr)) commands ();


(* command executions *)

fun define_exec (id: exec_id) exec =
  map_state (fn (versions, commands, execs, execution) =>
    let val execs' = Inttab.update_new (id, exec) execs
      handle Inttab.DUP dup => err_dup "command execution" dup
    in (versions, commands, execs', execution) end);

fun the_exec (State {execs, ...}) (id: exec_id) =
  (case Inttab.lookup execs id of
    NONE => err_undef "command execution" id
  | SOME exec => exec);


(* document execution *)

fun cancel (State {execution, ...}) =
  List.app Future.cancel execution;

fun await_cancellation (State {execution, ...}) =
  ignore (Future.join_results execution);

end;



(* toplevel transactions *)

local

fun timing tr t = Toplevel.status tr (Markup.timing t);

fun proof_status tr st =
  (case try Toplevel.proof_of st of
    SOME prf => Toplevel.status tr (Proof.status_markup prf)
  | NONE => ());

fun async_state tr st =
  ignore
    (singleton
      (Future.forks {name = "Document.async_state",
        group = SOME (Task_Queue.new_group NONE), deps = [], pri = 0})
      (fn () =>
        Toplevel.setmp_thread_position tr
          (fn () => Toplevel.print_state false st) ()));

fun run int tr st =
  (case Toplevel.transition int tr st of
    SOME (st', NONE) => ([], SOME st')
  | SOME (_, SOME exn_info) =>
      (case ML_Compiler.exn_messages (Runtime.EXCURSION_FAIL exn_info) of
        [] => Exn.interrupt ()
      | errs => (errs, NONE))
  | NONE => ([ML_Compiler.exn_message Runtime.TERMINATE], NONE));

in

fun run_command thy_name raw_tr st =
  (case
      (case Toplevel.init_of raw_tr of
        SOME name => Exn.capture (fn () =>
          let
            val path = Path.explode thy_name;
            val _ = Thy_Header.consistent_name (Path.implode (Path.base path)) name;
          in Toplevel.modify_master (SOME (Path.dir path)) raw_tr end) ()
      | NONE => Exn.Result raw_tr) of
    Exn.Result tr =>
      let
        val is_init = is_some (Toplevel.init_of tr);
        val is_proof = Keyword.is_proof (Toplevel.name_of tr);
        val do_print = not is_init andalso (Toplevel.print_of tr orelse is_proof);

        val start = Timing.start ();
        val (errs, result) =
          if Toplevel.is_toplevel st andalso not is_init then ([], SOME st)
          else run (is_init orelse is_proof) (Toplevel.set_print false tr) st;
        val _ = timing tr (Timing.result start);
        val _ = List.app (Toplevel.error_msg tr) errs;
        val res =
          (case result of
            NONE => (Toplevel.status tr Markup.failed; (false, st))
          | SOME st' =>
             (Toplevel.status tr Markup.finished;
              proof_status tr st';
              if do_print then async_state tr st' else ();
              (true, st')));
      in res end
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then reraise exn
      else
       (Toplevel.error_msg raw_tr (ML_Compiler.exn_message exn);
        Toplevel.status raw_tr Markup.failed;
        (false, Toplevel.toplevel)));

end;




(** editing **)

(* edit *)

local

fun is_changed node' ((_, id), exec) =
  (case try (the_entry node') id of
    NONE => true
  | SOME exec' => exec' <> exec);

fun new_exec name (id: command_id) (exec_id, updates, state) =
  let
    val exec = the_exec state exec_id;
    val exec_id' = new_id ();
    val future_tr = the_command state id;
    val exec' =
      Lazy.lazy (fn () =>
        let
          val st = #2 (Lazy.force exec);
          val exec_tr = Toplevel.put_id (print_id exec_id') (Future.join future_tr);
        in run_command name exec_tr st end);
    val state' = define_exec exec_id' exec' state;
  in (exec_id', (id, exec_id') :: updates, state') end;

in

fun edit (old_id: version_id) (new_id: version_id) edits state =
  let
    val old_version = the_version state old_id;
    val _ = Time.now ();  (* FIXME odd workaround *)
    val new_version = fold edit_nodes edits old_version;

    fun update_node name (rev_updates, version, st) =
      let val node = get_node version name in
        (case first_entry NONE (is_changed (get_node old_version name)) node of
          NONE => (rev_updates, version, st)
        | SOME ((prev, id), _) =>
            let
              val prev_exec =
                (case prev of
                  NONE => no_id
                | SOME prev_id => the_default no_id (the_entry node prev_id));
              val (_, rev_upds, st') =
                fold_entries (SOME id) (new_exec name o #2 o #1) node (prev_exec, [], st);
              val node' = fold update_entry rev_upds node;
            in (rev_upds @ rev_updates, put_node name node' version, st') end)
      end;

    (* FIXME proper node deps *)
    val (rev_updates, new_version', state') =
      fold update_node (node_names_of new_version) ([], new_version, state);
    val state'' = define_version new_id new_version' state';

    val _ = join_commands state'';  (* FIXME async!? *)
  in (rev rev_updates, state'') end;

end;


(* execute *)

fun execute version_id state =
  state |> map_state (fn (versions, commands, execs, _) =>
    let
      val version = the_version state version_id;

      fun force_exec NONE = ()
        | force_exec (SOME exec_id) = ignore (Lazy.force (the_exec state exec_id));

      val _ = cancel state;

      val execution' = (* FIXME proper node deps *)
        Future.forks {name = "Document.execute", group = NONE, deps = [], pri = 1}
          [fn () =>
            let
              val _ = await_cancellation state;
              val _ =
                node_names_of version |> List.app (fn name =>
                  fold_entries NONE (fn (_, exec) => fn () => force_exec exec)
                      (get_node version name) ());
            in () end];

      val _ = await_cancellation state;  (* FIXME async!? *)

    in (versions, commands, execs, execution') end);

end;

