(* Bootstrap a 'minimal' Isabelle environment. *)
use "ML-Systems/polyml.ML"; 

(* This provides alot of the standard Isabelle combinators, etc. *)
use "General/basics.ML";
use "library.ML";

(* Useful datastructures. *)
use "General/alist.ML";
use "General/table.ML";
use "General/ord_list.ML";
use "General/graph.ML";

(* Necessary to use the TPSP parser. *)
use "General/scan.ML";
use "General/print_mode.ML";
use "General/output.ML";
use "General/source.ML";
use "General/symbol.ML";
use "General/properties.ML";
use "General/markup.ML";
use "General/position.ML";
use "General/long_name.ML";
use "General/binding.ML";
use "General/name_space.ML";
use "General/path.ML";
use "Concurrent/simple_thread.ML";
use "Concurrent/single_assignment.ML";
use "Concurrent/synchronized.ML";
use "Concurrent/task_queue.ML";
use "Concurrent/future.ML";
use "General/same.ML";
use "name.ML";
use "term.ML";
use "proofterm.ML";
use "type.ML";
use "envir.ML";

use "../HOL/Tools/ATP/atp_util.ML";
(* Load the TPSP parser, etc. *)
(*
use "../HOL/Tools/ATP/atp_problem_new.ML"; 
use "../HOL/Tools/ATP/atp_proof_new.ML";*)
