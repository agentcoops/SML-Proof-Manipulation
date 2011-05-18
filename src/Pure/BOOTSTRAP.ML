(* Bootstrap a 'minimal' Isabelle environment. *)
use "ML-Systems/polyml.ML"; 

(* This provides alot of the standard Isabelle combinators, etc. *)
use "General/basics.ML";
use "library.ML";

(* Useful datastructures. *)
use "General/alist.ML";
use "General/table.ML";
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
use "name.ML";

(* Load the TPSP parser, etc. *)
use "../HOL/Tools/ATP/atp_problem.ML"; 
use "../HOL/Tools/ATP/atp_proof.ML";
