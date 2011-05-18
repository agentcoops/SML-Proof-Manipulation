(* Bootstrap a 'minimal' Isabelle environment. *)
use "ML-Systems/polyml.ML"; 

use "General/basics.ML";
use "library.ML";
use "General/alist.ML";
use "General/table.ML";
use "General/graph.ML";

(* Load the TPSP parser, etc. *)
use "../HOL/Tools/ATP/atp_problem.ML"; 
use "../HOL/Tools/ATP/atp_proof.ML";
