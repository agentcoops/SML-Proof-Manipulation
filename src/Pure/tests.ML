(* OK, I want to formalize the tests a bit better for this project. *)

use "ROOT.ML"; (* load the necessary isabelle environment. *)
use "proofgraph.ML"; (* load proofgraph. *)

(* Test tstp. *)
val simple2 = TSTPProofGraph.proof_graph_from_file "simple2.tstp"
val contra2 = TSTPProofGraph.proof_contraposition simple2
