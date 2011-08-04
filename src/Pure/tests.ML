(* OK, I want to formalize the tests a bit better for this project. *)

use "ROOT.ML"; (* load the necessary isabelle environment. *)
use "proofgraph.ML"; (* load proofgraph. *)
use "tisar.ML"; (* load all of the tisar code *)

(* Test tstp. *)
val simple2 = TSTPProofGraph.proof_graph_from_file "simple2.tstp"
val contra2 = TSTPProofGraph.proof_contraposition simple2
val contra_tisar = TSTPTisar.proof_graph_to_tisar contra2

val diabolo = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/diabolo/diabolo.tstp"
val contra_diabolo = TSTPProofGraph.proof_contraposition diabolo
val diabolo_tisar = TSTPTisar.proof_graph_to_tisar contra_diabolo

TSTPTisar.tisar_to_string contra_tisar |> writeln
