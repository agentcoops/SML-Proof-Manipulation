(* OK, I want to normalize the tests a bit better for this project. *)
use "ROOT.ML"; (* load the necessary isabelle environment. *)
use "proofgraph.ML"; (* load proofgraph. *)
use "tisar.ML"; (* load all of the tisar code *)

(* helper methods *)
fun debugging_graph (graph: TSTPProofGraph.proof_node T) node =
    let val thing = Graph.get_node graph node
    in
        (writeln ("graph: " ^ (thing |> PolyML.makestring));
         writeln ("preds: " ^ (Graph.imm_preds graph node |> PolyML.makestring));
         writeln ("succs: " ^ (Graph.imm_succs graph node |> PolyML.makestring)))
    end

(* "tests" *)
val simple2 = TSTPProofGraph.proof_graph_from_file "simple2.tstp";
val contra2 = TSTPProofGraph.proof_contraposition simple2;
val contra_tisar = TSTPTisar.proof_graph_to_tisar contra2;
TSTPTisar.tisar_to_string contra_tisar |> writeln;

val lasso1 = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/lasso1/lasso1.tstp";
val contra_lasso1 = TSTPProofGraph.proof_contraposition lasso1;
val  (TSTPProofGraph.ProofGraph lasso1_graph) = contra_lasso1;
val lasso1_tisar = TSTPTisar.proof_graph_to_tisar contra_lasso1;
TSTPTisar.tisar_to_string lasso1_tisar |> writeln;

val lasso2 = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/lasso2/lasso2.tstp";
val contra_lasso2 = TSTPProofGraph.proof_contraposition lasso2;
val lasso2_tisar = TSTPTisar.proof_graph_to_tisar contra_lasso2;
TSTPTisar.tisar_to_string lasso2_tisar |> writeln;

val diabolo = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/diabolo/diabolo.tstp";
val contra_diabolo = TSTPProofGraph.proof_contraposition diabolo;
val diabolo_tisar = TSTPTisar.proof_graph_to_tisar contra_diabolo;
TSTPTisar.tisar_to_string diabolo_tisar |> writeln;
