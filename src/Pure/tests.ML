(* OK, I want to normalize the tests a bit better for this project. *)
use "ROOT.ML"; (* load the necessary isabelle environment. *)
use "tisarhelp.ML";
use "negatableformula.ML";
use "proofgraph.ML"; (* load proofgraph. *)
use "tisar.ML"; (* load all of the tisar code *)

(* "tests" *)
val simple2 = TSTPProofGraph.proof_graph_from_file "simple2.tstp";
val contra2 = TSTPProofGraph.proof_contraposition simple2;
val  (TSTPProofGraph.ProofGraph contra_graph) = contra2;
val contra_tisar = TSTPTisar.proof_graph_to_tisar contra2;
TSTPTisar.tisar_to_string contra_tisar |> writeln;

val linear = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/linear/linear.tstp";
val contra_linear = TSTPProofGraph.proof_contraposition linear;
val  (TSTPProofGraph.ProofGraph linear_graph) = contra_linear;
val linear_tisar = TSTPTisar.proof_graph_to_tisar contra_linear;
TSTPTisar.tisar_to_string linear_tisar |> writeln;

val lasso1 = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/lasso1/lasso1.tstp";
val contra_lasso1 = TSTPProofGraph.proof_contraposition lasso1;
val  (TSTPProofGraph.ProofGraph lasso1_graph) = contra_lasso1;
val lasso1_tisar = TSTPTisar.proof_graph_to_tisar contra_lasso1;
TSTPTisar.tisar_to_string lasso1_tisar |> writeln;

val lasso2 = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/lasso2/lasso2.tstp";
val contra_lasso2 = TSTPProofGraph.proof_contraposition lasso2;
val  (TSTPProofGraph.ProofGraph lasso2_graph) = contra_lasso2;
val lasso2_tisar = TSTPTisar.proof_graph_to_tisar contra_lasso2;
TSTPTisar.tisar_to_string lasso2_tisar |> writeln;

val torch = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/torch/torch.tstp";
val  (TSTPProofGraph.ProofGraph torch_graph_norm) = torch;
val contra_torch = TSTPProofGraph.proof_contraposition torch;
val  (TSTPProofGraph.ProofGraph torch_graph) = contra_torch;
TSTPProofGraph.proof_graph_to_graphviz contra_torch "torch.gv" false;
val torch_tisar = TSTPTisar.proof_graph_to_tisar contra_torch;
TSTPTisar.tisar_to_string torch_tisar |> writeln;


(*THE BROKEN!*)
val cube = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/cube/cube.tstp";
TSTPProofGraph.proof_graph_to_graphviz cube "cube_original.gv" false;
val contra_cube = TSTPProofGraph.proof_contraposition cube;
val  (TSTPProofGraph.ProofGraph cube_graph) = contra_cube;
TSTPProofGraph.proof_graph_to_graphviz contra_cube "cube.gv" false;
val cube_tisar = TSTPTisar.proof_graph_to_tisar contra_cube;
TSTPTisar.tisar_to_string cube_tisar |> writeln;

val diabolo = TSTPProofGraph.proof_graph_from_file "../../gallery/crafted/diabolo/diabolo.tstp";
val  (TSTPProofGraph.ProofGraph diabolo_plain) = diabolo;
val contra_diabolo = TSTPProofGraph.proof_contraposition diabolo;
val  (TSTPProofGraph.ProofGraph diabolo_graph) = contra_diabolo;
TSTPProofGraph.proof_graph_to_graphviz contra_diabolo "diabolo.gv" false;
val diabolo_tisar = TSTPTisar.proof_graph_to_tisar contra_diabolo;
TSTPTisar.tisar_to_string diabolo_tisar |> writeln;

(*
notes: remember, I think the issue might even go back to the proof graph, sadly... 

OK. So, definitately a problem in the original proofgraph code.
2, for example, leads to 1 | 4 | 5.

looking in proofgraph, it looks like, before disjunctions are
introduced, we get 4 as both pred and succ of 2. NOT GOOD.
*)
