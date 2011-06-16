(* 

This is just me learning how to use all of these structures...
If anything here is horribly wrong -- that is, if I'm butchering any of these elegent but
undocumented data structures -- please let me know!

For a while, until I get my bearings, this is just going to be a semi-literate programming
experiment that will eventually be restructured into a proper library.

AUTHOR: coopf
*)

open ATP_Proof;
open ATP_Problem;
open Graph;
(*open Symtab;*)


(* This is just actually getting a proof... Some basic SML manipulation. *)
val test_proof = ATP_Proof.atp_proof_from_tstp_file "" "test.tstp";
val an_element = nth test_proof 0;

(* Table sample code... *)
val table1 = Symtab.make [("foo", "bar"), ("baz", "bin")];

(* 
datatype 'a T = Graph of ('a * (key list * key list)) Table.table;
So, a key maps to (content, (preds, succes))
*)

(* Ah! so in this version, we must filter out the actual dependencies. 
 This could be a much nicer implementation... Need something like flatmap. 
 Also probably better way to check is int... blah. *)
fun dependencies_from_inference (Inference inf) = 
    (List.map (fn justification => #1 justification |> Int.fromString) 
              (#justification inf))
        |> List.filter Option.isSome
        |> List.map (Int.toString o Option.valOf);

(* We now need a more robust node type than before. Role information,
for example, must be included. I think this will be extended alot so, at
least for now, a record type will make development easier... *)
datatype proof_node = ProofNode of {
         formula: (string, string, string fo_term) formula,
         kind: ATP_Problem.formula_kind
         (*, justification? *)
}


(* Graph needs to indicate beginning and end of proof for ease of manipulation. *)
datatype proof_graph = ProofGraph of string * string * proof_node T

(* So, now we have a form of the proof which contains this necessary
pre-processing step.  the information exists in two ways: 1) analyzing
the structure of the proof, 2) in the tstp format.  seems like we
might not always be able to assume that we have the fact that x is
negated conjecture so a mapping between a "raw" proof structure and
one with metadata seems useful. 

TODO: for now, I'm just trusting the TSTP role information, but really
I should flesh out this preprocessing stage such that
negated_conjecture is deduced for greater generality.

fun preprocessed_proof proof = 
*)


(* ProofGraph is: start node, end node, graph. *)
datatype proof_graph = ProofGraph of string * string * proof_node T

(* Do we need to preserve the string names or just keep the numerical identifiers? *)
fun add_proof_step_to_graph (inference as Inference inf, graph) =
    let val name = #1 (#name inf)
        val graph_with_node = 
            new_node (name, ProofNode {formula = #formula inf, kind = #kind inf}) 
                     graph
        val dependencies = dependencies_from_inference inference
        fun add_justification_edge (x, graph) = add_edge (x, name) graph     
    in
        List.foldl add_justification_edge graph_with_node dependencies
    end;

(*
So, we get a problem file which specifies a description of the theory in 
which the ATP is operating.  This is also in TSTP format. Formula here are 
given string identifiers. Seems to be around 500 axioms which is large but
not insurmountable... Benchmark loading that whole structure into memory.
AH! Don't have to! All of the used theorems are actually put into the final
proof as we should expect.

Then, we get a proof. TSTP format is basically:
(identifier for a formula, the formula iteself, what it is justified by)

Identifier will be a number and possibly a name if it comes from a
problem description. We just need to put this into a graph structure!
*)
fun proof_to_graph proof = 
    List.foldl add_proof_step_to_graph Graph.empty proof;

fun graph_from_tstp_file file =
    ATP_Proof.atp_proof_from_tstp_file "" file |> proof_to_graph

val proof_graph = proof_to_graph test_proof;



(* helper functions to affect the negativity of a node. *)
fun formula_from_node (ProofNode node) = #formula node

fun formula_is_negated (AConn(ANot, _)) = true
  | formula_is_negated _ = false

fun node_is_negated (ProofNode node) = 
    #formula node |> formula_is_negated

fun unnegated_formula (AConn(ANot, rest)) = hd rest
  | unnegated_formula otherwise = otherwise

fun unnegated_node (ProofNode node) = 
    ProofNode {formula = #formula node |> unnegated_formula, kind = #kind node} 

fun negated_formula formula = AConn(ANot, [formula])

fun negated_node (ProofNode node) =
    ProofNode {formula = #formula node |> negated_formula, kind = #kind node} 

(* 
"The algorithm relies on the proof by contradiction expressed as a set
of sequents, which are turned around using the contrapositive so that
the formulas are unnegated (as we did in all the examples). It
maintains a set of proved nodes (initially the empty set) and a set of
target nodes that it may proceed to prove (initially the set of all
unnegated nodes). The constructed proof is expressed using the
shorthand notation.

1. Derive as many sequents as possible with their conclusion in the
target set based on the proved nodes. Each time a sequent is appended
to the proof, its conclusion is added to the set of proved nodes.

2. If all the nodes in the target set are proved, we are
done. Otherwise, the last sequent must be a disjunctive expression
with at least 2 clauses. Perform an n-way case split:

3. For each of the branches, invoke the procedure recursively, with
the assumption added to the proved set and with all the nodes that
dominate the branch and no other branch as the target set.

4. After the case split, go back to step 1. The case split itself is
seen as a disjunctive sequent."
*)

(*

Start from terminating node. 
Get set of proving nodes.
Add each to 


OK! So, with this we can merge two subgraphs...
merge (fn (x,y) => x=y) (graph, graph2);
*)



fun conjectures graph = 
    let fun is_conjecture (_, (ProofNode node, _)) =
            case #kind node of
                Conjecture => true
              | _ => false
    in
        Graph.filter_nodes is_conjecture graph
    end;

fun negated_conjectures_in_list graph nodes =
    let fun is_negated_conjecture key =
            let val (ProofNode node) = Graph.get_node graph key
            in
                case #kind node of
                    NegatedConjecture => true
                  | _ => false
            end
    in
        List.filter is_negated_conjecture nodes
    end;

(* So this now does nothing to the node itself, rather just swapping the appropriate edges. *)
fun proof_contraposition graph =
    let fun node_contraposition (node_id, graph) = 
            let fun constant_list_of_same_size value lst = 
                    List.tabulate (length lst, fn _ => value) 
                val succ_reversals = 
                    (Graph.imm_succs graph node_id) 
                        |> negated_conjectures_in_list graph 
                        |> (fn succs => 
                               ListPair.zip (constant_list_of_same_size node_id succs, 
                                             succs))
                val pred_reversals = 
                    (Graph.imm_preds graph node_id) 
                        |> negated_conjectures_in_list graph 
                        |> (fn preds => 
                               ListPair.zip (preds,
                                             constant_list_of_same_size node_id preds))
            in
                graph |> Graph.reverse_edges (succ_reversals @ pred_reversals) 
            end
        fun new_node (node_id, graph) =
            let val (ProofNode node) = Graph.get_node graph node_id
                val negated_formula = #formula node |> negated_formula              
            in       
                case #kind node of
                    NegatedConjecture =>  
                    Graph.map_node node_id 
                                   (fn _ =>
                                       ProofNode {formula = negated_formula, 
                                                  kind = Plain})
                                   graph
                  | _ => graph
            end
        val keys = Graph.keys graph
    in
        List.foldl node_contraposition graph keys
                   |> (fn g1 => List.foldl new_node g1 keys)
    end

fun node_info graph id = 
    let val node = Graph.get_node graph id
        val succs = Graph.imm_succs graph id
        val preds = Graph.imm_preds graph id
    in (node, preds, succs) end;


fun proof_contraposition graph =
    





fun new_node (ProofNode node) =
    case #kind node of
        NegatedConjecture => 
        ProofNode
            {formula = #formula node |> negated_formula, 
             kind = Plain}
      | other => ProofNode node

(* also, the preceding method seems not to be exactly what is needed
here... Really just need to return subgraph centered on node... *)
fun sequent_contraposition graph node_id = 
    let val (ProofNode node) = Graph.get_node graph node_id
        val negated_formula = #formula node |> negated_formula
        val new_kind =        
            case #kind node of
                NegatedConjecture => Plain 
              | other => other
        val new_graph = 
        val new_edges = 
    in
        
    end
    

(* Now we can make a first pass at the algorithm... *)
fun negation_to_direct proof =
    let val unnegated_nodes = []
        fun negation_to_direct' proved target =
    in
        negation_to_direct' [] unnegated_nodes
    end;
