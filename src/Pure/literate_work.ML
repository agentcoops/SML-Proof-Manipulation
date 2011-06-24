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
datatype proof_graph = ProofGraph of string * proof_node Graph.T

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
datatype proof_graph = ProofGraph of string * string * proof_node Graph.T

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

fun conjectures_in_list graph nodes =
    let fun is_negated_conjecture key =
            let val (ProofNode node) = Graph.get_node graph key
            in
                case #kind node of
                    NegatedConjecture => true
                  | Conjecture => true
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
                val pred_reversals = 
                    (Graph.imm_preds graph node_id) 
                        |> conjectures_in_list graph 
                        |> (fn preds => 
                               ListPair.zip (preds,
                                             constant_list_of_same_size node_id preds))
            in
                graph |> Graph.reverse_edges pred_reversals
            end
        fun new_node (node_id, graph) =
            let val (ProofNode node) = Graph.get_node graph node_id
                val negated_formula = #formula node |> negated_formula
                fun make_node _ =
                    ProofNode 
                        {formula = negated_formula, 
                         kind = Plain}
            in       
                case #kind node of
                    NegatedConjecture => Graph.map_node node_id make_node graph
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


(* Ugh, this is crazy inefficient... *)
fun graph_to_graphviz get_node_name get_node_metadata graph file_name =
    let val graph_output = TextIO.openOut file_name
        val keys = Graph.keys graph
        fun output line = TextIO.output (graph_output, line)
        fun output_connection node1 node2 =
            output ("\t\"" ^ get_node_name node1 ^ "\" -> \"" 
                    ^ get_node_name node2 ^ "\";\n")
        fun plot_connections key = 
            List.app (fn node2 => output_connection key node2) 
                     (Graph.imm_succs graph key)
        fun plot_node_info key = get_node_metadata key |> output
    in 
        (output "digraph ml_graph {\n";
         List.app plot_node_info keys;
         List.app plot_connections keys;
         output "}\n";
         TextIO.closeOut graph_output)
    end
    
fun proof_graph_to_graphviz graph file_name use_formula_label =
    let fun handle_node_name key = 
            let val (ProofNode node) = Graph.get_node graph key
                val formula_string = 
                    if use_formula_label then
                        ": " ^ string_for_untyped_formula FOF (#formula node)
                    else ""
            in
                case #kind node of
                    NegatedConjecture => "~" ^ key ^ formula_string
                  | _ => key ^ formula_string
            end 
        fun handle_node_metadata key = 
            let val (ProofNode node) = Graph.get_node graph key
                fun make_line_string color = 
                    "\t\"" ^ handle_node_name key ^ 
                    "\" [ style=\"filled\", color=\"" ^ 
                    color ^ "\"];\n"
            in 
                case #kind node of
                    Conjecture => make_line_string "darkturquoise"
                  | NegatedConjecture => make_line_string "crimson"
                  | Axiom => make_line_string "yellow"
                  | Lemma => make_line_string "lightskyblue"
                  | Hypothesis => make_line_string "chartreuse"
                  | _ => ""
            end
    in 
        graph_to_graphviz handle_node_name handle_node_metadata graph file_name
    end

fun direct_and_original_graphviz_for_tstp_file file_name use_formula_label =
    let val proof = graph_from_tstp_file file_name
        val contra = proof_contraposition proof
    in
        (proof_graph_to_graphviz contra (file_name ^ ".direct.gv") use_formula_label;
         proof_graph_to_graphviz proof (file_name ^ ".negation.gv") use_formula_label)
    end


fun contains list element = List.exists (fn x => x = element) list


(* So, it seems like we should perhaps extend the datatype to actually
include the start of the graph in question, but for now we'll kill two
birds with one stone and, given that it remains unclear whether all
proofs will include actual conjecture types as the start, derive the
start of a graph as the first non-"TRUE" nodes with no (non-"TRUE")
ancestors 

I think we also want to ignore conjectures here? *)
fun get_proof_start proof = 
    let fun is_undesirable node_id = 
            let val (ProofNode node) = Graph.get_node proof node_id 
            in 
                (case #formula node of 
                   AAtom (ATerm ("$true", _)) => true
                 | AConn (ANot, [AAtom (ATerm ("$false", _))]) => true
                 | _ => false)
                orelse 
                (case #kind node of
                     Conjecture => true
                   | _ => false)
            end
            
        val undesirables = 
            Graph.filter_nodes (fn (key, _) => is_undesirable key) proof

        fun desirable id = not (contains undesirables id)

        fun desirable_preds id = List.filter desirable (Graph.imm_preds proof id) 
                                    
        fun non_true_conjectures node_ids =
            let fun folder (id, nodes) = 
                    if desirable id andalso desirable_preds id = []
                    then id :: nodes
                    else nodes
                val surviving_ids = List.foldl folder [] node_ids
            in 
                if (List.rev surviving_ids) = node_ids then
                    surviving_ids
                else non_true_conjectures surviving_ids
            end
    in
        (non_true_conjectures (Graph.keys proof), undesirables)
    end            

(* TISAR! *)
datatype 'a tisar_proof =
         Block of 'a tisar_proof list
       | Branch of 'a tisar_proof list
       | Have of 'a list
       | Assume of 'a
       | Hence of 'a                    

datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof * 'a tisar_proof
       | Have of 'a list
       | Assume of 'a
       | Hence of 'a
       | QED

val lasso1 = 
    Block [Have ["5", "6"], 
           Branch 
               [Block [Assume "5", Hence "3", Hence "2"], 
                Block [Assume "6", Hence "4", Hence "2"]],
           Hence "1", 
           Hence "0"]

val lasso_graph = 
    graph_from_tstp_file "../../gallery/crafted/lasso1/lasso1.tstp" 
       |> proof_contraposition

(* next we must proceed down the graph...

so the start will probably either be a have or an assume. if it's a
negated conjecture then what we have is assumption (proof by negation)
and we act accordingly; otherwise, it's a have. 

basically, if it's a 

 *)
fun graph_to_tisar proof = 
    let val (proof_start, to_ignore) = get_proof_start proof

        fun handle_id node_id = Graph.imm_succs proof node_id |> handle_nodes
                       
        and handle_node node_id = 
            let val (ProofNode node) = Graph.get_node proof node_id
                val pred_count = 
                    Graph.imm_preds proof node_id 
                                    |> List.filter (fn x => contains to_ignore x)
                                    |> length
            in
                case #kind node of
                    NegatedConjecture => Hence ("~" ^ node_id)
                  | _ => if (pred_count = 0) then (Have [node_id]) else (Hence node_id)
            end
         
        and handle_branching (node :: []) = Block (Assume node, handle_id node)
          | handle_branching (node :: tail) = 
            Branch (handle_branching [node], handle_branching tail)
            
        and handle_nodes [] = QED
          | handle_nodes (node :: []) = Block (handle_node node, handle_id node)
          | handle_nodes nodes = handle_branching nodes
    in
        handle_nodes proof_start
    end
