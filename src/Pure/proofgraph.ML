(* OK. Now it's time to make this a real library... *)
open ATP_Proof;
open ATP_Problem;
open Graph;


signature NEGATABLE_FORMULA = sig
    type formula

    val negated_formula: formula -> formula
    val disjunct_formulae: formula list -> formula
    val is_disjunct: formula -> bool
    val is_top: formula -> bool
    val is_bottom: formula -> bool
    val string_for_formula: formula -> string
    val should_skip: formula -> bool
    val possibly_proof_from_file: (string -> formula ATP_Proof.step list) option
end


signature PROOF_GRAPH = sig
    type formula
    val negated_formula: formula -> formula
                
    datatype proof_node = ProofNode of {
         formula: formula,
         kind: formula_kind
         (*, justification? *)
    }
    type proof = formula ATP_Proof.step list
    datatype proof_graph = ProofGraph of proof_node Graph.T

    val proof_to_graph: proof -> proof_graph
    val proof_contraposition: proof_graph -> proof_graph        
    val proof_graph_to_graphviz: proof_graph -> string -> bool -> unit
    val proof_graph_from_file: string -> proof_graph
    val get_proof_start: proof_graph -> (key list * key list)
    val get_proof_node_formula: proof_node -> formula
end


(* This is my standard library. Just contains various helper functions. *)
structure Help = struct

fun constant_list_of_same_size value lst = 
    List.tabulate (length lst, fn _ => value)
    
fun contains list element = List.exists (fn x => x = element) list

fun list_to_string lst delimiter =
    let fun folder (value, accum) = 
            if not (accum = "") then (accum ^ delimiter ^ value)
            else value
    in 
        List.foldl folder "" lst 
    end

fun partition_graph f graph =
    let val keys = Graph.keys graph
    in 
        List.partition f keys
    end
    
fun swap_edges graph _ [] = graph
  | swap_edges graph node_id ((node1, node2) :: nodes) =
    let val new_graph = 
            if node1 = node2 then 
                graph
            else
                Graph.del_edge (node_id, node1) graph
                               |> Graph.add_edge (node_id, node2)
    in 
        swap_edges new_graph node_id nodes
    end
    
(* the reduce step. naive merging for now. *)
fun merge_subgraphs sub_graph new_graph = 
    Graph.join (fn _ => fn (left, _) => left) 
               (sub_graph, new_graph)
    
fun node_subgraph graph node = 
    let val surroundings = Graph.imm_preds graph node @ [node]
    in
        Graph.filter 
            (fn (key, _) => contains surroundings key) 
            graph
    end

fun del_edges id ([]) graph = graph
  | del_edges id (node :: nodes) graph = 
    Graph.del_edge (id, node) graph |> del_edges id nodes

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
end


open Help


functor MakeProofGraph(formula_struct: NEGATABLE_FORMULA): PROOF_GRAPH = 
struct

open formula_struct
(*open ATP_Problem
open ATP_Proof*)

type proof = formula ATP_Proof.step list        
(*datatype formula_kind = 
         Axiom | Definition | Lemma | Hypothesis |
         Conjecture | NegatedConjecture | Plain*)


fun dependencies_from_inference (ATP_Proof.Inference inf) = 
    (List.map (fn justification => #1 justification |> Int.fromString) 
              (#justification inf))
        |> List.filter Option.isSome
        |> List.map (Int.toString o Option.valOf);

datatype proof_node = ProofNode of {
         formula: formula,
         kind: formula_kind
         (*, justification? *)
}

datatype proof_graph = ProofGraph of proof_node Graph.T

exception ProofFromFileNotDefined

fun add_proof_step_to_graph (inference as ATP_Proof.Inference inf, graph) =
    let val name = #1 (#name inf)
        val graph_with_node = 
            Graph.new_node (name, ProofNode {formula = #formula inf, kind = #kind inf})
                           graph
        val dependencies = dependencies_from_inference inference
        fun add_justification_edge (x, graph) = 
            Graph.add_edge (x, name) graph     
    in
        List.foldl add_justification_edge graph_with_node dependencies
    end

fun proof_to_graph proof = 
    ProofGraph (List.foldl add_proof_step_to_graph Graph.empty proof);

fun proof_graph_from_file proof_location =
    case possibly_proof_from_file of
        SOME function => function proof_location |> proof_to_graph
      | NONE => raise ProofFromFileNotDefined                  
    
fun get_proof_start (ProofGraph proof) = 
    let fun is_undesirable node_id = 
            let val (ProofNode node) = Graph.get_node proof node_id 
            in       
                (case #kind node of
                     Conjecture => true
                   | _ => false)
                orelse
                (#formula node |> should_skip)
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

fun proof_graph_to_graphviz (ProofGraph graph) file_name use_formula_label =
    let fun handle_node_name key = 
            let val (ProofNode node) = Graph.get_node graph key
                val formula_string = 
                    if use_formula_label then
                        ": " ^ string_for_formula (#formula node)
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

fun is_conjecture graph node_id = 
    let val (ProofNode node) = Graph.get_node graph node_id
    in 
        case #kind node of
            NegatedConjecture => true
          | Conjecture => true
          | _ => false
    end

fun conjectures_in_list graph nodes = 
    List.filter (is_conjecture graph) nodes

fun conjectures graph = 
    conjectures_in_list graph (Graph.keys graph)

fun get_proof_node_formula (ProofNode node) = #formula node

fun proof_contraposition (ProofGraph original_graph) =
    (* first need to be able to get subgraph around a node. *)
    let val get_subgraph = node_subgraph original_graph
         
        fun node_contraposition (node_id, graph) = 
            let val subgraph = get_subgraph node_id
                val conjecture_check = is_conjecture subgraph
                val (conjectures, plains) = 
                    partition_graph conjecture_check subgraph
                val reversals = 
                    if (contains conjectures node_id) then
                        ListPair.zip 
                            (conjectures,
                             constant_list_of_same_size node_id conjectures)
                    else []
                val swaps = 
                    ListPair.zip 
                        (constant_list_of_same_size node_id conjectures,
                         conjectures)
                val swapped_subgraph = 
                    List.foldl (fn (plain_id, graph_accum) => 
                                   swap_edges graph_accum plain_id swaps)
                               subgraph
                               plains
                      |> Graph.reverse_edges reversals
            in
                merge_subgraphs swapped_subgraph graph
            end
            
        fun new_node (node_id, graph) =
            let val (ProofNode node) = Graph.get_node graph node_id
                val formula = #formula node
                val new_formula = 
                    if not (is_bottom formula)
                    then negated_formula formula
                    else Graph.imm_succs graph node_id 
                          |> List.map (fn id => Graph.get_node graph id 
                                                 |> get_proof_node_formula)
                          |> disjunct_formulae 
                fun make_node _ =
                    ProofNode 
                        {formula = new_formula, 
                         kind = ATP_Problem.Plain}
            in       
                case #kind node of
                    NegatedConjecture => Graph.map_node node_id make_node graph
                  | _ => graph
            end
            
        val keys = Graph.keys original_graph
        val redirected_graph = List.foldl node_contraposition Graph.empty keys
    in
        ProofGraph (List.foldl new_node redirected_graph keys)
    end
end


structure TSTPFormula: NEGATABLE_FORMULA = 
struct

type formula = (string, string, string fo_term) ATP_Proof.formula (* this might be ATP_Problem? *)

fun negated_formula formula = ATP_Problem.mk_anot formula

fun disjunct_formulae formulae = AConn (AOr, formulae)

fun is_disjunct (AConn (AOr, _)) = true
  | is_disjunct _ = false

fun is_bottom (AAtom (ATerm ("$false", _))) = true
  | is_bottom (AConn (ANot, [AAtom (ATerm ("$true", _))])) = true
  | is_bottom _ = false

fun is_top (AAtom (ATerm ("$true", _))) = true
  | is_top (AConn (ANot, [AAtom (ATerm ("$false", _))])) = true
  | is_top _ = false

fun string_for_formula formula = 
    ATP_Problem.string_for_untyped_formula FOF formula

fun should_skip (AAtom (ATerm ("$true", _))) = true
  | should_skip (AConn (ANot, [AAtom (ATerm ("$false", _))])) = true
  | should_skip _ = false

val possibly_proof_from_file = 
    SOME (fn loc => ATP_Proof.atp_proof_from_tstp_file "" loc)

end


structure TSTPProofGraph = MakeProofGraph(TSTPFormula)
