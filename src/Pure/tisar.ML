(* Library for manipulating and generating tisar, an isar-like proof
   representation, proofs. *)

signature TISAR = sig
    datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof * 'a tisar_proof
       | Have of 'a list
       | Assume of 'a
       | Hence of 'a
       | QED

    val proof_graph_to_tisar: proof_graph -> string tisar_proof
    val tisar_to_string: string tisar_proof -> string
    val proof_graph_to_tisar_string: proof_graph -> string

end

structure Tisar: TISAR = struct

datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof * 'a tisar_proof
       | Have of 'a list
       | Assume of 'a
       | Hence of 'a
       | QED
       | Start

(* Need to be able to do fast lookups on dependencies... *)
structure Set = Linear_Set(type key = string val ord = fast_string_ord);

fun proof_graph_to_tisar_origin (ProofGraph proof) = 
    let val (proof_start, to_ignore) = get_proof_start (ProofGraph proof)

        fun get_node_string node_id = 
            let val (ProofNode node) = Graph.get_node proof node_id
            in case #kind node of
                   NegatedConjecture => "~" ^ node_id
                 | _ => node_id
            end

        fun handle_id node_id = Graph.imm_succs proof node_id |> handle_nodes
                       
        and handle_node node_id = 
            let val (ProofNode node) = Graph.get_node proof node_id
                val pred_count = 
                    Graph.imm_preds proof node_id 
                                    |> List.filter (fn x => not (contains to_ignore x))
                                    |> length
                val node_string = get_node_string node_id
            in
                if (pred_count = 0) then (Have [node_string]) 
                else (Hence node_string)
            end
         
        and handle_branching (node :: []) = 
            Block (Assume (get_node_string node), handle_id node)
          | handle_branching (node :: nodes) = 
            Branch (handle_branching [node], handle_branching nodes)
            
        and handle_nodes [] = QED
          | handle_nodes (node :: []) = Block (handle_node node, handle_id node)
          | handle_nodes nodes = handle_branching nodes
    in
        handle_nodes proof_start
    end


(* CPS-style implementation of tisar.
   Previous implementation was woefully inadequate -- an obvious failure... *)
fun proof_graph_to_tisar (ProofGraph proof) = 
    let val (proof_start, to_ignore) = get_proof_start (ProofGraph proof)

        fun handle_node node_id proved = 
            let val children = Graph.imm_succs proof node_id
                fun is_provable child =
                    let val predecessors = Graph.imm_preds proof child
                        fun is_not_proven predecessor = 
                            not (Set.defined proved predecessor)
                    in 
                        not List.exists is_not_proven predecessors
                    end
                val provable_children = List.filter is_provable children

            in
                (, provable_children)
            end



        fun proof_graph_to_tisar' proved [] [] tisar_accum_cps = tisar_accum_cps ()

          | proof_graph_to_tisar' proved [] handle_next tisar_accum_cps =
            proof_graph_to_tisar' proved handle_next [] tisar_accum_cps

          | proof_graph_to_tisar' proved (node_id::node_ids) handle_next tisar_accum = 
            let val (tisar_node, provable_children) = handle_node node_id proved
            in
                proof_graph_to_tisar' 
                    (Set.insert_after NONE (node_id, "") proved)
                    node_ids 
                    (provable_children @ handle_next)
                    (fn x => Block (tisar_node, x))
            end
    in
        proof_graph_to_tisar' Set.empty proof_start (fn x => x)
    end


fun tisar_to_string value =
    let fun make_indentation 0 = ""
          | make_indentation x = make_indentation (x-1) ^ " "
                                 
        fun tisar_to_string' indent value = 
            let val indentation = make_indentation indent
            in case value of
                   QED => ""
                 | Assume x => "Assume " ^ x 
                 | Hence x => "\n" ^ indentation ^ " Hence " ^ x 
                 | Have lst => 
                   indentation ^ "Have " ^ (list_to_string lst " or ")
                 | Block (first, rest) =>
                   tisar_to_string' indent first ^ tisar_to_string' indent rest
                 | Branch (left, right) =>
                   indentation ^ "\n{ " ^ tisar_to_string' (indent + 1) left 
                   ^ " }\nmoreover\n" ^ indentation ^ "{ " 
                   ^ tisar_to_string' (indent + 1) right ^ " }\n"
            end
    in
        tisar_to_string' 0 value
    end

fun proof_graph_to_tisar_string proof_graph = 
    proof_graph_to_tisar proof_graph |> tisar_to_string 

end
