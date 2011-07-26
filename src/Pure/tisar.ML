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
end

structure Tisar: TISAR = struct

datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof * 'a tisar_proof
       | Have of 'a list
       | Assume of 'a
       | Hence of 'a
       | QED

fun proof_graph_to_tisar (ProofGraph proof) = 
    let val (proof_start, to_ignore) = get_proof_start proof

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

end
