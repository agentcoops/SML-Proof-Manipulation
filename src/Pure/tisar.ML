(* Library for manipulating and generating tisar, an isar-like proof
   representation, proofs. *)

signature TISAR = sig
    
    datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof * 'a tisar_proof * ('a list * 'a list)
       | Have of 'a list * 'a list
       | Assume of 'a
       | Hence of 'a
       | End

    type proof_graph

    val proof_graph_to_tisar: proof_graph -> string tisar_proof
    val tisar_to_string: string tisar_proof -> string
    val proof_graph_to_tisar_string: proof_graph -> string
end


functor MakeTisar(ProofGraphStruct: PROOF_GRAPH): TISAR = struct

(*structure FormulaProofGraph = MakeProofGraph(FormulaStruct)

open FormulaStruct*)
open ProofGraphStruct

datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof * 'a tisar_proof * ('a list * 'a list)
       | Have of 'a list * 'a list
       | Assume of 'a
       | Hence of 'a
       | End

(* Need to be able to do fast lookups on dependencies... *)
structure Set = Linear_Set(type key = string val ord = fast_string_ord);

(* fun proof_graph_to_tisar_origin (ProofGraph proof) = 
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
            
        and handle_nodes [] = End
          | handle_nodes (node :: []) = Block (handle_node node, handle_id node)
          | handle_nodes nodes = handle_branching nodes
    in
        handle_nodes proof_start
    end *)


(* CPS-style implementation of tisar.
   Previous implementation was woefully inadequate -- an obvious failure... *)
fun proof_graph_to_tisar (ProofGraph proof) = 
    let val (proof_start, to_ignore) = get_proof_start (ProofGraph proof)

        fun is_branch node_id = 
            let val formula = Graph.get_node proof node_id |> get_proof_node_formula
            in
                if (((is_disjunct formula) orelse (is_top formula))
                    andalso ((Graph.imm_succs proof node_id |> List.length) > 1))
                then true
                else false
            end                    
            
        fun get_node_string node_id = 
            let val (ProofNode node) = Graph.get_node proof node_id
            in case #kind node of
                   NegatedConjecture => "~" ^ node_id
                 | _ => node_id
            end

        fun provable_subset proved nodes =
            let fun is_provable child =
                    Graph.imm_preds proof child 
                      |> List.all (Set.defined proved) 
            in
                List.partition is_provable nodes
            end

        fun get_provable_children node_id proved =
            Graph.imm_succs proof node_id
              |> provable_subset proved

        val get_preds = Graph.imm_preds proof
        val get_succs = Graph.imm_succs proof

        fun set_add set value = 
            (Set.insert_after NONE (value, "") set) 
            handle DUPLICATE => set

        fun handle_node node_id proved = 
            let val node_string = get_node_string node_id
                val preds = get_preds node_id
                val node = 
                    if (List.length preds) = 0 
                    then Have ([node_string], [])
                    else Have ([node_string], preds) (*Hence node_string no hence yet!*)
                val (provable, unprovable) = get_provable_children node_id proved
            in
                (node, provable, unprovable)
            end

        fun handle_branch node_id proved =
            let val proved' = set_add proved node_id
                val branches = get_succs node_id
                               
                fun common_conclusion unproved proved = 
                    let val _ = PolyML.makestring proved |> writeln
                        val preds = List.hd unproved |> get_preds
                        val _ = PolyML.makestring preds |> writeln
                        val provable = 
                            List.filter (Set.defined proved) preds
                    in
                        Block (Have (unproved, provable), End)
                    end

                fun make_branch root_id = 
                    let val (provable, unprovable) = get_provable_children root_id proved
                        val (branch, proved'', unproved) = 
                            proof_graph_to_tisar'
                                (set_add proved' root_id)
                                unprovable
                                provable
                                []
                                []
                                (fn x => Block (Assume root_id, x))
                    in
                        (common_conclusion unproved proved'' |> branch,
                         proved'',
                         unproved)
                    end

                val (left_branch, left_proved, conclusion) = 
                    List.nth (branches, 0) |> make_branch
                val (right_branch, right_proved, _) = 
                    List.nth (branches, 1) |> make_branch
                val proved'' = Set.merge (=) (left_proved, right_proved)
            in
                (fn x => 
                    Block (Have ([get_node_string node_id], []), 
                           Block (Branch (left_branch, 
                                          right_branch, 
                                          (conclusion, [node_id])), 
                                  x)),
                 set_add proved'' (List.hd conclusion),
                 conclusion)
            end
            
        (* args are: proved unproved working_set todo_next branches accum_continuation *)
        and proof_graph_to_tisar' 
                proved unproved [] [] [] tisar_accum_cps = 
            (tisar_accum_cps, 
             proved, 
             List.filter (fn x => not (Set.defined proved x)) unproved)

          | proof_graph_to_tisar' proved unproved [] [] (branch :: branches) tisar_accum_cps =
            let val (node, proved', unprovable) = handle_branch branch proved
                val remaining = 
                    List.filter 
                        (fn x => 
                             List.all (Set.defined proved') 
                                      (Graph.imm_preds proof x))
                        unprovable
            in
                proof_graph_to_tisar' 
                    proved'
                    (unprovable @ unproved)
                    remaining
                    []
                    branches
                    (fn x => node x |> tisar_accum_cps)
            end

          | proof_graph_to_tisar' proved unproved [] handle_next branches tisar_accum_cps =
            proof_graph_to_tisar' proved unproved handle_next [] branches tisar_accum_cps
            
          | proof_graph_to_tisar' 
                proved unproved (node_id :: node_ids) 
                handle_next branches tisar_accum_cps =
            if is_branch node_id then
                proof_graph_to_tisar' 
                    proved 
                    unproved
                    node_ids 
                    handle_next 
                    (node_id :: branches) 
                    tisar_accum_cps
            else let val (tisar_node, provable_children, more_unproved) = 
                         handle_node 
                             node_id 
                             ((Set.insert_after NONE (node_id, "") proved) 
                              handle DUPLICATE => proved)
                     val (handle_next', tisar_accum_cps') = 
                         if (Set.defined proved node_id) then
                             (handle_next, tisar_accum_cps)
                         else (provable_children @ handle_next, 
                               (fn x => Block (tisar_node, x) |> tisar_accum_cps))
                 in
                     proof_graph_to_tisar' 
                         ((Set.insert_after NONE (node_id, "") proved) handle DUPLICATE => proved)
                         (more_unproved @ unproved)
                         node_ids
                         handle_next'
                         branches
                         tisar_accum_cps'
                 end
                 
        val (tisar_accum, _, _) = 
            proof_graph_to_tisar' Set.empty [] proof_start [] [] (fn x => x)
    in
        tisar_accum End
    end


fun tisar_to_string value =
    let fun make_indentation 0 = ""
          | make_indentation x = make_indentation (x-1) ^ " "
                                 
        fun tisar_to_string' indent value = 
            let val indentation = make_indentation indent
            in case value of
                   End => ""
                 | Assume x => "Assume " ^ x 
                 | Hence x => "\n" ^ indentation ^ " Hence " ^ x 
                 | Have (things, []) => ""
                 | Have (things, deps) => 
                   indentation ^ "Have " ^ (list_to_string things " or ") ^ 
                   " by " ^ (list_to_string deps " and ")
                 | Block (first, rest) =>
                   tisar_to_string' indent first ^ "\n" ^ tisar_to_string' indent rest
                 | Branch (left, right, (conclude, by)) =>
                   indentation ^ "\n{ " ^ tisar_to_string' (indent + 1) left 
                   ^ " } moreover {\n " ^ indentation 
                   ^ tisar_to_string' (indent + 1) right ^ " }\n"
                   ^ "ultimately have " ^ (list_to_string conclude " or ") ^ " by " 
                   ^ (list_to_string by " and ") ^ "\n"
            end
    in
        tisar_to_string' 0 value
    end

fun proof_graph_to_tisar_string proof_graph = 
    proof_graph_to_tisar proof_graph |> tisar_to_string 

end

structure TSTPTisar = MakeTisar(TSTPProofGraph);
