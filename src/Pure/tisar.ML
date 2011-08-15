(* Library for manipulating and generating tisar, an isar-like proof
   representation, proofs. *)

signature TISAR = sig
    
    datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof list * ('a list * 'a list)
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
open Help

datatype 'a tisar_proof =
         Block of 'a tisar_proof * 'a tisar_proof
       | Branch of 'a tisar_proof list * ('a list * 'a list)
       | Have of 'a list * 'a list
       | Assume of 'a
       | Hence of 'a
       | End

(* CPS-style implementation of tisar. *)
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
                    let val preds = Graph.imm_preds proof child 
                        (*val _ = writeln ("is " ^ child ^ " provable?")
                        val _ = PolyML.makestring proved |> writeln
                        val _ = PolyML.makestring preds |> writeln*)
                    in
                        List.all (Set.defined proved) preds
                    end
            in
                List.partition is_provable nodes
            end

        fun get_provable_children node_id proved =
            Graph.imm_succs proof node_id
              |> provable_subset proved

        val get_preds = Graph.imm_preds proof
        val get_succs = Graph.imm_succs proof

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
                    let val preds = List.hd unproved |> get_preds
                        val provable = 
                            List.filter (Set.defined proved) preds
                    in
                        Block (Have (unproved, provable), End)
                    end
                    
                fun make_branch root_id = 
                    let val proved'' = set_add proved' root_id
                        val (provable, unprovable) = get_provable_children root_id proved''
                        (*val _ = writeln ("For branch from " ^ root_id)
                        val _ = PolyML.makestring unprovable |> writeln
                        val _ = List.map (fn x => get_preds x) unprovable 
                                         |> PolyML.makestring |> writeln
                        val _ = PolyML.makestring proved'' |> writeln
                        val _ = PolyML.makestring provable |> writeln *)
                        val _ = writeln ("For branch from " ^ root_id)
                        val (branch, proved''', unproved) = 
                            proof_graph_to_tisar'
                                proved''
                                unprovable
                                provable
                                []
                                []
                                (fn x => Block (Assume root_id, x))
                    in
                        (common_conclusion unproved proved''' |> branch,
                         proved'',
                         unproved)
                    end
                        
                fun make_branches (branch_id, (branches, proved, _)) = 
                    let val (branch, branch_proved, unproved) = make_branch branch_id
                    in
                        (branch :: branches, 
                         Set.merge (op =) (branch_proved, proved),
                         unproved)
                    end
                    
                val (branch_nodes, proved'', conclusion) = 
                    List.foldl make_branches ([], Set.empty, []) branches
            in
                (fn x => 
                    Block (Have ([get_node_string node_id], get_preds node_id), 
                           Block (Branch (branch_nodes,
                                          (conclusion, [node_id])), 
                                  x)),
                 set_add proved'' (List.hd conclusion),
                 conclusion)
            end
            
        (* args are: proved unproved working_set todo_next branches accum_continuation *)
        and proof_graph_to_tisar' 
                proved unproved [] [] [] tisar_accum_cps = 
            let val _ = PolyML.makestring unproved |> writeln
                val _ = List.map (fn x => get_preds x) unproved 
                                 |> PolyML.makestring |> writeln
                val _ = PolyML.makestring proved |> writeln
            in
                (tisar_accum_cps, 
                 proved, 
                 List.filter (fn x => not (Set.defined proved x)) unproved)
            end
          | proof_graph_to_tisar' proved unproved [] [] (branch :: branches) tisar_accum_cps =
            let val (node, proved', conclusion) = handle_branch branch proved
                val remaining = 
                    List.filter 
                        (fn x => 
                             List.all (Set.defined proved') 
                                      (Graph.imm_preds proof x))
                        (List.map get_succs conclusion |> List.concat)
            in
                proof_graph_to_tisar' 
                    proved'
                    (unproved)
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
                             (set_add proved node_id)
                     val (handle_next', tisar_accum_cps') = 
                         if (Set.defined proved node_id) then
                             (handle_next, tisar_accum_cps)
                         else (provable_children @ handle_next, 
                               (fn x => Block (tisar_node, x) |> tisar_accum_cps))
                 in
                     proof_graph_to_tisar' 
                         (set_add proved node_id)
                         (more_unproved @ unproved)
                         node_ids
                         handle_next'
                         branches
                         tisar_accum_cps'
                 end
                 
        val (tisar_accum, _, _) = 
            proof_graph_to_tisar' (set_add_list Set.empty to_ignore) [] proof_start [] [] (fn x => x)
    in
        tisar_accum End
    end


fun tisar_to_string value =
    let fun make_indentation 0 = ""
          | make_indentation x = make_indentation (x-1) ^ " "
                                 
        fun tisar_to_string' indent value = 
            let val indentation = make_indentation indent
                fun branch_string branch =
                    "\n{ " ^ tisar_to_string' (indent + 1) branch ^ " }\n"
                fun moreover lst = list_to_string lst "moreover"

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
                 | Branch (branches, (conclude, by)) =>
                   indentation ^ (List.map branch_string branches |> moreover)
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
