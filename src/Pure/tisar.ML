(* Title: Pure/tisar.ML
   Author: Charles Francis

Library for manipulating and generating tisar, an isar-like proof
representation, proofs. 
*)

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

exception option_deal

(* CPS-style implementation of tisar.

I'm presently in the process of cleaning this 
code as, unfortunately, it's a bit messy... *)
fun proof_graph_to_tisar (ProofGraph proof) = 
    let val (proof_start, to_ignore) = get_proof_start (ProofGraph proof)
                          
        fun get_preds proof = Graph.imm_preds proof
        fun get_succs proof = Graph.imm_succs proof
            
        fun is_provable proof proved node = 
            get_preds proof node
              |> List.all (set_defined proved)

        fun provable_subset proof proved nodes =
            List.partition (is_provable proof proved) nodes

        fun get_provable_children proof node_id proved =
            get_succs proof node_id
              |> provable_subset proof proved

        (* args are: proof proved unproved working_set 
           todo_next branches accum_continuation *)

        (* the case where there the working_set, branches and todo_next 
           are empty... return results along with the proved and unproved. *)
        and proof_graph_to_tisar' proof proved unproved [] [] [] tisar_accum_cps = 
            (tisar_accum_cps, 
             proved, 
             List.filter (fn x => not (set_defined proved x)) unproved)
           
         (* working_set and todo_next are empty, but there's a branch to handle *)
          | proof_graph_to_tisar' 
                proof proved 
                unproved [] [] 
                (branch :: branches) 
                tisar_accum_cps =
            let fun handle_branch node_id proved =
                    let val _ = writeln ("Disjunction is: " ^ node_id)
                        val proved' = set_add proved node_id
                        val branches = get_succs proof node_id
                                       
                        (* assuming proofs are valid coming in, the first 
                           "unproved" result on a branch is the  earliest
                           common result. *)
                        fun common_conclusion unproved proved = 
                            let val id = disjunct_id unproved
                                val (ProofNode node) = Graph.get_node proof id
                                val (SOME provable) = 
                                    case #justification_splits node of
                                        [] => 
                                        SOME (get_preds proof id
                                          |> List.filter (set_defined proved))
                                      | lst => 
                                        List.find 
                                            (fn just => 
                                                List.all (set_defined proved) just)
                                            lst
                            in
                                Block (Have (unproved, sort_unique provable), End)
                            end
                            
                        fun make_branch root_id = 
                            (writeln ("on branch " ^ root_id);
                             get_preds proof root_id |> PolyML.makestring |> writeln;
                             PolyML.makestring proved' |> writeln;
                            if is_provable proof proved' root_id then
                                let val _ = writeln "provable"
                                    val proved'' = set_add proved' root_id
                                    val (provable, unprovable) = 
                                        get_provable_children proof root_id proved''
                                    val (branch, proved''', unproved) = 
                                        proof_graph_to_tisar'
                                            proof
                                            proved''
                                            unprovable
                                            provable
                                            []
                                            []
                                            (fn x => Block (Assume root_id, x))
                                    val _ = PolyML.makestring unproved |> writeln
                                in
                                    (common_conclusion unproved proved''' |> branch |> SOME,
                                     proved'',
                                     unproved)
                                end
                            else (NONE, proved', [root_id]))
                                 
                        fun make_branches (branch_id, (branches, proved, unproved)) = 
                            let val (branch, branch_proved, unproved') = make_branch branch_id
                            in
                                (branch :: branches, 
                                 set_union branch_proved proved,
                                 unproved' @ unproved)
                            end
                            
                        val (possible_branch_nodes, proved'', conclusion) = 
                            List.foldl make_branches ([], [], []) branches
                        val branch_nodes = List.mapPartial I possible_branch_nodes
                        val conclusion_node = merge_disjuncts conclusion
                        val proof' = 
                            insert_disjunct_after 
                                proof 
                                conclusion 
                                (List.map (fn x => get_succs proof x) conclusion |> List.concat)
                    in
                        case branch_nodes of
                            [] => (NONE, proved, node_id, proof)
                          | nodes =>
                            (SOME (fn x => 
                                      (Block (Branch (nodes,
                                                      ([conclusion_node], [node_id])),
                                              x))
                                          |> (if set_defined proved node_id then I 
                                              else (fn x => 
                                                       Block (Have ([get_node_string proof node_id], 
                                                                    get_preds proof node_id), 
                                                              x)))),
                             set_add proved'' conclusion_node,
                             conclusion_node, 
                             proof')
                    end

                val (node, proved', conclusion, proof') = handle_branch branch proved
                val (remaining, new_branches) = 
                    if is_branch proof' conclusion then 
                        ([], conclusion :: branches)
                    else
                        (List.filter 
                             (fn x => 
                                 List.all (set_defined proved') 
                                          (Graph.imm_preds proof' x))
                             (get_succs proof' conclusion),
                         branches)
            in
                case node of
                    SOME branch_tisar =>
                    proof_graph_to_tisar' 
                        proof'
                        proved'
                        unproved
                        remaining
                        []
                        new_branches
                        (fn x => branch_tisar x |> tisar_accum_cps)
                  | NONE =>
                    proof_graph_to_tisar'
                        proof'
                        proved'
                        (branch :: unproved)
                        remaining
                        []
                        branches
                        tisar_accum_cps
            end

          | proof_graph_to_tisar' proof proved unproved [] handle_next branches tisar_accum_cps =
            proof_graph_to_tisar' proof proved unproved handle_next [] branches tisar_accum_cps
            
          | proof_graph_to_tisar' 
                proof proved unproved (node_id :: node_ids) handle_next branches tisar_accum_cps =
            let fun handle_node node_id proved = 
                    let val node_string = get_node_string proof node_id
                        val preds = get_preds proof node_id
                        val node = 
                            if (List.length preds) = 0 
                            then Have ([node_string], [])
                            else Have ([node_string], preds) (*Hence node_string no hence yet!*)
                        val (provable, unprovable) = get_provable_children proof node_id proved
                    in
                        (node, provable, unprovable)
                    end
            in                    
                if is_branch proof node_id then
                    proof_graph_to_tisar' 
                        proof
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
                             if (set_defined proved node_id) then
                                 (handle_next, tisar_accum_cps)
                             else (provable_children @ handle_next, 
                                   (fn x => Block (tisar_node, x) |> tisar_accum_cps))
                     in
                         proof_graph_to_tisar' 
                             proof
                             (set_add proved node_id)
                             (more_unproved @ unproved)
                             node_ids
                             handle_next'
                             branches
                             tisar_accum_cps'
                     end
            end
                     
        val (tisar_accum, _, _) = 
            proof_graph_to_tisar' 
                proof
                (set_add_list [] to_ignore) 
                [] 
                proof_start 
                [] 
                [] 
                (fn x => x)
    in
        tisar_accum End
    end


fun tisar_to_string value =
    let fun make_indentation 0 = ""
          | make_indentation x = make_indentation (x-1) ^ " "
                                 
        fun tisar_to_string' indent value = 
            let val indentation = make_indentation indent
                fun branch_string branch =
                    "{ " ^ tisar_to_string' (indent + 1) branch ^ " }\n"
                fun moreover lst = list_to_string lst "moreover\n"

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
                   ^ (list_to_string by " and ")
            end
    in
        tisar_to_string' 0 value
    end

fun proof_graph_to_tisar_string proof_graph = 
    proof_graph_to_tisar proof_graph |> tisar_to_string 

end

structure TSTPTisar = MakeTisar(TSTPProofGraph);
