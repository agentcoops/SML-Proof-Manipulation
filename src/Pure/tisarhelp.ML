(* This is my standard library. Just contains various helper functions. 

TODO: switch to ord_list and I don't need all the set methods,
tabulate replaces constant list... *)
structure Help = struct

fun sort_unique lst = Ord_List.make fast_string_ord lst

fun set_defined set value = 
    Ord_List.member fast_string_ord set value (* comment on this api... a bit wonk *)

fun set_add set value = 
    Ord_List.insert fast_string_ord value set

fun set_union set1 set2 = 
    Ord_List.union fast_string_ord set1 set2

fun set_add_list set lst = 
    set_union set (sort_unique lst)

(* fun set_add set value = 
    (Set.insert_after NONE (value, "") set) 
    handle DUPLICATE => set

fun set_add_list set values = 
    List.foldl (fn (value, accum) => set_add accum value) set values
*)

fun constant_list_of_same_size value lst = 
    List.tabulate (length lst, fn _ => value)
    
fun contains list element = List.exists (fn x => x = element) list

fun max ord list = 
    List.foldl (fn (value, max) => if (ord value max) then value else max) (List.hd list) list

fun string_max (lst: string list) = 
    List.foldl (fn (value, max) => if (value > max) then value else max) (List.hd lst) lst

fun list_to_string lst delimiter =
    let fun folder (value, accum) = 
            if not (accum = "") then (accum ^ delimiter ^ value)
            else value
    in 
        List.foldl folder "" lst 
    end

(* This isn't fully generic (ie the included strip behavior isn't
   sufficient for all cases (in particular where there is whitespace
   within one of the splits) but it works in my case here! *)
fun string_split delimiter str = 
    String.tokens 
        (fn x => 
            (SOME x) = (Char.fromString delimiter) 
            orelse (SOME x) = (Char.fromString " ")) 
        str

fun disjunct_id ids = list_to_string (sort_unique ids) " | "

(* disjuncts really need to be first class! this is terrible
desperation to fix this bug today! after gsoc's termination this will
be cleaned up! *)
fun merge_disjuncts disjuncts = 
    List.map (string_split "|") disjuncts
     |> List.concat
     |> disjunct_id

fun partition_graph f graph =
    let val keys = Graph.keys graph
    in 
        List.partition f keys
    end
        
(* fun reverse_edges_node node G = 
    let val succs = imm_succs G node
        val preds = imm_preds G node
        fun constant_list_of_same_size value lst = 
            List.tabulate (length lst, fn x => value) 
    in
        G |> reverse_edges (ListPair.zip (constant_list_of_same_size node succs, succs))
          |> reverse_edges (ListPair.zip (preds, constant_list_of_same_size node preds))
    end; *)

fun swap_edges2 graph _ [] = graph
  | swap_edges2 graph node_id ((node1, node2) :: nodes) =
    let val new_graph = 
            if node1 = node2 then
                graph
            else
                Graph.del_edge (node1, node2) graph 
                  |> Graph.add_edge (node_id, node2)
    in
        swap_edges2 new_graph node_id nodes
    end


(* this inserts a new node into a graph after an existent node, making all of 
the original node's decendants now children of the new node. *)
fun insert_node graph (id, value) prev_id =
    let val graph_with_node = 
            ((Graph.new_node (id, value) graph) handle DUPLICATE => graph)
                |> Graph.add_edge (prev_id, id)
        val succs = Graph.imm_succs graph prev_id
        val old_connections = 
            ListPair.zip 
                (constant_list_of_same_size prev_id succs,
                 succs)
    in
        swap_edges2 graph_with_node id old_connections
    end
    
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
