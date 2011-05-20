(* 

This is just me learning how to use all of these structures...
If anything here is horribly wrong -- that is, if I'm butchering any of these elegent but
undocumented data structures -- please let me know!

For a while, until I get my bearings, this is just going to be a semi-literate programming
experiment that could result in code that goes in to the final library.

AUTHOR: coopf
*)

open ATP_Proof;
open ATP_Problem;
open Graph;
open Symtab;


(* This is just actually getting a proof... Some basic SML manipulation. *)
val test_proof = ATP_Proof.from_tstp_file true "test.tstp";
val an_element = nth test_proof 0;
val tuple_for_play = 
    case an_element of Inference (name, formula, steps) => (name, formula, steps);
val element_name = #1 tuple_for_play;


(* Table sample code... *)
val table1 = make [("foo", "bar"), ("baz", "bin")];

(* Graph sample code... *)
val graph1: string uniform_formula T = empty;

(* 
datatype 'a T = Graph of ('a * (key list * key list)) Table.table;
So, a key maps to (content, (preds, succes))
*)

(* Do we need to preserve the string names or just keep the numerical identifiers? *)
fun add_proof_step_to_graph (Inference (name, formula, justifications), graph) =
    let val graph_with_node = new_node (#1 name, formula) graph
        fun add_justification_edge (x, graph) = add_edge (#1 x, #1 name) graph
    in
        List.foldl add_justification_edge graph_with_node justifications
    end;

val graph_with_step = add_proof_step_to_graph (an_element, graph1);

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
    List.foldl add_proof_step_to_graph empty proof;

