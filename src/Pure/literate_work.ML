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
(*open Symtab;*)


(* This is just actually getting a proof... Some basic SML manipulation. *)
val test_proof = ATP_Proof.from_tstp_file true "test.tstp";
val an_element = nth test_proof 0;
val tuple_for_play = 
    case an_element of Inference (name, formula, steps) => (name, formula, steps);
val element_name = #1 tuple_for_play;


(* Table sample code... *)
val table1 = Symtab.make [("foo", "bar"), ("baz", "bin")];

(* Graph sample code... *)
val graph1: string uniform_formula T = Graph.empty;

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
    List.foldl add_proof_step_to_graph Graph.empty proof;

fun graph_from_tstp_file file =
    ATP_Proof.from_tstp_file true file |> proof_to_graph

(* 

Naive proof graph in hand, we need to define the necessary operations
there upon to convert proof by negation to direct proof.

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

Needed:
*)

(* a way to determine if any given clause is negated and to remove
negation. *) 

fun formula_from_inference (Inference(_, formula, _)) = formula

fun formula_is_negated (AConn(ANot, _)) = true
  | formula_is_negated _ = false

fun inference_is_negated inference = 
    formula_is_negated (formula_from_inference inference)

fun node_is_negated graph node = 
    inference_is_negated (Graph.get_node graph node)

fun unnegated_formula (AConn(ANot, rest)) = hd rest
  | unnegated_formula otherwise = otherwise

fun unnegated_inference (Inference(id, formula, rest)) = 
    Inference(id, unnegated_formula formula, rest)
            

(* a sequent structure: identifier,  *)
type a' sequent = Sequent of string * bool * 'a list * 'a list;

(*Wait! can't we just use a node in the graph? 
This seems right. Keep track of finished/todo nodes elsewhere, then traverse 
graph from the bottom, updating accordingly. *)

(* Also, I think we want to complicate the type of a node... *)

datatype proof_role = Axiom | Conjecture | NegatedConjecture | Plain;

type proof_node = {
     formula: string uniform_formula,
     role: proof_role
}

(* Graph needs to indicate beginning and end of proof for ease of manipulation. *)
datatype proof_graph = ProofGraph of string * string * proof_node T

(* So, now we have a form of the proof which contains this necessary
pre-processing step.  the information exists in two ways: 1) analyzing
the structure of the proof, 2) in the tstp format.  seems like we
might not always be able to assume that we have the fact that x is
negated conjecture so a mapping between a "raw" proof structure and
one with metadata seems useful. *)

fun preprocessed_proof proof = 


(* a way to turn sequents around using contraposition: negs to other
side. *)

(*

One thing to note in the TSTP: we get the metadata that this is a
conjecture or a negated_conjecture.  This is lost, though, in the tstp
parser. It could be easy to infer this, but this might be a necessary
modification to the parser itself (a better, more information
preserving internal representation). 

Ask Jasmin?

Across proofs, the "role" function seems to be:
axiom, plain, conjecture, negated_conjecture

Are there more options here?

Also, remember: disjunction -> or, must factor out the common
sub-componants!
*)

(* Ok, one attempt at locating the subgraph that is negated_conjecture. *)

fun conjectures graph = 
    let fun is_conjecture (_, (_, (preds, _))) = 
            if preds = [] then true else false
    in
        Graph.filter_nodes is_conjecture graph
    end;

fun negated_conjectures graph =
    

fun node_contraposition graph node = 
    let new_formula = unnegated_formula node
        negated_formula
    in
        
    end
    

(* Now we can make a first pass at the algorithm... *)
fun negation_to_direct proof =
    let val unnegated_nodes = []
        fun negation_to_direct' proved target =
    in
        negation_to_direct' [] unnegated_nodes
    end;
