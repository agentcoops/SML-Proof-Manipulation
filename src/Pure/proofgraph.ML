(* OK. Now it's time to make this a real library... *)

signature NegatableFormula = sig
    type Formula
    val negated_formula: Formula -> Formula
end

signature ProofGraph = sig
    type Formula
    val negated_formula: Formula -> Formula
                        
    val 
end

functor MakeProofGraph(formula: NegatableFormula): ProofGraph = 
struct

type Formula = formula.Formula
val negated_formula = formula.negated_formula


    
end
