(* Title:   Pure/negatableformula.ML 
   Author:  Charles Francis 

*)
open ATP_Proof;
open ATP_Problem;

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
