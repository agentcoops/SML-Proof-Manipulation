(*  Title:      Pure/morphism.ML
    Author:     Makarius

Abstract morphisms on formal entities.
*)

infix 1 $>

signature BASIC_MORPHISM =
sig
  type morphism
  type declaration = morphism -> Context.generic -> Context.generic
  val $> : morphism * morphism -> morphism
end

signature MORPHISM =
sig
  include BASIC_MORPHISM
  val binding: morphism -> binding -> binding
  val typ: morphism -> typ -> typ
  val term: morphism -> term -> term
  val fact: morphism -> thm list -> thm list
  val thm: morphism -> thm -> thm
  val cterm: morphism -> cterm -> cterm
  val morphism:
   {binding: binding -> binding,
    typ: typ -> typ,
    term: term -> term,
    fact: thm list -> thm list} -> morphism
  val binding_morphism: (binding -> binding) -> morphism
  val typ_morphism: (typ -> typ) -> morphism
  val term_morphism: (term -> term) -> morphism
  val fact_morphism: (thm list -> thm list) -> morphism
  val thm_morphism: (thm -> thm) -> morphism
  val identity: morphism
  val compose: morphism -> morphism -> morphism
  val transform: morphism -> (morphism -> 'a) -> morphism -> 'a
  val form: (morphism -> 'a) -> 'a
end;

structure Morphism: MORPHISM =
struct

datatype morphism = Morphism of
 {binding: binding -> binding,
  typ: typ -> typ,
  term: term -> term,
  fact: thm list -> thm list};

type declaration = morphism -> Context.generic -> Context.generic;

fun binding (Morphism {binding, ...}) = binding;
fun typ (Morphism {typ, ...}) = typ;
fun term (Morphism {term, ...}) = term;
fun fact (Morphism {fact, ...}) = fact;
val thm = singleton o fact;
val cterm = Drule.cterm_rule o thm;

val morphism = Morphism;

fun binding_morphism binding = morphism {binding = binding, typ = I, term = I, fact = I};
fun typ_morphism typ = morphism {binding = I, typ = typ, term = I, fact = I};
fun term_morphism term = morphism {binding = I, typ = I, term = term, fact = I};
fun fact_morphism fact = morphism {binding = I, typ = I, term = I, fact = fact};
fun thm_morphism thm = morphism {binding = I, typ = I, term = I, fact = map thm};

val identity = morphism {binding = I, typ = I, term = I, fact = I};

fun compose
    (Morphism {binding = binding1, typ = typ1, term = term1, fact = fact1})
    (Morphism {binding = binding2, typ = typ2, term = term2, fact = fact2}) =
  morphism {binding = binding1 o binding2, typ = typ1 o typ2,
    term = term1 o term2, fact = fact1 o fact2};

fun phi1 $> phi2 = compose phi2 phi1;

fun transform phi f = fn psi => f (phi $> psi);
fun form f = f identity;

end;

structure Basic_Morphism: BASIC_MORPHISM = Morphism;
open Basic_Morphism;
