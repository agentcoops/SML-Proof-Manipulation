(*  Title:      Pure/Concurrent/lazy_sequential.ML
    Author:     Florian Haftmann and Makarius, TU Muenchen

Lazy evaluation with memoing of results and regular exceptions
(sequential version).
*)

structure Lazy: LAZY =
struct

(* datatype *)

datatype 'a expr =
  Expr of unit -> 'a |
  Result of 'a Exn.result;

abstype 'a lazy = Lazy of 'a expr Unsynchronized.ref
with

fun peek (Lazy r) =
  (case ! r of
    Expr _ => NONE
  | Result res => SOME res);

fun lazy e = Lazy (Unsynchronized.ref (Expr e));
fun value a = Lazy (Unsynchronized.ref (Result (Exn.Result a)));


(* force result *)

fun force_result (Lazy r) =
  let
    val result =
      (case ! r of
        Expr e => Exn.capture e ()
      | Result res => res);
    val _ = if Exn.is_interrupt_exn result then () else r := Result result;
  in result end;

fun force r = Exn.release (force_result r);

end;
end;

type 'a lazy = 'a Lazy.lazy;

