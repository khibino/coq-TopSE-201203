Require Import Streams.

Print Stream.

CoFixpoint from n := Cons n (from (n+1)).

Require Import List.

Print list.

Fixpoint take {A:Type} n (xs : Stream A) :=
  match (n, xs) with
    | (0, _) => nil
    | (S n', Cons x xs) => x :: take n' xs
  end.

Eval compute in take 10 (from 0).
Eval compute in from 0.

(*
Inductive が引数のときには Fixpoint
CoInductive が返り値のときには CoFixpoint
 *)

(* Inductive MyStream (A : Type) : Type := *)
(*   SCons : A -> MyStream A -> MyStream A. *)
