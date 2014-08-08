(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/9 0:15:24> *)
(*
  binheap.v 
  - mathink : Author
 *)

(**
 ** Binary Heap Structure
 *)

(* SSReflect libraries *)
Require Import
  Ssreflect.ssreflect
  Ssreflect.ssrbool
  Ssreflect.ssrfun
  Ssreflect.eqtype
  Ssreflect.ssrnat
  Ssreflect.seq.

Require Import
        MathComp.path.

Require Import
  Adlibssr.btree.


(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(**
 ** Binary Search Tree 
 *)

Section Heap.
  
  Variables (T: eqType)(ordb: rel T).
  Hypothesis
    (ordb_antisym: antisymmetric ordb)
    (ordb_transitive: transitive ordb).

  Local Close Scope nat_scope.
  Delimit Scope ord with ord_scope.
  Local Open Scope ord_scope.
  Local Notation "[<=]" := ordb.
  Local Notation "[ '<=' y ]" := (ordb^~ y).
  Local Notation "[ '=>' x ]" := (ordb x).
  Local Notation "x <= y" := (ordb x y) (at level 70, no associativity).
  
  Definition strict_ordb x y := ((x <= y) && (x != y)).
  Local Notation "[<]" := strict_ordb.
  Local Notation "[ '<' y ]" := (strict_ordb^~ y).
  Local Notation "[ '>' x ]" := (strict_ordb x).
  Local Notation "x < y" := (strict_ordb x y) (at level 70, no associativity).


  Fixpoint bt_ordb a t: bool :=
    if t is tl -< x >- tr
    then (a <= x) && (bt_ordb x tl) && (bt_ordb x tr)
    else true.

  (* heap property *)
  Definition bt_oredered t: bool :=
    if t is tl -< x >- tr
    then (bt_ordb x tl) && (bt_ordb x tr)
    else true.

  Lemma bt_ordb_min a t:
    bt_ordb a t -> all [=> a] t.
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
    by rewrite -!andbA => /and3P [Hord /IHl Hbl /IHr Hbr]; apply /and3P; split; try done;
      apply/allP=> y Hin; apply ordb_transitive with x => //;
       [move: Hbl | move: Hbr]; move=>/allP; apply.
  Qed.

(* W.I.P. *)
End Heap.