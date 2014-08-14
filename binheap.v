(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/15 0:59:18> *)
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
  Adlibssr.btree
  Adlibssr.order.


(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(**
 ** Binary Search Tree 
 *)

Section Heap.
  
  Variables (T: eqType)(ord: totalOrder T).

  Fixpoint bt_ord a t: bool :=
    if t is tl -< x >- tr
    then (ord a x) && (bt_ord x tl) && (bt_ord x tr)
    else true.

  (* heap property *)
  Definition bt_ordered t: bool :=
    if t is tl -< x >- tr
    then (bt_ord x tl) && (bt_ord x tr)
    else true.

  Lemma bt_ord_min a t:
    bt_ord a t -> all (ord a) t.
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
    by rewrite -!andbA => /and3P [Hord /IHl Hbl /IHr Hbr]; apply /and3P; split; try done;
      apply/allP=> y Hin; apply ord_transitive with x => //;
       [move: Hbl | move: Hbr]; move=>/allP; apply.
  Qed.

(* TODO: shape property *)
(* W.I.P. *)

End Heap.