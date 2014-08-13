(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/13 23:3:35> *)
(*
  order.v 
  - mathink : Author
 *)

(* SSReflect libraries *)
Require Import
  Ssreflect.ssreflect
  Ssreflect.ssrbool
  Ssreflect.ssrfun
  Ssreflect.eqtype
  Ssreflect.ssrnat
  Ssreflect.seq.

(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition relation (T: Type) := T -> T -> Prop.
Section OrderClasses.

  Variables (T: Type)(ord: rel T).

  Class PreOrder :=
    { ord_reflexive: reflexive ord;
      ord_transitive: transitive ord }.

  Class PartialOrder :=
    { partial_pre: PreOrder;
      ord_antisymmetric: antisymmetric ord }.
  Coercion partial_pre: PartialOrder >-> PreOrder.

  Class TotalOrder :=
    { total_partial: PartialOrder;
      ord_total: total ord }.
  Coercion total_partial: TotalOrder >-> PartialOrder.

End OrderClasses.


Structure totalOrder (T: Type) :=
  { dec_ord: rel T;
    dec_ord_spec: TotalOrder dec_ord }.



