(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/15 20:57:12> *)
(*
  monad.v 
  - mathink : Author
 *)

(* SSReflect libraries *)
Require Import
  Ssreflect.ssreflect
  Ssreflect.ssrbool
  Ssreflect.ssrfun
  Ssreflect.eqtype
  Ssreflect.ssrnat
  Ssreflect.seq
  Ssreflect.fintype.

(* Mathematical Components libraries *)

(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Reserved Notation "m >>= f" (at level 57, left associativity).
Class eqMonad (m: eqType -> eqType) :=
  { emb {X: eqType}: X -> m X;
    bind {X Y: eqType}(f: X -> m Y): m X -> m Y
    where "m >>= f" := (bind f m);

    emb_bind {X Y: eqType}(f: X -> m Y)(x: X):
      (emb x >>= f) == f x;
    bind_emb {X: eqType} (mx: m X):
      (mx >>= emb) == mx;
    bind_assoc {X Y Z: eqType}(f: X -> m Y)(g: Y -> m Z)(mx: m X):
      mx >>= f >>= g == mx >>= (bind g \o f) }.
Notation "m >>= f" := (bind f m) (at level 57, left associativity).
Notation "x <- m ; p" := (m >>= fun x => p) (at level 65, right associativity).  

Program Instance eqMaybe: eqMonad option_eqType :=
  { emb X x := Some x;
    bind X Y f mx := if mx is Some x then f x else None }.
Next Obligation.
  case: mx => //=.
Qed.
Next Obligation.
  case: mx => //=.
Qed.

Class eqMonad_F `(monad: eqMonad m) :=
  { failure {X: eqType}: m X;
    handle {X: eqType}: m X -> m X -> m X;

    failure_end {X Y: eqType}(f: X -> m Y):
      failure >>= f == failure;
    handle_failure {X: eqType}(mx: m X):
      handle failure mx == mx }.

Program Instance eqMaybe_F: eqMonad_F eqMaybe :=
  { failure X := None (A:=X);
    handle X mx1 mx2 := if mx1 is None then mx2 else mx1 }.


