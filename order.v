(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/22 1:34:0> *)
(*
  order.v 
  - mathink : Author
 *)

(* SSReflect libraries *)
Require Import
  Ssreflect.ssreflect
  Ssreflect.ssrbool
  Ssreflect.ssrfun
  Ssreflect.eqtype.

(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Structure totalOrder (T: Type) :=
  { total_ord:> rel T;

    ord_antisymmetric: antisymmetric total_ord;
    ord_transitive: transitive total_ord;
    ord_total: total total_ord }.
Notation makeTotalOrder ord := (@Build_totalOrder _ ord _ _ _).
Lemma ord_reflexive T (ord: totalOrder T): reflexive ord.
Proof.
  move=> x.
  move: (ord_total ord x x) => /orP [] //.
Qed.

Hint Resolve ord_antisymmetric ord_transitive ord_total ord_reflexive.


Definition strict_ord  {T: eqType}(ord: totalOrder T): rel T :=
  fun x y => (ord x y) && (x != y).

Notation "ord !" := (strict_ord ord) (at level 5, left associativity).

Section Strict.

  Context {T: eqType}(ord: totalOrder T).

  Lemma sord_transitive: transitive ord!.
  Proof.
    move=> y x z /andP [Hlexy Hneqxy] /andP [Hleyz Hneqyz].
    apply/andP; split.
    - by apply ord_transitive with y.
    - apply/eqP=> Heqxz; move: Hneqxy => /eqP; apply.
        by rewrite -Heqxz in Hleyz;
        apply: ord_antisymmetric => //; apply/andP; split.
  Qed.
  Hint Resolve sord_transitive.


  Lemma sord_irrefl x:
    ~~ (ord! x x).
  Proof.
      by rewrite negb_and ord_reflexive eq_refl //=.
  Qed.

  Lemma ord_neg_sord x y:
    ~~ (ord x y) = (ord! y x).
  Proof.
    move: (ord_total ord x y) => /orP [] Hle; apply/eqP.
    - rewrite Hle /=.
      case Hle':  (ord y x); rewrite /strict_ord Hle' //=.
      have: x = y; first by apply: ord_antisymmetric=>//; apply/andP.
        by move=> ->; rewrite eq_refl.
    - rewrite /strict_ord Hle /=.
      case Hle':  (ord x y) => //=.
      + have: x = y; first by apply: ord_antisymmetric=>//; apply/andP.
          by move=> ->; rewrite eq_refl.
      + case: (x =P y) => [Heq | Hneq].
        * by rewrite Heq eq_refl /= -Hle' Heq ord_reflexive.
        * by rewrite [y==x]eq_sym; move: Hneq => /eqP ->.
  Qed.

  Lemma sord_neg_ord x y:
    ~~ (ord! x y) = (ord y x).
  Proof.
      by apply/eqP; rewrite eqb_negLR ord_neg_sord.
  Qed.

End Strict.
