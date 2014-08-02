(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/2 13:16:11> *)
(*
  binsearch.v 
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

Require Import
        MathComp.path.

Require Import
  Adlibssr.btree.


(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(**
 ** Additional Lemmas for [sorted]
 *)

Section SortedLemma.

  Variables (T: eqType)
            (ordb: rel T).
  Hypothesis
    (ordb_transitive: transitive ordb).

  Implicit Type (s: seq T).

  Lemma sorted_consn x y s:
    (ordb x y) && sorted ordb (y :: s) = sorted ordb ([:: x , y & s]).
  Proof.
    by [].
  Qed.

  Lemma sorted_cons1 x s:
    sorted ordb (x :: s) = (seq.all (ordb x) s) && sorted ordb s.
  Proof.
    elim: s x => [//=|/= h s IHs] x.
    rewrite -andbA; apply andb_id2l => Hord.
    rewrite IHs andbC andbCA; apply andb_id2l => Hsorted.
    rewrite -seq.all_predI /=.
    apply seq.eq_all => y /=.
    rewrite -{1}[ordb h y]andbT [_ && true]andbC;
    apply andb_id2r => Hord'; apply esym.
    by move: Hord' ; apply ordb_transitive.
  Qed.

  Lemma sorted_rcons s x:
    sorted ordb (rcons s x) =  (seq.all (ordb^~x) s) && sorted ordb s.
  Proof.
    elim: s x => [//=| h s IHs] x.
    rewrite rcons_cons sorted_cons1
            /= IHs andbCA andbAC [_&& seq.all _ _]andbC.
    apply andb_id2l => Hall.
    rewrite seq.all_rcons -andbA; apply andb_id2l => Hord.
    by rewrite -sorted_cons1.
  Qed.

  Lemma sorted_cat x s1 s2:
    sorted ordb (x :: s1 ++ s2) =
    (sorted ordb (x::s1)) && (sorted ordb s2)
    && (seq.all (ordb (last x s1)) s2).
  Proof.
    move=> /=.
    rewrite cat_path -andbA; apply andb_id2l.
    elim: s1 x => [//=|/= h1 s1 IH1] x => [_ | /andP [Hord Hpath1]].
    - elim: s2 x => [//= | /= h2 s2 IH2] x.
      rewrite andbC; apply andb_id2l => Hpath2.
      rewrite -{1}[ordb x h2]andbT; apply andb_id2l => Hord.
      rewrite IH2 in Hpath2.
      move: Hpath2 => /andP [Hsorted Hall].
      rewrite -Hall; apply seq.eq_in_all.
      move=> y /= Hin2.
      have: ordb h2 y; first move: (Hall) => /seq.allP -> //=.
      move=> Hord2; rewrite Hord2; apply esym.
      apply ordb_transitive with h2 => //=.
    - apply IH1 => //=.
  Qed.

  Lemma sorted_cat_cons s1 x s2:
    sorted ordb (s1 ++ x :: s2) =
    (sorted ordb (rcons s1 x)) && (sorted ordb (x::s2)).
  Proof.
    elim: s1 s2 x => [//= | h1 s1 IH1] s2 x.
    rewrite cat_cons sorted_cons1 IH1 rcons_cons [sorted _ (h1 :: _)]sorted_cons1 seq.all_cat seq.all_rcons /= !andbA.
    apply andb_id2r => Hpath2.
    apply andb_id2r => Hsorted.
    rewrite -andbA andbC -andbA; apply andb_id2l => Hord.
    rewrite andbC -{2}[seq.all _ _]andbT; apply andb_id2l => Hall.
    apply order_path_min in Hpath2 => //=.
    apply /seq.allP => y Hin.
    move: Hpath2 => /seq.allP H; apply ordb_transitive with x => //=.
    by apply H.
  Qed.

End SortedLemma.


(**
 ** Binary Search Tree 
 *)

Section BinarySearchTree.

  Variables (T: eqType)
            (ordb: rel T).
  Hypothesis
    (ordb_transitive: transitive ordb).

  Implicit Type (t: btree T).


  Fixpoint bst t: bool :=
    if t is tl -< x >- tr
    then (bst tl) && (all (ordb ^~ x) tl) && (bst tr) && (all (ordb x) tr)
    else true.


  Lemma sorted_bst t:
    sorted ordb (flatten t) = bst t.
  Proof.
    elim: t => [//= | /= x tl IHl tr IHr].
    rewrite sorted_cat_cons // sorted_rcons // sorted_cons1 // IHl IHr
            !flatten_all -andbCA andbC.
    apply andb_id2r => Hallr.
    apply andb_id2r => Hbstr.
    apply andbC.
  Qed.



  Section Operations.

    Hypothesis
      (ordb_total: total ordb)
      (ordb_antisym: antisymmetric ordb).
    
    Fixpoint search a t: bool :=
      if t is tl -< x >- tr
      then if a == x then true
           else if ordb a x then search a tl else search a tr
      else false.

    Lemma bst_search_aux a t:
      (a \in t) && (bst t) -> search a t.
    Proof.
      elim: t => [//= |/= x tl IHl tr IHr].
      rewrite in_bnode.
      case: (a =P x) => [<- | Hneq] //=.
      rewrite -!andbA.
      move=> /andP
              [/orP [Hinl | Hinr]
                /and4P [Hbstl /allP Halll Hbstr /allP Hallr]].
      - by rewrite Halll //; apply IHl; apply/andP.
      - move: (Hallr _ Hinr) => Hord.
        have: ~~ordb a x.
        + apply/negP => Hord'; apply Hneq.
          by apply ordb_antisym; apply /andP.
        + by move=> /negbTE->; apply IHr; apply/andP.
    Qed.


    Lemma bst_search a t:
      bst t -> (a \in t) = (search a t).
    Proof.
      move=> Hbst.
      case Hin: (a \in t).
      - by apply esym; apply bst_search_aux; apply/andP.
      - move: {Hbst} Hin; elim: t => [//=|/= x tl IHl tr IHr].
        rewrite in_bnode.
        case: (a =P x) => [Heq | Hneq] //=.
        move/negbT; rewrite negb_or =>/andP [/negbTE/IHl<- /negbTE/IHr<-].
        by rewrite if_same.
    Qed.    
    
(* In Progress... *)

  End Operations.

End BinarySearchTree.

  