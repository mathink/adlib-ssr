(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/20 0:46:10> *)
(*
  binsearch.v 
  - mathink : Author
 *)

(* SSReflect libraries *)
Require Import
  Ssreflect.ssreflect
  Ssreflect.ssrbool
  Ssreflect.ssrfun
  Ssreflect.ssrnat
  Ssreflect.eqtype
  Ssreflect.seq.

Require Import
        MathComp.path.

Require Import
  Adlibssr.btree
  Adlibssr.sorted.


(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(**
 ** Binary Search Tree 
 *)

Require Import Adlibssr.order.

(* Aux *)
Definition flip {X Y Z: Type}(f: X -> Y -> Z): Y -> X -> Z :=
  fun y x => f x y.
Arguments flip X Y Z f / y x.

Section BinarySearchTree.

  Variables (T: eqType)
            (le: T -> T -> Prop)
            (ord: totalOrder T).
  Notation "x <= y" := (le x y).
  Hypothesis (ordP: forall x y, reflect (x <= y) (ord x y)).
  
  Implicit Types (t: btree T)(s: seq T).

  (* Inductive isBst: btree T -> Prop := *)
  (* | isBst_bleaf: isBst # *)
  (* | isBst_bnode_one: *)
  (*     forall x, isBst (#-< x >-#) *)
  (* | isBst_bnode_l: *)
  (*     forall x xl tl tr, *)
  (*       xl <= x -> *)
  (*       isBst (tl -< xl >- tr) ->  *)
  (*       isBst ((tl -< xl >- tr)-< x >-#) *)
  (* | isBst_bnode_r: *)
  (*     forall x xr tl tr, *)
  (*       x <= xr -> *)
  (*       isBst (tl -< xr >- tr) ->  *)
  (*       isBst (#-< x >-(tl -< xr >- tr)) *)
  (* | isBst_bnode_bnode: *)
  (*     forall x xl xr tll trl tlr trr, *)
  (*       xl <= x -> x <= xr -> *)
  (*       isBst (tll -< xl >- trl) -> *)
  (*       isBst (tlr -< xr >- trr) -> *)
  (*       isBst ((tll -< xl >- trl)-< x >-(tlr -< xr >- trr)). *)
  (* Hint Constructors isBst. *)

  Fixpoint bst t: bool :=
    if t is tl -< x >- tr
    then (bst tl) && (all (flip ord x) tl) && (bst tr) && (all (ord x) tr)
    else true.

  (* Lemma isBst_bnode x tl tr: *)
  (*   (forall y, y \in tl -> ord y x) -> *)
  (*   (forall y, y \in tr -> ord x y) -> *)
  (*   isBst tl -> isBst tr -> isBst (tl -< x >- tr). *)
  (* Proof. *)
  (*   move=> Hl Hr Hbl Hbr. *)
  (*   inversion Hbl => //=. *)
  (*   -{ inversion Hbr => //=. *)
  (*      + apply isBst_bnode_r => //; apply/ordP; apply Hr. *)
  (*          by rewrite -H0 /= in_bnode /= -orbA; apply/orP; left. *)
  (*      + apply isBst_bnode_r => //; first (apply/ordP; apply Hr). *)
  (*        * by rewrite -H2 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * by apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_r => //; first (apply/ordP; apply Hr). *)
  (*        * by rewrite -H2 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * by apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_r => //; first (apply/ordP; apply Hr). *)
  (*        * by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * by apply isBst_bnode_bnode => //. *)
  (*    } *)
  (*   -{ inversion Hbr => //=. *)
  (*      + apply isBst_bnode_l => //; apply/ordP; apply Hl. *)
  (*          by rewrite -H /= in_bnode /= -orbA; apply/orP; left. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H0 /= in_bnode /= -orbA; apply/orP; left. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H2 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H2 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*    }  *)
  (*   -{ inversion Hbr => //=. *)
  (*      + apply isBst_bnode_l => //; first (apply/ordP; apply Hl). *)
  (*        * by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H2 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_l => //. *)
  (*        * apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_l => //. *)
  (*        * apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H6 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_l => //. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*    } *)
  (*   -{ inversion Hbr => //=. *)
  (*      + apply isBst_bnode_l => //; first (apply/ordP; apply Hl). *)
  (*        * by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H2 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_r => //. *)
  (*        * apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_r => //. *)
  (*        * apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H1 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H6 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_r => //. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*    } *)
  (*   -{ inversion Hbr => //=. *)
  (*      + apply isBst_bnode_l => //; first (apply/ordP; apply Hl). *)
  (*        * by rewrite -H3 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H3 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H4 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H3 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H6 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*        * apply isBst_bnode_l => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H3 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H6 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*        * apply isBst_bnode_r => //. *)
  (*      + apply isBst_bnode_bnode => //. *)
  (*        * apply/ordP; apply Hl. *)
  (*            by rewrite -H3 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply/ordP; apply Hr. *)
  (*            by rewrite -H8 /= in_bnode /= -orbA; apply/orP; left. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*        * apply isBst_bnode_bnode => //. *)
  (*    } *)
  (* Qed.     *)

  (* Lemma isBst_ord_l x tl tr t: *)
  (*   isBst t -> t = tl -< x >- tr -> *)
  (*   isBst tl/\isBst tr /\ *)
  (*   (forall y, y \in tl -> le y x)/\(forall y, y \in tr -> le x y). *)
  (* Proof. *)
  (*   elim: t x tl tr => [//=|/= x tl IHl tr IHr y tl' tr'] Hb [] <- <- <-. *)
  (*   inversion Hb => //; subst; (repeat split) => //; try (move=> z; by rewrite in_bleaf); move=> z; *)
  (*     rewrite in_bnode -orbA => /or3P [/eqP Heq| Hin | Hin ]; subst=> //. *)
  (*   - apply/ordP; apply ord_transitive with xl; apply/ordP => //. *)
  (*     by move: z Hin; apply IHl with tr0 => //. *)
  (*   - apply/ordP; apply ord_transitive with xl; apply/ordP => //. *)
  (*     move: z Hin; apply IHl with tr0 => //. *)
  (*   - subst.  *)
  (*     rewrite in_bnode -orbA => /or3P [/eqP->//|Hin|Hin]. *)
  (*     + apply/ordP; apply ord_transitive with xl; apply/ordP => //. *)
  (*       move: z Hin; apply IHl with tr0 => //. *)
  (*     + apply/ordP; apply ord_transitive with xl; apply/ordP => //. *)
  (*       move: z Hin; apply IHr with tl0 => //. *)
  (*     apply IHl with tr'. *)
    
    
  (* Lemma isBst_ord_l x tl tr: *)
  (*   isBst (tl -< x >- tr) -> *)
  (*   forall y, y \in tl -> le y x. *)
  (* Proof. *)
  (*   move=> Hb; inversion Hb=> y. *)
  (*   - by rewrite in_bleaf. *)
  (*   - rewrite in_bnode -orbA=> /or3P [/eqP->//|Hin|Hin]. *)
  (*     subst. *)
  (* Lemma bstP t: *)
  (*   reflect (isBst t) (bst t). *)
  (* Proof. *)
  (*   elim: t => [//=|/= x tl IHl tr IHr]; first by left. *)
  (*   case: IHl => IHl /=. *)
  (*   - case: IHr => IHr /=. *)
  (*     + rewrite andbT. *)
  (*       case: (allP (flip ord x) tl) => Hal /=. *)
  (*       * case: (allP (ord x) tr) => Har /=; first by left; apply isBst_bnode. *)
  (*         right; move=> Hb; apply Har. *)
  (*       * by right; move=> Hb; apply Hal; inversion Hb. *)
  (*     + rewrite andbF /=. *)
  (*       by right; move=> Hb; apply IHr; inversion Hb. *)
  (*   - by right; move=> Hb; apply IHl; inversion Hb. *)
  (* Qed. *)

  Lemma bst_bnode x tl tr:
    bst (tl -< x >- tr) = (bst tl) && (all (flip ord x) tl) && (bst tr) && (all (ord x) tr).
  Proof.
    by [].
  Qed.

  Lemma all_revtree p t:
    all p (revtree t) = all p t.
  Proof.
    elim: t => [//=|/= x tl -> tr ->].
    by rewrite andbAC.
  Qed.

  Lemma sorted_bst t:
    sorted ord (flatten t) = bst t.
  Proof.
    elim: t => [//= | /= x tl IHl tr IHr].
    rewrite sorted_cat_cons // sorted_rcons // sorted_cons1 // IHl // IHr
    // !flatten_all -andbCA andbC.
    apply andb_id2r => Hallr.
    apply andb_id2r => Hbstr.
    by apply andbC.
  Qed.


  Section Operations.

    Fixpoint search a t: bool :=
      if t is tl -< x >- tr
      then if a == x then true
           else if ord! a x then search a tl else search a tr
      else false.

    Lemma bst_search_aux a t:
      (a \in t) && (bst t) -> search a t.
    Proof.
      elim: t => [//= |/= x tl IHl tr IHr].
      rewrite in_bnode.
      case: (a =P x) => [<- | /eqP /negbTE Hneq] //=.
      rewrite -!andbA.
      move=> /andP
              [/orP [Hinl | Hinr]
                /and4P [Hbstl /allP Halll Hbstr /allP Hallr]].
      - move: (Halll _ Hinl) => /=; rewrite /strict_ord Hneq andbT => ->.
        by apply IHl; apply/andP.
      - move: (Hallr _ Hinr) => /=; rewrite -ord_neg_sord => -> /=.
        by apply IHr; apply/andP.
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


    Fixpoint insert a t: btree T :=
      if t is tl -< x >- tr
      then if ord! a x
           then (insert a tl) -< x >- tr
           else tl -< x >- (insert a tr)
      else #-< a >-#.

    Lemma mem_insert a b t:
      b \in (insert a t) = (b == a) || (b \in t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      case: (ord! a x) => /=.
      - by rewrite !in_bnode IHl orbCA // !orbA.
      - by rewrite !in_bnode IHr orbCA // !orbA.
    Qed.

    Lemma bst_bst_insert a t:
      bst t -> bst (insert a t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      rewrite -!andbA => /and4P [Hbstl Halll Hbstr Hallr].
      case Hord: (ord! a x) => /=; rewrite -!andbA; apply/and4P.
      - repeat split; move=>//=; first by apply IHl.
        apply/allP=> y Hin.
        move: Hin; rewrite mem_insert => /orP [/eqP-> | Hin] //=.
        + by move: Hord => /eqP; rewrite eqb_id => /andP [].
        + by move: Halll => /allP H; apply H.
      - repeat split; move=>//=; first by apply IHr.
        apply/allP=> y Hin.
        move: Hord => /negbT; rewrite sord_neg_ord => Hord.
        move: Hin; rewrite mem_insert => /orP [/eqP-> | Hin] //=.
        by move: Hallr => /allP H; apply H.
    Qed.

    Lemma bst_insert_bst a t:
      bst (insert a t) -> bst t.
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      case Hord: (ord ! a x) => /=;
        rewrite -!andbA => /and4P [Hbstl Halll Hbstr Hallr];
          apply /and4P; repeat split; move=> //=.
      - by apply IHl.
      - apply/allP=> y Hin.
        move: Halll => /allP Halll; apply Halll.
        by rewrite mem_insert Hin orbT.
      - by apply IHr.
      - apply/allP=> y Hin.
        move: Hallr => /allP Hallr; apply Hallr.
        by rewrite mem_insert Hin orbT.
    Qed.

    Lemma bst_insert a t:
      bst t = bst (insert a t).
    Proof.
      case H: (bst t).
      - by apply esym; apply bst_bst_insert.
      - apply esym; apply/negbTE; move: H => /negbT; apply contraL.
        by move=> Hbst; apply/negPn; apply bst_insert_bst with a.
    Qed.

    Lemma in_insert a t:
      a \in insert a t.
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr]; first by rewrite mem_bnode1.
      by case: (ord! a x); rewrite in_bnode ?IHl ?IHr /= orbC //= orbA orbC.
    Qed.

    Lemma search_insert a t:
      bst t -> search a (insert a t).
    Proof.
      move=> Hbst; rewrite -bst_search; first exact: in_insert.
      by apply bst_bst_insert.
    Qed.
    

    (* lend & rend with bst *)
    Lemma bst_lend a t:
      all (ord a) t -> bst t ->
      all (ord (lend a t)) t.
    Proof.
      rewrite -!flatten_all -sorted_bst lend_flatten_head.
      remember (flatten t) as l.
      clear Heql t.
      case: l a => [//=| h l] a.
      rewrite sorted_cons1 // => /=.
      move=> /andP [Hordah Hallal] /andP [Hallhl Hsorted].
      by apply/andP; split; first apply ord_reflexive.
    Qed.      
    
    Lemma bst_rend a t:
      all (flip ord a) t -> bst t ->
      all (flip ord (rend t a)) t.
    Proof.
      rewrite -!flatten_all -sorted_bst rend_flatten_rhead.
      remember (flatten t) as l.
      clear Heql t.
      case: l a => [//=| h l] a.
      rewrite sorted_cons1 // => /=.
      move=> /andP [Hordah Hallal] /andP [Hallhl Hsorted].
      apply/andP; split.
      - move: (mem_last h l); rewrite in_cons => /orP [/eqP->|Hin];
          first by apply ord_reflexive.
        by move: Hallhl => /seq.allP Hallhl; apply Hallhl.
      - move: Hallhl Hsorted => {a} {Hordah} {Hallal}.
        elim: l h => [//=| h' l IHl] h.
        rewrite sorted_cons1 // => /=.
        move=> /andP [Hordhh' Hallhl] /andP [Hallh'l Hsorted].
        apply/andP; split.
        + move: (mem_last h' l); rewrite in_cons => /orP [/eqP->|Hin];
            first by apply ord_reflexive.
          by move: Hallh'l => /seq.allP Hallh'l; apply Hallh'l.
        + by apply IHl.
    Qed.      


    Fixpoint delete_l a t: btree T :=
      if t is tl -< x >- tr
      then if a == x
           then rem_root_r t
           else if ord! a x
                then (delete_l a tl) -< x >- tr
                else tl -< x >- (delete_l a tr)
      else #.

    Lemma bst_lend_remove a t:
      bst t -> bst (lend_remove a t).2.
    Proof.
      rewrite -!sorted_bst lend_remove_behead.
      remember (flatten t) as l.
      clear Heql t.
      case: l => [//=| h l] .
      by rewrite sorted_cons1 // /= => /andP [Hord Hsorted].
    Qed.

    Lemma bst_rend_remove t a:
      bst t -> bst (rend_remove t a).1.
    Proof.
      rewrite -!sorted_bst rend_remove_rbehead.
      remember (flatten t) as l.
      clear Heql t.
      elim: l => [//=| h l] .
      rewrite sorted_cons1 //.
      elim: l => [//=| h' l IHl].
      move=> IH /andP [Hall Hsorted].
      rewrite rbehead_cons sorted_cons1 //.
      apply /andP; split.
      - move: Hall => {IHl Hsorted} /seq.allP H.
        apply /seq.allP => x Hin; apply H.
        by apply mem_rbehead.
      - by apply IH.
    Qed.

    Lemma bst_rem_root_r t:
      bst t -> bst (rem_root_r t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      rewrite -!andbA => /and4P [Hbl Hal Hbr Har].
      remember (rend_remove tl x).
      case: p Heqp => t node Heq /=.
      rewrite -!andbA; apply/and4P; split; try done.
      - by move: (bst_rend_remove x Hbl); rewrite -Heq.
      - apply/allP => y Hin.
        move: (rend_remove_rend tl x); rewrite -Heq => /= ->.
        move: (bst_rend Hal Hbl) => /allP; apply.
        by move: (@mem_rend_remove _ y tl x); rewrite -Heq; apply.
      - apply/allP => y Hin.
        move: (rend_remove_rend tl x) (mem_rend tl x);
          rewrite -Heq => /= <- /orP [/eqP->|Hin'].
        + by move: Har => /allP; apply.
        + apply ord_transitive with x.
          * by move: Hal => /allP; apply.
          * by move: Har => /allP; apply.
    Qed.

    Lemma all_delete_l p a t:
       all p t -> all p (delete_l a t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      case: (a =P x) => [<-{x}|Hneq];
        rewrite -!andbA => /and3P [Hp Hal Har].
      - remember (rend_remove tl a).
        case: p0 Heqp0 => t x Heq /=.
        rewrite -!andbA; apply/and3P; split; try done.
        + move: (rend_remove_rend tl a) (mem_rend tl a);
          rewrite -Heq /= => <- /orP [/eqP->//|Hin].
          by move: Hal => /allP; apply.
        + apply/allP => y Hin.
          move: Hal => /allP; apply.
          by move: (@mem_rend_remove _ y tl a); rewrite -Heq; apply.
      - case: (ord! a x) => /=; rewrite -!andbA;
          apply/and3P; split; try done.
        + by apply IHl.
        + by apply IHr.
    Qed.
      
    Lemma bst_delete_l a t:
      bst t -> bst (delete_l a t).
    Proof.
      elim: t => [//=| x tl IHl tr IHr].
      move=> Hbst; move: (Hbst) => /bst_rem_root_r H /=.
      case: (a =P x) => [Heq | Hneq]; first done.
      move: Hbst => /=; rewrite -!andbA => /and4P [Hbl Hal Hbr Har].
      case Hord: (ord! a x) => /=.
      - rewrite -!andbA; apply/and4P; split; try done.
        + by apply: IHl.
        + by apply: all_delete_l.
      - rewrite -!andbA; apply/and4P; split; try done.
        + by apply: IHr.
        + by apply: all_delete_l.
    Qed.

    
    (* I want to prove them *)
    Lemma mem_delete_l x a t:
      x \in (delete_l a t) -> x \in t.
    Proof.
      elim: t x => [//=| y tl IHl tr IHr /=] x.
      case: (a =P y) => [<-{y} | /eqP Hneq].
      - remember (rend_remove tl a).
        move: p Heqp => [tl' node] Heq.
        rewrite in_bnode -orbA => /or3P [/eqP-> | Hin | Hin].
        + move: (mem_rend tl a); rewrite -rend_remove_rend -Heq /=.
          by move=> H; rewrite in_bnode; apply/orP; left.
        + rewrite in_bnode -orbA; apply/or3P; apply Or32.
          by move: (@mem_rend_remove _ x tl a); rewrite -Heq /=; apply.
        + by rewrite in_bnode -orbA; apply/or3P; apply Or33.
      - rewrite /strict_ord Hneq andbT.
        case Hord: (ord a y); 
          rewrite !in_bnode -!orbA => /or3P [Heq | Hin | Hin]; apply/or3P;
            try (by apply Or33); try (by apply Or32); try (by apply Or31).
        + by apply Or32; apply: IHl.
        + by apply Or33; apply: IHr.
    Qed.


    Lemma delete_l_eq a t:
      (a \notin t) -> (delete_l a t == t).
    Proof.
      elim: t a => [//=|/= x tl IHl tr IHr] a.
      - rewrite in_bnode // !negb_or -!andbA
        => /and3P [/negbTE-> /IHl/eqP-> /IHr/eqP->].
        by rewrite if_same.
    Qed.

    Lemma size_delete_l a t:
      (size (delete_l a t) < size t)%nat -> a \in t.
    Proof.
      apply contraTT => Hnin.
      move: (delete_l_eq Hnin) => /eqP->.
      by rewrite ltnn.
    Qed.

    Fixpoint delete_r t a: btree T :=
      if t is tl -< x >- tr
      then if a == x
           then rem_root_l t
           else if ord! a x
                then (delete_r tl a) -< x >- tr
                else tl -< x >- (delete_r tr a)
      else #.

    Lemma mem_lend_remove x a t:
      x \in (lend_remove a t).2 -> x \in t.
    Proof.
      rewrite
      -{1}[t]revtree_involutive
          lend_remove_revtree swap_app_fst /= mem_revtree.
      by move=> /mem_rend_remove Hin; rewrite -mem_revtree.
    Qed.      

    Lemma all_delete_r p t a:
       all p t -> all p (delete_r t a).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      case: (a =P x) => [<-{x}|Hneq];
        rewrite -!andbA => /and3P [Hp Hal Har].
      - remember (lend_remove a tr).
        case: p0 Heqp0 => t x Heq /=.
        rewrite -!andbA; apply/and3P; split; try done.
        + move: (lend_remove_lend a tr) (mem_lend a tr);
          rewrite -Heq /= => <- /orP [/eqP->//|Hin].
          by move: Har => /allP; apply.
        + apply/allP => y Hin.
          move: Har => /allP; apply.
          by move: (@mem_lend_remove y a tr); rewrite -Heq; apply.
      - case: (ord! a x) => /=; rewrite -!andbA;
          apply/and3P; split; try done.
        + by apply IHl.
        + by apply IHr.
    Qed.

    Lemma bst_rem_root_l t:
      bst t -> bst (rem_root_l t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      rewrite -!andbA => /and4P [Hbl Hal Hbr Har].
      remember (lend_remove x tr).
      case: p Heqp => node t Heq /=.
      rewrite -!andbA; apply/and4P; split; try done.
      - apply/allP => y Hin.
        move: (lend_remove_lend x tr) (mem_lend x tr);
          rewrite -Heq => /= <- /orP [/eqP->|Hin'].
        + by move: Hal => /allP; apply.
        + apply ord_transitive with x.
          * by move: Hal => /allP; apply.
          * by move: Har => /allP; apply.
      - by move: (bst_lend_remove x Hbr); rewrite -Heq.
      - apply/allP => y Hin.
        move: (lend_remove_lend x tr); rewrite -Heq => /= ->.
        move: (bst_lend Har Hbr) => /allP; apply.
        by move: (@mem_lend_remove y x tr); rewrite -Heq; apply.
    Qed.

    Lemma bst_delete_r t a:
      bst t -> bst (delete_r t a).
    Proof.
      elim: t => [//=| x tl IHl tr IHr].
      move=> Hbst; move: (Hbst) => /bst_rem_root_l H /=.
      case: (a =P x) => [Heq | Hneq]; first done.
      move: Hbst => /=; rewrite -!andbA => /and4P [Hbl Hal Hbr Har].
      case Hord: (ord! a x) => /=.
      - rewrite -!andbA; apply/and4P; split; try done.
        + by apply: IHl.
        + by apply: all_delete_r.
      - rewrite -!andbA; apply/and4P; split; try done.
        + by apply: IHr.
        + by apply: all_delete_r.
    Qed.

    Lemma mem_delete_r x t a:
      x \in (delete_r t a) -> x \in t.
    Proof.
      elim: t x => [//=| y tl IHl tr IHr /=] x.
      case: (a =P y) => [<-{y} | /eqP Hneq].
      - remember (lend_remove a tr).
        move: p Heqp => [node tr'] Heq.
        rewrite in_bnode -orbA => /or3P [/eqP-> | Hin | Hin].
        + move: (mem_lend a tr); rewrite -lend_remove_lend -Heq /=.
          by move=> H; rewrite in_bnode -orbAC; apply/orP; left.
        + by rewrite in_bnode -orbA; apply/or3P; apply Or32.
        + rewrite in_bnode -orbA; apply/or3P; apply Or33.
          by move: (@mem_lend_remove x a tr); rewrite -Heq /=; apply.
      - rewrite /strict_ord Hneq andbT.
        case Hord: (ord a y); 
          rewrite !in_bnode -!orbA => /or3P [Heq | Hin | Hin]; apply/or3P;
            try (by apply Or33); try (by apply Or32); try (by apply Or31).
        + by apply Or32; apply: IHl.
        + by apply Or33; apply: IHr.
    Qed.

    Lemma delete_r_eq t a:
      (a \notin t) -> (delete_r t a == t).
    Proof.
      elim: t a => [//=|/= x tl IHl tr IHr] a.
      - rewrite in_bnode // !negb_or -!andbA
        => /and3P [/negbTE-> /IHl/eqP-> /IHr/eqP->].
        by rewrite if_same.
    Qed.

    Lemma size_delete_r t a:
      (size (delete_r t a) < size t)%nat -> a \in t.
    Proof.
      apply contraTT => Hnin.
      move: (delete_r_eq Hnin) => /eqP->.
      by rewrite ltnn.
    Qed.

  (* Sorting by using binary-search tree *)
    Fixpoint btsort_insert s t: btree T :=
      if s is h :: s' then btsort_insert s' (insert h t) else t.

    Definition btsort s := flatten (btsort_insert s #).

    Lemma btsort_insert_bst s t:
      bst t -> bst (btsort_insert s t).
    Proof.
      elim: s t => [//=|/= h s IHs].
      by move=> t Hbst; apply IHs; rewrite -bst_insert.
    Qed.

    Lemma btsort_sorted s:
      sorted ord (btsort s).
    Proof.
      by rewrite /btsort sorted_bst; apply btsort_insert_bst.
    Qed.

    Lemma insert_count a t p:
      count p (insert a t) = (p a + count p t)%nat.
    Proof.
      elim: t a p => [//=|/= x tl IHl tr IHr] a p.
      case: (ord! a x) => /=.
      - rewrite addnAC -IHr addnC.
        by rewrite addnAC  -[(p x + _)%nat]IHr addnCA -IHl addnC.
      - by rewrite -IHl addnA addnAC -IHr addnC.
    Qed.
        
    Lemma btsort_insert_count s t p:
        (seq.count p s + count p t)%nat = count p (btsort_insert s t).
    Proof.
      elim: s t p => [//=|/= h s IHs] t p.
      by rewrite -IHs insert_count addnCA addnA.
    Qed.      
    
    Lemma btsort_insert_perm s t:
      perm_eq (s ++ flatten t) (flatten (btsort_insert s t)).
    Proof.
      apply/perm_eqP.
      move=> p /=.
      elim: s p => [//=|/= h s IHs] p.
      by rewrite IHs // !flatten_count -!btsort_insert_count insert_count addnCA.
    Qed.

    Lemma btsort_perm_eq s:
      perm_eq s (btsort s).
    Proof.
      case: s => [//=|/= h s].
      rewrite /btsort /=.
      replace (h :: s) with (flatten (#-<h>-#) ++ s); last by [].
      apply perm_eq_trans with (s ++ flatten (#-<h>-#)).
      - by rewrite perm_catC perm_eq_refl.
      - by rewrite btsort_insert_perm.
    Qed.


  End Operations.



End BinarySearchTree.


(* Eval compute in (btsort (fun x y => x < y) [::3;1;4;1;5;9;2;6]). *)
(* = [:: 1; 1; 2; 3; 4; 5; 6; 9] *)
(* : seq nat_eqType *)

(* Definition tb := ((# -< 1 >- # -< 2 >- (# -< 3 >- #)) -< 4 >- (# -< 5 >- #)). *)
(* Eval compute in (delete (fun x y => x < y) 4 tb). *)
(* Eval compute in (rend_remove 6 tb). *)
(* Eval compute in (lend_remove 0 (lend_remove 0 tb).2). *)
