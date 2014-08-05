(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/5 22:15:56> *)
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

  Let eordb x y := (ordb x y) || (x == y).
  Lemma
    eordb_transitive: transitive eordb.
  Proof.
    move=> y x z /orP [Hordxy | /eqP->] /orP [Hordyz | /eqP<-] //=.
    - apply/orP; left; apply ordb_transitive with y => //.
    - by apply/orP; left.      
    - by apply/orP; left.      
    - by apply/orP; right.
  Qed.
  Hint Resolve eordb_transitive.
  Implicit Types (t: btree T)(s: seq T).


  Fixpoint bst t: bool :=
    if t is tl -< x >- tr
    then (bst tl) && (all (eordb ^~ x) tl) && (bst tr) && (all (eordb x) tr)
    else true.

  Lemma bst_bnode x tl tr:
    bst (tl -< x >- tr) = (bst tl) && (all (eordb ^~ x) tl) && (bst tr) && (all (eordb x) tr).
  Proof.
    by [].
  Qed.

  Lemma sorted_bst t:
    sorted eordb (flatten t) = bst t.
  Proof.
    elim: t => [//= | /= x tl IHl tr IHr].
    rewrite sorted_cat_cons // sorted_rcons // sorted_cons1 // IHl IHr
            !flatten_all -andbCA andbC.
    apply andb_id2r => Hallr.
    apply andb_id2r => Hbstr.
    by apply andbC.
  Qed.



  Section Operations.

    Hypothesis
      (ordb_rel:
         forall x y,
           ~~ ordb x y = (x == y) || (ordb y x))
      (ordb_total:
         forall x y,
           (ordb x y) (+) (x == y) (+) (ordb y x)).
    
    Lemma eordb_total:
      total eordb.
    Proof.
      rewrite/total /eordb => x y.
      move: (ordb_total x y) => /addbP <-.
      rewrite negb_add [y == x]eq_sym.
      case: (x =P y) => [<- | Hneq]; first by rewrite orbCA orbA orbC.
      by rewrite !orbF eqbF_neg orbN.
    Qed.
    
    Lemma ordb_irrefl x y:
      ~~ (ordb x y && ordb y x).
    Proof.
      by rewrite negb_and ordb_rel -orbA orbN orbT.
    Qed.

    Lemma eordb_antisym:
      antisymmetric eordb.
    Proof.
      rewrite /antisymmetric /eordb
      => x y /andP [/orP [Hordxy | Heq] /orP [Hordyx | Heq']];
        try by apply/eqP.
      - by move: (ordb_irrefl x y); rewrite Hordxy Hordyx //.
      - by move: Heq' => /eqP->.
    Qed.

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
      case: (a =P x) => [<- | /eqP /negbTE Hneq] //=.
      rewrite -!andbA.
      move=> /andP
              [/orP [Hinl | Hinr]
                /and4P [Hbstl /allP Halll Hbstr /allP Hallr]].
      - move: (Halll _ Hinl) => /=; rewrite /eordb Hneq orbF => ->.
        by apply IHl; apply/andP.
      - move: (Hallr _ Hinr) => /=;
          rewrite /eordb [_==a]eq_sym Hneq orbF => Hord.
        have: ~~ ordb a x; first by rewrite ordb_rel Hord orbT.
        by move=> /negbTE ->; apply IHr; apply/andP.
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
      then if ordb a x
           then (insert a tl) -< x >- tr
           else tl -< x >- (insert a tr)
      else #-< a >-#.

    Lemma mem_insert a b t:
      b \in (insert a t) = (b == a) || (b \in t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      case: (ordb a x) => /=.
      - by rewrite !in_bnode IHl orbCA !orbA.
      - by rewrite !in_bnode IHr orbCA !orbA.
    Qed.

    Lemma bst_bst_insert a t:
      bst t -> bst (insert a t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      rewrite -!andbA => /and4P [Hbstl Halll Hbstr Hallr].
      case Hord: (ordb a x) => /=; rewrite -!andbA; apply/and4P.
      - repeat split; move=>//=; first by apply IHl.
        apply/allP=> y Hin.
        move: Hin; rewrite mem_insert => /orP [/eqP-> | Hin] //=.
        + by rewrite /eordb Hord.
        + by move: Halll => /allP H; apply H.
      - repeat split; move=>//=; first by apply IHr.
        apply/allP=> y Hin.
        move: Hord => /negbT; rewrite ordb_rel => /orP [/eqP Heq | Hord].
        + subst a.
          move: Hin; rewrite mem_insert => /orP [/eqP-> | Hin] //=.
          * by apply/orP; right.
          * by move: Hallr => /allP H; apply H.
        + move: Hin; rewrite mem_insert => /orP [/eqP-> | Hin] //=.
          * by apply/orP; left.
          * by move: Hallr => /allP H; apply H.
    Qed.

    Lemma bst_insert_bst a t:
      bst (insert a t) -> bst t.
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      case Hord: (ordb a x) => /=;
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
      by case: (ordb a x); rewrite in_bnode ?IHl ?IHr /= orbC //= orbA orbC.
    Qed.

    Lemma search_insert a t:
      bst t -> search a (insert a t).
    Proof.
      move=> Hbst; rewrite -bst_search; first exact: in_insert.
      by apply bst_bst_insert.
    Qed.
    

    (* lend & rend with bst *)
    Lemma bst_lend a t:
      all (eordb a) t -> bst t ->
      all (eordb (lend a t)) t.
    Proof.
      rewrite -!flatten_all -sorted_bst lend_flatten_head.
      remember (flatten t) as l.
      clear Heql t.
      case: l a => [//=| h l] a.
      rewrite sorted_cons1 // => /=.
      move=> /andP [Hordah Hallal] /andP [Hallhl Hsorted].
      by apply/andP; split; first by apply/orP; right.
    Qed.      
    
    Lemma bst_rend a t:
      all (eordb^~ a) t -> bst t ->
      all (eordb^~ (rend t a)) t.
    Proof.
      rewrite -!flatten_all -sorted_bst rend_flatten_rhead.
      remember (flatten t) as l.
      clear Heql t.
      case: l a => [//=| h l] a.
      rewrite sorted_cons1 // => /=.
      move=> /andP [Hordah Hallal] /andP [Hallhl Hsorted].
      apply/andP; split.
      - move: (mem_last h l); rewrite in_cons => /orP [/eqP->|Hin];
          first by apply/orP; right.
        by move: Hallhl => /seq.allP Hallhl; apply Hallhl.
      - move: Hallhl Hsorted => {a} {Hordah} {Hallal}.
        elim: l h => [//=| h' l IHl] h.
        rewrite sorted_cons1 // => /=.
        move=> /andP [Hordhh' Hallhl] /andP [Hallh'l Hsorted].
        apply/andP; split.
        + move: (mem_last h' l); rewrite in_cons => /orP [/eqP->|Hin];
            first by apply/orP; right.
          by move: Hallh'l => /seq.allP Hallh'l; apply Hallh'l.
        + by apply IHl.
    Qed.      

    Definition lend_merge a tl tr: btree T :=
      if tl is # then tr
      else let (tl', node) := rend_remove tl a in
           tl' -< node >- tr.

    Definition rend_merge tl tr a: btree T :=
      if tr is # then tl
      else let (node, tr') := lend_remove a tr in
           tl -< node >- tr'.
    
    Lemma rend_remove_bnode x tl tr a:
      rend_remove (tl -< x >- tr) a =

    Lemma lend_merge_bnode a x tl t tr t':
      lend_merge a (tl -< x >- tr) tr' =
      let (tl', node) := rend_remove tl a in
      tl' -< node >- tr'
    Fixpoint delete a t: btree T :=
      if t is tl -< x >- tr
      then if a == x
           then lend_merge x tl tr
           else if ordb a x
                then (delete a tl) -< x >- tr
                else tl -< x >- (delete a tr)
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

    Lemma bst_delete a t:
      bst t -> bst (delete a t).
    Proof.
      elim: t => [//=|/= x tl IHl tr IHr].
      rewrite -!andbA => /and4P [Hbstl Hal Hbstr Har].
      case: (a =P x) => [Heq | Hneq]; first subst x.
      - move=> {IHl IHr}.
        elim: tl Hbstl Hal Hbstr Har => [//=|x tl IHl t IH].
        move=> Hbstl Hal Hbstr Har.
        remeb

        

      - move: (IHl Hbstl) (IHr Hbstr) => Hbstdl {IHl} Hbstdr {IHr}.
        move: tl Hbstl Hbstdl Hal => [? ? ?|y tl tr'].
        + by move: tr Hbstr Hbstdr Har => [|] //.
        + move: tr Hbstr Hbstdr Har => [|z tl' tr] //.
          remember (rend_remove (tl -< y >- tr') x) as rrt.
          destruct rrt.
          move=> Hbstz ? Hallz Hbsty ? Hall.
          rewrite bst_bnode.
          rewrite -andbA -andbA; apply /and4P. 
    Abort.
          

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
      sorted eordb (btsort s).
    Proof.
      by rewrite /btsort sorted_bst; apply btsort_insert_bst.
    Qed.

    Lemma insert_count a t p:
      count p (insert a t) = p a + count p t.
    Proof.
      elim: t a p => [//=|/= x tl IHl tr IHr] a p.
      case: (ordb a x) => /=.
      - rewrite addnAC -IHr addnC.
        by rewrite addnAC -[p x + _]IHr addnCA -IHl addnC.
      - by rewrite -IHl addnA addnAC -IHr addnC.
    Qed.
        
    Lemma btsort_insert_count s t p:
        seq.count p s + count p t = count p (btsort_insert s t).
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
      by rewrite IHs !flatten_count -!btsort_insert_count insert_count addnCA.
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

  (* In Progress... *)

  End Operations.



End BinarySearchTree.


(* Eval compute in (btsort (fun x y => x < y) [::3;1;4;1;5;9;2;6]). *)
(* = [:: 1; 1; 2; 3; 4; 5; 6; 9] *)
(* : seq nat_eqType *)

(* Definition tb := ((# -< 1 >- # -< 2 >- (# -< 3 >- #)) -< 4 >- (# -< 5 >- #)). *)
(* Eval compute in (delete (fun x y => x < y) 4 tb). *)
(* Eval compute in (rend_remove 6 tb). *)
(* Eval compute in (lend_remove 0 (lend_remove 0 tb).2). *)
