(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/23 13:4:32> *)
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
  Adlibssr.sorted
  Adlibssr.order.

(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(**
 ** Binary Search Tree 
 *)

(* Aux *)
Definition flip {X Y Z: Type}(f: X -> Y -> Z): Y -> X -> Z :=
  fun y x => f x y.
Arguments flip X Y Z f / y x.

Inductive btR {T}(R: T -> T -> Prop)(a: T): btree T -> Prop :=
| btR_bleaf: btR R a #
| btR_bnode: forall x tl tr,
                R a x -> btR R a tl -> btR R a tr ->
                btR R a (tl -< x >- tr).
Hint Constructors btR.

Lemma btRP {T}(R: T -> T -> Prop) ord a t:
  (forall x y, reflect (R x y) (ord x y)) ->
  reflect (btR R a t) (all (ord a) t).
Proof.
  move=> ordP.
  elim: t => [//=|/= x tl IHl tr IHr]; first by left.
  move: IHl IHr => [Hl | Hnl] /= [Hr | Hnr] /=;
    rewrite ?andbT ?andbF; try (right; move=> Hb).
  - case: (ordP a x) => [HR | HnR]; [left; apply btR_bnode=> //| right].
    move=> Hb; apply HnR; inversion Hb => //.
  - apply Hnr; inversion Hb => //.
  - apply Hnl; inversion Hb => //.
  - apply Hnr; inversion Hb => //.
Qed.

Section BinarySearchTree.

  Variables (T: eqType)
            (le: T -> T -> Prop)
            (ord: totalOrder T).
  Notation "x <= y" := (le x y).
  Hypothesis (ordP: forall x y, reflect (x <= y) (ord x y)).

  Lemma ordP' x y: reflect (flip le x y) (ord^~ x y).
  Proof.
    simpl; apply ordP.
  Qed.
  
  Implicit Types (t: btree T)(s: seq T).

  Inductive isBst: btree T -> Prop :=
  | isBst_bleaf: isBst #
  | isBst_bnode: forall x tl tr,
                   isBst tl -> btR (flip le) x tl ->
                   isBst tr -> btR le x tr ->
                   isBst (tl -< x >- tr).
  Hint Constructors isBst.

  Fixpoint bst t: bool :=
    if t is tl -< x >- tr
    then (bst tl) && (all (flip ord x) tl) && (bst tr) && (all (ord x) tr)
    else true.
  Functional Scheme bst_ind := Induction for bst Sort Prop.


  Lemma bstP t: reflect (isBst t) (bst t).
  Proof.
    elim: t => [//=|/= x tl IHl tr IHr]; first by left.
    move: IHl IHr => [Hbl | Hnbl] [Hbr | Hnbr] /=.
    - rewrite andbT.
      case: (btRP x tl ordP') => Hal /=;
        last by right; move=> Hb; apply Hal; inversion Hb.
      case: (btRP x tr ordP) => Har /=;
        last by right; move=> Hb; apply Har; inversion Hb.
        by left; apply isBst_bnode => //.
    - by rewrite andbF /=; right; move=> Hb; apply Hnbr; inversion Hb.
    - by right; move=> Hb; apply Hnbl; inversion Hb.
    - by right; move=> Hb; apply Hnbl; inversion Hb.
  Qed.

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

  Lemma sorted_walk_bst t s:
    sorted ord (walk t s) = (bst t) && (sorted ord s)
                                    && (all (fun x => seq.all (ord x) s) t).
  Proof.
    elim/walk_ind: t s /(walk t s)=> t s; first by rewrite andbT.
    move=> x tl tr _ Heqr ->.
    rewrite sorted_cons1 // Heqr /= ?andbA /=.
    case (bst tl) => //=.
    case (bst tr) => //=;
    rewrite /= ?andbT ?andbF //.
    case (all (fun x0 : T => seq.all (ord x0) s) tr);
    rewrite /= ?andbT ?andbF //.
    case (sorted ord s) => //=;
    rewrite /= ?andbT ?andbF //.
    case Hta: (all (fun x0 : T => ord x0 x && seq.all (ord x0) (walk tr s)) tl).
    - move: Hta => /eqP; rewrite eqb_id andbT /= => /allP Hta.
      case Hsa: (seq.all (ord x) (walk tr s)).
      move: Hsa => /eqP; rewrite eqb_id => /seq.allP Hsa.
      + apply esym; apply/eqP; rewrite eqb_id -!andbA; apply/and4P; split.
        * by apply/allP=> y Hin; move: (Hta _ Hin) => /andP [] //.
        * by apply/allP=> y Hin; apply Hsa; rewrite mem_walk; apply/orP; left.
        * by apply/seq.allP=> y Hin; apply Hsa; rewrite mem_walk; apply/orP; right.
        * apply/allP=> y Hiny; apply/seq.allP=> z Hinz.
          move: (Hta _ Hiny) => /andP [] _ /seq.allP; apply.
          by rewrite mem_walk; apply/orP; right.
      + apply esym; apply/eqP; rewrite eqbF_neg; apply/negP => H.
        move: Hsa => /eqP; rewrite eqbF_neg => /negP; apply.
        move: H; rewrite -!andbA => /and4P [/allP Hal /allP Har /seq.allP Has /allP Hsal].
        apply/seq.allP=> y; rewrite mem_walk => /orP [Hin | Hin].
        * by apply Har.
        * by apply Has.
    - rewrite andbF /=; apply esym; apply/eqP; rewrite eqbF_neg -!andbA;
      apply/negP => /and4P [/allP Hal /allP Har /seq.allP Has /allP Hsal].
      move: Hta => /eqP; rewrite eqbF_neg => /negP; apply.
      apply/allP=> y Hin; apply/andP; split; first by apply Hal.
      apply/seq.allP => z; rewrite mem_walk => /orP [Hinr | Hins].
      + apply ord_transitive with x.
        * by apply Hal.
        * by apply Har.
      + by move: (Hsal _ Hin) => /seq.allP; apply.
  Qed.
 
  Lemma all_predT t:
    all predT t.
  Proof.
    by elim: t => [//=|/= x tl -> tr ->].
  Qed.

  Lemma sorted_bst t:
    sorted ord (flatten t) = bst t.
  Proof.
    by rewrite sorted_walk_bst /= andbT all_predT andbT.
  Qed.


  Section Operations.

    Fixpoint search a t: bool :=
      if t is tl -< x >- tr
      then if a == x then true
           else if ord! a x then search a tl else search a tr
      else false.
    Functional Scheme search_ind := Induction for search Sort Prop.
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
      (* functional induction (search a t) => //=; *)
      (*   rewrite in_bnode -!orbA -!andbA e0 /=; *)
      (*     move=>/and4P [/orP [Hin | Hin] Hbl Hal /andP [Hbr Har]]; *)
      (*       apply IHb; apply/andP; split=> //. *)
      (* - by move: Har => /allP Har; move: (Har a Hin); *)
      (*       rewrite -sord_neg_ord e1 //. *)
      (* - by move: Hal => /allP Hal; move: e1 (Hal a Hin) =>/eqP; rewrite eqbF_neg /strict_ord negb_and e0 orbF/= -eqbF_neg => /eqP->//. *)
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
    Functional Scheme insert_ind := Induction for insert Sort Prop.

    Lemma mem_insert a b t:
      b \in (insert a t) = (b == a) || (b \in t).
    Proof.
      by functional induction (insert a t)
        as [| _ x tl tr _ _ IH
            | _ x tl tr _ _ IH] => //;
        rewrite !in_bnode /= IH orbCA -!orbA.
    Qed.
    
    Lemma all_insert p a t:
      all p (insert a t) = p a && all p t.
    Proof.
      by functional induction (insert a t)
        as [| _ x tl tr _ Hord IH
            | _ x tl tr _ Hord IH] => //=;
        rewrite ?andbT // IH andbCA -!andbA.
    Qed.

    Lemma bst_bst_insert a t:
      bst t -> bst (insert a t).
    Proof.
      functional induction (insert a t)
        as [| _ x tl tr _ Hord IH
            | _ x tl tr _ Hord IH] => //=; rewrite -!andbA all_insert;
      [ move=> /and4P [/IH-> -> -> ->]
      | move=> /and4P [-> -> /IH-> ->]];
      rewrite /= !andbT //.
      - by move: Hord=>/eqP; rewrite eqb_id=>/andP []//.
      - by rewrite -sord_neg_ord Hord.
    Qed.

    Lemma bst_insert_bst a t:
      bst (insert a t) -> bst t.
    Proof.
      by functional induction (insert a t)
        as [| _ x tl tr _ Hord IH
            | _ x tl tr _ Hord IH] => //=; rewrite -!andbA all_insert;
      [ move=> /and4P [/IH-> /andP [Ho ->] -> ->]
      | move=> /and4P [-> -> /IH-> /andP [Ho ->]]].
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
      by functional induction (insert a t)
        as [| _ x tl tr _ Hord IH
            | _ x tl tr _ Hord IH] => //=;
        rewrite ?mem_bnode1 ?in_bnode //= IH orbT //.
    Qed.

    Lemma search_insert a t:
      bst t -> search a (insert a t).
    Proof.
        by move=> Hbst; rewrite -bst_search; [apply: in_insert | apply: bst_bst_insert].
    Qed.
    
  (* Sorting by using binary-search tree *)
    Fixpoint btsort_insert s t: btree T :=
      if s is h :: s' then btsort_insert s' (insert h t) else t.
    Functional Scheme btsort_insert_ind := Induction for btsort_insert Sort Prop.

    Definition btsort s := flatten (btsort_insert s #).

    Lemma btsort_insert_bst s t:
      bst t -> bst (btsort_insert s t).
    Proof.
      by functional induction (btsort_insert s t) => //=;
       move=> Hbst; apply IHb; move: Hbst; apply bst_bst_insert.
    Qed.

    Lemma btsort_sorted s:
      sorted ord (btsort s).
    Proof.
      by rewrite /btsort sorted_bst; apply btsort_insert_bst.
    Qed.

    Lemma insert_count a t p:
      count p (insert a t) = (p a + count p t)%nat.
    Proof.
      by functional induction (insert a t)
        as [| _ x tl tr _ Hord IH
            | _ x tl tr _ Hord IH] => //=; rewrite IH addnCA -!addnA.
    Qed.
        
    Lemma btsort_insert_count s t p:
        (seq.count p s + count p t)%nat = count p (btsort_insert s t).
    Proof.
        by functional induction (btsort_insert s t) => //=;
        rewrite -IHb insert_count addnCA addnA.
    Qed.      
    
    Lemma btsort_insert_perm s t:
      perm_eq (s ++ flatten t) (flatten (btsort_insert s t)).
    Proof.
      apply/perm_eqP=> p /=.
      by functional induction (btsort_insert s t) => //=;
        rewrite -IHb ?count_cat ?flatten_count insert_count addnCA.
    Qed.

    Lemma btsort_perm_eq s:
      perm_eq s (btsort s).
    Proof.
      by eapply perm_eq_trans; [| apply btsort_insert_perm]; rewrite cats0.
    Qed.

    Definition sorting f := forall s, perm_eq s (f s) /\ sorted ord (f s).

    Theorem btsort_sorting: sorting btsort.
    Proof. by split; [apply btsort_perm_eq | apply btsort_sorted]. Qed.

    (* lend & rend with bst *)
    Lemma bst_lend a t:
      bst t ->
      all (ord a) t -> 
      all (ord (lend a t)) t.
    Proof.
      rewrite -!flatten_all -sorted_bst -head_flatten_lend.
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
      rewrite -!flatten_all -sorted_bst -rend_flatten_rhead.
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
    Functional Scheme delete_l_ind := Induction for delete_l Sort Prop.


    Lemma bst_lend_remove a t:
      bst t -> bst (lend_remove a t).2.
    Proof.
      rewrite -!sorted_bst flatten_lend_remove_behead.
      remember (flatten t) as l.
      clear Heql t.
      case: l => [//=| h l] .
      by rewrite sorted_cons1 // /= => /andP [Hord Hsorted].
    Qed.

    Lemma bst_rend_remove t a:
      bst t -> bst (rend_remove t a).1.
    Proof.
      rewrite -!sorted_bst flatten_rend_remove_rbehead.
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
      remember (rend_remove tl x).
      case: p Heqp => t node Heq /=.
      rewrite -!andbA => /and4P [Hbl Hal -> Har] /=.
      move: (bst_rend_remove x Hbl); rewrite -Heq/= => -> /=.
      apply/andP; split.
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
      functional induction (delete_l a t) => //=; rewrite -!andbA.
      - remember (rend_remove tl x) as tn.
        case: tn Heqtn => t node Heq /= /and3P [Hp /allP Hal ->]; rewrite andbT.
        + apply/andP; split.
          * by move: (rend_remove_rend tl x) (mem_rend tl x);
            rewrite -Heq/= => <- /orP [/eqP->//|Hin]; apply Hal.
          * by apply/allP=> y Hin; apply Hal; apply mem_rend_remove with x; rewrite -Heq.
      - by move=> /and3P [-> /IHb-> ->].
      - by move=> /and3P [-> -> /IHb->].
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
        move: (bst_lend Hbr Har) => /allP; apply.
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


  End Operations.  



End BinarySearchTree.


(* Eval compute in (btsort (fun x y => x < y) [::3;1;4;1;5;9;2;6]). *)
(* = [:: 1; 1; 2; 3; 4; 5; 6; 9] *)
(* : seq nat_eqType *)

(* Definition tb := ((# -< 1 >- # -< 2 >- (# -< 3 >- #)) -< 4 >- (# -< 5 >- #)). *)
(* Eval compute in (delete (fun x y => x < y) 4 tb). *)
(* Eval compute in (rend_remove 6 tb). *)
(* Eval compute in (lend_remove 0 (lend_remove 0 tb).2). *)
