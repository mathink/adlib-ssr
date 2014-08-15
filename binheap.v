(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/16 0:27:22> *)
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
  MathComp.path
  MathComp.div.

Require Import
  Adlibssr.btree
  Adlibssr.order
  Adlibssr.monad.

Require Import Wf_nat Recdef.

(* Implicity *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Section Accessor.
  
  Variables (T: eqType).

  Inductive pos :=
  | pos_on
  | pos_l of pos
  | pos_r of pos.

  Fixpoint pos_cat (p1 p2: pos) := 
    match p1 with
      | pos_on => p2
      | pos_l p => pos_l (pos_cat p p2)
      | pos_r p => pos_r (pos_cat p p2)
    end.

  Fixpoint btget t p: option T :=
    match t, p with
      | _ -< x >- _, pos_on => Some x
      | t' -< _ >- _, pos_l p'
      | _ -< _ >- t', pos_r p' => btget t' p'
      | #, _ => None
    end.

  (* pos の適用順が逆 *)
  Fixpoint pos2n_base (acc: nat)(p: pos) :=
    match p with
      | pos_on => acc
      | pos_l p' => (pos2n_base (acc.*2.+1) p')
      | pos_r p' => (pos2n_base (acc.+1.*2) p')
    end.

  Definition pos2n := pos2n_base 0.

  Eval compute in (pos2n (pos_l (pos_l (pos_l pos_on)))).
  
  Definition ltn (x y: nat): Prop := x < y.
  Hint Unfold ltn.
  Definition wf_ltn: well_founded ltn.
  Proof.
    apply well_founded_lt_compat with id.
    move=> x y Hlt; apply/ltP=>//.
  Defined.

  Function n2pos_base (n: nat){wf ltn}: pos -> pos :=
    match n with
      | O => id
      | n'.+1 => let (q, r) := edivn n' 2 in
                 if r == 0
                 then n2pos_base q \o pos_l
                 else n2pos_base q \o pos_r
    end.
  Proof.
    - move=> n n' Heqn q r.
      rewrite edivn_def /ltn => Heq; move: Heq => [] <- <- /eqP _. 
      apply leq_ltn_trans with n'; last by apply ltnSn.
      by apply leq_div.
    - move=> n n' Heqn q r.
      rewrite /ltn edivn_def => Heq; move: Heq => [] <- <- /eqP _. 
      apply leq_ltn_trans with n'; last by apply ltnSn.
      by apply leq_div.
    - by apply wf_ltn.
  Defined.

  Definition n2pos n := n2pos_base n pos_on.

  
  Lemma n2pos_pos2n_base n p:
   pos2n_base 0 (n2pos_base n p) = pos2n_base n p.
  Proof.
    move: p; pattern n.
    apply well_founded_induction with ltn; first by apply wf_ltn.
    rewrite /ltn => {n} x IH p /=.
    rewrite n2pos_base_equation.
    case: x IH => [| x] IH //=.
    rewrite edivn_def modn2 eqb0 if_arg fun_if /=.
    do 2 (rewrite IH; last by (rewrite ltnS; apply leq_div)).
    case Hodd: (odd x) => /=.
    - have: ((x %/ 2).+1.*2 = x.+1); last by move=>->//.
      rewrite /= -addn1 addnC -muln2 mulnDl muln2 -addnn addnAC addn1 muln2 divn2.
      move: Hodd => /eqP; rewrite eqb_id -[odd x]eqb1 => /eqP {1}<-.
      by rewrite odd_double_half.
    - have: ((x %/ 2).*2.+1 = x.+1); last by move=>->//.
      apply eq_S; apply/eqP.
      by rewrite -muln2 -dvdn_eq dvdn2 Hodd.
  Qed.

  Lemma n2pos_pos2n_cancel: cancel n2pos pos2n.
  Proof.
    move=> n /=.
    by rewrite/n2pos /pos2n n2pos_pos2n_base.
  Qed.


  Lemma pos2n_n2pos_base n p1 p2:
    n2pos_base (pos2n_base n p1) p2 =
    n2pos_base n (pos_cat p1 p2).
  Proof.
    elim: p1 p2 n => [| p1 /= IHp | p1 /= IHp] //= p2 n.
    - by rewrite IHp n2pos_base_equation edivn_def -muln2 modnMl/= mulnK//.
    - by rewrite IHp n2pos_base_equation -addn1 -addnn /= addnAC addnC /= addnA edivn_def addnn -muln2 modnMDl/= divnMDl//= divn_small// addn0.
  Qed. 

  Lemma pos_catp0 p: pos_cat p pos_on = p.
  Proof.
    by elim: p => [|p/=->|p/=->].
  Qed.

  Lemma pos2n_n2pos_cancel: cancel pos2n n2pos.
  Proof.
    move=> p /=.
    rewrite/n2pos /pos2n pos2n_n2pos_base pos_catp0 //.
  Qed.


  Lemma bij_n2pos: bijective n2pos.
  Proof.
    apply Bijective with pos2n.
    - apply n2pos_pos2n_cancel.
    - apply pos2n_n2pos_cancel.
  Qed.

  Lemma bij_pos2n: bijective pos2n.
  Proof.
    apply Bijective with n2pos.
    - apply pos2n_n2pos_cancel.
    - apply n2pos_pos2n_cancel.
  Qed.

End Accessor.


Require Import MathComp.prime MathComp.bigop.


(* Eval compute in (avl ((#-< 1 >-#) -< 2 >- (#-< 3 >-#))). *)
(* Eval compute in (avl (((#-< 2 >-#) -< 1 >- (#-< 3 >-#))-< 0 >- (#-< 4 >-#))). *)
(* Eval compute in (map n2pos [:: 0 ; 1 ; 2 ; 3;  4 ]). *)
(* Eval compute in (let t := (((#-< 3 >-#) -< 1 >- (#-< 4 >-#))-< 0 >- (#-< 2 >-#)) in (btget t (pos_l (pos_r pos_on)))). *)
(* Eval compute in (let t := (((#-< 3 >-#) -< 1 >- (#-< 4 >-#))-< 0 >- (#-< 2 >-#)) in (map (btget t \o n2pos) [:: 0 ; 1 ; 2 ; 3;  4 ])). *)
(* Eval compute in (btget ((#-< 1 >-#) -< 2 >- (#-< 3 >-#)) pos_on). *)
(* Eval compute in (btget ((#-< 1 >-#) -< 2 >- (#-< 3 >-#)) (pos_l pos_on)). *)
(* Eval compute in (btget ((#-< 1 >-#) -< 2 >- (#-< 3 >-#)) (n2pos 0)). *)



Section Heap.
  
  Variables (T: eqType)(ord: totalOrder T).
  Implicit Type (t: btree T).

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


  Definition btgetn t := btget t \o n2pos.
(* shape property *)
  Definition bt_shape t: bool :=
    seq.all (fun n => btgetn t n != None) (iota 0 (size t)).

  Context `(mon: eqMonad m)(monf: eqMonad_F mon).

  Fixpoint put t p a: m (btree_eqType T) :=
    match t, p with
      | #, pos_on => emb (#-< a >-#)
      | tl -< x >- tr, pos_l p' =>
        tl' <- put tl p' a;
          emb (tl' -< x >- tr)
      | tl -< x >- tr, pos_r p' =>
        tr' <- put tr p' a;
          emb (tl -< x >- tr')
      | _, _ => failure
    end.

  (* Section InitBase. *)
  (*   Variable (a: T). *)
  (*   Compute (map (fun x => (x, half x, uphalf x)) (iota 0 15)). *)

  (*   Function init_base (n: nat){wf ltn}: btree T := *)
  (*     match n with *)
  (*       | O => # *)
  (*       | 1 => #-< a >-# *)
  (*       | n'.+1 => *)
  (*         init_base (uphalf n') -< a >- init_base (half n') *)
  (*     end. *)
  (*   Proof. *)
  (*     - move=> n ? n' ? Heqn; rewrite/ltn -divn2. *)
  (*       remember (n'.+1) as n1. *)
  (*       rewrite -addn1 -[n1.+1]addn1 leq_add2r. *)
  (*       by apply leq_div. *)
  (*     - move=> n ? n' ? Heqn; rewrite/ltn. *)
  (*       rewrite uphalf_half -modn2 -divn2 addnC. *)
  (*       remember (n'.+1) as n1. *)
  (*       rewrite -addn1 -[n1.+1]addn1 leq_add2r. *)
  (*       rewrite {3}[n1](divn_eq n1 2) leq_add2r. *)
  (*       by apply leq_pmulr => //. *)
  (*     - by apply wf_ltn. *)
  (*   Defined. *)

  (* End InitBase. *)

  (* Lemma bt_shape_put t a: *)
  (*   bt_shape t -> *)
  (*   exists t', put t (n2pos (size t)) a = emb t'. *)
  (* Proof. *)
  (*   elim: t => [| x tl IHl tr IHr] //=. *)
  (*   - by move=> _; exists (#-< a >-#). *)
  (*   -  *)
        
(* W.I.P. *)

End Heap.

(* Compute (let ft := init_base 0 in *)
(*          (map (bt_shape (T:=nat_eqType) \o ft) (iota 0 15))). *)

Fixpoint bits2pos (bits: list bool): pos :=
  match bits with
    | [::] => pos_on
    | true :: bits' => pos_l (bits2pos bits')
    | false :: bits' => pos_r (bits2pos bits')
  end.


Compute ((pos2n \o bits2pos) [::false]).
Compute (pos2n (pos_l (pos_r (pos_l pos_on)))).
Compute (pos2n (pos_r (pos_r (pos_l pos_on)))).
Compute (pos2n (pos_l (pos_l (pos_r (pos_l pos_on))))).
Compute (pos2n (pos_r (pos_l (pos_r (pos_l pos_on))))).
Compute (height (#-< 1 >-#: btree nat)).

Definition ttree :=
  bnode
    50
    (bnode
       17
       (bnode
          12
          (bnode 9 # #)
          (bnode 14 # #))
       (bnode
          23
          (bnode 19 # #)
          #))
    (bnode
       72
       (bnode 54 # #)
       (bnode 76 # #)).

Eval compute in (x <- (put eqMaybe_F ttree (n2pos (size ttree)) 0); emb (bt_shape x)).

Eval compute in
    (let t :=
         bnode
           50
           (bnode
              17
              (bnode
                 12
                 (bnode 9 # #)
                 (bnode 14 # #))
              (bnode
                 23
                 (bnode 19 # #)
                 #))
           (bnode
              72
              (bnode 54 # #)
              (bnode 76 # #))
     in bt_shape t).
              