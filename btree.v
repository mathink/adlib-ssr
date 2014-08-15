(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/15 12:52:48> *)
(**
 * Binary tree on Coq with SSReflect
 *)

(* SSReflect *)
Require Import
  Ssreflect.ssreflect
  Ssreflect.ssrfun
  Ssreflect.ssrbool
  Ssreflect.eqtype
  Ssreflect.seq
  Ssreflect.ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
 ** Definitions of Type of Binary-tree *)
Inductive btree (T: Type) :=
| bleaf
| bnode (x: T)(tl tr: btree T).
Arguments bleaf {T}.
Arguments bnode {T}(x tl tr).

Notation "#" := bleaf.
Notation "tl -< x >- tr" := (bnode x tl tr) (at level 65, no associativity).

Section BinaryTree.

  Variable (T: Type).
  Implicit Type (t: btree T).

  Fixpoint size t : nat :=
    if t is tl -< x >- tr
    then (size tl + size tr).+1
    else 0.

  Lemma size0bleaf t:
    size t = 0 -> t = #.
  Proof.
    by case: t.
  Qed.
  
  Definition bleafSp t := size t == 0.

  Lemma bleafSP t:
    reflect (t = #) (bleafSp t).
  Proof.
    by case: t; constructor.
  Qed.


  Fixpoint height t : nat :=
    if t is tl -< x >- tr 
    then let hl := height tl in
         let hr := height tr in
         (maxn hl hr).+1
    else 0.

  Lemma height0bleaf t:
    height t = 0 -> t = #.
  Proof.
    by case: t.
  Qed.

  Definition bleafHp t := height t == 0.

  Lemma bleafHP t:
    reflect (t = #) (bleafHp t).
  Proof.
    by case: t; constructor.
  Qed.

  Lemma bleafSH t:
    bleafSp t == bleafHp t.
  Proof.
    by case: t.
  Qed.  
  

  Fixpoint revtree t : btree T :=
    if t is tl -< x >- tr
    then revtree tr -< x >- revtree tl
    else #.

  Lemma revtree_idempotent t:
    revtree (revtree t) = t.
  Proof.
    by elim: t => [| x /= tl -> tr ->].
  Qed.

  Lemma revtree_size t :
    size (revtree t) = size t.
  Proof.
    by elim: t => [//= | _ /= tl -> tr ->]; rewrite addnC.
  Qed.

  Lemma revtree_height t:
    height (revtree t) = height t.
  Proof.
    by elim: t => [//= | _ /= tl -> tr -> ]; rewrite maxnC.
  Qed.

  
  Fixpoint flatten t : seq T :=
    if t is tl -< x >- tr
    then flatten tl ++ [:: x & flatten tr ]
    else [::].

  Lemma flatten_size t:
    seq.size (flatten t) = size t.
  Proof.
    elim: t => [//= | x /= tl IHl tr IHr].
    by rewrite seq.size_cat /= addnS IHl IHr.
  Qed.

  Lemma flatten_rev t:
    rev (flatten t) = flatten (revtree t).
  Proof.
    elim: t => [//= | x /= tl IHl tr IHr].
    by rewrite rev_cat rev_cons cat_rcons IHl IHr.
  Qed.

  Fixpoint flatten_m t : seq T :=
    if t is tl -< x >- tr
    then [:: x & flatten_m tl ++ flatten_m tr ]
    else [::].
  
  Fixpoint flatten_r t : seq T :=
    if t is tl -< x >- tr
    then flatten_r tr ++ [:: x & flatten_r tl ]
    else [::].
  
  Definition flatten_l := flatten.

  Lemma flatten_lr t:
    rev (flatten_l t) = flatten_r t.
  Proof.
    elim: t => [//= | x /= tl IHl tr IHr].
    by rewrite rev_cat rev_cons cat_rcons IHl IHr.
  Qed.


  Section BtreePred.

    Variable (p: pred T).

    Fixpoint count t: nat :=
      if t is tl -< x >- tr
      then let: cl := count tl in
           let: cr := count tr in
           p x + cl + cr
      else 0.

    Lemma flatten_count t:
      seq.count p (flatten t) = count t.
    Proof.
      elim: t => [//= | /= x tl IHl tr IHr].
      by rewrite count_cat /= addnCA IHl IHr addnA.
    Qed.


    Fixpoint has t: bool :=
      if t is tl -< x >- tr
      then p x || has tl || has tr 
      else false.

    Lemma flatten_has t:
      seq.has p (flatten t) = has t.
    Proof.
      elim: t => [//= | /= x tl IHl tr IHr].
      by rewrite has_cat /= orbCA IHl IHr orbA.
    Qed.

    Lemma has_bleaf:
      has # = false.
    Proof.
      by [].
    Qed.

    Lemma has_bnode1 x:
      has (#-< x >-#) = p x.
    Proof.
      by rewrite /= 2!orbF.
    Qed.


    Fixpoint all t: bool :=
      if t is tl -< x >- tr
      then p x && all tl && all tr
      else true.

    Lemma flatten_all t:
      seq.all p (flatten t) = all t.

    Proof.
      elim: t => [//= | /= x tl IHl tr IHr].
      by rewrite all_cat /= andbCA IHl IHr andbA.
    Qed.

    Lemma all_bleaf:
      all # = true.
    Proof.
      by [].
    Qed.

    Lemma all_bnode1 x:
      all (#-< x >-#) = p x.
    Proof.
      by rewrite /= 2!andbT.
    Qed.    


    Lemma has_count t:
      has t = (0 < count t).
    Proof.
      (* rewrite -flatten_count -flatten_has; apply seq.has_count. *)
      elim: t => [//= | /= x tl IHl tr IHr].
      by rewrite 2!addn_gt0 -IHl -IHr lt0b.
    Qed.

    Lemma count_size t:
      count t <= size t.
    Proof.
      (* rewrite -flatten_count -flatten_size; apply seq.count_size. *)
      elim: t => [//= | /= x tl IHl tr IHr].
      by rewrite -addn1 -addnA [_ + 1]addnC; apply: leq_add (leq_b1 _) (leq_add _ _).
    Qed.
    
    Lemma leq_add_eq m1 m2 n1 n2:
      m1 <= n1 -> m2 <= n2 ->
      (m1 == n1) && (m2 == n2) = (m1 + m2 == n1 + n2).
    Proof.
      rewrite leq_eqVlt; move=> /orP [/eqP -> /=|]; first by rewrite eqn_add2l eq_refl.
      move=> Hlt Hle; rewrite [m1 == n1]eq_sym (gtn_eqF Hlt) /=.
      have H: m1 + m2 < n1 + n2; last by rewrite [_ == _]eq_sym (gtn_eqF H).
      apply leq_ltn_trans with (m1 + n2); first by rewrite leq_add2l.
      by rewrite ltn_add2r.
    Qed.

    Lemma all_count t:
      all t = (count t == size t).
    Proof.
      (* rewrite -flatten_count -flatten_size -flatten_all; apply seq.all_count. *)
      elim: t => [//= | /= x tl IHl tr IHr].
      rewrite -addn1 -addnA [_ + 1]addnC.
      case: (p x) => //=.
      - by rewrite IHl IHr eqn_add2l leq_add_eq; try apply count_size.
      - rewrite add0n add1n.
        have Hlt: (count tl + count tr < (size tl + size tr).+1);
          last by rewrite [_ == _]eq_sym (gtn_eqF Hlt).
        by rewrite ltnS; apply leq_add; apply count_size.
    Qed.

  End BtreePred.

  Lemma eq_count p1 p2:
    p1 =1 p2 -> count p1 =1 count p2.
  Proof.
    move=> Heq; elim=> [//= | /= x tl -> tr ->].
    by rewrite Heq.
  Qed.

  Lemma eq_has p1 p2:
    p1 =1 p2 -> has p1 =1 has p2.
  Proof.
    move=> Heq; elim=> [//= | /= x tl -> tr ->].
    by rewrite Heq.
  Qed.

  Lemma eq_all p1 p2:
    p1 =1 p2 -> all p1 =1 all p2.
  Proof.
    move=> Heq; elim=> [//= | /= x tl -> tr ->].
    by rewrite Heq.
  Qed.

  
  (* traverse tree *)
  Inductive path :=
  | path_here
  | path_left of path
  | path_right of path.

  Notation "><" := path_here.
  Notation "<< p" := (path_left p) (at level 45, right associativity).
  Notation ">> p" := (path_right p) (at level 45, right associativity).

  Implicit Type (p: path).
  
  Fixpoint length p: nat :=
    match p with
      | >< => 0
      | << p' | >> p' => (length p').+1
    end.

  Fixpoint traverse p t: option T :=
    if t is tl -< x >- tr
    then match p with
           | >< => Some x
           | << p' => traverse p' tl
           | >> p' => traverse p' tr
         end
    else None.

  Lemma traverse_height p t:
    height t < length p -> traverse p t = None.
  Proof.
    by elim: p t => [//= | p IHp | p IHp] [//= | x tl tr] /=;
     rewrite ltnS gtn_max; move=> /andP [Hltl Hltr]; apply IHp.
  Qed.

End BinaryTree.

Arguments bleafSP {T t}.
Arguments bleafHP {T t}.

Prenex Implicits size bleafSP bleafHP revtree flatten traverse.
Prenex Implicits count all has.

(** 
 ** Constructing Instanse of [eqtype] for [btree]
 *)
Section EqBtree.

  Variable (T: eqType).

  Implicit Type t: btree T.

  (* Define decision procedure for equality of btree *)
  Fixpoint eqbtree t1 t2 :=
    match t1, t2 with
      | #, # => true
      | tl1 -< x1 >- tr1, tl2 -< x2 >- tr2
        => (x1 == x2) && (eqbtree tl1 tl2) && (eqbtree tr1 tr2)
      | _, _ => false
    end.

  (* Prove it indeed compute equality *)
  Lemma eqbtreeP: Equality.axiom eqbtree.
  Proof.
    rewrite /Equality.axiom.
    elim=> [| x1 tl1 IHl1 tr1 IHr1] [| x2 tl2 tr2] /=; try by constructor.
    case: (x1 =P x2) => [<- | Hneqx] /=.
    - case: (IHl1 tl2) => [<- | Hneql] /=.
      + case: (IHr1 tr2) => [<- | Hneqr] /=; try by constructor.
        by right; move=> [Heqr]; apply: Hneqr.
      + by right; move=> [Heql _]; apply Hneql.
    - by right; move=> [Heqx _ _]; apply Hneqx.
  Defined.

  (* Canonicalize (?) *)
  Canonical btree_eqMixin := EqMixin eqbtreeP.
  Canonical btree_eqType := Eval hnf in EqType (btree T) btree_eqMixin.

  (* Identifies eqbtree as eq_op (==) *)
  Lemma eqbtreeE: eqbtree = eq_op.
  Proof.
    by [].
  Qed.

  (* destructuring equality *)
  Lemma eqbtree_btnode x1 x2 tl1 tl2 tr1 tr2:
    (tl1 -< x1 >- tr1) == (tl2 -< x2 >- tr2) = (x1 == x2) && (tl1 == tl2) && (tr1 == tr2).
  Proof.
    by [].
  Qed.


  (* Regard Binary-tree as container *)
  Fixpoint mem_btree (t: btree T): pred T :=
    if t is tl -< x >- tr
    then xpredU1 x (xpredU (mem_btree tl) (mem_btree tr))
    else xpred0.

  (* Define constrained btree ; source types are eqtype  *)
  Definition eqbtree_class := btree T.
  Identity Coercion btree_of_eqbtree: eqbtree_class >-> btree.

  (* Predicate *)
  Coercion pred_of_eq_btree (t : eqbtree_class) : pred_class := [eta mem_btree t].
  Canonical btree_predType := @mkPredType T (btree T) pred_of_eq_btree.
  Canonical mem_btree_predType := mkPredType mem_btree.

  
  (* Lemma about mem_btree *)
  Lemma in_bnode a x tl tr:
    (a \in tl -< x >- tr) = (a == x) || (a \in tl) || (a \in tr).
  Proof.
    by rewrite /= -orbA.
  Qed.

  Lemma in_bleaf a:
    (a \in #) = false.
  Proof.
    by [].
  Qed.

  Lemma mem_bnode1 a x:
    (a \in #-< x >-#) = (a == x).
  Proof.
    by rewrite in_bnode /= 2!orbF.
  Qed.

  
  (* Somebody sais that 'to be repeated after the Section discharge.'. *)
  Let inE := (mem_bnode1, in_bnode, inE).

  Lemma mem_root x tl tr:
    x \in tl -< x >- tr.
  Proof.
    (* Check predU1l. *)
    (* predU1l *)
    (*      : forall (T : eqType) (x y : T) (b : bool), x = y -> (x == y) || b *)
    exact: predU1l.
  Qed.

  Section Preds.

    Variable (p: pred T).
    
    Lemma hasP t:
      reflect (exists2 x, x \in t & p x) (has p t).
    Proof.
      elim: t => [| /= x tl IHl tr IHr]; first by right; case.
      case Heqpx: (p x) => /=; first by left; exists x; rewrite ?mem_root.
      evar (P:Prop); apply: iffP; first exact: P.
      - apply: orP.
        unfold P.
        case=> [H | H].
        by case: (elimT IHl H) => [y Hin Hp]; exists y; rewrite ?inE ?Hin 1?orbAC 1?orbC.
        by case: (elimT IHr H) => [y Hin Hp]; exists y; rewrite ?inE ?Hin 1?orbC.
      - unfold P.
        move=> [y Hin Hp]; rewrite in_bnode orbC in Hin; move: Hin => /or3P [Hin | Heq | Hin].
        + by right; apply (introT IHr); exists y.
        + by move: Heq Hp => /eqP ->; rewrite Heqpx.
        + by left; apply (introT IHl); exists y.
    Qed.

    Lemma hasPn t:
      reflect (forall x, x \in t -> ~~ p x) (~~ has p t).
    Proof.
      apply: (iffP idP) => [Hnhas | Himp] => [x Hin|].
      - by apply: contra Hnhas => Hhas; apply /hasP; exists x. 
      - apply /hasP => [[x Hin]]; apply /negP; exact: Himp.
    Qed.

    Lemma allP t:
      reflect (forall x, x \in t -> p x) (all p t).
    Proof.
      elim: t => [| /= x tl IHl tr IHr]; first by left.
      rewrite -andbA andbC; case: IHl => /= IHl; last right=> H.
      - case: IHr => /= IHr; last right=> H.
        + apply: (iffP idP) => [Hp y|]; last by apply; exact: mem_root.
          rewrite /= in_bnode orbC orbCA.
            by case/predU1P => [-> | /orP [Hy|Hy]]; auto.
        + by apply IHr; move=> y Hin; apply H; rewrite in_bnode orbC Hin.
      - by apply IHl; move=> y Hin; apply H; rewrite in_bnode orbAC orbC Hin.
    Qed.

    Lemma allPn t:
      reflect (exists2 x, x \in t & ~~ p x) (~~ all p t).
    Proof.
      elim: t => [//= | /= x tl IHl tr IHr]; first by right=> [[x Hin Hp]].
      rewrite andbC negb_and; case: IHr => IHr /=.
      - by left; case: IHr => [y Hin Hnp]; exists y; rewrite ?in_bnode 1?orbC ?Hin.
      - rewrite andbC negb_and; case: IHl => IHl /=.
        + by left; case: IHl => [y Hin Hnp]; exists y; rewrite ?in_bnode 1?orbAC 1?orbC ?Hin.
        + apply: (iffP idP) => [Hnp | [y]]; first by exists x; rewrite ?mem_root.
          rewrite in_bnode -orbA; move=> /or3P [/eqP -> //= | Hin Hnp | Hin Hnp]; apply/negP.
          * by case: IHl; exists y.
          * by case: IHr; exists y.
    Qed.


  End Preds.

  (* TODO: EqIn *)
  Section EqIn.
    
    Variables (p1 p2: pred T).

    Lemma eq_in_count t:
      {in t, p1 =1 p2 } -> count p1 t = count p2 t.
    Proof.
      elim: t => [//= | /= x tl IHl tr IHr].
      move=> Heq.
      rewrite Heq ?IHl ?IHr //=; last exact: mem_root.
      - by move=> y Hin /=; apply Heq; rewrite inE orbC Hin.
      - by move=> y Hin /=; apply Heq; rewrite inE orbAC orbC Hin.
    Qed.

    Lemma eq_in_all t:
      {in t, p1 =1 p2 } -> all p1 t = all p2 t.
    Proof.
      by move=> Heq ; rewrite 2!all_count eq_in_count.
    Qed.

    Lemma eq_in_has t:
      {in t, p1 =1 p2 } -> has p1 t = has p2 t.
    Proof.
      by move=> Heq ; rewrite 2!has_count eq_in_count.
    Qed.

    
    Lemma sub_all:
      subpred p1 p2 ->
      forall t, all p1 t -> all p2 t.
    Proof.
      move=> Hsub; elim=> [//=|/= x tl IHl tr IHr].
      rewrite -!andbA.
      move=> /and3P [Hp Hal Har].
      apply/and3P; repeat split; first by apply Hsub.
      - by apply IHl.
      - by apply IHr.
    Qed.

  End EqIn.

  
    
  (* Locate "=i". *)
  (* Notation            Scope      *)
  (* "A =i B" := eq_mem (mem A) (mem B) *)
  (*                       : type_scope *)
  (*                       (default interpretation) *)
  (* Locate "^~". *)
  (* Notation            Scope      *)
  (* "f ^~ y" := fun x => f x y     : fun_scope *)
  (*                       (default interpretation) *)
  
  Lemma eq_has_r t1 t2:
    t1 =i t2 -> has^~ t1 =1 has^~ t2.
  Proof.
    by move=> Heqi p; apply/hasP/hasP;
      move => [x Hin Hp]; exists x; rewrite // ?Heqi // -?Heqi.
  Qed.

  Lemma eq_all_r t1 t2:
    t1 =i t2 -> all^~ t1 =1 all^~ t2.
  Proof.
    by move=> Heqi p; apply/allP/allP;
      move => Hp x Hin //; apply Hp; rewrite // ?Heqi // -?Heqi.
  Qed.

  Lemma has_sym t1 t2:
    has (mem t1) t2 = has (mem t2) t1.
  Proof.
    by apply /hasP/hasP => [] /= [x Hin Hp]; exists x.
  Qed.

  Lemma has_pred1 x t:
    has (pred1 x) t = (x \in t).
  Proof.
    by rewrite -(eq_has (mem_bnode1^~ x)) -has_sym /= 2!orbF.
  Qed.

  Lemma mem_revtree t:
    revtree t =i t.
  Proof.
    elim: t => [//= | /= x tl IHl tr IHr] y.
    by rewrite 2!in_bnode IHl IHr orbAC.
  Qed.

  
  Notation count_mem x := (count (pred1 x)).

  Lemma count_memPn a t:
    reflect (count_mem a t = 0) (a \notin t).
  Proof.
    by rewrite -has_pred1 has_count -eqn0Ngt; apply eqP.
  Qed.


  Lemma mem_flatten a t:
    (a \in t) = (a \in flatten t).
  Proof.
    elim: t => [//= | /= x tl IHl tr IHr].
      by rewrite mem_cat in_cons in_bnode IHl IHr orbCA orbA.
  Qed.

  Lemma bleaf_flatten_nil t:
    (t == #) = (flatten t == [::]).
  Proof.
    case: t => //= x tl tr.
    case: (flatten tl) => //=.
  Qed.

  (* Uniqueness *)
  Fixpoint uniq t: bool :=
    if t is tl -< x >- tr
    then (x \notin tl) && (uniq tl)
           && (x \notin tr) && (uniq tr)
           && (all (negb \o mem tr) tl)
           && (all (negb \o mem tl) tr)
    else true.

  Lemma count_uniq_mem t a:
    uniq t -> count_mem a t = (a \in t).
  Proof.
    elim: t => [//= | /= x tl IHl tr IHr].
    rewrite -4!andbA.
    move=> /and3P [/negbTE Hninl /IHl->{IHl}
                   /and4P [/negbTE Hninr /IHr->{IHr} Hrl Hlr]].
    rewrite in_bnode [x == a]eq_sym; case: eqP => [-> | Hneq] /=;
      first by rewrite Hninl Hninr //=.
    rewrite add0n.
    case Haninl: (a \in tl) => //=.
    move: Hrl => /allP H.
    move: (H a Haninl) => /= /negbTE -> //=.
  Qed.

  Definition app_fst {A A' B: Type}(f: A -> A')(p: A * B) := (f p.1, p.2).
  Arguments app_fst A A' B f / p.
  Notation "f ^1 p" := (app_fst f p) (at level 3, left associativity).

  Definition app_snd {A B B': Type}(f: B -> B')(p: A * B) := (p.1, f p.2).
  Arguments app_snd A B B' f / p.
  Notation "f ^2 p" := (app_snd f p) (at level 3, left associativity).

  (* lend & ren *)
  (* Temp *)
  Fixpoint lend a t: T :=
    if t is tl -< x >- tr
    then lend x tl
    else a.
  
  Fixpoint rend t a: T :=
    if t is tl -< x >- tr
    then rend tr x
    else a.

  Lemma lend_rev_rend a t:
    lend a t = rend (revtree t) a.
  Proof.
      by elim: t a => [//=|/= x tl IHl tr ?] a; rewrite IHl.
  Qed.

  Lemma mem_lend a t:
    (lend a t == a) || (lend a t \in t).
  Proof.
    elim: t a => [//=|/= x tl IHl tr ?] a.
    - by apply/orP; left.
    - apply/orP; right.
      rewrite in_bnode; apply/orP; left; apply/orP.
      move: (IHl x) => /orP [/eqP-> | Hin]; by [left | right].
  Qed.

  Lemma mem_rend t a:
    (rend t a == a) || (rend t a \in t).
  Proof.
    elim: t a => [//=|/= x tl ? tr IHr] a.
    - by apply/orP; left.
    - apply/orP; right.
      rewrite in_bnode orbAC; apply/orP; left; apply/orP.
      move: (IHr x) => /orP [/eqP-> | Hin]; by [left | right].
  Qed.

  (* temp *)
  Implicit Type (s: seq T).

  Notation rhead s a := (last a s).
  
  Fixpoint rbehead s: seq T :=
    if s is x :: s'
    then if s' is [::] then [::]
         else x :: rbehead s'
    else [::].

  Lemma rbehead_cons x y s:
    rbehead (x :: y :: s) = x :: (rbehead (y :: s)).
  Proof.
      by [].
  Qed.

  Lemma rbehead_cat_cons s1 x s2:
    rbehead (s1 ++ x :: s2) = s1 ++ rbehead (x :: s2).
  Proof.
    elim: s1 s2 x => [//=|/= h1 s1 IHs] [| h2 s2] x //=.
    - rewrite cats0; elim: s1 {IHs} h1 => //= h1' s1 IH1 h1. 
        by rewrite IH1. 
    - rewrite IHs.
      elim: s1 {IHs} h1 => //= h1' s1 IH1 h1. 
  Qed.

  Lemma mem_rbehead a s:
    a \in (rbehead s) -> a \in s.
  Proof.
    elim: s a => [//=| h s IHs] a /=.
    move: IHs; remember (rbehead s).
    move: Heql; case: s => // h' s Heq IH.
    rewrite in_cons => /orP [/eqP-> | Hin].
    - by rewrite in_cons; apply/orP; left.
    - by rewrite in_cons; apply/orP; right; apply IH.
  Qed.      


  Lemma head_cat_cons a x s1 s2:
    head a (s1 ++ x :: s2) = head a (rcons s1 x).
  Proof.
    move: s1 => [|] //=.
  Qed.
  
  Lemma lend_flatten_head a t:
    lend a t = head a (flatten t).
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
      by rewrite head_cat_cons headI /= IHl.
  Qed.      

  Lemma rend_flatten_rhead t a:
    rend t a =  rhead (flatten t) a.
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
      by rewrite last_cat /= IHr.
  Qed.      


  Fixpoint lend_remove a t: T * btree T :=
    if t is tl -< x >- tr
    then if tl is # then (x, tr)
         else let (node, t') := lend_remove x tl in
              (node , t' -< x >- tr)
    else (a, #).

  Fixpoint rend_remove t a: btree T * T :=
    if t is tl -< x >- tr
    then if tr is # then (tl, x)
         else let (t', node) := rend_remove tr x in
              (tl -< x >- t', node)
    else (#, a).

  Definition swap {A B: Type}(p: A * B): B * A := (p.2,p.1).
  Arguments swap A B / p.

  Lemma swap_idempotent {A B: Type}(p: A * B):
    swap (swap p) = p.
  Proof.
    case: p => //.
  Qed.      

  Lemma swap_flip {A B: Type}(p: A * B) q:
    p = swap q -> swap p = q.
  Proof.
    move=> ->; apply swap_idempotent.
  Qed.
  
  Lemma swap_app_fst {A A' B: Type}(f: A -> A')(p: A*B):
    swap (f ^1 p) = f ^2 (swap p).
  Proof.
    by [].
  Qed.

  Lemma swap_app_snd {A B B': Type}(f: B -> B')(p: A*B):
    swap (f ^2 p) = f ^1 (swap p).
  Proof.
    by [].
  Qed.

  Lemma lend_remove_revtree a t:
    lend_remove a (revtree t) = swap (revtree^1 (rend_remove t a)).
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
    rewrite IHr => /=.
    remember (rend_remove tr x).
    destruct p => /= {IHl IHr}.
    move: tr Heqp => [] //=.
  Qed.

  Lemma rend_remove_revtree t a:
    rend_remove (revtree t) a = swap (revtree^2 (lend_remove a t)).
  Proof.
    rewrite -{2}[t]revtree_idempotent swap_app_snd lend_remove_revtree swap_idempotent /= revtree_idempotent.
    by case: (rend_remove (revtree t) a) => //.
  Qed.  

  Lemma lend_remove_lend a t:
    (lend_remove a t).1 = lend a t.
  Proof.
    elim: t a => [//=|/= x tl IHl tr ?] a.
    rewrite -IHl.
    remember (lend_remove x tl) as lrxtl.
    destruct lrxtl.
    clear IHl; case: tl Heqlrxtl => //=.
      by case=> ->.
  Qed.

  Lemma rend_remove_rend t a:
    (rend_remove t a).2 = rend t a.
  Proof.
    elim: t a => [//=|/= x tl ? tr IHr] a.
    rewrite -IHr.
    remember (rend_remove tr x) as rrxtr.
    destruct rrxtr.
    clear IHr; case: tr Heqrrxtr => //=.
      by case=> _ ->.
  Qed.

  Lemma lend_remove_behead a t:
    flatten (lend_remove a t).2 = behead (flatten t).
  Proof.
    elim: t a => [//=|/= x tl IHl tr ?] _.
    move: (IHl x) => {IHl}; case (lend_remove x tl) => /= y t.
    case: tl => //= z tl tr' ->.
    case: (flatten tl) => //=.
  Qed.

  Lemma lend_remove_head a t:
    (lend_remove a t).1 = head a (flatten t).
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
    move: (IHl x) => {IHl}; case (lend_remove x tl) => /= y t.
    case: tl => //= z tl tr' ->.
    case: (flatten tl) => //=.
  Qed.
  
  Lemma lend_remove_head_behead a t:
    flatten^2 (lend_remove a t) = (head a (flatten t), behead (flatten t)).
  Proof.
      by rewrite /= lend_remove_head lend_remove_behead.
  Qed.

  Lemma rend_remove_rhead t a:
    (rend_remove t a).2 = rhead (flatten t) a.
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
    move: (IHr x) => {IHr}; case (rend_remove tr x) => /= y t ->.
    case: tr => [/=|/= z tl' tr]; first by rewrite last_cat.
      by rewrite /= !last_cat /= !last_cat /=.
  Qed.

  Lemma rend_remove_rbehead t a:
    flatten (rend_remove t a).1 = rbehead (flatten t).
  Proof.
    elim: t a => [//=|/= x tl IHl tr IHr] a.
    rewrite rbehead_cat_cons.
    move: (IHr x) => {IHr}; case (rend_remove tr x) => /= y t.
    case: tr => [/=|/= z tl' tr]; first by rewrite cats0.
    move=> -> //=.
    remember (flatten tl' ++ z :: flatten tr) as l.
    elim: l Heql => //=.
    case: (flatten tl') => //=.
  Qed.

  Lemma rend_remove_rhead_rbehead t a:
    flatten^1 (rend_remove t a) = (rbehead (flatten t),rhead (flatten t) a).
  Proof.
      by rewrite /= rend_remove_rhead rend_remove_rbehead.
  Qed.


  Lemma mem_lend_remove x a t:
    x \in (lend_remove a t).2 -> x \in t.
  Proof.
    elim: t a => [//=|/= y tl IHl tr IHr] a.
    move: (IHl y) => {IHl IHr a}.
    case: tl => [//= ? Hin | z tl t H Hin].
    - by rewrite in_bnode -orbA orbCA; apply/orP; right; apply/orP; right.
    - remember (lend_remove y (tl -< z >- t)).
      destruct p.
      rewrite in_bnode -orbA; apply/or3P.
      move: Hin; rewrite/= in_bnode -orbA => /or3P [/eqP<- | Hin | Hin].
      + by apply Or31.
      + by apply Or32, H.
      + by apply Or33.
  Qed.

  Lemma mem_rend_remove x t a:
    x \in (rend_remove t a).1 -> x \in t.
  Proof.
    elim: t a => [//=|/= y tl IHl tr IHr] a.
    move: (IHr y) => {IHl IHr a}.
    case: tr => [//= ? Hin | z t tr H Hin].
    - by rewrite in_bnode -orbA orbCA; apply/orP; left.
    - remember (rend_remove (t -< z >- tr) y).
      destruct p.
      rewrite in_bnode -orbA; apply/or3P.
      move: Hin; rewrite/= in_bnode -orbA => /or3P [/eqP<- | Hin | Hin].
      + by apply Or31.
      + by apply Or32.
      + by apply Or33, H.
  Qed.

  Definition rem_root_l t: btree T :=
    if t is tl -< x >- tr
    then let (node, tr') := lend_remove x tr in
         tl -< node >- tr'
    else #.

  Definition rem_root_r t: btree T :=
    if t is tl -< x >- tr
    then let (tl', node) := rend_remove tl x in
         tl' -< node >- tr
    else #.

  Lemma rem_root_l_revtree t:
    rem_root_l (revtree t) = revtree (rem_root_r t).
  Proof.
    elim: t => [//=|/= y tl IHl tr IHr].
    rewrite lend_remove_revtree /=.
    by case: (rend_remove tl y) => //.
  Qed.

  Lemma rem_root_r_revtree t:
    rem_root_r (revtree t) = revtree (rem_root_l t).
  Proof.
    by rewrite -{2}[t]revtree_idempotent rem_root_l_revtree revtree_idempotent.
  Qed.

  Definition lend_merge a tl tr: btree T :=
    if tr is # then tl
    else let (node, tr') := lend_remove a tr in
         tl -< node >- tr'.

  Definition rend_merge tl tr a: btree T :=
    if tl is # then tr
    else let (tl', node) := rend_remove tl a in
         tl' -< node >- tr.

  Lemma lend_merge_revtree a tl tr:
    lend_merge a (revtree tl) (revtree tr)
    = revtree (rend_merge tr tl a).
  Proof.
    case: tr => [//=| x t tr /=].
    rewrite lend_remove_revtree /=.
    remember (rend_remove tr x).
    destruct p => /=.
    move: tr Heqp => [] //=.
  Qed.    

End EqBtree.

Definition inE := (mem_bnode1, in_bnode, inE).

Require Import Wf_nat Recdef MathComp.div.


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


Section AVL.

  Variable (T: Type).
  Implicit Types (t: btree T).

  Fixpoint avl t: bool :=
    if t is tl -< x >- tr
    then let: hl := height tl in
         let: hr := height tr in
         (hl - hr <= 1) && (hr - hl <= 1) && (avl tl) && (avl tr)
    else true.


End AVL.

Eval compute in (avl ((#-< 1 >-#) -< 2 >- (#-< 3 >-#))).
Eval compute in (avl (((#-< 2 >-#) -< 1 >- (#-< 3 >-#))-< 0 >- (#-< 4 >-#))).
Eval compute in (map n2pos [:: 0 ; 1 ; 2 ; 3;  4 ]).
Eval compute in (let t := (((#-< 3 >-#) -< 1 >- (#-< 4 >-#))-< 0 >- (#-< 2 >-#)) in (btget t (pos_l (pos_r pos_on)))).
Eval compute in (let t := (((#-< 3 >-#) -< 1 >- (#-< 4 >-#))-< 0 >- (#-< 2 >-#)) in (map (btget t \o n2pos) [:: 0 ; 1 ; 2 ; 3;  4 ])).
(* Eval compute in (btget ((#-< 1 >-#) -< 2 >- (#-< 3 >-#)) pos_on). *)
(* Eval compute in (btget ((#-< 1 >-#) -< 2 >- (#-< 3 >-#)) (pos_l pos_on)). *)
(* Eval compute in (btget ((#-< 1 >-#) -< 2 >- (#-< 3 >-#)) (n2pos 0)). *)

