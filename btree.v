(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/4 18:9:23> *)
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
 ** Constructing Instanse of eqtype for [btree]
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

  
  (* lend & rend *)
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


    Lemma rbehead_cat_cons s1 x s2:
      rbehead (s1 ++ x :: s2) = s1 ++ rbehead (x :: s2).
    Proof.
      elim: s1 s2 x => [//=|/= h1 s1 IHs] [| h2 s2] x //=.
      - rewrite cats0; elim: s1 {IHs} h1 => //= h1' s1 IH1 h1. 
        by rewrite IH1. 
      - rewrite IHs.
        elim: s1 {IHs} h1 => //= h1' s1 IH1 h1. 
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

    Lemma rend_flatten_rhead a t:
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

    Fixpoint rend_remove a t: T * btree T :=
      if t is tl -< x >- tr
      then if tr is # then (x, tl)
           else let (node, t') := rend_remove x tr in
                (node , tl -< x >- t')
      else (a, #).


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
    
    Notation "f ^1" := (fun x => (f x.1, x.2)) (at level 3, left associativity).
    Notation "f ^2" := (fun x => (x.1, f x.2)) (at level 3, left associativity).
    Lemma lend_remove_head_behead a t:
      flatten^2 (lend_remove a t) = (head a (flatten t), behead (flatten t)).
    Proof.
      by rewrite /= lend_remove_head lend_remove_behead.
    Qed.

    Lemma rend_remove_rhead a t:
      (rend_remove a t).1 = rhead (flatten t) a.
    Proof.
      elim: t a => [//=|/= x tl IHl tr IHr] a.
      move: (IHr x) => {IHr}; case (rend_remove x tr) => /= y t ->.
      case: tr => [/=|/= z tl' tr]; first by rewrite last_cat.
      by rewrite /= !last_cat /= !last_cat /=.
    Qed.

    Lemma rend_remove_rbehead a t:
      flatten (rend_remove a t).2 = rbehead (flatten t).
    Proof.
      elim: t a => [//=|/= x tl IHl tr IHr] a.
      rewrite rbehead_cat_cons.
      move: (IHr x) => {IHr}; case (rend_remove x tr) => /= y t.
      case: tr => [/=|/= z tl' tr]; first by rewrite cats0.
      move=> -> //=.
      remember (flatten tl' ++ z :: flatten tr) as l.
      elim: l Heql => //=.
      case: (flatten tl') => //=.
    Qed.

    Lemma rend_remove_rhead_rbehead a t:
      flatten^2 (rend_remove a t) = (rhead (flatten t) a, rbehead (flatten t)).
    Proof.
      by rewrite /= rend_remove_rhead rend_remove_rbehead.
    Qed.

End EqBtree.

Definition inE := (mem_bnode1, in_bnode, inE).
