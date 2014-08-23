(* -*- mode: coq -*- *)
(* Time-stamp: <2014/8/23 3:6:41> *)
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

  Lemma revtree_involutive t:
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

  Fixpoint walk t s: seq T :=
    if t is tl -< x >- tr
    then walk tl (x :: walk tr s)
    else s.
  Functional Scheme walk_ind := Induction for walk Sort Prop.

  Definition flatten t := walk t [::].
  Arguments flatten / t.
  
  Lemma walk_size t s:
    seq.size (walk t s) = size t + seq.size s.
  Proof.
    elim: t s => [//= | x /= tl IHl tr IHr] s.
    by rewrite IHl /= IHr -addn1 -[(_+_).+1]addn1 [(_+1)+_]addnAC !addnA.
  Qed.

  Lemma flatten_size t:
    seq.size (flatten t) = size t.
  Proof.
    by rewrite walk_size /= addn0.
  Qed.

  Lemma walk_cat t s1 s2:
    walk t s1 ++ s2 = walk t (s1 ++ s2).
  Proof.
    elim: t s1 s2 => [//= | x /= tl IHl tr IHr] s1 s2.
    by rewrite IHl /= IHr /=.
  Qed.

  Lemma walk_rev t s:
    rev (walk t s) = rev s ++ walk (revtree t) [::].
  Proof.
    elim: t s => [//= | x /= tl IHl tr IHr] s.
    - by rewrite cats0.
    - by rewrite IHl /= rev_cons cat_rcons IHr -catA walk_cat /=.
  Qed.

  Lemma flatten_rev t:
    rev (flatten t) = flatten (revtree t).
  Proof.
    by rewrite walk_rev /=.
  Qed.

  Section BtreePred.

    Variable (p: pred T).

    Fixpoint count t: nat :=
      if t is tl -< x >- tr
      then let: cl := count tl in
           let: cr := count tr in
           p x + cl + cr
      else 0.

    Lemma walk_count t s:
      seq.count p (walk t s) = seq.count p s + count t.
    Proof.
      elim: t s => [//= | /= x tl IHl tr IHr] s.
      by rewrite IHl /= IHr /= addnCA -addnA addnAC.
    Qed.
    
    Lemma flatten_count t:
      seq.count p (flatten t) = count t.
    Proof.
      by rewrite walk_count /=.
    Qed.


    Fixpoint has t: bool :=
      if t is tl -< x >- tr
      then p x || has tl || has tr 
      else false.

    Lemma walk_has t s:
      seq.has p (walk t s) = seq.has p s || has t.
    Proof.
      elim: t s => [//= | /= x tl IHl tr IHr] s; first by rewrite orbF.
      by rewrite IHl /= IHr /= orbCA -orbA orbAC.
    Qed.

    Lemma flatten_has t:
      seq.has p (flatten t) = has t.
    Proof.
      by rewrite walk_has /=.
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

    Lemma walk_all t s:
      seq.all p (walk t s) = seq.all p s && all t.
    Proof.
      elim: t s => [//= | /= x tl IHl tr IHr] s; first by rewrite andbT.
      by rewrite IHl /= IHr /= andbCA -andbA andbAC.
    Qed.

    Lemma flatten_all t:
      seq.all p (flatten t) = all t.
    Proof.
      by rewrite walk_all /=.
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
  Functional Scheme traverse_ind := Induction for traverse Sort Prop.

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

  Implicit Types (t: btree T)(s: seq T).

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

  
  Lemma mem_walk a t s:
    (a \in walk t s) = (a \in t) || (a \in s).
  Proof.
    elim/walk_ind: t s / (walk t s) => t s //=.
    move=> {t} x tl tr _ Heqr Heql.
    by rewrite in_bnode /= Heql /= in_cons Heqr orbCA -!orbA.
  Qed.

  Lemma mem_flatten a t:
    (a \in flatten t) = (a \in t).
  Proof.
    by rewrite mem_walk /= in_nil orbF.
  Qed.

  Lemma size_neq s1 s2:
    seq.size s1 != seq.size s2 -> s1 != s2.
  Proof.
    elim: s1 s2 => [| h1 s1 IHs] /= [| h2 s2] //=.
    move=> /eqP Hneq; rewrite eqseq_cons negb_and;
           apply/orP; right; rewrite IHs //=.
    by apply/eqP=>Heq; apply Hneq; rewrite Heq.
  Qed.

  Lemma bleaf_walk t s:
    (walk t s == s) = (t == #). 
  Proof.
    elim/walk_ind: t s / (walk t s) => t s //=; first by rewrite ?eq_refl.
    move=> x tl tr _. 
    have Hneq: (seq.size (walk tl (x::walk tr s)) != seq.size s)
      by rewrite walk_size /= walk_size -addn1 addnAC !addnA
         -{2}[seq.size s]add0n eqn_add2r addn1 -lt0n ltn0Sn.
    by move: (size_neq Hneq); rewrite -eqbF_neg => /eqP -> //=.
  Qed.

  Lemma bleaf_flatten_nil t:
    (flatten t == [::]) = (t == #).
  Proof.
    by rewrite bleaf_walk.
  Qed.

  (* Uniqueness *)
  Fixpoint uniq t: bool :=
    if t is tl -< x >- tr
    then (x \notin tl) && (uniq tl)
           && (x \notin tr) && (uniq tr)
           && (all (negb \o mem tr) tl)
           && (all (negb \o mem tl) tr)
    else true.
  Functional Scheme uniq_ind := Induction for uniq Sort Prop.

  Lemma count_uniq_mem t a:
    uniq t -> count_mem a t = (a \in t).
  Proof.
    elim/uniq_ind: t / (uniq t) => t //=.
    move=> x tl tr _ IHl IHr; rewrite -4!andbA.
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

  
  
  (* Temp *)
  Notation rhead s a := (last a s).
  
  Fixpoint rbehead s: seq T :=
    match s with
      | [::] | [:: _] => [::]
      | x :: s' => x :: rbehead s'
    end.
  Functional Scheme rbehead_ind := Induction for rbehead Sort Prop.

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

  Lemma rbehead_rcons s x:
    rbehead (rcons s x) = s.
  Proof.
    by rewrite -cats1 rbehead_cat_cons /= cats0.
  Qed.

  Lemma mem_rbehead a s:
    a \in (rbehead s) -> a \in s.
  Proof.
    elim/rbehead_ind: s /(rbehead s) => s0 //= x s _ {s0} h t -> IH.
    rewrite in_cons=>/orP [/eqP->|Hin];
      first by rewrite in_cons; apply/orP; left.
    by apply/orP; right; apply: IH Hin.
  Qed.      

  Lemma head_cat_cons a x s1 s2:
    head a (s1 ++ x :: s2) = head a (rcons s1 x).
  Proof.
    move: s1 => [|] //=.
  Qed.
  
  Lemma head_walk_lend_head a t s:
    head a (walk t s) = lend (head a s) t.
  Proof.
    by elim/walk_ind: t s /(walk t s) => t s //.
  Qed.

  Lemma head_flatten_lend a t:
    head a (flatten t) = lend a t.
  Proof.
    by rewrite head_walk_lend_head.
  Qed.      

  Lemma rhead_walk_rhead_rend a t s:
    rhead (walk t s) a = rhead s (rend t a).
  Proof.
    move: a.
    elim/walk_ind: t s /(walk t s) => t s //= x tl tr _ IHr IHl a.
    by rewrite IHl IHr.
  Qed.
    
  Lemma rend_flatten_rhead t a:
    rhead (flatten t) a = rend t a.
  Proof.
    by rewrite rhead_walk_rhead_rend //=.
  Qed.      


  Fixpoint lend_remove a t: T * btree T :=
    if t is tl -< x >- tr
    then if tl is # then (x, tr)
         else let (node, t') := lend_remove x tl in
              (node , t' -< x >- tr)
    else (a, #).
  Functional Scheme lend_remove_ind := Induction for lend_remove Sort Prop.

  Fixpoint rend_remove t a: btree T * T :=
    if t is tl -< x >- tr
    then if tr is # then (tl, x)
         else let (t', node) := rend_remove tr x in
              (tl -< x >- t', node)
    else (#, a).
  Functional Scheme rend_remove_ind := Induction for rend_remove Sort Prop.

  Definition swap {A B: Type}(p: A * B): B * A := (p.2,p.1).
  Arguments swap A B / p.

  Lemma swap_involutive {A B: Type}(p: A * B):
    swap (swap p) = p.
  Proof.
    case: p => //.
  Qed.      

  Lemma swap_flip {A B: Type}(p: A * B) q:
    p = swap q -> swap p = q.
  Proof.
    move=> ->; apply swap_involutive.
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
    rewrite -{2}[t]revtree_involutive swap_app_snd lend_remove_revtree swap_involutive /= revtree_involutive.
    by case: (rend_remove (revtree t) a) => //.
  Qed.  

  Lemma lend_remove_lend a t:
    (lend_remove a t).1 = lend a t.
  Proof.
    elim/lend_remove_ind: a t/(lend_remove a t)=> a t // x tl tr _.
    move=> y tl' tr' -> Heq z t' Heq' /=.
    by move: Heq' Heq => -> /=.
  Qed.

  Lemma rend_remove_rend t a:
    (rend_remove t a).2 = rend t a.
  Proof.
    elim/rend_remove_ind: t a/(rend_remove t a)=> t a // x tl tr _.
    move=> y tl' tr' -> Heq z t' Heq' /=.
    by move: Heq' Heq => -> /=.
  Qed.

  Lemma behead_cat s1 s2:
    0 < seq.size s1 -> behead s1 ++ s2 = behead (s1 ++ s2).
  Proof.
    case: s1 => [| h1 s1] //=.
  Qed.

  Lemma walk_lend_remove_behead a t s:
    walk (lend_remove a t).2 s = behead (walk t [::]) ++ s.
  Proof.
    move: s.
    elim/lend_remove_ind: a t/(lend_remove a t)=> a t //= x tl tr _.
    - move=> _ s; by rewrite walk_cat //.
    - move=> y tl' tr' -> {tl} Heq node t' Heq' s.
      move: Heq' Heq => -> /= -> //=.
      by rewrite behead_cat ?walk_cat /= ?walk_cat /= ?behead_cat ?walk_cat /= ?walk_cat /= ?walk_cat //=; repeat rewrite walk_size //= addnS.
  Qed.

  Lemma flatten_lend_remove_behead a t:
    flatten (lend_remove a t).2 = behead (flatten t).
  Proof.
    by rewrite /flatten walk_lend_remove_behead cats0.
  Qed.

  Lemma lend_remove_head a t:
    (lend_remove a t).1 = head a (flatten t).
  Proof.
    by rewrite lend_remove_lend head_flatten_lend.
  Qed.
  
  Lemma lend_remove_head_behead a t node t':
    (node, t') = (lend_remove a t) ->
    (node == head a (flatten t)) && (flatten t' == behead (flatten t)).
  Proof.
    rewrite -lend_remove_head -(flatten_lend_remove_behead a)=> <- //=;
      by rewrite !eq_refl.
  Qed.

  Lemma rend_remove_rhead t a:
    (rend_remove t a).2 = rhead (flatten t) a.
  Proof.
    by rewrite rend_remove_rend rend_flatten_rhead.
  Qed.

  Lemma rbehead_cat s1 s2:
    0 < seq.size s2 -> s1 ++ rbehead s2 = rbehead (s1 ++ s2).
  Proof.
    by case: s2 => [| h2 s2] //; rewrite rbehead_cat_cons.
  Qed.

  Lemma eqseq_cat2r s s1 s2:
    (s1 ++ s == s2 ++ s) = (s1 == s2).
  Proof.
    elim: s s1 s2 => [| h s IHs] s1 s2; first by rewrite ?cats0.
    by rewrite -2!cat_rcons IHs eqseq_rcons eq_refl andbT.
  Qed.

  Lemma walk_rend_remove_rbehead t a s:
    walk (rend_remove t a).1 s = rbehead (walk t [::]) ++ s.
  Proof.
    move: s.
    elim/rend_remove_ind: t a/(rend_remove t a)=> t a //= x tl tr _.
    - by move=> _ s;
         rewrite -[[::x]]cat0s -walk_cat cats1 rbehead_rcons walk_cat//.
    - move=> y tl' tr' -> {tr} Heq node t' Heq' s.
      move: Heq' (Heq s) => -> /= ->.
      rewrite -cat_cons -walk_cat; apply/eqP; rewrite eqseq_cat2r.
      rewrite -[x :: walk _ _]cat0s -walk_cat rbehead_cat_cons.
      by rewrite -{2}[y :: _]cat0s -walk_cat -cat_cons !rbehead_cat_cons catA !walk_cat !cat0s cat_cons walk_cat cat0s.
  Qed.

  Lemma flatten_rend_remove_rbehead t a:
    flatten (rend_remove t a).1 = rbehead (flatten t).
  Proof.
    by rewrite /flatten walk_rend_remove_rbehead cats0.
  Qed.

  Lemma rend_remove_rhead_rbehead t a t' node:
    (t', node) = (rend_remove t a) ->
    (node == rhead (flatten t) a) && (flatten t' == rbehead (flatten t)).
  Proof.
    rewrite -rend_remove_rhead -(flatten_rend_remove_rbehead t a)=> <- //=;
      by rewrite !eq_refl.
  Qed.

  Lemma mem_lend_remove x a t:
    x \in (lend_remove a t).2 -> x \in t.
  Proof.
    rewrite -mem_flatten flatten_lend_remove_behead -mem_flatten.
      by apply mem_behead.
  Qed.

  Lemma mem_rend_remove x t a:
    x \in (rend_remove t a).1 -> x \in t.
  Proof.
    rewrite -mem_flatten flatten_rend_remove_rbehead -mem_flatten.
      by apply mem_rbehead.
  Qed.


  Definition rem_root_l t: btree T :=
    if t is tl -< x >- tr
    then let (node, tr') := lend_remove x tr in
         tl -< node >- tr'
    else #.
  Functional Scheme rem_root_l_ind := Induction for rem_root_l Sort Prop.
  
  Definition rem_root_r t: btree T :=
    if t is tl -< x >- tr
    then let (tl', node) := rend_remove tl x in
         tl' -< node >- tr
    else #.
  Functional Scheme rem_root_r_ind := Induction for rem_root_r Sort Prop.

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
    by rewrite -{2}[t]revtree_involutive rem_root_l_revtree revtree_involutive.
  Qed.

  Definition lend_merge a tl tr: btree T :=
    if tr is # then tl
    else let (node, tr') := lend_remove a tr in
         tl -< node >- tr'.
  Functional Scheme lend_merge_ind := Induction for lend_merge Sort Prop.

  Definition rend_merge tl tr a: btree T :=
    if tl is # then tr
    else let (tl', node) := rend_remove tl a in
         tl' -< node >- tr.
  Functional Scheme rend_merge_ind := Induction for rend_merge Sort Prop.

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
