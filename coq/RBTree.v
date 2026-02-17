(** * Functional Specification: Red-Black Tree Map

    Ported from [Rbtree/Daedalus.lean]. This module defines the pure functional
    spec against which we verify the C++ [DDL::Map<int,int>] implementation.

    The C++ code follows Okasaki's red-black tree with split rebalancing:
    [setRebalanceLeft] handles LL/LR cases, [setRebalanceRight] handles RL/RR.
    We mirror that structure here rather than using unified [balance].

    All definitions correspond 1:1 with the Lean formalization. See
    [Rbtree/Daedalus.lean] for the detailed documentation of each definition.
*)

From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.

(** ** Types *)

(** Node color. Mirrors [Node::Color] in [map.h]. *)
Inductive Color : Type :=
  | Red : Color
  | Black : Color.

(** A red-black tree storing key-value pairs. Mirrors the [Node] struct.
    - [Leaf] represents a null pointer (conventionally black).
    - [Node c l k v r] stores color, left subtree, key, value, right subtree. *)
Inductive tree (K V : Type) : Type :=
  | Leaf : tree K V
  | Node : Color -> tree K V -> K -> V -> tree K V -> tree K V.

Arguments Leaf {K V}.
Arguments Node {K V}.

(** ** Color predicates *)

(** Mirrors [Node::is_black]: empty trees (null) are black. *)
Definition is_black {K V : Type} (t : tree K V) : bool :=
  match t with
  | Leaf => true
  | Node Black _ _ _ _ => true
  | Node Red _ _ _ _ => false
  end.

(** Mirrors [Node::is_red]. *)
Definition is_red {K V : Type} (t : tree K V) : bool :=
  negb (is_black t).

(** ** Split rebalancing *)

(** Rebalance after inserting into the left subtree.
    Mirrors [Node::setRebalanceLeft] from [map.h].

    Handles LL and LR rotation cases. *)
Definition setRebalanceLeft {K V : Type}
    (c : Color) (newLeft : tree K V) (k : K) (v : V) (r : tree K V)
    : tree K V :=
  match c, newLeft with
  (* LL: left child's left child is red *)
  | Black, Node Red (Node Red a kx vx b) ky vy c1 =>
      Node Red (Node Black a kx vx b) ky vy (Node Black c1 k v r)
  (* LR: left child's right child is red *)
  | Black, Node Red a kx vx (Node Red b ky vy c1) =>
      Node Red (Node Black a kx vx b) ky vy (Node Black c1 k v r)
  (* No violation *)
  | _, _ =>
      Node c newLeft k v r
  end.

(** Rebalance after inserting into the right subtree.
    Mirrors [Node::setRebalanceRight] from [map.h].

    Handles RL and RR rotation cases. *)
Definition setRebalanceRight {K V : Type}
    (c : Color) (l : tree K V) (k : K) (v : V) (newRight : tree K V)
    : tree K V :=
  match c, newRight with
  (* RL: right child's left child is red *)
  | Black, Node Red (Node Red b ky vy c1) kz vz d =>
      Node Red (Node Black l k v b) ky vy (Node Black c1 kz vz d)
  (* RR: right child's right child is red *)
  | Black, Node Red b ky vy (Node Red c1 kz vz d) =>
      Node Red (Node Black l k v b) ky vy (Node Black c1 kz vz d)
  (* No violation *)
  | _, _ =>
      Node c l k v newRight
  end.

(** ** Core operations *)

(** Recursive insert with split rebalancing. Mirrors [Node::ins].

    Unlike Okasaki's unified [balance], uses [setRebalanceLeft] and
    [setRebalanceRight]. Updates the value when the key already exists,
    matching the C++ behavior [n->value = v]. *)
Fixpoint ins (k : Z) (v : Z) (t : tree Z Z) : tree Z Z :=
  match t with
  | Leaf => Node Red Leaf k v Leaf
  | Node c l kn vn r =>
      if (k <? kn)%Z then
        setRebalanceLeft c (ins k v l) kn vn r
      else if (kn <? k)%Z then
        setRebalanceRight c l kn vn (ins k v r)
      else
        (* k = kn: update value, keep key *)
        Node c l kn v r
  end.

(** Force root to black. Mirrors [curr->color = black] in [Node::insert]. *)
Definition makeBlack {K V : Type} (t : tree K V) : tree K V :=
  match t with
  | Node _ l k v r => Node Black l k v r
  | Leaf => Leaf
  end.

(** Top-level insert: [ins] then force root black. Mirrors [Node::insert]. *)
Definition insert (k : Z) (v : Z) (t : tree Z Z) : tree Z Z :=
  makeBlack (ins k v t).

(** Lookup a key, returning its value if found.
    Mirrors [Node::findNode] (which returns a Node pointer; we return option). *)
Fixpoint findNode (k : Z) (t : tree Z Z) : option Z :=
  match t with
  | Leaf => None
  | Node _ l kn vn r =>
      if (k <? kn)%Z then findNode k l
      else if (kn <? k)%Z then findNode k r
      else Some vn
  end.

(** ** Invariants *)

(** Every key in the tree satisfies predicate [p]. *)
Fixpoint ForAll {K V : Type} (p : K -> Prop) (t : tree K V) : Prop :=
  match t with
  | Leaf => True
  | Node _ l k _ r => ForAll p l /\ p k /\ ForAll p r
  end.

(** BST ordering invariant on keys. *)
Fixpoint IsBST (t : tree Z Z) : Prop :=
  match t with
  | Leaf => True
  | Node _ l k _ r =>
      IsBST l /\ IsBST r /\
      ForAll (fun x => (x < k)%Z) l /\
      ForAll (fun x => (k < x)%Z) r
  end.

(** No red node has a red child (recursive, whole-tree property). *)
Fixpoint NoRedRed {K V : Type} (t : tree K V) : Prop :=
  match t with
  | Leaf => True
  | Node Red (Node Red _ _ _ _) _ _ _ => False
  | Node Red _ _ _ (Node Red _ _ _ _) => False
  | Node _ l _ _ r => NoRedRed l /\ NoRedRed r
  end.

(** No red-red violation at the top level only. *)
Definition NoRedRedChildren {K V : Type} (t : tree K V) : Prop :=
  match t with
  | Node Red (Node Red _ _ _ _) _ _ _ => False
  | Node Red _ _ _ (Node Red _ _ _ _) => False
  | _ => True
  end.

(** ** Validation *)

Definition Color_eqb (c1 c2 : Color) : bool :=
  match c1, c2 with
  | Red, Red => true
  | Black, Black => true
  | _, _ => false
  end.

(** Runtime invariant checker returning black-depth, 0 on failure.
    Mirrors [Node::valid] from [map.h]. *)
Fixpoint validAux {K V : Type} (t : tree K V) : nat :=
  match t with
  | Leaf => 1
  | Node c l _ _ r =>
      if (andb (Color_eqb c Red) (orb (is_red l) (is_red r)))
      then 0
      else
        let ld := validAux l in
        let rd := validAux r in
        if (orb (Nat.eqb ld 0) (negb (Nat.eqb ld rd)))
        then 0
        else if Color_eqb c Black then S ld else ld
  end.

(** ** Traversal *)

(** In-order traversal producing sorted key-value pairs. *)
Fixpoint toList {K V : Type} (t : tree K V) : list (K * V) :=
  match t with
  | Leaf => nil
  | Node _ l k v r => toList l ++ (k, v) :: toList r
  end.

(** Build a tree by left-folding [insert] over a list. *)
Definition fromList (kvs : list (Z * Z)) : tree Z Z :=
  fold_left (fun t kv => insert (fst kv) (snd kv) t) kvs Leaf.

(* ================================================================== *)
(** * Invariant Proofs

    Ported from [Rbtree/Daedalus/Proofs.lean]. *)
(* ================================================================== *)

(** ** ForAll monotonicity *)

Lemma forAll_lt_weaken : forall (v w : Z) (t : tree Z Z),
  (v < w)%Z ->
  ForAll (fun x => (x < v)%Z) t ->
  ForAll (fun x => (x < w)%Z) t.
Proof.
  intros v w t Hvw. induction t as [| c l IHl k val r IHr]; simpl; auto.
  intros [Hl [Hk Hr]]. repeat split; auto. lia.
Qed.

Lemma forAll_gt_weaken : forall (v w : Z) (t : tree Z Z),
  (w < v)%Z ->
  ForAll (fun x => (v < x)%Z) t ->
  ForAll (fun x => (w < x)%Z) t.
Proof.
  intros v w t Hwv. induction t as [| c l IHl k val r IHr]; simpl; auto.
  intros [Hl [Hk Hr]]. repeat split; auto. lia.
Qed.

(** ** ForAll distributes through rebalancing *)

Lemma forAll_setRebalanceLeft : forall (p : Z -> Prop) c (newLeft : tree Z Z) k v (r : tree Z Z),
  ForAll p newLeft -> p k -> ForAll p r ->
  ForAll p (setRebalanceLeft c newLeft k v r).
Proof.
  intros p c newLeft k v r Hl Hk Hr.
  unfold setRebalanceLeft.
  destruct c; simpl; auto.
  destruct newLeft as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    simpl in *; tauto.
Qed.

Lemma forAll_setRebalanceRight : forall (p : Z -> Prop) c (l : tree Z Z) k v (newRight : tree Z Z),
  ForAll p l -> p k -> ForAll p newRight ->
  ForAll p (setRebalanceRight c l k v newRight).
Proof.
  intros p c l k v newRight Hl Hk Hr.
  unfold setRebalanceRight.
  destruct c; simpl; auto.
  destruct newRight as [| [] [| [] b ky vy c1] kz vz [| [] c1' kz' vz' d]];
    simpl in *; tauto.
Qed.

(** ** setRebalanceLeft preserves BST *)

(** Solve a rebalance BST case: decompose conjunctions, split goal,
    then solve each subgoal by assumption, lia, or ForAll transitivity.
    The semicolons chain across all subgoals from [repeat split]. *)
Local Ltac solve_rebalance_case :=
  simpl in *;
  repeat match goal with H: _ /\ _ |- _ => destruct H end;
  repeat split; trivial; try lia;
  try (eapply forAll_gt_weaken; [| eassumption]; lia);
  try (eapply forAll_lt_weaken; [| eassumption]; lia).

Lemma isBST_setRebalanceLeft : forall c (newLeft : tree Z Z) k v (r : tree Z Z),
  IsBST newLeft -> IsBST r ->
  ForAll (fun x => (x < k)%Z) newLeft ->
  ForAll (fun x => (k < x)%Z) r ->
  IsBST (setRebalanceLeft c newLeft k v r).
Proof.
  intros c newLeft k v r HbstL HbstR HltL HgtR.
  unfold setRebalanceLeft.
  destruct c; [simpl; tauto |].
  destruct newLeft as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    simpl in *; intuition auto;
    try lia;
    try (eapply forAll_gt_weaken; [| eassumption]; lia);
    try (eapply forAll_lt_weaken; [| eassumption]; lia).
Qed.

(** ** setRebalanceRight preserves BST *)

Lemma isBST_setRebalanceRight : forall c (l : tree Z Z) k v (newRight : tree Z Z),
  IsBST l -> IsBST newRight ->
  ForAll (fun x => (x < k)%Z) l ->
  ForAll (fun x => (k < x)%Z) newRight ->
  IsBST (setRebalanceRight c l k v newRight).
Proof.
  intros c l k v newRight HbstL HbstR HltL HgtR.
  unfold setRebalanceRight.
  destruct c; [simpl; tauto |].
  destruct newRight as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    simpl in *; intuition auto;
    try lia;
    try (eapply forAll_gt_weaken; [| eassumption]; lia);
    try (eapply forAll_lt_weaken; [| eassumption]; lia).
Qed.

(** ** ins preserves ForAll bounds *)

Lemma forAll_lt_ins : forall x xv v t,
  (x < v)%Z ->
  ForAll (fun y => (y < v)%Z) t ->
  ForAll (fun y => (y < v)%Z) (ins x xv t).
Proof.
  intros x xv v t Hxv. induction t as [| c l IHl w wv r IHr]; simpl.
  - auto.
  - intros [Hl [Hw Hr]].
    destruct (x <? w)%Z.
    + apply forAll_setRebalanceLeft; auto.
    + destruct (w <? x)%Z.
      * apply forAll_setRebalanceRight; auto.
      * simpl. auto.
Qed.

Lemma forAll_gt_ins : forall x xv v t,
  (v < x)%Z ->
  ForAll (fun y => (v < y)%Z) t ->
  ForAll (fun y => (v < y)%Z) (ins x xv t).
Proof.
  intros x xv v t Hvx. induction t as [| c l IHl w wv r IHr]; simpl.
  - auto.
  - intros [Hl [Hw Hr]].
    destruct (x <? w)%Z.
    + apply forAll_setRebalanceLeft; auto.
    + destruct (w <? x)%Z.
      * apply forAll_setRebalanceRight; auto.
      * simpl. auto.
Qed.

(** ** ins preserves BST *)

Theorem isBST_ins : forall x xv t,
  IsBST t -> IsBST (ins x xv t).
Proof.
  intros x xv t. induction t as [| c l IHl k kv r IHr]; simpl.
  - intros _. repeat split; simpl; auto.
  - intros [Hl [Hr [HltL HgtR]]].
    destruct (x <? k)%Z eqn:Hlt.
    + apply Z.ltb_lt in Hlt.
      apply isBST_setRebalanceLeft; auto.
      apply forAll_lt_ins; auto.
    + destruct (k <? x)%Z eqn:Hgt.
      * apply Z.ltb_lt in Hgt.
        apply isBST_setRebalanceRight; auto.
        apply forAll_gt_ins; auto.
      * simpl. auto.
Qed.

(** ** makeBlack preserves BST *)

Theorem isBST_makeBlack : forall t,
  IsBST t -> IsBST (makeBlack t).
Proof.
  intros [| c l k v r]; simpl; tauto.
Qed.

(** ** Main theorem: insert preserves BST *)

Theorem isBST_insert : forall x xv t,
  IsBST t -> IsBST (insert x xv t).
Proof.
  intros. unfold insert. apply isBST_makeBlack. apply isBST_ins. auto.
Qed.

(** ** Structural lemmas for InsertSpec.v *)

(** [setRebalanceLeft] always returns a [Node], never a [Leaf]. *)
Lemma setRebalanceLeft_is_node : forall c (nl : tree Z Z) k v (r : tree Z Z),
  exists c' l' k' v' r', setRebalanceLeft c nl k v r = Node c' l' k' v' r'.
Proof.
  intros c nl k v r.
  unfold setRebalanceLeft.
  destruct c;
  [ eexists; eexists; eexists; eexists; eexists; reflexivity |].
  destruct nl as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    eexists; eexists; eexists; eexists; eexists; reflexivity.
Qed.

(** [setRebalanceRight] always returns a [Node], never a [Leaf]. *)
Lemma setRebalanceRight_is_node : forall c (l : tree Z Z) k v (nr : tree Z Z),
  exists c' l' k' v' r', setRebalanceRight c l k v nr = Node c' l' k' v' r'.
Proof.
  intros c l k v nr.
  unfold setRebalanceRight.
  destruct c;
  [ eexists; eexists; eexists; eexists; eexists; reflexivity |].
  destruct nr as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    eexists; eexists; eexists; eexists; eexists; reflexivity.
Qed.

(** [ins] always returns a [Node], never a [Leaf].
    Needed in InsertSpec.v to unfold the result of [ins] before writing
    [curr->color = black] (which requires a non-null pointer). *)
Lemma ins_is_node : forall k v t,
  exists c l k' v' r, ins k v t = Node c l k' v' r.
Proof.
  intros k v t. induction t as [| c l IHl kn vn r IHr].
  - simpl. eexists; eexists; eexists; eexists; eexists; reflexivity.
  - simpl.
    destruct (k <? kn)%Z.
    + apply setRebalanceLeft_is_node.
    + destruct (kn <? k)%Z.
      * apply setRebalanceRight_is_node.
      * eexists; eexists; eexists; eexists; eexists; reflexivity.
Qed.

(** [makeBlack] on a [Node] sets color to [Black]. Trivial by computation. *)
Lemma makeBlack_node : forall (c : Color) l (k v : Z) r,
  makeBlack (Node c l k v r) = Node Black l k v r.
Proof. reflexivity. Qed.

(** ** NoRedRed preservation *)

(** Children of a NoRedRed tree are NoRedRed. *)
Lemma noRedRed_children : forall c (l : tree Z Z) k v r,
  NoRedRed (Node c l k v r) -> NoRedRed l /\ NoRedRed r.
Proof.
  intros c l k v r H.
  destruct c; [| exact H].
  destruct l as [| [] ll kl vl rl];
  destruct r as [| [] lr kr vr rr]; simpl in *; tauto.
Qed.

(** A tree satisfying NoRedRed also satisfies NoRedRedChildren. *)
Lemma noRedRed_implies_noRedRedChildren : forall (t : tree Z Z),
  NoRedRed t -> NoRedRedChildren t.
Proof.
  intros [| c l k v r] H; simpl in *; auto.
  destruct c; auto.
  destruct l as [| [] ll kl vl rl];
  destruct r as [| [] lr kr vr rr]; simpl in *; tauto.
Qed.

(** A nearly-valid tree: children satisfy NoRedRed but root may violate. *)
Definition NearlyNoRedRed {K V : Type} (t : tree K V) : Prop :=
  match t with
  | Leaf => True
  | Node _ l _ _ r => NoRedRed l /\ NoRedRed r
  end.

Lemma noRedRed_implies_nearlyNoRedRed : forall (t : tree Z Z),
  NoRedRed t -> NearlyNoRedRed t.
Proof.
  intros [| c l k v r] H; [exact I |].
  simpl. exact (noRedRed_children _ _ _ _ _ H).
Qed.

(** makeBlack fixes any root violation. *)
Lemma noRedRed_makeBlack_of_nearly : forall (t : tree Z Z),
  NearlyNoRedRed t -> NoRedRed (makeBlack t).
Proof.
  intros [| c l k v r]; simpl; auto.
Qed.

(** In a NoRedRed tree with a red root, both children have black roots. *)
Lemma isBlack_children_of_red : forall (l : tree Z Z) k v r,
  NoRedRed (Node Red l k v r) ->
  is_black l = true /\ is_black r = true.
Proof.
  intros l k v r H. simpl in H.
  destruct l as [| [] ll kl vl rl];
  destruct r as [| [] lr kr vr rr]; simpl in *; tauto.
Qed.

(** setRebalanceLeft Black preserves NoRedRed when left child is
    nearly valid and right child is fully valid. *)
(** Decompose NearlyNoRedRed into child NoRedRed facts.
    Uses [cbn] to unfold only NearlyNoRedRed (not NoRedRed) so that
    [noRedRed_children] can be applied to structured children. *)
Local Ltac decompose_nearly Hnl :=
  cbn [NearlyNoRedRed] in Hnl;
  let H1 := fresh "Hl" in let H2 := fresh "Hr" in
  destruct Hnl as [H1 H2];
  try (apply noRedRed_children in H1; destruct H1);
  try (apply noRedRed_children in H2; destruct H2).

Lemma noRedRed_setRebalanceLeft_black : forall (nl : tree Z Z) k v r,
  NearlyNoRedRed nl -> NoRedRed r ->
  NoRedRed (setRebalanceLeft Black nl k v r).
Proof.
  intros nl k v r Hnl Hr.
  unfold setRebalanceLeft.
  destruct nl as [| [] ll knl vnl rl]; [simpl; auto | | simpl; auto].
  (* nl = Node Red ll knl vnl rl *)
  destruct ll as [| [] a kx vx b].
  - (* ll = Leaf: check rl *)
    destruct rl as [| [] lrl krl vrl rrl]; [simpl; auto | | simpl; auto].
    (* LR case *)
    decompose_nearly Hnl. simpl. repeat split; assumption.
  - (* ll = Node Red: LL case *)
    decompose_nearly Hnl. simpl. repeat split; assumption.
  - (* ll = Node Black: check rl *)
    destruct rl as [| [] lrl krl vrl rrl]; [| | simpl; auto].
    + (* rl = Leaf *) decompose_nearly Hnl. simpl. repeat split; assumption.
    + (* rl = Node Red: LR case *)
      decompose_nearly Hnl. simpl. repeat split; assumption.
Qed.

(** Symmetric for setRebalanceRight. *)
Lemma noRedRed_setRebalanceRight_black : forall (l : tree Z Z) k v nr,
  NoRedRed l -> NearlyNoRedRed nr ->
  NoRedRed (setRebalanceRight Black l k v nr).
Proof.
  intros l k v nr Hl Hnr.
  unfold setRebalanceRight.
  destruct nr as [| [] rl knr vnr rr]; [simpl; auto | | simpl; auto].
  (* nr = Node Red rl knr vnr rr *)
  destruct rl as [| [] a kx vx b].
  - (* rl = Leaf: check rr *)
    destruct rr as [| [] lrr krr vrr rrr]; [simpl; auto | | simpl; auto].
    (* RR case *)
    decompose_nearly Hnr. simpl. repeat split; assumption.
  - (* rl = Node Red: RL case *)
    decompose_nearly Hnr. simpl. repeat split; assumption.
  - (* rl = Node Black: check rr *)
    destruct rr as [| [] lrr krr vrr rrr]; [| | simpl; auto].
    + (* rr = Leaf *) decompose_nearly Hnr. simpl. repeat split; assumption.
    + (* rr = Node Red: RR case *)
      decompose_nearly Hnr. simpl. repeat split; assumption.
Qed.

(** ins produces a NearlyNoRedRed tree, and if the input has a black root,
    the result is fully NoRedRed. *)
Theorem ins_noRedRed : forall k v (t : tree Z Z),
  NoRedRed t ->
  NearlyNoRedRed (ins k v t) /\
  (is_black t = true -> NoRedRed (ins k v t)).
Proof.
  intros k v t. induction t as [| c l IHl kn vn r IHr].
  - simpl. intros _. split; simpl; auto.
  - intros Hvalid.
    destruct (noRedRed_children _ _ _ _ _ Hvalid) as [Hl Hr].
    simpl.
    destruct (IHl Hl) as [IHl1 IHl2].
    destruct (IHr Hr) as [IHr1 IHr2].
    destruct (k <? kn)%Z.
    + (* k < kn: setRebalanceLeft *)
      split.
      * destruct c.
        -- (* Red *) simpl.
           split; [apply IHl2; exact (proj1 (isBlack_children_of_red _ _ _ _ Hvalid)) | exact Hr].
        -- (* Black *)
           apply noRedRed_implies_nearlyNoRedRed.
           apply noRedRed_setRebalanceLeft_black; auto.
      * intro Hb. destruct c; [simpl in Hb; discriminate |].
        apply noRedRed_setRebalanceLeft_black; auto.
    + destruct (kn <? k)%Z.
      * (* kn < k: setRebalanceRight *)
        split.
        -- destruct c.
           ++ simpl. split; [exact Hl | apply IHr2; exact (proj2 (isBlack_children_of_red _ _ _ _ Hvalid))].
           ++ apply noRedRed_implies_nearlyNoRedRed.
              apply noRedRed_setRebalanceRight_black; auto.
        -- intro Hb. destruct c; [simpl in Hb; discriminate |].
           apply noRedRed_setRebalanceRight_black; auto.
      * (* k = kn: no change *)
        split.
        -- simpl. auto.
        -- intro Hb. destruct c; [simpl in Hb; discriminate |]. simpl. auto.
Qed.

(** ** Main theorem: insert preserves NoRedRed *)

Theorem noRedRed_insert : forall k v (t : tree Z Z),
  NoRedRed t -> NoRedRed (insert k v t).
Proof.
  intros. unfold insert.
  apply noRedRed_makeBlack_of_nearly.
  exact (proj1 (ins_noRedRed k v t H)).
Qed.

(** ** Rebalancing preserves in-order traversal *)

(** Key structural lemma: rotation is just tree restructuring that preserves
    the sorted element sequence. Provable by case analysis + list associativity. *)
(** Proof strategy: destruct only enough to identify each rotation case.
    Rotations reassociate the in-order list. We alternate [app_assoc]
    rewrites with [simpl] to handle the interaction between [app] and [cons]:
    [simpl] reduces [app (cons a l) m] to [cons a (app l m)], which can
    hide [app_assoc] patterns. *)
Local Ltac solve_toList_rebalance :=
  simpl; repeat (try rewrite <- app_assoc; simpl); reflexivity.

Lemma toList_setRebalanceLeft : forall c (nl : tree Z Z) k v (r : tree Z Z),
  toList (setRebalanceLeft c nl k v r) = toList nl ++ (k, v) :: toList r.
Proof.
  intros c nl k v r. unfold setRebalanceLeft.
  destruct c; [reflexivity |].
  destruct nl as [| [] lnl knl vnl rnl]; [reflexivity | | reflexivity].
  destruct lnl as [| [] a kx vx b].
  - destruct rnl as [| [] b' ky vy c1]; [reflexivity | | reflexivity].
    solve_toList_rebalance.
  - solve_toList_rebalance.
  - destruct rnl as [| [] b' ky vy c1]; [reflexivity | | reflexivity].
    solve_toList_rebalance.
Qed.

Lemma toList_setRebalanceRight : forall c (l : tree Z Z) k v (nr : tree Z Z),
  toList (setRebalanceRight c l k v nr) = toList l ++ (k, v) :: toList nr.
Proof.
  intros c l k v nr. unfold setRebalanceRight.
  destruct c; [reflexivity |].
  destruct nr as [| [] lnr knr vnr rnr]; [reflexivity | | reflexivity].
  destruct lnr as [| [] a kx vx b].
  - destruct rnr as [| [] c1 kz vz d]; [reflexivity | | reflexivity].
    solve_toList_rebalance.
  - solve_toList_rebalance.
  - destruct rnr as [| [] c1 kz vz d]; [reflexivity | | reflexivity].
    solve_toList_rebalance.
Qed.

(** ** findNode correctness *)

Lemma findNode_leaf : forall k, findNode k Leaf = None.
Proof. reflexivity. Qed.

Lemma findNode_eq : forall k c l v r,
  findNode k (Node c l k v r) = Some v.
Proof.
  intros. simpl.
  destruct (k <? k)%Z eqn:E; [lia |].
  destruct (k <? k)%Z eqn:E2; [lia |].
  reflexivity.
Qed.

(** makeBlack doesn't change lookup results (only root color changes). *)
Lemma findNode_makeBlack : forall k (t : tree Z Z),
  findNode k (makeBlack t) = findNode k t.
Proof.
  intros k [| c l kn vn r]; reflexivity.
Qed.

(** ** findNode through rebalancing *)

(** Helper: when all keys satisfy [p] in a tree, all keys in [toList]
    satisfy [p] too. Used to show findNode skips irrelevant subtrees. *)
Lemma ForAll_toList : forall (p : Z -> Prop) (t : tree Z Z),
  ForAll p t -> Forall (fun kv => p (fst kv)) (toList t).
Proof.
  intros p t. induction t as [| c l IHl k v r IHr]; simpl.
  - intros _. constructor.
  - intros [Hl [Hk Hr]].
    apply Forall_app. split; auto.
Qed.

(** Associative list lookup. *)
Fixpoint assoc_lookup (k : Z) (l : list (Z * Z)) : option Z :=
  match l with
  | nil => None
  | (k', v') :: rest => if (k =? k')%Z then Some v' else assoc_lookup k rest
  end.

Lemma assoc_lookup_app : forall k l1 l2,
  assoc_lookup k (l1 ++ l2) =
  match assoc_lookup k l1 with
  | Some v => Some v
  | None => assoc_lookup k l2
  end.
Proof.
  intros k l1. induction l1 as [| [k' v'] rest IH]; simpl; auto.
  intros l2. destruct (k =? k')%Z; auto.
Qed.

(** If [k] doesn't appear among the keys of [l], lookup returns None. *)
Lemma assoc_lookup_not_in : forall k l,
  Forall (fun kv => fst kv <> k) l ->
  assoc_lookup k l = None.
Proof.
  intros k l. induction l as [| [k' v'] rest IH]; simpl; auto.
  intros Hfa. inversion Hfa; subst. simpl in H1.
  destruct (k =? k')%Z eqn:E.
  - apply Z.eqb_eq in E. exfalso. auto.
  - auto.
Qed.

(** findNode is equivalent to assoc_lookup on toList for BSTs. *)
Lemma findNode_toList : forall k (t : tree Z Z),
  IsBST t -> findNode k t = assoc_lookup k (toList t).
Proof.
  intros k t. induction t as [| c l IHl kn vn r IHr]; simpl; auto.
  intros [Hbst_l [Hbst_r [Hlt Hgt]]].
  rewrite assoc_lookup_app. simpl.
  destruct (k <? kn)%Z eqn:Eklt.
  - (* k < kn: findNode goes left *)
    apply Z.ltb_lt in Eklt.
    rewrite IHl by auto.
    destruct (assoc_lookup k (toList l)); auto.
    simpl. destruct (k =? kn)%Z eqn:Ekn.
    + apply Z.eqb_eq in Ekn. lia.
    + symmetry. apply assoc_lookup_not_in.
      apply ForAll_toList in Hgt.
      eapply Forall_impl; [| exact Hgt]. simpl. intros [k' v'] Hk'. lia.
  - (* k >= kn *)
    destruct (kn <? k)%Z eqn:Ekgt.
    + (* kn < k: findNode goes right *)
      apply Z.ltb_lt in Ekgt.
      rewrite IHr by auto.
      rewrite (assoc_lookup_not_in k (toList l)).
      * simpl. destruct (k =? kn)%Z eqn:Ekn.
        -- apply Z.eqb_eq in Ekn. lia.
        -- reflexivity.
      * apply ForAll_toList in Hlt.
        eapply Forall_impl; [| exact Hlt]. simpl. intros [k' v'] Hk'. lia.
    + (* k = kn *)
      apply Z.ltb_ge in Eklt. apply Z.ltb_ge in Ekgt.
      assert (k = kn) by lia. subst.
      rewrite (assoc_lookup_not_in kn (toList l)).
      * simpl. rewrite Z.eqb_refl. reflexivity.
      * apply ForAll_toList in Hlt.
        eapply Forall_impl; [| exact Hlt]. simpl. intros [k' v'] Hk'. lia.
Qed.

(** findNode on a rebalanced tree equals findNode on the unbalanced version.
    Follows from toList preservation + findNode/toList equivalence. *)
Lemma findNode_setRebalanceLeft : forall k c (nl : tree Z Z) kn vn (r : tree Z Z),
  IsBST nl -> IsBST r ->
  ForAll (fun x => (x < kn)%Z) nl ->
  ForAll (fun x => (kn < x)%Z) r ->
  findNode k (setRebalanceLeft c nl kn vn r) =
  findNode k (Node c nl kn vn r).
Proof.
  intros k c nl kn vn r Hbst_nl Hbst_r Hlt Hgt.
  rewrite findNode_toList by (apply isBST_setRebalanceLeft; auto).
  rewrite findNode_toList by (simpl; auto).
  rewrite toList_setRebalanceLeft. reflexivity.
Qed.

Lemma findNode_setRebalanceRight : forall k c (l : tree Z Z) kn vn (nr : tree Z Z),
  IsBST l -> IsBST nr ->
  ForAll (fun x => (x < kn)%Z) l ->
  ForAll (fun x => (kn < x)%Z) nr ->
  findNode k (setRebalanceRight c l kn vn nr) =
  findNode k (Node c l kn vn nr).
Proof.
  intros k c l kn vn nr Hbst_l Hbst_nr Hlt Hgt.
  rewrite findNode_toList by (apply isBST_setRebalanceRight; auto).
  rewrite findNode_toList by (simpl; auto).
  rewrite toList_setRebalanceRight. reflexivity.
Qed.

(** ** findNode after ins *)

Lemma findNode_ins : forall k v (t : tree Z Z),
  IsBST t -> findNode k (ins k v t) = Some v.
Proof.
  intros k v t. induction t as [| c l IHl kn vn r IHr]; simpl.
  - intros _. rewrite Z.ltb_irrefl. reflexivity.
  - intros [Hbst_l [Hbst_r [Hlt Hgt]]].
    destruct (k <? kn)%Z eqn:Eklt.
    + apply Z.ltb_lt in Eklt.
      rewrite findNode_setRebalanceLeft; auto.
      * simpl. rewrite (proj2 (Z.ltb_lt k kn) Eklt). auto.
      * apply isBST_ins. auto.
      * apply forAll_lt_ins; auto.
    + destruct (kn <? k)%Z eqn:Ekgt.
      * apply Z.ltb_lt in Ekgt.
        rewrite findNode_setRebalanceRight; auto.
        -- simpl. rewrite Eklt. rewrite (proj2 (Z.ltb_lt kn k) Ekgt). auto.
        -- apply isBST_ins. auto.
        -- apply forAll_gt_ins; auto.
      * (* k = kn: value updated in place *)
        simpl. rewrite Eklt. rewrite Ekgt. reflexivity.
Qed.

(** After inserting (k, v), looking up k returns v. *)
Theorem findNode_after_insert : forall k v t,
  IsBST t ->
  findNode k (insert k v t) = Some v.
Proof.
  intros k v t Hbst. unfold insert.
  rewrite findNode_makeBlack. apply findNode_ins. auto.
Qed.

(** ** findNode for other keys after ins *)

Lemma findNode_ins_other : forall k k' v (t : tree Z Z),
  k <> k' ->
  IsBST t ->
  findNode k (ins k' v t) = findNode k t.
Proof.
  intros k k' v t Hneq. induction t as [| c l IHl kn vn r IHr]; simpl.
  - intros _. destruct (k <? k')%Z eqn:E1.
    + reflexivity.
    + destruct (k' <? k)%Z eqn:E2; [reflexivity |].
      apply Z.ltb_ge in E1. apply Z.ltb_ge in E2.
      assert (k = k') by lia. contradiction.
  - intros [Hbst_l [Hbst_r [Hlt Hgt]]].
    destruct (k' <? kn)%Z eqn:Eklt.
    + apply Z.ltb_lt in Eklt.
      rewrite findNode_setRebalanceLeft; auto.
      * simpl. destruct (k <? kn)%Z eqn:Ek; auto.
      * apply isBST_ins. auto.
      * apply forAll_lt_ins; auto.
    + destruct (kn <? k')%Z eqn:Ekgt.
      * apply Z.ltb_lt in Ekgt.
        rewrite findNode_setRebalanceRight; auto.
        -- simpl. destruct (k <? kn)%Z; auto.
           destruct (kn <? k)%Z; auto.
        -- apply isBST_ins. auto.
        -- apply forAll_gt_ins; auto.
      * (* k' = kn: value updated, tree structure unchanged *)
        apply Z.ltb_ge in Eklt. apply Z.ltb_ge in Ekgt.
        assert (k' = kn) by lia. subst.
        (* ins kn v (Node c l kn vn r) = Node c l kn v r (value updated).
           findNode k differs only in the k=kn branch, but k ≠ kn. *)
        simpl. destruct (k <? kn)%Z eqn:E1; [reflexivity |].
        destruct (kn <? k)%Z eqn:E2; [reflexivity |].
        (* k = kn: impossible since k ≠ kn *)
        apply Z.ltb_ge in E1. apply Z.ltb_ge in E2. exfalso. lia.
Qed.

(** Inserting a different key doesn't affect lookup. *)
Theorem findNode_insert_other : forall k k' v t,
  k <> k' ->
  IsBST t ->
  findNode k (insert k' v t) = findNode k t.
Proof.
  intros k k' v t Hneq Hbst. unfold insert.
  rewrite findNode_makeBlack. apply findNode_ins_other; auto.
Qed.

(** ** fromList preserves invariants *)

Theorem fromList_isBST : forall kvs,
  IsBST (fromList kvs).
Proof.
  unfold fromList. intros.
  assert (H: IsBST (Leaf (K:=Z) (V:=Z))) by (simpl; auto).
  revert H. generalize (Leaf (K:=Z) (V:=Z)) as acc.
  induction kvs as [| [k v] kvs IH]; simpl; auto.
  intros acc Hacc. apply IH. apply isBST_insert. auto.
Qed.

Theorem fromList_noRedRed : forall kvs,
  NoRedRed (fromList kvs).
Proof.
  unfold fromList. intros.
  assert (H: NoRedRed (Leaf (K:=Z) (V:=Z))) by (simpl; auto).
  revert H. generalize (Leaf (K:=Z) (V:=Z)) as acc.
  induction kvs as [| [k v] kvs IH]; simpl; auto.
  intros acc Hacc. apply IH. apply noRedRed_insert. auto.
Qed.
