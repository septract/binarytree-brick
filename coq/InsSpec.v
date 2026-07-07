(** * ins Specification and Proof — Phase 5B
    Created: 2026-02-22

    Proves that the C++ [Node::ins] function refines the functional
    [ins] from [RBTree.v].

    == Architecture ==

    Uses Löb induction ([iLöb]) for the recursive function: the
    induction hypothesis provides [▷ func_ok source ins_func ins_spec],
    which is consumed by the later modality at each recursive call site.

    == C++ function under verification ==

<<
    static Node* ins(Key k, Value v, Node *n) {
      if (n == nullptr)
        return new Node(red, nullptr, k, v, nullptr);
      n = makeCopy(n);
      if (k < n->key) return setRebalanceLeft(n, ins(k, v, n->left));
      if (n->key < k) return setRebalanceRight(n, ins(k, v, n->right));
      if constexpr (hasRefs<Key>()) k.free();
      if constexpr (hasRefs<Value>()) n->value.free();
      n->value = v;
      return n;
    }
>>

    == Proof outline ==

    1. [iLöb as "IH"] — Löb induction for recursive calls
    2. Extract arguments (k, v, n) from spec
    3. Step through variable declaration / function prefix
    4. Case-split on [t]:
       a. [Leaf] (n = nullptr): base case
          - [new Node(red, nullptr, k, v, nullptr)]
          - Fold into [treeR (Node Red Leaf k v Leaf)]
          - Show this equals [ins k v Leaf]
       b. [Node c l kn vn r] (n != nullptr):
          - Call [makeCopy(n)] (Admitted spec)
          - Unfold [treeR] at result to read fields
          - Compare [k] with [n->key]
          i.  [k < kn]: read [n->left], recursive [ins(k,v,n->left)] via IH,
              then [setRebalanceLeft(n, result)]
          ii. [kn < k]: mirror with [setRebalanceRight]
          iii.[k = kn]: write [n->value = v], fold back, skip hasRefs branches

    == Dependencies ==

    - [setRebalanceLeft_ok], [setRebalanceRight_ok]: from InsertDefs.v (Admitted)
      or RebalanceSpec.v (when proved)
    - [makeCopy_ok]: Admitted (Phase 6)
    - [is_black_ok], [is_red_ok]: Admitted

    == AST Reference ==

    ins (line 93452 in map_int_int_cpp.v):
<<
    Sseq([
      Sif(n == nullptr, return Enew(Node(red,nullptr,k,v,nullptr)), Sskip),
      n = makeCopy(n),
      Sif(k < n->key, return setRebalanceLeft(n, ins(k,v,n->left)), Sskip),
      Sif(n->key < k, return setRebalanceRight(n, ins(k,v,n->right)), Sskip),
      Sif(hasRefs<Key>() [constexpr false], Sskip, Sskip),
      Sif(hasRefs<Value>() [constexpr false], Sskip, Sskip),
      n->value = v,
      return n
    ])
>>
*)

From Stdlib Require Import ZArith Bool Lia.

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.Tactics.
Require Import daedalus_rb.InsertDefs.

(* ================================================================= *)
(** * ins_ok — Löb Induction Proof *)
(* ================================================================= *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

Hypothesis MODULE : |-- denoteModule source.

(** ** Main proof

    The Löb induction hypothesis [IH : ▷ func_ok source ins_func ins_spec]
    is placed before [iIntros "!>"] so that it quantifies over ALL future
    invocations.  At each recursive call site, the later modality [▷]
    is consumed by the step taken through the function call.

    The proof uses [wp_call_from_hyp] (from WpTactics.v) to invoke [ins]
    via the Iris hypothesis [IH] rather than a Coq lemma — this is what
    enables the recursion. *)
Lemma ins_ok :
  |-- func_ok source ins_func ins_spec.
Proof using MOD MODULE.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.
  - iLöb as "IH".
    iIntros "!>" (Q vals) "Hspec".
    iPoseProof MODULE as "#HMOD".
    iApply wp_func_intro.
    rewrite /ins_func /=.
    (** Step 1: Extract args: k, v, n from spec. *)
    iDestruct "Hspec" as (pk vk pv vv pn vn)
      "(%Hvals & Hpk & Hpv & Hpn & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (k v n t)
      "(%Hargs & Htree & Hcont)".
    injection Hargs as -> ->. subst.
    (** Step 2: wp through initial Sseq. *)
    wp_auto.
    (** Step 3: [Sif(n == nullptr, ...)]
        Case-split on [t] to determine if [n = nullptr]. *)
    destruct t as [| c l kn vn0 r].
    + (** Case A: [t = Leaf] → [n = nullptr].

          The C++ code creates [new Node(red, nullptr, k, v, nullptr)].
          This involves [Enew] + the 5-arg constructor.  The result is
          a fresh [treeR (Node Red Leaf k v Leaf)] which equals
          [ins k v Leaf] by computation.

          The [Enew] + [Econstructor] pattern involves:
          1. [wp_operand_new] — allocate memory
          2. [wp_init_constructor] — run the constructor body
          3. Constructor sets ref_count=1, color=param, key=param, etc.

          This is a new BRiCk pattern not yet exercised in this codebase.
          Admitted as a sub-goal. *)
      admit.
    + (** Case B: [t = Node c l kn vn0 r] → [n != nullptr].

          The C++ code:
          1. [n = makeCopy(n)] — COW copy
          2. Compare [k] with [n->key]
          3. Branch: recursive left, recursive right, or update value *)

      (** Step 4: Handle [n != nullptr] branch of the outer if.
          Need to show [n != nullptr] from [treeR (Node ...)]. *)
      iDestruct (treeR_node_nonnull with "Htree") as "[Htree %Hne]".
      iDestruct (treeR_node_valid with "Htree") as "[Htree #Hvalid]".

      (** Step 5: Evaluate [n == nullptr] → false, skip if-body.

          The [Sif] condition is [Ebinop Bne (Evar "n") (Ecast Cnull nullptr)].
          For [n != nullptr]: condition is true... wait, the code is:
            [if (n == nullptr) return ...; ]
          So the condition is [Beq], not [Bne].  When [n != nullptr],
          the comparison is false, so we skip to the else (Sskip). *)

      (** TODO: Step through the nullptr comparison, prove it's false,
          take the Sskip branch. The comparison involves:
          - [wp_operand_binop] with [Beq]
          - [eval_ptr_self_eq] or similar
          - The false branch falls through to [n = makeCopy(n)] *)
      admit.

      (** Proof sketch for the non-null case (after the nullptr check):

          Step 6: [n = makeCopy(n)]
          Call makeCopy with [Htree : n |-> treeR 1 (Node c l kn vn0 r)].
          Post: [copy |-> treeR 1 (Node c l kn vn0 r)] for some copy ptr.
          Then [n] (the local variable) is updated to point to [copy].

          Step 7: Unfold treeR at the copy to access fields.

          Step 8: Read [n->key] for comparison with [k].

          Step 9: Case-split on [k <? kn]:
          - [k < kn]: Read n->left, recursive [ins(k,v,lp)] via
            [wp_call_from_hyp "IH"], then [setRebalanceLeft(n, result)]
            with field-level ownership.
          - [kn < k]: Mirror with [setRebalanceRight].
          - [k = kn]: Skip hasRefs branches (constexpr false),
            write [n->value = v], fold [treeR (Node c l kn v r)]. *)
Admitted.

End with_Sigma.
