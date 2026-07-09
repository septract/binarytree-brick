(** * Rebalance Specifications and Proofs — Phase 5B
    Created: 2026-02-22

    Proves that the C++ [setRebalanceLeft] and [setRebalanceRight] functions
    refine their functional counterparts from [RBTree.v].

    == Architecture ==

    Uses field-level ownership at the [n] node (not a full [treeR]):
    - Struct fields (ref_count, color, key, value, left, right, structR)
    - The preserved subtree (right for Left, left for Right)
    - The new subtree from recursive [ins] (full treeR)

    This matches the caller's state: after [ins(k,v,n->left)] consumes
    the left subtree, the caller retains field-level ownership at [n]
    plus the right subtree.

    == Proof strategy ==

    Case-split on [(c, newL)] matching the functional [setRebalanceLeft]:
    - Default cases (c=Red, newL=Leaf, newL=Node Black): Eseqand
      short-circuits, fall through to [res=n; res->left=newLeft; return res]
    - LL rotation: [is_black(n) && is_red(newLeft) && is_red(sub2)]
      where sub2 = newLeft->left
    - LR rotation: [is_black(n) && is_red(newLeft) && is_red(sub2)]
      where sub2 = newLeft->right (after LL check fails)

    == Dependencies ==

    - [is_black_ok], [is_red_ok]: Admitted (Phase 5B deferred)
    - [makeCopy_ok]: Admitted (Phase 6)

    == AST Reference ==

    setRebalanceLeft (line 93536 in map_int_int_cpp.v):
<<
    Sseq([
      Sif(Eseqand(call is_black(Cnoop n), call is_red(Cnoop newLeft)),
        Sseq([
          Sdecl(sub2 = newLeft->left),
          Sif(call is_red(Cnoop sub2),       // LL check
            [LL rotation body; return],
            Sskip),
          sub2 = newLeft->right,
          Sif(call is_red(Cnoop sub2),       // LR check
            [LR rotation body; return],
            Sskip)
        ]),
        Sskip),
      Sdecl(res = n),                        // Default case
      res->left = newLeft,
      return res
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
(* Real is_black_ok / is_red_ok proofs (InsertDefs.v has only Admitted stubs). *)
Require Import daedalus_rb.IsBlackSpec.

(* ================================================================= *)
(** * Pure helper lemmas (outside Section — no cpp_logic context) *)
(* ================================================================= *)

(** ** Default case helper: [setRebalanceLeft c newL k v r = Node c newL k v r]

    When neither LL nor LR rotation applies, [setRebalanceLeft] returns
    the node unchanged (with the new left child). This covers:
    - [c = Red] (any newL)
    - [c = Black, newL = Leaf]
    - [c = Black, newL = Node Black _ _ _ _]
    - [c = Black, newL = Node Red (non-Red) _ _ (non-Red)] *)
Lemma setRebalanceLeft_default (c : Color) (newL : tree Z Z) (k : Z) (v : Z) (r : tree Z Z) :
  ~ (c = Black /\ exists a kx vx b ky vy c1,
       newL = Node Red (Node Red a kx vx b) ky vy c1) ->
  ~ (c = Black /\ exists a kx vx b ky vy c1,
       newL = Node Red a kx vx (Node Red b ky vy c1)) ->
  setRebalanceLeft c newL k v r = Node c newL k v r.
Proof.
  intros Hno_ll Hno_lr.
  unfold setRebalanceLeft.
  destruct c; [reflexivity |].
  destruct newL as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    try reflexivity;
    solve [
      exfalso; apply Hno_ll; split; [reflexivity |]; do 7 eexists; reflexivity
    | exfalso; apply Hno_lr; split; [reflexivity |]; do 7 eexists; reflexivity
    ].
Qed.

(** ** Analogous for setRebalanceRight *)
Lemma setRebalanceRight_default (c : Color) (l : tree Z Z) (k : Z) (v : Z) (newR : tree Z Z) :
  ~ (c = Black /\ exists b ky vy c1 kz vz d,
       newR = Node Red (Node Red b ky vy c1) kz vz d) ->
  ~ (c = Black /\ exists b ky vy c1 kz vz d,
       newR = Node Red b ky vy (Node Red c1 kz vz d)) ->
  setRebalanceRight c l k v newR = Node c l k v newR.
Proof.
  intros Hno_rl Hno_rr.
  unfold setRebalanceRight.
  destruct c; [reflexivity |].
  destruct newR as [| [] [| [] a kx vx b] ky vy [| [] b' ky' vy' c1]];
    try reflexivity;
    solve [
      exfalso; apply Hno_rl; split; [reflexivity |]; do 7 eexists; reflexivity
    | exfalso; apply Hno_rr; split; [reflexivity |]; do 7 eexists; reflexivity
    ].
Qed.

(* ================================================================= *)
(** * setRebalanceLeft_ok *)
(* ================================================================= *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

Hypothesis MODULE : |-- denoteModule source.

(** ** Main proof: setRebalanceLeft_ok

    Proof structure: case-split on [(c, newL)] to match the functional
    definition, then step through the AST path for each case.

    The proof proceeds by:
    1. Extracting arguments from the spec
    2. Case-splitting on [c] and [newL] to determine the AST path
    3. For each case:
       a. Handle the [Eseqand] condition ([is_black(n) && is_red(newLeft)])
       b. Follow the resulting AST path (default / LL / LR)
       c. Fold the result into [treeR (setRebalanceLeft c newL k v r)]

    The [Eseqand] handling and [is_black]/[is_red] calls involve novel
    BRiCk patterns not yet exercised in this codebase.  These are
    admitted as sub-goals while the overall structure is validated. *)
Lemma setRebalanceLeft_ok :
  |-- func_ok source setRebalanceLeft_func setRebalanceLeft_spec.
Proof using MOD MODULE.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.
  - iIntros "!>" (Q vals) "Hspec".
    iPoseProof MODULE as "#HMOD".
    iApply wp_func_intro.
    rewrite /setRebalanceLeft_func /=.
    (** Step 1: Extract argument bindings.
        Two args (n, newLeft) → 4 existentials for physical pairs. *)
    iDestruct "Hspec" as (pn vn pnl vnl)
      "(%Hvals & Hpn & Hpnl & Hspec)".
    subst vals. simpl.
    (** Step 2: Extract logical values + [pre] existentials.
        [n_ptr] from [\arg], [nl_ptr] from [\arg],
        [c k v lp rp rc r newL] from [\pre]. *)
    iDestruct "Hspec" as (n_ptr nl_ptr c k v lp rp rc r newL)
      "(%Hargs & Hpre & Hcont)".
    injection Hargs as -> ->. subst.
    (** Step 3: Split the precondition resources. *)
    iDestruct "Hpre" as "(Hnode & Htree_r & Htree_nl)".
    iDestruct "Hnode" as
      "(Hrc & Hcolor & Hkey & Hval & Hleft & Hright & Hstruct)".
    (** Step 4: wp through initial Sseq.
        The body starts with: Sseq([ Sif(Eseqand(...), ..., Sskip); ... ]) *)
    wp_auto.
    (** Step 5: Handle [Sif(Eseqand(is_black(n), is_red(newLeft)), ...)]

        The [Eseqand] evaluates [is_black(Cnoop n)] first.
        - If [c = Red]: [is_black] returns false → short-circuit → default path
        - If [c = Black]: [is_black] returns true → evaluate [is_red(newLeft)]
          - If [newL] is Leaf or Node Black: [is_red] returns false → default
          - If [newL] is Node Red: [is_red] returns true → enter rebalance body

        For now, admit the Eseqand + is_black/is_red call handling and
        case-split at the functional level to validate the spec shape. *)
    destruct c.
    + (** Case 1: [c = Red] → default path. *)
      iApply (wp_if source); iNext.
      rewrite /wp.WPE.wp_test /=.
      iApply wp_operand_seqand.
      rewrite /wp.WPE.wp_test /=.
      iApply wp_operand_call;
        rewrite /wp_call /=;
        iIntros "%_";
        rewrite /wp.WPE.Mbind /wp.WPE.Mmap /=.
      iApply wp_operand_cfun2ptr_global; [ exact is_black_lookup | exact is_black_has_body | ].
      iSplitL "HMOD"; [ iExact "HMOD" |].
      iExists (_global is_black_name).
      iSplit; [ iPureIntro; reflexivity |].
      rewrite /wp.WPE.nd_seqs /=.
      iIntros (pre post q) "%Hnd".
      destruct pre as [| ?x0 [| ?x1 ?rest]]; simpl in Hnd; try congruence.
      injection Hnd; clear Hnd; intros; subst; simpl.
      rewrite /wp.WPE.Mbind /call.wp_arg /=.
      iIntros (argp).
      rewrite /wp_initialize /qual_norm /=.
      try rewrite wp_initialize_unqualified.unlock /=.
      iApply wp_operand_cast_noop.
      wp_read_local "Hpn" (Vptr n_ptr).
      iDestruct (observe (reference_to _ n_ptr) with "Hstruct") as "#_rt".
      iDestruct (reference_to_elim with "_rt") as "(%_align & %_nn & #_val & _)".
      iSplitR.
      { rewrite has_type_ptr'.
        iSplitR; [ iApply "_val" |].
        iPureIntro. rewrite aligned_ptr_ty_erase_qualifiers /=. exact _align. }
      iIntros "Hargp".
      rewrite /wp.WPE.Mmap /wp.WPE.Mret /=.
      iNext.
      iPoseProof (code_at_of_denoteModule _ _ _ is_black_lookup is_black_has_body
        with "HMOD") as "#_call_ca".
      iPoseProof (is_black_ok MODULE) as "#_call_fok".
      (** Apply [wp_fptr_of_func_ok] directly; the goal's call-site function type
          equals [type_of_value (Ofunction is_black_func)] up to qualifier
          normalization (both go through [to_arg_type]/[normalize_type]), so
          replace it by [vm_compute] rather than [change] (which needs syntactic
          convertibility and fails on the [merge_tq QM] residue). *)
      match goal with |- context[wp_fptr _ ?ft _ _ _] =>
        replace ft with (type_of_value (Ofunction is_black_func))
          by (vm_compute; reflexivity)
      end.
      iApply (wp_fptr_of_func_ok_compat _ _ _ _ _ _ (tu_compat)).
      iSplitR; [ iExact "_call_ca" |].
      iSplitR; [ iExact "_call_fok" |].
      (** Provide [is_black_spec] precond: arg [argp]→[n_ptr], ghost [Some Red],
          resources [Hcolor]+[Hstruct] assembled into the [_color ∗ structR]
          conjunct; received back (read-only) in the post. *)
      rewrite /is_black_spec /=.
      iExists argp, (Vptr n_ptr).
      iSplit; [ iPureIntro; reflexivity |].
      iSplitL "Hargp"; [ iFrame "Hargp" |].
      iExists n_ptr, (Some Red), (cQp.m 1).
      iSplit; [ iPureIntro; reflexivity |].
      iSplitL "Hcolor Hstruct".
      { rewrite _at_sep /=. iFrame "Hcolor Hstruct". }
      (** Receive the color resources back + the [is_black]=false result. *)
      iIntros (ret) "Hpost".
      iIntros (rx) "(Hany & Hres)".
      wp_auto.
      wp_destroy_prim_temp "Hany".
      iModIntro; rewrite operand_receive.unlock /=.
      iExists (Vbool false).
      iFrame "Hres".
      (** [is_black]=false ⇒ [is_true (Vbool false) = Some false] ⇒ [Eseqand]
          short-circuits (no [is_red] call) ⇒ guard is false ⇒ [Sif] else. *)
      simpl.
      (** Recover the [_color]/[structR] resources from the read-only post
          (now at the concrete fraction [cQp.m 1] we lent — no opaque existential). *)
      iDestruct "Hpost" as "[Hpost _]".
      rewrite _at_sep /=.
      iDestruct "Hpost" as "[Hcolor Hstruct]".
      (** Default path: [res = n; res->left = newLeft; return res]. *)
      wp_auto.
      iIntros (addr).
      (** [res = n]: initialize the [res] local with the pointer value [n]. *)
      wp_read_local "Hpn" (Vptr n_ptr).
      iIntros "Hres_local".
      wp_auto.
      (** [res->left = newLeft]: assignment. RHS reads [newLeft], LHS is the
          [_left] field of [res(=n_ptr)]; overwrite [lp] with [nl_ptr]. *)
      wp_assign_setup.
      wp_read_local "Hpnl" (Vptr nl_ptr).
      wp_offset "Hleft".
      wp_assign_member_field "Hres_local" (Vptr n_ptr) "Hstruct" "Hleft".
      iIntros "Hleft_new".
      wp_auto.
      (** [return res]: read [res(=n_ptr)], destroy the [res] local, fold the
          field hyps into [treeR (Node Red newL k v r)], discharge [Hcont]. *)
      iIntros (retp).
      wp_read_local "Hres_local" (Vptr n_ptr).
      iIntros "Hret_store".
      wp_auto.
      wp_destroy_local "Hres_local".
      (** Fold the field hyps into [treeR (Node Red newL k v r)] at [n_ptr]:
          [_left] now points to [nl_ptr] (holding [newL]); [_right] to [rp]. *)
      wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nl_ptr) I.
      iPoseProof (treeR_node_fold _ Red newL k v r nl_ptr rp rc n_ptr
        with "[$Htree_nl $Htree_r $Hrc $Hcolor $Hkey $Hval $Hleft2 $Hright $Hstruct]")
        as "Htree".
      (** [setRebalanceLeft Red newL k v r = Node Red newL k v r] (c=Red arm).
          Discharge [Hcont] with the folded tree at [n_ptr]; frame the parameter
          pointers ([pn]/[pnl] → anyR) and the return store. *)
      iPoseProof ("Hcont" $! n_ptr with "[Htree]") as "Hc".
      { rewrite /setRebalanceLeft /=. iExact "Htree". }
      (** Strip the fupd + [KP]/[ReturnVal] wrapper down to [Q retp]. *)
      repeat wp_step.
      iApply ("Hc" $! retp with "[Hpn Hpnl Hret_store]").
      iFrame "Hret_store".
      iSplitL "Hpn"; [ rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] |].
      rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpnl" | done ].
    + (** Case 2: [c = Black] → check newL *)
      destruct newL as [| c_nl l_nl k_nl v_nl r_nl].
      * (** Case 2a: [newL = Leaf] → default path.
            [is_black(n)] returns true, [is_red(newLeft)] returns false
            (newLeft is nullptr).  Fall through to default. *)
        admit.
      * (** Case 2b: [newL = Node c_nl l_nl k_nl v_nl r_nl] *)
        destruct c_nl.
        -- (** Case 2b-Red: [newL = Node Red ...] → check LL/LR *)
           destruct l_nl as [| c_ll l_ll k_ll v_ll r_ll].
           ++ (** [newL->left = Leaf] → check LR *)
              destruct r_nl as [| c_rl l_rl k_rl v_rl r_rl].
              ** (** Both children Leaf → default *)
                 admit.
              ** destruct c_rl.
                 --- (** [newL->right = Node Red ...] → LR rotation *)
                     admit.
                 --- (** [newL->right = Node Black ...] → default *)
                     admit.
           ++ destruct c_ll.
              ** (** [newL->left = Node Red ...] → LL rotation *)
                 admit.
              ** (** [newL->left = Node Black ...] → check LR *)
                 destruct r_nl as [| c_rl l_rl k_rl v_rl r_rl].
                 --- (** [newL->right = Leaf] → default *)
                     admit.
                 --- destruct c_rl.
                     +++ (** [newL->right = Node Red ...] → LR rotation *)
                         admit.
                     +++ (** [newL->right = Node Black ...] → default *)
                         admit.
        -- (** Case 2b-Black: [newL = Node Black ...] → default path.
              [is_red(newLeft)] returns false. *)
           admit.
Admitted.

(* ================================================================= *)
(** * setRebalanceRight_ok *)
(* ================================================================= *)

(** Mirror of [setRebalanceLeft_ok] with left/right swapped. *)
Lemma setRebalanceRight_ok :
  |-- func_ok source setRebalanceRight_func setRebalanceRight_spec.
Proof using MOD MODULE.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.
  - iIntros "!>" (Q vals) "Hspec".
    iPoseProof MODULE as "#HMOD".
    iApply wp_func_intro.
    rewrite /setRebalanceRight_func /=.
    (** Extract args: n, newRight *)
    iDestruct "Hspec" as (pn vn pnr vnr)
      "(%Hvals & Hpn & Hpnr & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (n_ptr nr_ptr c k v lp rp rc l newR)
      "(%Hargs & Hpre & Hcont)".
    injection Hargs as -> ->. subst.
    iDestruct "Hpre" as "(Hnode & Htree_l & Htree_nr)".
    iDestruct "Hnode" as
      "(Hrc & Hcolor & Hkey & Hval & Hleft & Hright & Hstruct)".
    wp_auto.
    (** Case split mirrors setRebalanceLeft *)
    destruct c.
    + (* c = Red: default *) admit.
    + destruct newR as [| c_nr l_nr k_nr v_nr r_nr].
      * (* newR = Leaf: default *) admit.
      * destruct c_nr.
        -- (* Node Red: check RL/RR *)
           destruct l_nr as [| c_ll l_ll k_ll v_ll r_ll].
           ++ destruct r_nr as [| c_rr l_rr k_rr v_rr r_rr].
              ** (* Both Leaf: default *) admit.
              ** destruct c_rr.
                 --- (* RR rotation *) admit.
                 --- (* default *) admit.
           ++ destruct c_ll.
              ** (* RL rotation *) admit.
              ** destruct r_nr as [| c_rr l_rr k_rr v_rr r_rr].
                 --- (* default *) admit.
                 --- destruct c_rr.
                     +++ (* RR rotation *) admit.
                     +++ (* default *) admit.
        -- (* Node Black: default *) admit.
Admitted.

End with_Sigma.
