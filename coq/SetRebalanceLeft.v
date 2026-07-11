(** * setRebalanceLeft_ok — C++ setRebalanceLeft refinement (default cases).

    Split out of the former monolithic RebalanceSpec.v (see
    docs/notes/2026-07-10_rebalance_perf_plan.md). All 7 default (no-rotation)
    cases are proved; the LL/LR rotation cases remain [admit] (blocked on Phase D
    makeCopy). Shared defs/tactics are in RebalanceDefs.v. *)
From Stdlib Require Import ZArith Bool Lia.

Require Import skylabs.lang.cpp.cpp.
Require Import skylabs.iris.extra.proofmode.proofmode.
Import cQp_compat.

Require Import daedalus_rb.RBTree.
Require Import daedalus_rb.TreeRep.
Require Import daedalus_rb.Tactics.
Require Import daedalus_rb.InsertDefs.
Require Import daedalus_rb.IsBlackSpec.
Require Import daedalus_rb.RebalanceDefs.

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.
Hypothesis MODULE : |-- denoteModule source.

Lemma setRebalanceLeft_ok :
  |-- func_ok source setRebalanceLeft_func setRebalanceLeft_spec.
Proof using MOD MODULE.
  wp_open_func_mod MODULE.
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
    + (** Case 1: [c = Red] → is_black(n)=false short-circuits ⇒ default path. *)
      wp_guard_isblack_false MODULE n_ptr.
      wp_srl_default Red newL n_ptr nl_ptr k v r rp rc.
    + (** Case 2: [c = Black] → check newL *)
      destruct newL as [| c_nl l_nl k_nl v_nl r_nl].
      * (** Case 2a: [newL = Leaf] → default path.
            [is_black(n)] returns true, [is_red(newLeft)] returns false
            (newLeft is nullptr).  Fall through to default. *)
        iApply (wp_if source); iNext.
        rewrite /wp.WPE.wp_test /=.
        iApply wp_operand_seqand.
        rewrite /wp.WPE.wp_test /=.
        (** First guard operand: [is_black(n)] → true (Black node). *)
        wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
          is_black_name (is_black_ok MODULE) is_black_func
          "Hpn" (Vptr n_ptr) "Hstruct".
        rewrite /is_black_spec /=.
        iExists _, (Vptr n_ptr).
        iSplit; [ iPureIntro; reflexivity |].
        iSplitL "Hargp"; [ iFrame "Hargp" |].
        iExists n_ptr, (Some Black), (cQp.m 1).
        iSplit; [ iPureIntro; reflexivity |].
        iSplitL "Hcolor Hstruct".
        { rewrite _at_sep /=. iFrame "Hcolor Hstruct". }
        iIntros (ret) "Hpost".
        iIntros (rx) "(Hany & Hres)".
        wp_auto.
        wp_destroy_prim_temp "Hany".
        iModIntro; rewrite operand_receive.unlock /=.
        iExists (Vbool true).
        iFrame "Hres".
        (** [is_black] = true ⇒ evaluate second operand [is_red(newLeft)]. *)
        simpl.
        iDestruct "Hpost" as "[Hpost _]".
        rewrite _at_sep /=.
        iDestruct "Hpost" as "[Hcolor Hstruct]".
        (** [newL = Leaf] ⇒ [nl_ptr = nullptr]. [treeR _ Leaf] is already reduced
            to [as_Rep (λ p, [|p=nullptr|])] (the fixpoint fires on the concrete
            [Leaf]), so only [_at_as_Rep] is needed, not [treeR_leaf]. *)
        rewrite _at_as_Rep.
        iDestruct "Htree_nl" as "%Hnl_null". subst nl_ptr.
        (** Second guard operand [is_red(newLeft)] with [newLeft = nullptr]:
            resolve the call, provide [is_red_spec]'s [None] branch. The arg is a
            null pointer, so its [has_type] comes from [valid_ptr_nullptr], not a
            [structR] — resolve this call inline rather than via
            [wp_operand_call_direct1]. *)
        iApply wp_operand_call;
          rewrite /wp_call /=;
          iIntros "%Hty2";
          rewrite /wp.WPE.Mbind /wp.WPE.Mmap /=.
        iApply wp_operand_cfun2ptr_global; [ exact is_red_lookup | exact is_red_has_body | ].
        iSplitL "HMOD"; [ iExact "HMOD" |].
        iExists (_global is_red_name).
        iSplit; [ iPureIntro; reflexivity |].
        rewrite /wp.WPE.nd_seqs /=.
        iIntros (pre post q2) "%Hnd".
        destruct pre as [| ?y0 [| ?y1 ?yr]]; simpl in Hnd; try congruence.
        injection Hnd; clear Hnd; intros; subst; simpl.
        rewrite /wp.WPE.Mbind /call.wp_arg /=.
        iIntros (argp2).
        rewrite /wp_initialize /qual_norm /=.
        try rewrite wp_initialize_unqualified.unlock /=.
        iApply wp_operand_cast_noop.
        wp_read_local "Hpnl" (Vptr nullptr).
        (* Extract [_Node]'s alignment fact from the live [structR] at [n_ptr]
           BEFORE the [iSplitR] (Hstruct is spatial; the split would move it). *)
        iDestruct (observe (reference_to _ n_ptr) with "Hstruct") as "#_rtn".
        iDestruct (reference_to_elim with "_rtn") as "(%HalignN & _)".
        iSplitR.
        { (* has_type (Vptr nullptr) (Tptr (const Node)): valid_ptr from
             valid_ptr_nullptr; alignment reuses [_Node]'s [align_of]. *)
          rewrite has_type_ptr'.
          iSplitR; [ iApply valid_ptr_nullptr |].
          iPureIntro. rewrite aligned_ptr_ty_erase_qualifiers /=.
          destruct HalignN as (a & Ha & _). exists a. split; [ exact Ha |].
          left. exists 0%N. rewrite ptr_vaddr_nullptr. split; [ reflexivity |].
          apply N.divide_0_r. }
        iIntros "Hargp2".
        rewrite /wp.WPE.Mmap /wp.WPE.Mret /=.
        iNext.
        iPoseProof (code_at_of_denoteModule _ _ _ is_red_lookup is_red_has_body
          with "HMOD") as "#_call_ca2".
        iPoseProof (is_red_ok MODULE) as "#_call_fok2".
        match goal with |- context[wp_fptr _ ?ft _ _ _] =>
          replace ft with (type_of_value (Ofunction is_red_func))
            by (vm_compute; reflexivity)
        end.
        iApply (wp_fptr_of_func_ok_compat _ _ _ _ _ _ (tu_compat)).
        iSplitR; [ iExact "_call_ca2" |].
        iSplitR; [ iExact "_call_fok2" |].
        (** [is_red_spec] precond, [None] branch: [nl_ptr = nullptr]. *)
        rewrite /is_red_spec /=.
        iExists _, (Vptr nullptr).
        iSplit; [ iPureIntro; reflexivity |].
        iSplitL "Hargp2"; [ iFrame "Hargp2" |].
        iExists nullptr, None, (cQp.m 1).
        iSplit; [ iPureIntro; reflexivity |].
        iSplitR; [ iPureIntro; reflexivity |].
        (** Receive [is_red] = false; guard [true && false = false] ⇒ default. *)
        iIntros (ret2) "Hpost2".
        iIntros (rx2) "(Hany2 & Hres2)".
        wp_auto.
        wp_destroy_prim_temp "Hany2".
        iModIntro; rewrite operand_receive.unlock /=.
        iExists (Vbool false).
        iFrame "Hres2".
        simpl.
        (** Recover [_color]/[structR] at [n_ptr] from is_red's read-only post
            ([None] branch returns just the pure [nl=nullptr], so [Hpost2] is the
            is_black-returned color/struct — wait: is_red's None post is emp; the
            color/struct we still hold from the is_black post). *)
        (** Re-establish [nullptr |-> treeR _ Leaf] for the fold (it reduces to
            [|nullptr = nullptr|]). *)
        iAssert (nullptr |-> treeR (cQp.m 1) (Leaf (K:=Z) (V:=Z)))%I as "Htree_nl".
        { rewrite treeR_leaf _at_as_Rep. done. }
        (** Default path: [res = n; res->left = newLeft(=nullptr); return res]. *)
        wp_auto.
        iIntros (addr).
        wp_read_local "Hpn" (Vptr n_ptr).
        iIntros "Hres_local".
        wp_auto.
        wp_assign_setup.
        wp_read_local "Hpnl" (Vptr nullptr).
        wp_offset "Hleft".
        wp_assign_member_field "Hres_local" (Vptr n_ptr) "Hstruct" "Hleft".
        iIntros "Hleft_new".
        wp_auto.
        iIntros (retp).
        wp_read_local "Hres_local" (Vptr n_ptr).
        iIntros "Hret_store".
        wp_auto.
        wp_destroy_local "Hres_local".
        wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nullptr) I.
        iPoseProof (treeR_node_fold _ Black Leaf k v r nullptr rp rc n_ptr
          with "[$Htree_nl $Htree_r $Hrc $Hcolor $Hkey $Hval $Hleft2 $Hright $Hstruct]")
          as "Htree".
        iPoseProof ("Hcont" $! n_ptr with "[Htree]") as "Hc".
        { rewrite /setRebalanceLeft /=. iExact "Htree". }
        repeat wp_step.
        iApply ("Hc" $! retp with "[Hpn Hpnl Hret_store]").
        iFrame "Hret_store".
        iSplitL "Hpn"; [ rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] |].
        rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpnl" | done ].
      * (** Case 2b: [newL = Node c_nl l_nl k_nl v_nl r_nl] *)
        destruct c_nl.
        -- (** Case 2b-Red: [newL = Node Red ...] → check LL/LR *)
           destruct l_nl as [| c_ll l_ll k_ll v_ll r_ll].
           ++ (** [newL->left = Leaf] → check LR *)
              destruct r_nl as [| c_rl l_rl k_rl v_rl r_rl].
              ** (** Both children Leaf → default (no rotation).
                    Guard [is_black(n)=true && is_red(newLeft)=true] enters the
                    rotation body; [is_red(sub2=newLeft->left=null)=false] and
                    [is_red(sub2=newLeft->right=null)=false] short-circuit both
                    rotation checks; default path folds [Node Black newL k v r]. *)
                 iApply (wp_if source); iNext.
                 rewrite /wp.WPE.wp_test /=.
                 iApply wp_operand_seqand.
                 rewrite /wp.WPE.wp_test /=.
                 (** is_black(n) → true. *)
                 wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
                   is_black_name (is_black_ok MODULE) is_black_func
                   "Hpn" (Vptr n_ptr) "Hstruct".
                 rewrite /is_black_spec /=.
                 iExists _, (Vptr n_ptr).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "Hargp"; [ iFrame "Hargp" |].
                 iExists n_ptr, (Some Black), (cQp.m 1).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "Hcolor Hstruct".
                 { rewrite _at_sep /=. iFrame "Hcolor Hstruct". }
                 iIntros (ret) "Hpost".
                 iIntros (rx) "(Hany & Hres)".
                 wp_auto.
                 wp_destroy_prim_temp "Hany".
                 iModIntro; rewrite operand_receive.unlock /=.
                 iExists (Vbool true).
                 iFrame "Hres".
                 simpl.
                 iDestruct "Hpost" as "[Hpost _]".
                 rewrite _at_sep /=.
                 iDestruct "Hpost" as "[Hcolor Hstruct]".
                 (** is_red(newLeft) → true (Node Red). Unfold newL's fields. *)
                 wp_unfold_node "Htree_nl".
                 wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                   is_red_name (is_red_ok MODULE) is_red_func
                   "Hpnl" (Vptr nl_ptr) "_nstruct".
                 rewrite /is_red_spec /=.
                 iExists _, (Vptr nl_ptr).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "Hargp"; [ iFrame "Hargp" |].
                 iExists nl_ptr, (Some Red), (cQp.m 1).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "_ncolor _nstruct".
                 { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                 iIntros (ret2) "Hpost2".
                 iIntros (rx2) "(Hany2 & Hres2)".
                 wp_auto.
                 wp_destroy_prim_temp "Hany2".
                 iModIntro; rewrite operand_receive.unlock /=.
                 iExists (Vbool true).
                 iFrame "Hres2".
                 simpl.
                 iDestruct "Hpost2" as "[Hpost2 _]".
                 rewrite _at_sep /=.
                 iDestruct "Hpost2" as "[_ncolor _nstruct]".
                 (** [newL->left = Leaf] ⇒ [_lp = nullptr]; likewise [_rp]. *)
                 rewrite (_at_as_Rep _lp) (_at_as_Rep _rp).
                 iDestruct "_ntl" as "%Hlp_null".
                 iDestruct "_ntr" as "%Hrp_null".
                 subst _lp _rp.
                 (** [sub2 = newLeft->left] (= nullptr): declare local, read. *)
                 wp_auto.
                 iIntros (sub2p).
                 wp_read_field "Hpnl" (Vptr nl_ptr) "_nstruct" "_nleft" (Vptr nullptr).
                 iIntros "Hsub2_local".
                 wp_auto.
                 (** LL-check [is_red(sub2 = nullptr)] → false. *)
                 iApply (wp_if source); iNext.
                 rewrite /wp.WPE.wp_test /=.
                 wp_operand_call_direct1_null "HMOD" is_red_lookup is_red_has_body
                   is_red_name (is_red_ok MODULE) is_red_func "Hsub2_local" "Hstruct".
                 rewrite /is_red_spec /=.
                 iExists _, (Vptr nullptr).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "Hargp"; [ iFrame "Hargp" |].
                 iExists nullptr, None, (cQp.m 1).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitR; [ iPureIntro; reflexivity |].
                 iIntros (ret3) "Hpost3".
                 iIntros (rx3) "(Hany3 & Hres3)".
                 wp_auto.
                 wp_destroy_prim_temp "Hany3".
                 iModIntro; rewrite operand_receive.unlock /=.
                 iExists (Vbool false).
                 iFrame "Hres3".
                 simpl.
                 (** [sub2 = newLeft->right] (= nullptr): reassign the local. *)
                 wp_auto.
                 iApply wp_lval_assign.
                 rewrite /=.
                 wp_read_field "Hpnl" (Vptr nl_ptr) "_nstruct" "_nright" (Vptr nullptr).
                 wp_assign_local "Hsub2_local".
                 iIntros "Hsub2_new".
                 iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                 wp_auto.
                 (** LR-check [is_red(sub2 = nullptr)] → false. *)
                 iApply (wp_if source); iNext.
                 rewrite /wp.WPE.wp_test /=.
                 wp_operand_call_direct1_null "HMOD" is_red_lookup is_red_has_body
                   is_red_name (is_red_ok MODULE) is_red_func "Hsub2_local" "Hstruct".
                 rewrite /is_red_spec /=.
                 iExists _, (Vptr nullptr).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "Hargp"; [ iFrame "Hargp" |].
                 iExists nullptr, None, (cQp.m 1).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitR; [ iPureIntro; reflexivity |].
                 iIntros (ret4) "Hpost4".
                 iIntros (rx4) "(Hany4 & Hres4)".
                 wp_auto.
                 wp_destroy_prim_temp "Hany4".
                 iModIntro; rewrite operand_receive.unlock /=.
                 iExists (Vbool false).
                 iFrame "Hres4".
                 simpl.
                 (** [sub2] goes out of scope at the end of the rotation-body
                     [Sseq]; destroy it before the outer default sequence. *)
                 wp_auto.
                 wp_destroy_local "Hsub2_local".
                 (** No rotation ⇒ default. Re-fold [newL = Node Red Leaf .. Leaf]
                     at [nl_ptr]. The Leaf children ([nullptr |-> treeR Leaf]) are
                     provided as the two [iSplitR] subgoals; the fields are matched
                     by [iExact] on the bundle after [_at_sep] (NOT [iFrame], which
                     misses on the [1$m] coercion-path form). *)
                 wp_revert_offset "_nleft".
                 wp_revert_offset "_nright".
                 iAssert (nl_ptr |-> treeR (cQp.m 1) (Node Red Leaf k_nl v_nl Leaf))%I
                   with "[_nrc _ncolor _nkey _nval _nleft _nright _nstruct]" as "Htree_nl".
                 { iApply (treeR_node_fold (cQp.m 1) Red Leaf k_nl v_nl Leaf
                     nullptr nullptr _rc nl_ptr).
                   iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].
                   iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].
                   rewrite !_at_sep.
                   iSplitL "_nrc"; [ iExact "_nrc" |].
                   iSplitL "_ncolor"; [ iExact "_ncolor" |].
                   iSplitL "_nkey"; [ iExact "_nkey" |].
                   iSplitL "_nval"; [ iExact "_nval" |].
                   iSplitL "_nleft"; [ iExact "_nleft" |].
                   iSplitL "_nright"; [ iExact "_nright" |].
                   iExact "_nstruct". }
                 (** Default path: [res = n; res->left = newLeft; return res]. *)
                 wp_auto.
                 iIntros (addr).
                 wp_read_local "Hpn" (Vptr n_ptr).
                 iIntros "Hres_local".
                 wp_auto.
                 wp_assign_setup.
                 wp_read_local "Hpnl" (Vptr nl_ptr).
                 wp_offset "Hleft".
                 wp_assign_member_field "Hres_local" (Vptr n_ptr) "Hstruct" "Hleft".
                 iIntros "Hleft_new".
                 wp_auto.
                 iIntros (retp).
                 wp_read_local "Hres_local" (Vptr n_ptr).
                 iIntros "Hret_store".
                 wp_auto.
                 wp_destroy_local "Hres_local".
                 wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nl_ptr) I.
                 iPoseProof (treeR_node_fold _ Black
                   (Node Red Leaf k_nl v_nl Leaf) k v r nl_ptr rp rc n_ptr
                   with "[$Htree_nl $Htree_r $Hrc $Hcolor $Hkey $Hval $Hleft2 $Hright $Hstruct]")
                   as "Htree".
                 iPoseProof ("Hcont" $! n_ptr with "[Htree]") as "Hc".
                 { rewrite /setRebalanceLeft /=. iExact "Htree". }
                 repeat wp_step.
                 iApply ("Hc" $! retp with "[Hpn Hpnl Hret_store]").
                 iFrame "Hret_store".
                 iSplitL "Hpn"; [ rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] |].
                 rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpnl" | done ].
              ** destruct c_rl.
                 --- (** [newL->right = Node Red ...] → LR rotation *)
                     admit.
                 --- (** [newL->right = Node Black ...] → default (no rotation).
                        newL = Node Red Leaf k_nl v_nl (Node Black ...). Guard
                        true/true → body; LL is_red(sub2=left=null)=false; LR
                        is_red(sub2=right=Node Black)=false (Some Black). *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     iApply wp_operand_seqand.
                     rewrite /wp.WPE.wp_test /=.
                     (** is_black(n) → true. *)
                     wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
                       is_black_name (is_black_ok MODULE) is_black_func
                       "Hpn" (Vptr n_ptr) "Hstruct".
                     rewrite /is_black_spec /=.
                     iExists _, (Vptr n_ptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists n_ptr, (Some Black), (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hcolor Hstruct".
                     { rewrite _at_sep /=. iFrame "Hcolor Hstruct". }
                     iIntros (ret) "Hpost".
                     iIntros (rx) "(Hany & Hres)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool true).
                     iFrame "Hres".
                     simpl.
                     iDestruct "Hpost" as "[Hpost _]".
                     rewrite _at_sep /=.
                     iDestruct "Hpost" as "[Hcolor Hstruct]".
                     (** is_red(newLeft) → true (Node Red). Unfold newL. *)
                     wp_unfold_node "Htree_nl".
                     wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func
                       "Hpnl" (Vptr nl_ptr) "_nstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr nl_ptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists nl_ptr, (Some Red), (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "_ncolor _nstruct".
                     { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                     iIntros (ret2) "Hpost2".
                     iIntros (rx2) "(Hany2 & Hres2)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany2".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool true).
                     iFrame "Hres2".
                     simpl.
                     iDestruct "Hpost2" as "[Hpost2 _]".
                     rewrite _at_sep /=.
                     iDestruct "Hpost2" as "[_ncolor _nstruct]".
                     (** newL->left = Leaf ⇒ _lp = nullptr. *)
                     rewrite (_at_as_Rep _lp).
                     iDestruct "_ntl" as "%Hlp_null". subst _lp.
                     (** sub2 = newLeft->left (= nullptr). *)
                     wp_auto.
                     iIntros (sub2p).
                     wp_read_field "Hpnl" (Vptr nl_ptr) "_nstruct" "_nleft" (Vptr nullptr).
                     iIntros "Hsub2_local".
                     wp_auto.
                     (** LL-check is_red(sub2 = nullptr) → false. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     wp_operand_call_direct1_null "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func "Hsub2_local" "Hstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr nullptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists nullptr, None, (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitR; [ iPureIntro; reflexivity |].
                     iIntros (ret3) "Hpost3".
                     iIntros (rx3) "(Hany3 & Hres3)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany3".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool false).
                     iFrame "Hres3".
                     simpl.
                     (** sub2 = newLeft->right (= _rp, a Node Black). *)
                     wp_auto.
                     iApply wp_lval_assign.
                     rewrite /=.
                     wp_read_field "Hpnl" (Vptr nl_ptr) "_nstruct" "_nright" (Vptr _rp).
                     wp_assign_local "Hsub2_local".
                     iIntros "Hsub2_new".
                     iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                     wp_auto.
                     (** LR-check is_red(sub2 = _rp = Node Black) → false (Some
                         Black). Rename newL's fields (free the [_n*] names), then
                         unfold the right child to borrow its color/struct. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     iRename "_nrc" into "L_nrc"; iRename "_ncolor" into "L_ncolor";
                     iRename "_nkey" into "L_nkey"; iRename "_nval" into "L_nval";
                     iRename "_nleft" into "L_nleft"; iRename "_nright" into "L_nright";
                     iRename "_nstruct" into "L_nstruct".
                     wp_unfold_node "_ntr".
                     wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func
                       "Hsub2_local" (Vptr _rp) "_nstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr _rp).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists _rp, (Some Black), (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "_ncolor _nstruct".
                     { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                     iIntros (ret4) "Hpost4".
                     iIntros (rx4) "(Hany4 & Hres4)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany4".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool false).
                     iFrame "Hres4".
                     simpl.
                     iDestruct "Hpost4" as "[Hpost4 _]".
                     rewrite _at_sep /=.
                     iDestruct "Hpost4" as "[_ncolor _nstruct]".
                     (** sub2 out of scope; destroy before outer default. *)
                     wp_auto.
                     wp_destroy_local "Hsub2_local".
                     (** Re-fold the right child [Node Black l_rl .. r_rl] at [_rp]
                         (its fields are the fresh [_n*] from [wp_unfold_node "_ntr"];
                         its child ptrs are [_lp0/_rp0/_rc0], grandchildren
                         [_ntl/_ntr]), then [newL = Node Red Leaf .. (Node Black ..)]
                         at [nl_ptr] (newL's fields are the renamed [L_n*]). *)
                     iPoseProof (treeR_node_fold _ Black l_rl k_rl v_rl r_rl
                       _ _ _ _rp
                       with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                       as "Htree_r_child".
                     wp_revert_offset "L_nleft".
                     wp_revert_offset "L_nright".
                     iAssert (nl_ptr |-> treeR (cQp.m 1)
                                (Node Red Leaf k_nl v_nl (Node Black l_rl k_rl v_rl r_rl)))%I
                       with "[L_nrc L_ncolor L_nkey L_nval L_nleft L_nright L_nstruct Htree_r_child]"
                       as "Htree_nl".
                     { iApply (treeR_node_fold (cQp.m 1) Red Leaf k_nl v_nl
                         (Node Black l_rl k_rl v_rl r_rl) nullptr _rp _rc nl_ptr).
                       iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].
                       iSplitL "Htree_r_child"; [ iExact "Htree_r_child" |].
                       rewrite !_at_sep.
                       iSplitL "L_nrc"; [ iExact "L_nrc" |].
                       iSplitL "L_ncolor"; [ iExact "L_ncolor" |].
                       iSplitL "L_nkey"; [ iExact "L_nkey" |].
                       iSplitL "L_nval"; [ iExact "L_nval" |].
                       iSplitL "L_nleft"; [ iExact "L_nleft" |].
                       iSplitL "L_nright"; [ iExact "L_nright" |].
                       iExact "L_nstruct". }
                     (** Default path. *)
                     wp_auto.
                     iIntros (addr).
                     wp_read_local "Hpn" (Vptr n_ptr).
                     iIntros "Hres_local".
                     wp_auto.
                     wp_assign_setup.
                     wp_read_local "Hpnl" (Vptr nl_ptr).
                     wp_offset "Hleft".
                     wp_assign_member_field "Hres_local" (Vptr n_ptr) "Hstruct" "Hleft".
                     iIntros "Hleft_new".
                     wp_auto.
                     iIntros (retp).
                     wp_read_local "Hres_local" (Vptr n_ptr).
                     iIntros "Hret_store".
                     wp_auto.
                     wp_destroy_local "Hres_local".
                     wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nl_ptr) I.
                     iPoseProof (treeR_node_fold _ Black
                       (Node Red Leaf k_nl v_nl (Node Black l_rl k_rl v_rl r_rl))
                       k v r nl_ptr rp rc n_ptr
                       with "[$Htree_nl $Htree_r $Hrc $Hcolor $Hkey $Hval $Hleft2 $Hright $Hstruct]")
                       as "Htree".
                     iPoseProof ("Hcont" $! n_ptr with "[Htree]") as "Hc".
                     { rewrite /setRebalanceLeft /=. iExact "Htree". }
                     repeat wp_step.
                     iApply ("Hc" $! retp with "[Hpn Hpnl Hret_store]").
                     iFrame "Hret_store".
                     iSplitL "Hpn"; [ rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] |].
                     rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpnl" | done ].
           ++ destruct c_ll.
              ** (** [newL->left = Node Red ...] → LL rotation *)
                 admit.
              ** (** [newL->left = Node Black ...] → check LR *)
                 destruct r_nl as [| c_rl l_rl k_rl v_rl r_rl].
                 --- (** [newL->right = Leaf] → default (no rotation).
                        newL = Node Red (Node Black ..) k_nl v_nl Leaf. Guard
                        true/true → body; LL is_red(sub2=left=Node Black)=false
                        (Some Black); LR is_red(sub2=right=null)=false. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     iApply wp_operand_seqand.
                     rewrite /wp.WPE.wp_test /=.
                     (** is_black(n) → true. *)
                     wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
                       is_black_name (is_black_ok MODULE) is_black_func
                       "Hpn" (Vptr n_ptr) "Hstruct".
                     rewrite /is_black_spec /=.
                     iExists _, (Vptr n_ptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists n_ptr, (Some Black), (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hcolor Hstruct".
                     { rewrite _at_sep /=. iFrame "Hcolor Hstruct". }
                     iIntros (ret) "Hpost".
                     iIntros (rx) "(Hany & Hres)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool true).
                     iFrame "Hres".
                     simpl.
                     iDestruct "Hpost" as "[Hpost _]".
                     rewrite _at_sep /=.
                     iDestruct "Hpost" as "[Hcolor Hstruct]".
                     (** is_red(newLeft) → true (Node Red). Unfold newL. *)
                     wp_unfold_node "Htree_nl".
                     wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func
                       "Hpnl" (Vptr nl_ptr) "_nstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr nl_ptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists nl_ptr, (Some Red), (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "_ncolor _nstruct".
                     { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                     iIntros (ret2) "Hpost2".
                     iIntros (rx2) "(Hany2 & Hres2)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany2".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool true).
                     iFrame "Hres2".
                     simpl.
                     iDestruct "Hpost2" as "[Hpost2 _]".
                     rewrite _at_sep /=.
                     iDestruct "Hpost2" as "[_ncolor _nstruct]".
                     (** newL->right = Leaf ⇒ _rp = nullptr. *)
                     rewrite (_at_as_Rep _rp).
                     iDestruct "_ntr" as "%Hrp_null". subst _rp.
                     (** sub2 = newLeft->left (= _lp, a Node Black). *)
                     wp_auto.
                     iIntros (sub2p).
                     wp_read_field "Hpnl" (Vptr nl_ptr) "_nstruct" "_nleft" (Vptr _lp).
                     iIntros "Hsub2_local".
                     wp_auto.
                     (** LL-check is_red(sub2 = _lp = Node Black) → false (Some
                         Black). Rename newL's fields, unfold the left child. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     iRename "_nrc" into "L_nrc"; iRename "_ncolor" into "L_ncolor";
                     iRename "_nkey" into "L_nkey"; iRename "_nval" into "L_nval";
                     iRename "_nleft" into "L_nleft"; iRename "_nright" into "L_nright";
                     iRename "_nstruct" into "L_nstruct".
                     wp_unfold_node "_ntl".
                     wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func
                       "Hsub2_local" (Vptr _lp) "_nstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr _lp).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists _lp, (Some Black), (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "_ncolor _nstruct".
                     { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                     iIntros (ret3) "Hpost3".
                     iIntros (rx3) "(Hany3 & Hres3)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany3".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool false).
                     iFrame "Hres3".
                     simpl.
                     iDestruct "Hpost3" as "[Hpost3 _]".
                     rewrite _at_sep /=.
                     iDestruct "Hpost3" as "[_ncolor _nstruct]".
                     (** sub2 = newLeft->right (= nullptr). *)
                     wp_auto.
                     iApply wp_lval_assign.
                     rewrite /=.
                     wp_read_field "Hpnl" (Vptr nl_ptr) "L_nstruct" "L_nright" (Vptr nullptr).
                     wp_assign_local "Hsub2_local".
                     iIntros "Hsub2_new".
                     iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                     wp_auto.
                     (** LR-check is_red(sub2 = nullptr) → false. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     wp_operand_call_direct1_null "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func "Hsub2_local" "Hstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr nullptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists nullptr, None, (cQp.m 1).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitR; [ iPureIntro; reflexivity |].
                     iIntros (ret4) "Hpost4".
                     iIntros (rx4) "(Hany4 & Hres4)".
                     wp_auto.
                     wp_destroy_prim_temp "Hany4".
                     iModIntro; rewrite operand_receive.unlock /=.
                     iExists (Vbool false).
                     iFrame "Hres4".
                     simpl.
                     (** sub2 out of scope; destroy before outer default. *)
                     wp_auto.
                     wp_destroy_local "Hsub2_local".
                     (** Re-fold the left child [Node Black l_ll .. r_ll] at [_lp],
                         then [newL = Node Red (Node Black ..) k_nl v_nl Leaf]. *)
                     iPoseProof (treeR_node_fold _ Black l_ll k_ll v_ll r_ll
                       _ _ _ _lp
                       with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                       as "Htree_l_child".
                     wp_revert_offset "L_nleft".
                     wp_revert_offset "L_nright".
                     iAssert (nl_ptr |-> treeR (cQp.m 1)
                                (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nl v_nl Leaf))%I
                       with "[L_nrc L_ncolor L_nkey L_nval L_nleft L_nright L_nstruct Htree_l_child]"
                       as "Htree_nl".
                     { iApply (treeR_node_fold (cQp.m 1) Red
                         (Node Black l_ll k_ll v_ll r_ll) k_nl v_nl Leaf
                         _lp nullptr _rc nl_ptr).
                       iSplitL "Htree_l_child"; [ iExact "Htree_l_child" |].
                       iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].
                       rewrite !_at_sep.
                       iSplitL "L_nrc"; [ iExact "L_nrc" |].
                       iSplitL "L_ncolor"; [ iExact "L_ncolor" |].
                       iSplitL "L_nkey"; [ iExact "L_nkey" |].
                       iSplitL "L_nval"; [ iExact "L_nval" |].
                       iSplitL "L_nleft"; [ iExact "L_nleft" |].
                       iSplitL "L_nright"; [ iExact "L_nright" |].
                       iExact "L_nstruct". }
                     (** Default path. *)
                     wp_auto.
                     iIntros (addr).
                     wp_read_local "Hpn" (Vptr n_ptr).
                     iIntros "Hres_local".
                     wp_auto.
                     wp_assign_setup.
                     wp_read_local "Hpnl" (Vptr nl_ptr).
                     wp_offset "Hleft".
                     wp_assign_member_field "Hres_local" (Vptr n_ptr) "Hstruct" "Hleft".
                     iIntros "Hleft_new".
                     wp_auto.
                     iIntros (retp).
                     wp_read_local "Hres_local" (Vptr n_ptr).
                     iIntros "Hret_store".
                     wp_auto.
                     wp_destroy_local "Hres_local".
                     wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nl_ptr) I.
                     iPoseProof (treeR_node_fold _ Black
                       (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nl v_nl Leaf)
                       k v r nl_ptr rp rc n_ptr
                       with "[$Htree_nl $Htree_r $Hrc $Hcolor $Hkey $Hval $Hleft2 $Hright $Hstruct]")
                       as "Htree".
                     iPoseProof ("Hcont" $! n_ptr with "[Htree]") as "Hc".
                     { rewrite /setRebalanceLeft /=. iExact "Htree". }
                     repeat wp_step.
                     iApply ("Hc" $! retp with "[Hpn Hpnl Hret_store]").
                     iFrame "Hret_store".
                     iSplitL "Hpn"; [ rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] |].
                     rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpnl" | done ].
                 --- destruct c_rl.
                     +++ (** [newL->right = Node Red ...] → LR rotation *)
                         admit.
                     +++ (** [newL->right = Node Black ...] → default (no rotation).
                            newL = Node Red (Node Black ..) k_nl v_nl (Node Black ..).
                            Guard true/true → body; LL is_red(sub2=left=Node Black)
                            =false; LR is_red(sub2=right=Node Black)=false. Both
                            children unfolded (via wp_unfold_node', robust against
                            the competing as_Rep of the sibling child) to borrow
                            color/struct (Some Black), then re-folded. *)
                         iApply (wp_if source); iNext.
                         rewrite /wp.WPE.wp_test /=.
                         iApply wp_operand_seqand.
                         rewrite /wp.WPE.wp_test /=.
                         (** is_black(n) → true. *)
                         wp_operand_call_direct1 "HMOD" is_black_lookup is_black_has_body
                           is_black_name (is_black_ok MODULE) is_black_func
                           "Hpn" (Vptr n_ptr) "Hstruct".
                         rewrite /is_black_spec /=.
                         iExists _, (Vptr n_ptr).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "Hargp"; [ iFrame "Hargp" |].
                         iExists n_ptr, (Some Black), (cQp.m 1).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "Hcolor Hstruct".
                         { rewrite _at_sep /=. iFrame "Hcolor Hstruct". }
                         iIntros (ret) "Hpost".
                         iIntros (rx) "(Hany & Hres)".
                         wp_auto.
                         wp_destroy_prim_temp "Hany".
                         iModIntro; rewrite operand_receive.unlock /=.
                         iExists (Vbool true).
                         iFrame "Hres".
                         simpl.
                         iDestruct "Hpost" as "[Hpost _]".
                         rewrite _at_sep /=.
                         iDestruct "Hpost" as "[Hcolor Hstruct]".
                         (** is_red(newLeft) → true. Unfold newL robustly: the OLD
                             wp_unfold_node's goal-wide [rewrite _at_as_Rep] would
                             ALSO reduce the (concrete-Node) children's [treeR] to
                             [as_Rep], blocking their later re-unfold — use
                             wp_unfold_node' so the children stay in [treeR (Node)]
                             head form. *)
                         wp_unfold_node' "Htree_nl".
                         wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                           is_red_name (is_red_ok MODULE) is_red_func
                           "Hpnl" (Vptr nl_ptr) "_nstruct".
                         rewrite /is_red_spec /=.
                         iExists _, (Vptr nl_ptr).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "Hargp"; [ iFrame "Hargp" |].
                         iExists nl_ptr, (Some Red), (cQp.m 1).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "_ncolor _nstruct".
                         { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                         iIntros (ret2) "Hpost2".
                         iIntros (rx2) "(Hany2 & Hres2)".
                         wp_auto.
                         wp_destroy_prim_temp "Hany2".
                         iModIntro; rewrite operand_receive.unlock /=.
                         iExists (Vbool true).
                         iFrame "Hres2".
                         simpl.
                         iDestruct "Hpost2" as "[Hpost2 _]".
                         rewrite _at_sep /=.
                         iDestruct "Hpost2" as "[_ncolor _nstruct]".
                         (** sub2 = newLeft->left (= _lp, a Node Black). *)
                         wp_auto.
                         iIntros (sub2p).
                         wp_read_field "Hpnl" (Vptr nl_ptr) "_nstruct" "_nleft" (Vptr _lp).
                         iIntros "Hsub2_local".
                         wp_auto.
                         (** LL-check is_red(sub2 = _lp = Node Black) → false.
                             Rename newL's fields to L_n*, robustly unfold the LEFT
                             child (_ntr is a competing as_Rep ⇒ need wp_unfold_node'). *)
                         iApply (wp_if source); iNext.
                         rewrite /wp.WPE.wp_test /=.
                         iRename "_nrc" into "L_nrc"; iRename "_ncolor" into "L_ncolor";
                         iRename "_nkey" into "L_nkey"; iRename "_nval" into "L_nval";
                         iRename "_nleft" into "L_nleft"; iRename "_nright" into "L_nright";
                         iRename "_nstruct" into "L_nstruct".
                         (** Also move the parent's RIGHT child treeR out of the
                             way so the left child's unfold ([_ntl]/[_ntr]/[_n*])
                             doesn't clash with it. *)
                         iRename "_ntr" into "R_child".
                         wp_unfold_node' "_ntl".
                         wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                           is_red_name (is_red_ok MODULE) is_red_func
                           "Hsub2_local" (Vptr _lp) "_nstruct".
                         rewrite /is_red_spec /=.
                         iExists _, (Vptr _lp).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "Hargp"; [ iFrame "Hargp" |].
                         iExists _lp, (Some Black), (cQp.m 1).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "_ncolor _nstruct".
                         { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                         iIntros (ret3) "Hpost3".
                         iIntros (rx3) "(Hany3 & Hres3)".
                         wp_auto.
                         wp_destroy_prim_temp "Hany3".
                         iModIntro; rewrite operand_receive.unlock /=.
                         iExists (Vbool false).
                         iFrame "Hres3".
                         simpl.
                         iDestruct "Hpost3" as "[Hpost3 _]".
                         rewrite _at_sep /=.
                         iDestruct "Hpost3" as "[_ncolor _nstruct]".
                         (** Re-fold the LEFT child now (its fields are the current
                             [_n] hyps), freeing those names for the right child. *)
                         iPoseProof (treeR_node_fold _ Black l_ll k_ll v_ll r_ll
                           _ _ _ _lp
                           with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                           as "Htree_l_child".
                         (** sub2 = newLeft->right (= _rp, a Node Black). *)
                         wp_auto.
                         iApply wp_lval_assign.
                         rewrite /=.
                         wp_read_field "Hpnl" (Vptr nl_ptr) "L_nstruct" "L_nright" (Vptr _rp).
                         wp_assign_local "Hsub2_local".
                         iIntros "Hsub2_new".
                         iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                         wp_auto.
                         (** LR-check is_red(sub2 = _rp = Node Black) → false.
                             Unfold the RIGHT child (Htree_l_child is a competing
                             as_Rep ⇒ need wp_unfold_node'). *)
                         iApply (wp_if source); iNext.
                         rewrite /wp.WPE.wp_test /=.
                         wp_unfold_node' "R_child".
                         wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                           is_red_name (is_red_ok MODULE) is_red_func
                           "Hsub2_local" (Vptr _rp) "_nstruct".
                         rewrite /is_red_spec /=.
                         iExists _, (Vptr _rp).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "Hargp"; [ iFrame "Hargp" |].
                         iExists _rp, (Some Black), (cQp.m 1).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "_ncolor _nstruct".
                         { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
                         iIntros (ret4) "Hpost4".
                         iIntros (rx4) "(Hany4 & Hres4)".
                         wp_auto.
                         wp_destroy_prim_temp "Hany4".
                         iModIntro; rewrite operand_receive.unlock /=.
                         iExists (Vbool false).
                         iFrame "Hres4".
                         simpl.
                         iDestruct "Hpost4" as "[Hpost4 _]".
                         rewrite _at_sep /=.
                         iDestruct "Hpost4" as "[_ncolor _nstruct]".
                         (** sub2 out of scope; destroy before outer default. *)
                         wp_auto.
                         wp_destroy_local "Hsub2_local".
                         (** Re-fold the RIGHT child, then newL. *)
                         iPoseProof (treeR_node_fold _ Black l_rl k_rl v_rl r_rl
                           _ _ _ _rp
                           with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                           as "Htree_r_child".
                         wp_revert_offset "L_nleft".
                         wp_revert_offset "L_nright".
                         iAssert (nl_ptr |-> treeR (cQp.m 1)
                                    (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nl v_nl
                                       (Node Black l_rl k_rl v_rl r_rl)))%I
                           with "[L_nrc L_ncolor L_nkey L_nval L_nleft L_nright L_nstruct Htree_l_child Htree_r_child]"
                           as "Htree_nl".
                         { iApply (treeR_node_fold (cQp.m 1) Red
                             (Node Black l_ll k_ll v_ll r_ll) k_nl v_nl
                             (Node Black l_rl k_rl v_rl r_rl) _lp _rp _rc nl_ptr).
                           iSplitL "Htree_l_child"; [ iExact "Htree_l_child" |].
                           iSplitL "Htree_r_child"; [ iExact "Htree_r_child" |].
                           rewrite !_at_sep.
                           iSplitL "L_nrc"; [ iExact "L_nrc" |].
                           iSplitL "L_ncolor"; [ iExact "L_ncolor" |].
                           iSplitL "L_nkey"; [ iExact "L_nkey" |].
                           iSplitL "L_nval"; [ iExact "L_nval" |].
                           iSplitL "L_nleft"; [ iExact "L_nleft" |].
                           iSplitL "L_nright"; [ iExact "L_nright" |].
                           iExact "L_nstruct". }
                         (** Default path. *)
                         wp_auto.
                         iIntros (addr).
                         wp_read_local "Hpn" (Vptr n_ptr).
                         iIntros "Hres_local".
                         wp_auto.
                         wp_assign_setup.
                         wp_read_local "Hpnl" (Vptr nl_ptr).
                         wp_offset "Hleft".
                         wp_assign_member_field "Hres_local" (Vptr n_ptr) "Hstruct" "Hleft".
                         iIntros "Hleft_new".
                         wp_auto.
                         iIntros (retp).
                         wp_read_local "Hres_local" (Vptr n_ptr).
                         iIntros "Hret_store".
                         wp_auto.
                         wp_destroy_local "Hres_local".
                         wp_field_to_primR "Hleft_new" "Hleft2" (Vptr nl_ptr) I.
                         iPoseProof (treeR_node_fold _ Black
                           (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nl v_nl
                              (Node Black l_rl k_rl v_rl r_rl))
                           k v r nl_ptr rp rc n_ptr
                           with "[$Htree_nl $Htree_r $Hrc $Hcolor $Hkey $Hval $Hleft2 $Hright $Hstruct]")
                           as "Htree".
                         iPoseProof ("Hcont" $! n_ptr with "[Htree]") as "Hc".
                         { rewrite /setRebalanceLeft /=. iExact "Htree". }
                         repeat wp_step.
                         iApply ("Hc" $! retp with "[Hpn Hpnl Hret_store]").
                         iFrame "Hret_store".
                         iSplitL "Hpn"; [ rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpn" | done ] |].
                         rewrite anyR_tptsto_fuzzyR_val_2; [ iFrame "Hpnl" | done ].
        -- (** Case 2b-Black: [newL = Node Black ...] → default path.
              [is_black(n)]=true, [is_red(newLeft)]=false (newLeft is Black). *)
           wp_guard_isblack_true MODULE n_ptr.
           (** Unfold [newL = Node Black ...]; [is_red(newLeft)] borrows its
               [_color]+[structR] (Some Black), returns false. *)
           wp_unfold_node "Htree_nl".
           wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
             is_red_name (is_red_ok MODULE) is_red_func
             "Hpnl" (Vptr nl_ptr) "_nstruct".
           rewrite /is_red_spec /=.
           iExists _, (Vptr nl_ptr).
           iSplit; [ iPureIntro; reflexivity |].
           iSplitL "Hargp"; [ iFrame "Hargp" |].
           iExists nl_ptr, (Some Black), (cQp.m 1).
           iSplit; [ iPureIntro; reflexivity |].
           iSplitL "_ncolor _nstruct".
           { rewrite _at_sep /=. iFrame "_ncolor _nstruct". }
           iIntros (ret2) "Hpost2".
           iIntros (rx2) "(Hany2 & Hres2)".
           wp_auto.
           wp_destroy_prim_temp "Hany2".
           iModIntro; rewrite operand_receive.unlock /=.
           iExists (Vbool false).
           iFrame "Hres2".
           simpl.
           iDestruct "Hpost2" as "[Hpost2 _]".
           rewrite _at_sep /=.
           iDestruct "Hpost2" as "[_ncolor _nstruct]".
           (** Re-fold [newL = Node Black l_nl k_nl v_nl r_nl] at [nl_ptr]. *)
           iPoseProof (treeR_node_fold _ Black l_nl k_nl v_nl r_nl _lp _rp _rc nl_ptr
             with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
             as "Htree_nl".
           (** Default tail. *)
           wp_srl_default Black (Node Black l_nl k_nl v_nl r_nl) n_ptr nl_ptr k v r rp rc.
Admitted.

End with_Sigma.
