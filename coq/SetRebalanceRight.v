(** * setRebalanceRight_ok — C++ setRebalanceRight refinement (default cases).

    Split out of the former monolithic RebalanceSpec.v (see
    docs/notes/2026-07-10_rebalance_perf_plan.md). All 7 default (no-rotation)
    cases are proved; the RR/RL rotation cases remain [admit] (blocked on Phase D
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
    + (** c = Red: is_black(n)=false short-circuits ⇒ default. *)
      wp_guard_isblack_false MODULE n_ptr.
      wp_srr_default Red newR n_ptr nr_ptr k v l lp rc.
    + destruct newR as [| c_nr l_nr k_nr v_nr r_nr].
      * (** newR = Leaf → default. is_black(n)=true, is_red(newRight=null)=false.
            Mirror of setRebalanceLeft Case 2a. *)
        wp_guard_isblack_true MODULE n_ptr.
        (** [newR = Leaf] ⇒ [nr_ptr = nullptr]. *)
        rewrite _at_as_Rep.
        iDestruct "Htree_nr" as "%Hnr_null". subst nr_ptr.
        (** [wp_guard_isblack_true] already left us at the SECOND [Eseqand] operand
            [is_red(newRight)] (no fresh [Sif]); evaluate it with the null arg. *)
        wp_operand_call_direct1_null "HMOD" is_red_lookup is_red_has_body
          is_red_name (is_red_ok MODULE) is_red_func "Hpnr" "Hstruct".
        rewrite /is_red_spec /=.
        iExists _, (Vptr nullptr).
        iSplit; [ iPureIntro; reflexivity |].
        iSplitL "Hargp"; [ iFrame "Hargp" |].
        iExists nullptr, None, (cQp.m 1).
        iSplit; [ iPureIntro; reflexivity |].
        iSplitR; [ iPureIntro; reflexivity |].
        iIntros (ret2) "Hpost2".
        iIntros (rx2) "(Hany2 & Hres2)".
        wp_auto.
        wp_destroy_prim_temp "Hany2".
        iModIntro; rewrite operand_receive.unlock /=.
        iExists (Vbool false).
        iFrame "Hres2".
        simpl.
        (** Re-establish [nullptr |-> treeR Leaf] for the fold. *)
        iAssert (nullptr |-> treeR (cQp.m 1) (Leaf (K:=Z) (V:=Z)))%I as "Htree_nr".
        { rewrite treeR_leaf _at_as_Rep. done. }
        wp_srr_default Black (Leaf (K:=Z) (V:=Z)) n_ptr nullptr k v l lp rc.
      * destruct c_nr.
        -- (* Node Red: check RL/RR *)
           destruct l_nr as [| c_ll l_ll k_ll v_ll r_ll].
           ++ destruct r_nr as [| c_rr l_rr k_rr v_rr r_rr].
              ** (** newR = Node Red Leaf .. Leaf → default. is_red(newRight)=true
                    enters body; RL is_red(sub2=newRight->left=null)=false, RR
                    is_red(sub2=newRight->right=null)=false. Mirror of SRL
                    2b-Red both-Leaf. *)
                 wp_guard_isblack_true MODULE n_ptr.
                 (** is_red(newRight) → true (Node Red). Unfold newR. *)
                 wp_unfold_node "Htree_nr".
                 wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                   is_red_name (is_red_ok MODULE) is_red_func
                   "Hpnr" (Vptr nr_ptr) "_nstruct".
                 rewrite /is_red_spec /=.
                 iExists _, (Vptr nr_ptr).
                 iSplit; [ iPureIntro; reflexivity |].
                 iSplitL "Hargp"; [ iFrame "Hargp" |].
                 iExists nr_ptr, (Some Red), (cQp.m 1).
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
                 (** [newR->left = Leaf] ⇒ [_lp = nullptr]; likewise [_rp]. *)
                 rewrite (_at_as_Rep _lp) (_at_as_Rep _rp).
                 iDestruct "_ntl" as "%Hlp_null".
                 iDestruct "_ntr" as "%Hrp_null".
                 subst _lp _rp.
                 (** [sub2 = newRight->left] (= nullptr). *)
                 wp_auto.
                 iIntros (sub2p).
                 wp_read_field "Hpnr" (Vptr nr_ptr) "_nstruct" "_nleft" (Vptr nullptr).
                 iIntros "Hsub2_local".
                 wp_auto.
                 (** RL-check [is_red(sub2 = nullptr)] → false. *)
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
                 (** [sub2 = newRight->right] (= nullptr): reassign. *)
                 wp_auto.
                 iApply wp_lval_assign.
                 rewrite /=.
                 wp_read_field "Hpnr" (Vptr nr_ptr) "_nstruct" "_nright" (Vptr nullptr).
                 wp_assign_local "Hsub2_local".
                 iIntros "Hsub2_new".
                 iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                 wp_auto.
                 (** RR-check [is_red(sub2 = nullptr)] → false. *)
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
                 wp_auto.
                 wp_destroy_local "Hsub2_local".
                 (** Re-fold [newR = Node Red Leaf .. Leaf] at [nr_ptr]. *)
                 wp_revert_offset "_nleft".
                 wp_revert_offset "_nright".
                 iAssert (nr_ptr |-> treeR (cQp.m 1) (Node Red Leaf k_nr v_nr Leaf))%I
                   with "[_nrc _ncolor _nkey _nval _nleft _nright _nstruct]" as "Htree_nr".
                 { iApply (treeR_node_fold (cQp.m 1) Red Leaf k_nr v_nr Leaf
                     nullptr nullptr _rc nr_ptr).
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
                 wp_srr_default Black (Node Red Leaf k_nr v_nr Leaf) n_ptr nr_ptr k v l lp rc.
              ** destruct c_rr.
                 --- (* RR rotation *) admit.
                 --- (** newR = Node Red Leaf .. (Node Black ..) → default.
                        RL is_red(sub2=newRight->left=null)=false; RR
                        is_red(sub2=newRight->right=Node Black)=false (Some Black).
                        Mirror of SRL left=Leaf,right=Node Black. *)
                     wp_guard_isblack_true MODULE n_ptr.
                     wp_unfold_node "Htree_nr".
                     wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func
                       "Hpnr" (Vptr nr_ptr) "_nstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr nr_ptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists nr_ptr, (Some Red), (cQp.m 1).
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
                     (** newR->left = Leaf ⇒ _lp = nullptr. *)
                     rewrite (_at_as_Rep _lp).
                     iDestruct "_ntl" as "%Hlp_null". subst _lp.
                     (** sub2 = newRight->left (= nullptr). *)
                     wp_auto.
                     iIntros (sub2p).
                     wp_read_field "Hpnr" (Vptr nr_ptr) "_nstruct" "_nleft" (Vptr nullptr).
                     iIntros "Hsub2_local".
                     wp_auto.
                     (** RL-check is_red(sub2 = nullptr) → false. *)
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
                     (** sub2 = newRight->right (= _rp, a Node Black). *)
                     wp_auto.
                     iApply wp_lval_assign.
                     rewrite /=.
                     wp_read_field "Hpnr" (Vptr nr_ptr) "_nstruct" "_nright" (Vptr _rp).
                     wp_assign_local "Hsub2_local".
                     iIntros "Hsub2_new".
                     iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                     wp_auto.
                     (** RR-check is_red(sub2 = _rp = Node Black) → false. Rename
                         newR's fields, unfold the right child. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     iRename "_nrc" into "R_nrc"; iRename "_ncolor" into "R_ncolor";
                     iRename "_nkey" into "R_nkey"; iRename "_nval" into "R_nval";
                     iRename "_nleft" into "R_nleft"; iRename "_nright" into "R_nright";
                     iRename "_nstruct" into "R_nstruct".
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
                     wp_auto.
                     wp_destroy_local "Hsub2_local".
                     (** Re-fold the right child [Node Black l_rr .. r_rr] at [_rp],
                         then [newR = Node Red Leaf .. (Node Black ..)] at [nr_ptr]. *)
                     iPoseProof (treeR_node_fold _ Black l_rr k_rr v_rr r_rr
                       _ _ _ _rp
                       with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                       as "Htree_r_child".
                     wp_revert_offset "R_nleft".
                     wp_revert_offset "R_nright".
                     iAssert (nr_ptr |-> treeR (cQp.m 1)
                                (Node Red Leaf k_nr v_nr (Node Black l_rr k_rr v_rr r_rr)))%I
                       with "[R_nrc R_ncolor R_nkey R_nval R_nleft R_nright R_nstruct Htree_r_child]"
                       as "Htree_nr".
                     { iApply (treeR_node_fold (cQp.m 1) Red Leaf k_nr v_nr
                         (Node Black l_rr k_rr v_rr r_rr) nullptr _rp _rc nr_ptr).
                       iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].
                       iSplitL "Htree_r_child"; [ iExact "Htree_r_child" |].
                       rewrite !_at_sep.
                       iSplitL "R_nrc"; [ iExact "R_nrc" |].
                       iSplitL "R_ncolor"; [ iExact "R_ncolor" |].
                       iSplitL "R_nkey"; [ iExact "R_nkey" |].
                       iSplitL "R_nval"; [ iExact "R_nval" |].
                       iSplitL "R_nleft"; [ iExact "R_nleft" |].
                       iSplitL "R_nright"; [ iExact "R_nright" |].
                       iExact "R_nstruct". }
                     wp_srr_default Black
                       (Node Red Leaf k_nr v_nr (Node Black l_rr k_rr v_rr r_rr))
                       n_ptr nr_ptr k v l lp rc.
           ++ destruct c_ll.
              ** (* RL rotation *) admit.
              ** destruct r_nr as [| c_rr l_rr k_rr v_rr r_rr].
                 --- (** newR = Node Red (Node Black ..) k_nr v_nr Leaf → default.
                        RL is_red(sub2=newRight->left=Node Black)=false (Some
                        Black); RR is_red(sub2=newRight->right=null)=false. Mirror
                        of SRL left=Node Black,right=Leaf. *)
                     wp_guard_isblack_true MODULE n_ptr.
                     wp_unfold_node "Htree_nr".
                     wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                       is_red_name (is_red_ok MODULE) is_red_func
                       "Hpnr" (Vptr nr_ptr) "_nstruct".
                     rewrite /is_red_spec /=.
                     iExists _, (Vptr nr_ptr).
                     iSplit; [ iPureIntro; reflexivity |].
                     iSplitL "Hargp"; [ iFrame "Hargp" |].
                     iExists nr_ptr, (Some Red), (cQp.m 1).
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
                     (** newR->right = Leaf ⇒ _rp = nullptr. *)
                     rewrite (_at_as_Rep _rp).
                     iDestruct "_ntr" as "%Hrp_null". subst _rp.
                     (** sub2 = newRight->left (= _lp, a Node Black). *)
                     wp_auto.
                     iIntros (sub2p).
                     wp_read_field "Hpnr" (Vptr nr_ptr) "_nstruct" "_nleft" (Vptr _lp).
                     iIntros "Hsub2_local".
                     wp_auto.
                     (** RL-check is_red(sub2 = _lp = Node Black) → false. Rename
                         newR's fields, unfold the left child. *)
                     iApply (wp_if source); iNext.
                     rewrite /wp.WPE.wp_test /=.
                     iRename "_nrc" into "R_nrc"; iRename "_ncolor" into "R_ncolor";
                     iRename "_nkey" into "R_nkey"; iRename "_nval" into "R_nval";
                     iRename "_nleft" into "R_nleft"; iRename "_nright" into "R_nright";
                     iRename "_nstruct" into "R_nstruct".
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
                     (** Re-fold the left child now (frees _n* for the RR check). *)
                     iPoseProof (treeR_node_fold _ Black l_ll k_ll v_ll r_ll
                       _ _ _ _lp
                       with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                       as "Htree_l_child".
                     (** sub2 = newRight->right (= nullptr). *)
                     wp_auto.
                     iApply wp_lval_assign.
                     rewrite /=.
                     wp_read_field "Hpnr" (Vptr nr_ptr) "R_nstruct" "R_nright" (Vptr nullptr).
                     wp_assign_local "Hsub2_local".
                     iIntros "Hsub2_new".
                     iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                     wp_auto.
                     (** RR-check is_red(sub2 = nullptr) → false. *)
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
                     wp_auto.
                     wp_destroy_local "Hsub2_local".
                     (** Re-fold [newR = Node Red (Node Black ..) k_nr v_nr Leaf]. *)
                     wp_revert_offset "R_nleft".
                     wp_revert_offset "R_nright".
                     iAssert (nr_ptr |-> treeR (cQp.m 1)
                                (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nr v_nr Leaf))%I
                       with "[R_nrc R_ncolor R_nkey R_nval R_nleft R_nright R_nstruct Htree_l_child]"
                       as "Htree_nr".
                     { iApply (treeR_node_fold (cQp.m 1) Red
                         (Node Black l_ll k_ll v_ll r_ll) k_nr v_nr Leaf
                         _lp nullptr _rc nr_ptr).
                       iSplitL "Htree_l_child"; [ iExact "Htree_l_child" |].
                       iSplitR; [ rewrite treeR_leaf _at_as_Rep; done |].
                       rewrite !_at_sep.
                       iSplitL "R_nrc"; [ iExact "R_nrc" |].
                       iSplitL "R_ncolor"; [ iExact "R_ncolor" |].
                       iSplitL "R_nkey"; [ iExact "R_nkey" |].
                       iSplitL "R_nval"; [ iExact "R_nval" |].
                       iSplitL "R_nleft"; [ iExact "R_nleft" |].
                       iSplitL "R_nright"; [ iExact "R_nright" |].
                       iExact "R_nstruct". }
                     wp_srr_default Black
                       (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nr v_nr Leaf)
                       n_ptr nr_ptr k v l lp rc.
                 --- destruct c_rr.
                     +++ (* RR rotation *) admit.
                     +++ (** newR = Node Red (Node Black ..) k_nr v_nr (Node Black
                            ..) → default. RL is_red(sub2=newRight->left=Node
                            Black)=false; RR is_red(sub2=newRight->right=Node
                            Black)=false. Both children unfolded (wp_unfold_node').
                            Mirror of SRL left=Node Black,right=Node Black. *)
                         wp_guard_isblack_true MODULE n_ptr.
                         wp_unfold_node' "Htree_nr".
                         wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
                           is_red_name (is_red_ok MODULE) is_red_func
                           "Hpnr" (Vptr nr_ptr) "_nstruct".
                         rewrite /is_red_spec /=.
                         iExists _, (Vptr nr_ptr).
                         iSplit; [ iPureIntro; reflexivity |].
                         iSplitL "Hargp"; [ iFrame "Hargp" |].
                         iExists nr_ptr, (Some Red), (cQp.m 1).
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
                         (** sub2 = newRight->left (= _lp, a Node Black). *)
                         wp_auto.
                         iIntros (sub2p).
                         wp_read_field "Hpnr" (Vptr nr_ptr) "_nstruct" "_nleft" (Vptr _lp).
                         iIntros "Hsub2_local".
                         wp_auto.
                         (** RL-check is_red(sub2 = _lp = Node Black) → false.
                             Rename newR fields to R_n*, move sibling out, unfold left. *)
                         iApply (wp_if source); iNext.
                         rewrite /wp.WPE.wp_test /=.
                         iRename "_nrc" into "R_nrc"; iRename "_ncolor" into "R_ncolor";
                         iRename "_nkey" into "R_nkey"; iRename "_nval" into "R_nval";
                         iRename "_nleft" into "R_nleft"; iRename "_nright" into "R_nright";
                         iRename "_nstruct" into "R_nstruct".
                         iRename "_ntr" into "RR_child".
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
                         (** Re-fold the LEFT child (frees _n* for the right child). *)
                         iPoseProof (treeR_node_fold _ Black l_ll k_ll v_ll r_ll
                           _ _ _ _lp
                           with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                           as "Htree_l_child".
                         (** sub2 = newRight->right (= _rp, a Node Black). *)
                         wp_auto.
                         iApply wp_lval_assign.
                         rewrite /=.
                         wp_read_field "Hpnr" (Vptr nr_ptr) "R_nstruct" "R_nright" (Vptr _rp).
                         wp_assign_local "Hsub2_local".
                         iIntros "Hsub2_new".
                         iDestruct (tptstoR_to_fuzzyR with "Hsub2_new") as "Hsub2_local".
                         wp_auto.
                         (** RR-check is_red(sub2 = _rp = Node Black) → false.
                             Unfold the RIGHT child. *)
                         iApply (wp_if source); iNext.
                         rewrite /wp.WPE.wp_test /=.
                         wp_unfold_node' "RR_child".
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
                         wp_auto.
                         wp_destroy_local "Hsub2_local".
                         (** Re-fold the RIGHT child, then newR. *)
                         iPoseProof (treeR_node_fold _ Black l_rr k_rr v_rr r_rr
                           _ _ _ _rp
                           with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
                           as "Htree_r_child".
                         wp_revert_offset "R_nleft".
                         wp_revert_offset "R_nright".
                         iAssert (nr_ptr |-> treeR (cQp.m 1)
                                    (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nr v_nr
                                       (Node Black l_rr k_rr v_rr r_rr)))%I
                           with "[R_nrc R_ncolor R_nkey R_nval R_nleft R_nright R_nstruct Htree_l_child Htree_r_child]"
                           as "Htree_nr".
                         { iApply (treeR_node_fold (cQp.m 1) Red
                             (Node Black l_ll k_ll v_ll r_ll) k_nr v_nr
                             (Node Black l_rr k_rr v_rr r_rr) _lp _rp _rc nr_ptr).
                           iSplitL "Htree_l_child"; [ iExact "Htree_l_child" |].
                           iSplitL "Htree_r_child"; [ iExact "Htree_r_child" |].
                           rewrite !_at_sep.
                           iSplitL "R_nrc"; [ iExact "R_nrc" |].
                           iSplitL "R_ncolor"; [ iExact "R_ncolor" |].
                           iSplitL "R_nkey"; [ iExact "R_nkey" |].
                           iSplitL "R_nval"; [ iExact "R_nval" |].
                           iSplitL "R_nleft"; [ iExact "R_nleft" |].
                           iSplitL "R_nright"; [ iExact "R_nright" |].
                           iExact "R_nstruct". }
                         wp_srr_default Black
                           (Node Red (Node Black l_ll k_ll v_ll r_ll) k_nr v_nr
                              (Node Black l_rr k_rr v_rr r_rr))
                           n_ptr nr_ptr k v l lp rc.
        -- (** newR = Node Black ...: is_black(n)=true, is_red(newRight)=false
              (Black) ⇒ default. Mirror of setRebalanceLeft 2b-Black. *)
           wp_guard_isblack_true MODULE n_ptr.
           wp_unfold_node "Htree_nr".
           wp_operand_call_direct1 "HMOD" is_red_lookup is_red_has_body
             is_red_name (is_red_ok MODULE) is_red_func
             "Hpnr" (Vptr nr_ptr) "_nstruct".
           rewrite /is_red_spec /=.
           iExists _, (Vptr nr_ptr).
           iSplit; [ iPureIntro; reflexivity |].
           iSplitL "Hargp"; [ iFrame "Hargp" |].
           iExists nr_ptr, (Some Black), (cQp.m 1).
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
           (** Re-fold [newR = Node Black l_nr k_nr v_nr r_nr] at [nr_ptr]. *)
           iPoseProof (treeR_node_fold _ Black l_nr k_nr v_nr r_nr _lp _rp _rc nr_ptr
             with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]")
             as "Htree_nr".
           wp_srr_default Black (Node Black l_nr k_nr v_nr r_nr) n_ptr nr_ptr k v l lp rc.
Admitted.

End with_Sigma.
