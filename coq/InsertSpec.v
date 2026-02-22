(** * Insert Specification and Proof — Phase 5A
    Created: 2026-02-17
    Updated: 2026-02-20 — Split to InsertDefs.v for fast iteration.

    Proves that the C++ [Node::insert] refines its functional counterpart
    from [RBTree.v].

    == Architecture (2026-02-20) ==

    - [InsertDefs.v]: Function names, pre-computed [Func] records (via
      [Eval vm_compute]), lookup proofs, specs, and Admitted callee proofs.
      Compiles once (~5-10 min), cached in [.vo].
    - [InsertSpec.v] (this file): Only the [insert_ok] proof.
      Imports [InsertDefs.v] — no AST traversal on rebuild.

    == C++ function under verification ==

<<
      static Node* insert(Key k, Value v, Node *n) {
        Node *curr = ins(k, v, n);
        curr->color = black;
        return curr;
      }
>>

    == Proof outline ==

    1. Extract arguments (k, v, n) from spec
    2. Step through variable declaration for [curr]
    3. Resolve [ins(k, v, n)] call → produces [curr |-> treeR 1 (ins k v t)]
    4. Destruct [ins k v t] (always a Node, by [ins_is_node])
    5. Unfold [treeR] at [curr] to access fields
    6. Write [curr->color = black]
    7. Fold [treeR] back with updated color
    8. Show result equals [insert k v t] (by [makeBlack_node] + [ins_is_node])
    9. Return
   10. Destroy [curr] local + postcondition
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
(** * insert_ok — Round 5A Target *)
(* ================================================================= *)

Section with_Sigma.
Context `{Sigma : cpp_logic} `{MOD: map_int_int_cpp.source ⊧ σ}.

Hypothesis MODULE : |-- denoteModule source.

Lemma insert_ok :
  |-- func_ok source insert_func insert_spec.
Proof using MOD MODULE.
  rewrite /func_ok. iSplit.
  - iPureIntro. reflexivity.
  - iIntros "!>" (Q vals) "Hspec".
    iPoseProof MODULE as "#HMOD".
    iApply wp_func_intro.
    rewrite /insert_func /=.
    (** Extract args: k, v, n from spec. *)
    iDestruct "Hspec" as (pk vk pn vn pn0 vn0) "(%Hvals & Hpk & Hpv & Hpn & Hspec)".
    subst vals. simpl.
    iDestruct "Hspec" as (k v n t) "(%Hargs & Htree & Hcont)".
    injection Hargs as -> ->. subst.
    (** Step 1: wp through Sseq → Sdecl → wp_initialize → ∀ addr. *)
    wp_auto_anon.
    (** Step 2: Resolve [ins(k, v, n)] call. *)
    wp_resolve_call "HMOD" ins_lookup ins_has_body ins_name.
    wp_nd_args ltac:(first [
      wp_read_local "Hpk" (Vint k) |
      wp_read_local "Hpv" (Vint v) |
      wp_read_local "Hpn" (Vptr n)
    ]).
    all: wp_call_direct "HMOD" ins_lookup ins_has_body ins_ok ins_func.
    (** Step 3: Provide [ins_spec] precondition. *)
    all: rewrite /ins_spec; simpl;
         lazymatch goal with
         | |- context[ @eq (list ptr) _ (?a :: ?b :: ?c :: nil) ] =>
           iExists a, (Vint k), b, (Vint v), c, (Vptr n)
         end;
         iSplit; [iPureIntro; reflexivity |];
         iFrame;
         iExists k, v;
         iSplit; [iPureIntro; reflexivity |].
    (** Step 4: Post-call cleanup. *)
    all: iIntros (curr) "Hins_tree";
         iIntros (recv_ptr) "(Hanyp & Hanyp0 & Hanyp1 & Hrecv)";
         wp_auto;
         wp_destroy_prim_temp "Hanyp1";
         wp_destroy_prim_temp "Hanyp0";
         wp_destroy_prim_temp "Hanyp";
         wp_operand_receive (Vptr curr) "Hrecv" "Hcurr_local";
         wp_auto.
    (** Steps 5-10: Identical across all 6 [wp_nd_args] branches. *)
    all: destruct (ins_is_node k v t) as [c' [l' [k' [v' [r' Hins_eq]]]]];
         iRevert "Hins_tree"; rewrite Hins_eq; iIntros "Hins_tree";
         wp_unfold_node "Hins_tree".
    all: wp_auto; wp_assign_setup;
         wp_read_global_const "HMOD" black_lookup (Vbool false);
         wp_offset "_ncolor";
         wp_assign_member_field "Hcurr_local" (Vptr curr) "_nstruct" "_ncolor";
         iIntros "_ncolor_new"; wp_auto.
    all: wp_field_to_primR "_ncolor_new" "_ncolor" (Vbool false) I;
         iPoseProof (treeR_node_fold _ Black l' k' v' r' _lp _rp _rc curr
           with "[$_ntl $_ntr $_nrc $_ncolor $_nkey $_nval $_nleft $_nright $_nstruct]") as "Htree".
    all: iRevert "Htree"; rewrite /RBTree.insert Hins_eq makeBlack_node; iIntros "Htree";
         wp_auto_anon;
         wp_read_local "Hcurr_local" (Vptr curr);
         iIntros "Hret_store"; repeat wp_step.
    (** Step 10: Destroy [curr] local + postcondition. *)
    all: wp_destroy_local_and_continue "Hcurr_local";
         iApply ("Hcont" $! curr with "[Htree]");
         [ iExact "Htree"
         | iFrame "Hret_store"; wp_cleanup_params "Hpk" "Hpv" "Hpn" ].
Qed.

End with_Sigma.
