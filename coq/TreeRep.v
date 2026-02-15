(** * Separation Logic Representation Predicate

    Links the Coq [tree Z Z] type from [RBTree.v] to the C++ [Node] heap
    layout using BRiCk's separation logic framework.

    The predicate [treeR] states: "the C++ pointer [p] points to a heap
    region whose shape and contents match the abstract tree [t]."

    == Design ==

    BRiCk represents C++ programs as deeply embedded Coq terms. The
    [wp_*] tactics discharge Hoare triples over these terms. To connect
    the C++ execution to our functional spec, we define:

      treeR : Qp -> tree Z Z -> Rep

    where [Rep] is BRiCk's representation predicate type (a monadic
    predicate indexed by [ptr]), and [Qp] is the fractional permission.

    The key clauses are:

    - [Leaf] ↔ the C++ pointer is [nullptr].
    - [Node c l k v r] ↔ the pointer is non-null and points to an
      allocated [DDL::Map<int,int>::Node] struct whose fields match
      [c], [k], [v] and whose [left]/[right] pointers recursively
      satisfy [treeR].

    == Field layout (from cpp2v-generated [map_int_int_cpp_names.v]) ==

    The C++ [Node] struct has these fields:
    - [ref_count : size_t]  (reference count, [Tulong])
    - [color : bool]        (red=true, black=false, [Tbool])
    - [key : int]           ([Tint])
    - [value : int]         ([Tint])
    - [left : Node*]        (pointer to Node)
    - [right : Node*]       (pointer to Node)

    == Pattern ==

    Following BRiCk's [treeR] pattern from [howto_sequential.v]:
    leaf → [| this = nullptr |];
    node → Exists child pointers, recursive treeR ** field assertions.
*)

Require Import skylabs.lang.cpp.cpp.
Import cQp_compat.

Require Import daedalus_rb.RBTree.

#[local] Set Warnings "-non-recursive".  (* treeR is not structurally recursive on Rep *)
#[local] Open Scope Z_scope.
#[local] Open Scope bs_scope.

Section with_Sigma.
Context `{Sigma : cpp_logic} {CU : genv}.

(** ** C++ name bindings

    Field names from the cpp2v-generated [map_int_int_cpp_names.v].
    The struct is [DDL::Map<int,int>::Node]. *)

(** The [Node] struct name and type (for pointer representations). *)
Definition _Node_name : globname :=
  Nscoped (Ninst (Nscoped (Nglobal (Nid "DDL")) (Nid "Map"))
            ((Atype Tint) :: (Atype Tint) :: nil)) (Nid "Node").
Definition _Node : type := Tnamed _Node_name.

(** Field offsets within [Node]. *)
Definition _ref_count := _field "DDL::Map<int,int>::Node::ref_count".
Definition _color     := _field "DDL::Map<int,int>::Node::color".
Definition _key       := _field "DDL::Map<int,int>::Node::key".
Definition _value     := _field "DDL::Map<int,int>::Node::value".
Definition _left      := _field "DDL::Map<int,int>::Node::left".
Definition _right     := _field "DDL::Map<int,int>::Node::right".

(** ** Color encoding

    The C++ code uses [bool] for color: [red = true], [black = false]. *)
Definition color_to_bool (c : Color) : bool :=
  match c with
  | Red => true
  | Black => false
  end.

(** ** Representation predicate

    [treeR q t] asserts that the "this" pointer represents abstract tree [t]
    with fractional permission [q].

    - [Leaf] maps to [nullptr].
    - [Node c l k v r] maps to a non-null pointer to an allocated
      [DDL::Map<int,int>::Node] struct. We existentially quantify
      over the child pointers [lp] and [rp], assert the field
      contents, and recurse into the subtrees.

    The [ref_count] field is existentially quantified since it is a
    runtime bookkeeping value not tracked by the functional spec.

    [structR _Node_name q] asserts the struct's identity and implies
    [nonnullR] (the pointer is non-null). This is required for
    BRiCk's automation to derive contradictions when a [Node] is
    asserted at [nullptr], following the pattern from [nodeR] in
    the linked list demo. *)
Fixpoint treeR (q : Qp) (t : tree Z Z) : Rep :=
  as_Rep (fun this =>
    match t with
    | Leaf =>
        [| this = nullptr |]
    | Node c l k v r =>
        Exists (lp : ptr) (rp : ptr) (rc : Z),
        lp |-> treeR q l **
        rp |-> treeR q r **
        this |-> (_ref_count |-> ulongR q rc **
                  _color     |-> boolR q (color_to_bool c) **
                  _key       |-> intR q k **
                  _value     |-> intR q v **
                  _left      |-> ptrR<_Node> q lp **
                  _right     |-> ptrR<_Node> q rp **
                  structR _Node_name q)
    end).

(** ** Characterization lemmas

    Definitional unfoldings of [treeR] — useful for rewriting in
    separation logic proofs without manual [simpl]/[unfold]. *)

Lemma treeR_leaf q : treeR q Leaf = as_Rep (fun p => [| p = nullptr |]).
Proof. reflexivity. Qed.

Lemma treeR_node q c l k v r :
  treeR q (Node c l k v r) =
  as_Rep (fun this =>
    Exists (lp : ptr) (rp : ptr) (rc : Z),
    lp |-> treeR q l **
    rp |-> treeR q r **
    this |-> (_ref_count |-> ulongR q rc **
              _color     |-> boolR q (color_to_bool c) **
              _key       |-> intR q k **
              _value     |-> intR q v **
              _left      |-> ptrR<_Node> q lp **
              _right     |-> ptrR<_Node> q rp **
              structR _Node_name q)).
Proof. reflexivity. Qed.

End with_Sigma.
