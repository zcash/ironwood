import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Zcash.Security.Common.RandomOracle

/-!
# Fixed-depth Merkle trees over a partial tree hash

This module holds the ledger layer's Merkle machinery, over the raw-encoding partial
compression interface (`MerklePrimitives`, adopted from the circuit-bridge work so that
the two layers share one model). The interface is faithful to the deployed hash in
two ways that the concrete collision bound needs:

* **Inputs are raw encodings.** The compression consumes child *encodings* of type `E`,
  and an Orchard field element can have more than one accepted 255-bit encoding — the
  circuit does not pay for a canonicity check, a conscious trade-off from Sapling onward.
  Collisions are therefore counted over the encoding domain. `canon` is the canonical
  encoding — a section of `decode` — used by honest tree construction.
* **Compression is partial.** `none` is an escaped compression (for Orchard, a Sinsemilla
  exceptional branch). Escapes are not totalized away: `Path` records per-height success,
  and a `Collision` demands *successful* evaluations on both queries
  (`RandomOracle.DefinedCollision`), so an escaped query can never constitute a
  collision. A totalized model would let two escapes masquerade as a collision that the
  concrete reduction to a hardness assumption could not consume.

Compression indices count from the leaves, with the leafmost hashes at height `0`:
`compress 0` combines two leaves, and in general `compress i` combines two height-`i`
children into their height-`(i + 1)` parent. Each height's compression is
personalized, so an adversary's queries count against one height's compression at a
time. The protocol spec's *layers* count from the root instead (§4.9, layer 0 at the
root). The index here equals `MerkleDepth − 1 − layer`, which is exactly the value
§5.4.1.3 encodes into the Sinsemilla input. So the index is faithful to the circuit,
and the spec's layer is recoverable by that subtraction. Positions are leaf-to-root
bit vectors: bit `i` selects the child at height `i`, so position bits align with
binary leaf indices.

Adversarial freedom differs by an input's role. A path's *sibling* encodings are
unconstrained; its *on-path* encodings are constrained only up to the decode fibre —
any accepted representative of the pinned running node, because the deployed circuit
constrains the decomposition to the field element, not to a canonical encoding. Only
the honest tree's inputs (`subRoot`) are canonical, by construction. Distinct encodings
of equal values are distinct queries, so a collision between them is a genuine
collision of the deployed hash.

`Path` (with `node`, `selectedChild`, and `Path.compress_isSome`) is the witness-side
path fact: both raw child encodings at every height plus the selected side, with the
selected encoding decoding to the running node and every compression succeeding. On top
of it this module proves the two lemmas the games consume:

* **Position binding** (`collisionOfWrongLeaf`): a valid path for a leaf that is *not*
  the committed one at its position, against a defined tree, computes a collision of one
  height's compression — as a computable `def` per the breaks-as-computed-data convention
  (documented in `Zcash.Security.RandomOracle`).
* **Completeness** (`path_of_root`): if the tree is defined, the honest authentication
  data (`authChildren`) exists and forms a valid `Path` for the committed leaf.

No hardness assumption appears here; prequantumly, collision-resistance of Sinsemilla
reduces to a DLR break (Zcash protocol specification Theorems 5.4.3 and 5.4.4). For the
ZIP 2005 Recovery Protocol, the Merkle tree will be rehashed using a hash function that
is assumed to be collapsing.
-/

namespace Zcash.Security.Ledger.Merkle

variable {B E : Type*}

/-- The Merkle-specific part of the ledger primitive interface.  `E` is the raw
encoding consumed by the compression function; it is deliberately separate from the
node type `B`, since an Orchard field element can have more than one accepted 255-bit
encoding. `canon` is the canonical encoding used by honest tree construction; it is a
section of `decode` (hence injective). -/
structure MerklePrimitives (B E : Type*) where
  depth : ℕ
  decode : E → B
  /-- Height-indexed, personalized compression of a raw child pair (heights count from
  the leaves; the spec's root-counted layer is `MerkleDepth − 1` minus this index).
  `none` is an escaped compression; for Orchard, a Sinsemilla exceptional branch.
  Definedness is not totalized away — it is recorded in `Path` and recoverable from a
  path fact. -/
  compress : Fin depth → E × E → Option B
  /-- The canonical encoding of a node value. -/
  canon : B → E
  /-- `canon` encodes faithfully: decoding a canonical encoding returns the node. -/
  decode_canon : ∀ b, decode (canon b) = b

/-- Select the raw child on the path.  `false` selects the left child and `true`
selects the right child. -/
def selectedChild (side : Bool) (children : E × E) : E :=
  if side then children.2 else children.1

/-- The running node after the first `i` leaf-to-root path cells.  In particular,
`node ... 0` is `some leaf` and `node ... (i + 1)` is the compression at height `i`,
which is `none` on an escaped compression.  The selected-child equations in `Path`
tie these otherwise raw inputs together. -/
def node (P : MerklePrimitives B E) (leaf : B) (children : Fin P.depth → E × E) :
    Fin (P.depth + 1) → Option B :=
  Fin.cases (some leaf) (fun i => P.compress i (children i))

/-- A raw Orchard-style authentication path, ordered from the leaf towards the root.
Every path cell carries both *raw* child encodings and its selected side.  The selected
encoding must decode to the current node, and compression at height `i` produces the
next node — each equation *also* asserts that the previous compression succeeded, so
definedness at every height is part of path validity and is recoverable from the `Path`
fact itself (see `Path.compress_isSome`). -/
def Path (P : MerklePrimitives B E) (leaf root : B)
    (children : Fin P.depth → E × E) (side : Fin P.depth → Bool) : Prop :=
  (∀ i, node P leaf children (Fin.castSucc i) =
      some (P.decode (selectedChild (side i) (children i)))) ∧
    node P leaf children (Fin.last P.depth) = some root

/-- Every height of a valid path has a defined compression: definedness is recorded
in the `Path` fact rather than carried as a separate bridge invariant.  This is the
property motivating the partial (`Option`-valued) compressor — the fact each `Path`
equation asserts `some _` on the running node lets a consumer recover a successful
evaluation at every height. -/
theorem Path.compress_isSome {P : MerklePrimitives B E} {leaf root : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool}
    (h : Path P leaf root children side) (i : Fin P.depth) :
    ∃ b, P.compress i (children i) = some b := by
  have hnode : node P leaf children i.succ = P.compress i (children i) := by
    simp [node, Fin.cases_succ]
  rcases Nat.lt_or_ge (i.1 + 1) P.depth with hlt | hge
  · have hcast : Fin.castSucc (⟨i.1 + 1, hlt⟩ : Fin P.depth) = i.succ := by
      apply Fin.ext
      simp [Fin.val_succ]
    have hstep := h.1 ⟨i.1 + 1, hlt⟩
    rw [hcast, hnode] at hstep
    exact ⟨_, hstep⟩
  · have heq : i.1 + 1 = P.depth := by have := i.isLt; omega
    have hlast : i.succ = Fin.last P.depth := by
      apply Fin.ext
      simp [Fin.val_succ, Fin.val_last, heq]
    have hroot := h.2
    rw [← hlast, hnode] at hroot
    exact ⟨_, hroot⟩

/-! ## The guarded (⊥-model) path

The circuit layer exports its Merkle contract in the specification's literal ⊥-model
: selected-child equations are unconditional, while a compression
equation fires only when the compression is defined — escapes are unconstrained.
`GuardedPath` is that statement in this module's own vocabulary (`node`,
`selectedChild`), so the circuit bridge assembles a strict `Path` by pairing the
guarded export with per-height definedness (`Path.of_guarded_of_defined`) instead of
re-deriving the node chain by hand.  `path_iff_guarded_defined` records that nothing
is lost in the split: a strict `Path` is exactly a guarded one all of whose
compressions are defined. -/

/-- The guarded counterpart of `Path`: every *defined* running node is the decoded
selected child at its height, and a *defined* final compression is the root.  Since
`node … 0 = some leaf` unconditionally, the leaf equation is not guarded; an escaped
compression leaves its height unconstrained (the ⊥-model). -/
def GuardedPath (P : MerklePrimitives B E) (leaf root : B)
    (children : Fin P.depth → E × E) (side : Fin P.depth → Bool) : Prop :=
  (∀ i, ∀ b, node P leaf children (Fin.castSucc i) = some b →
      P.decode (selectedChild (side i) (children i)) = b) ∧
  ∀ b, node P leaf children (Fin.last P.depth) = some b → b = root

/-- A strict path is in particular guarded. -/
theorem Path.toGuarded {P : MerklePrimitives B E} {leaf root : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool}
    (h : Path P leaf root children side) :
    GuardedPath P leaf root children side := by
  refine ⟨fun i b hb => ?_, fun b hb => ?_⟩
  · rw [h.1 i] at hb
    exact Option.some.inj hb
  · rw [h.2] at hb
    exact (Option.some.inj hb).symm

/-- A guarded path all of whose compressions are defined is a strict `Path`. -/
theorem Path.of_guarded_of_defined {P : MerklePrimitives B E} {leaf root : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool}
    (hg : GuardedPath P leaf root children side)
    (hdef : ∀ i, ∃ b, P.compress i (children i) = some b) :
    Path P leaf root children side := by
  -- Every running node is defined: index `0` is `some leaf`, and each successor
  -- index is a compression, defined by `hdef`.
  have hsome : ∀ k : Fin (P.depth + 1), ∃ b, node P leaf children k = some b := by
    intro k
    induction k using Fin.cases with
    | zero => exact ⟨leaf, by simp [node]⟩
    | succ j =>
        obtain ⟨b, hb⟩ := hdef j
        exact ⟨b, by simp [node, Fin.cases_succ, hb]⟩
  refine ⟨fun i => ?_, ?_⟩
  · -- Pin the defined running node with the guarded selected-child clause.
    obtain ⟨b, hb⟩ := hsome (Fin.castSucc i)
    rw [hb, hg.1 i b hb]
  · -- Pin the defined final compression with the guarded root clause.
    obtain ⟨b, hb⟩ := hsome (Fin.last P.depth)
    rw [hb, hg.2 b hb]

/-- The strict/guarded split is lossless: `Path` is exactly `GuardedPath` together
with per-height definedness. -/
theorem path_iff_guarded_defined {P : MerklePrimitives B E} {leaf root : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool} :
    Path P leaf root children side ↔
      GuardedPath P leaf root children side ∧
        ∀ i, ∃ b, P.compress i (children i) = some b :=
  ⟨fun h => ⟨h.toGuarded, h.compress_isSome⟩,
   fun ⟨hg, hdef⟩ => Path.of_guarded_of_defined hg hdef⟩

/-- A Merkle collision records the height whose personalized compression was collided,
and demands *successful* evaluations on both queries (a `DefinedCollision`): an escaped
compression, being `none`, can therefore never constitute a collision. -/
abbrev Collision (P : MerklePrimitives B E) :=
  Σ i : Fin P.depth, RandomOracle.DefinedCollision (P.compress i)

/-! ## The honest tree

The honest tree over a leaf assignment, built with canonical child encodings. A
height-`h` subtree compresses its two height-`(h - 1)` children with
`compress (h - 1)`, so a subtree's compression indices depend only on its height, not
its location. The construction is partial because the compression is. -/

/-- The root of the height-`h` subtree over leaves `f`, or `none` if any compression
along the way escapes. Positions are leaf-to-root: the last bit selects between the two
height-`(h-1)` halves. -/
def subRoot (P : MerklePrimitives B E) :
    (h : ℕ) → h ≤ P.depth → ((Fin h → Bool) → B) → Option B
  | 0, _, f => some (f (fun i => i.elim0))
  | h + 1, hle, f =>
    match subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)),
          subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)) with
    | some bl, some br => P.compress ⟨h, hle⟩ (P.canon bl, P.canon br)
    | _, _ => none

/-- The root of the full tree over leaves `f`, or `none` if any compression escapes. -/
def root (P : MerklePrimitives B E) (f : (Fin P.depth → Bool) → B) : Option B :=
  subRoot P P.depth le_rfl f

/-! ## Machinery over subtree heights

The recursions below work on subtrees of height `h ≤ depth`; `nodeAux` is the running
node chain of a height-`h` path, using the same absolute compression indices as the
full tree. At `h = P.depth` it is definitionally `node`, and `PathAux` is
definitionally `Path`. -/

/-- The running node chain of a height-`h` path (the height-`h` analogue of `node`). -/
def nodeAux (P : MerklePrimitives B E) (h : ℕ) (hle : h ≤ P.depth) (leaf : B)
    (children : Fin h → E × E) : Fin (h + 1) → Option B :=
  Fin.cases (some leaf) (fun i => P.compress (Fin.castLE hle i) (children i))

/-- The height-`h` analogue of `Path`, over the same absolute compression indices. -/
def PathAux (P : MerklePrimitives B E) (h : ℕ) (hle : h ≤ P.depth) (leaf root : B)
    (children : Fin h → E × E) (side : Fin h → Bool) : Prop :=
  (∀ i, nodeAux P h hle leaf children (Fin.castSucc i) =
      some (P.decode (selectedChild (side i) (children i)))) ∧
    nodeAux P h hle leaf children (Fin.last h) = some root

/-- At full height the auxiliary path fact is the path fact. -/
theorem pathAux_depth_iff (P : MerklePrimitives B E) {leaf root : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool} :
    PathAux P P.depth le_rfl leaf root children side ↔ Path P leaf root children side :=
  Iff.rfl

/-- Dropping the topmost compression of a height-`(h+1)` chain gives the height-`h` chain of the
initial segments. -/
theorem nodeAux_init (P : MerklePrimitives B E) {h : ℕ} (hle : h + 1 ≤ P.depth)
    (leaf : B) (children : Fin (h + 1) → E × E) (i : Fin (h + 1)) :
    nodeAux P h (Nat.le_of_succ_le hle) leaf (Fin.init children) i
      = nodeAux P (h + 1) hle leaf children (Fin.castSucc i) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      rw [← Fin.succ_castSucc]
      simp only [nodeAux, Fin.cases_succ]
      rfl

/-! ## Completeness: the honest authentication data -/

/-- Inversion for a defined height-`(h+1)` subtree: both halves are defined and the top
compression succeeds on their canonical encodings. -/
theorem subRoot_succ (P : MerklePrimitives B E) {h : ℕ} (hle : h + 1 ≤ P.depth)
    (f : (Fin (h + 1) → Bool) → B) {rt : B} :
    subRoot P (h + 1) hle f = some rt ↔
      ∃ bl br, subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)) = some bl ∧
        subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)) = some br ∧
        P.compress ⟨h, hle⟩ (P.canon bl, P.canon br) = some rt := by
  cases hbl : subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)) <;>
    cases hbr : subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)) <;>
    simp [subRoot, hbl, hbr]

/-- The honest authentication data for position `pos` in the height-`h` subtree over
`f`: at each height, the canonical encodings of the two child subroots along the path.
`none` when the tree is not defined there. -/
def authChildren (P : MerklePrimitives B E) :
    (h : ℕ) → h ≤ P.depth → ((Fin h → Bool) → B) → (Fin h → Bool) → Option (Fin h → E × E)
  | 0, _, _, _ => some (fun i => i.elim0)
  | h + 1, hle, f, pos =>
    match subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)),
          subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)),
          authChildren P h (Nat.le_of_succ_le hle)
            (fun p => f (Fin.snoc p (pos (Fin.last h)))) (Fin.init pos) with
    | some bl, some br, some rest => some (Fin.snoc rest (P.canon bl, P.canon br))
    | _, _, _ => none

/-- Inversion for defined honest authentication data at height `h + 1`. -/
theorem authChildren_succ (P : MerklePrimitives B E) {h : ℕ} (hle : h + 1 ≤ P.depth)
    (f : (Fin (h + 1) → Bool) → B) (pos : Fin (h + 1) → Bool)
    {children : Fin (h + 1) → E × E} :
    authChildren P (h + 1) hle f pos = some children ↔
      ∃ bl br rest,
        subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)) = some bl ∧
        subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)) = some br ∧
        authChildren P h (Nat.le_of_succ_le hle)
          (fun p => f (Fin.snoc p (pos (Fin.last h)))) (Fin.init pos) = some rest ∧
        children = Fin.snoc rest (P.canon bl, P.canon br) := by
  cases hbl : subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)) <;>
    cases hbr : subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)) <;>
    cases hrest : authChildren P h (Nat.le_of_succ_le hle)
      (fun p => f (Fin.snoc p (pos (Fin.last h)))) (Fin.init pos) <;>
    simp [authChildren, hbl, hbr, hrest, eq_comm]

/-- A defined subtree has defined honest authentication data at every position. -/
theorem authChildren_isSome (P : MerklePrimitives B E) :
    ∀ (h : ℕ) (hle : h ≤ P.depth) (f : (Fin h → Bool) → B) (pos : Fin h → Bool) {rt : B},
      subRoot P h hle f = some rt → (authChildren P h hle f pos).isSome
  | 0, _, _, _, _, _ => by simp [authChildren]
  | h + 1, hle, f, pos, rt, hroot => by
    obtain ⟨bl, br, hbl, hbr, -⟩ := (subRoot_succ P hle f).mp hroot
    have hchosen : subRoot P h (Nat.le_of_succ_le hle)
        (fun p => f (Fin.snoc p (pos (Fin.last h)))) = some (cond (pos (Fin.last h)) br bl) := by
      rcases Bool.eq_false_or_eq_true (pos (Fin.last h)) with hbv | hbv <;> rw [hbv] <;>
        first
        | exact hbl
        | exact hbr
    have hrec := authChildren_isSome P h (Nat.le_of_succ_le hle)
      (fun p => f (Fin.snoc p (pos (Fin.last h)))) (Fin.init pos) hchosen
    obtain ⟨rest, hrest⟩ := Option.isSome_iff_exists.mp hrec
    simp [authChildren, hbl, hbr, hrest]

/-- **Completeness at subtree height.** If the subtree is defined, the honest
authentication data forms a valid height-`h` path for the committed leaf, with the
position bits as the side selectors. -/
theorem pathAux_of_subRoot (P : MerklePrimitives B E) :
    ∀ (h : ℕ) (hle : h ≤ P.depth) (f : (Fin h → Bool) → B) (pos : Fin h → Bool)
      {rt : B} {children : Fin h → E × E},
      subRoot P h hle f = some rt → authChildren P h hle f pos = some children →
      PathAux P h hle (f pos) rt children pos
  | 0, _, f, pos, rt, children, hroot, hauth => by
    refine ⟨fun i => i.elim0, ?_⟩
    have hrt : f (fun i => i.elim0) = rt := by simpa [subRoot] using hroot
    have hpos : pos = fun i => i.elim0 := funext fun i => i.elim0
    simp [nodeAux, Fin.last, hpos, hrt]
  | h + 1, hle, f, pos, rt, children, hroot, hauth => by
    obtain ⟨bl, br, hbl, hbr, hcomp⟩ := (subRoot_succ P hle f).mp hroot
    obtain ⟨bl', br', rest, hbl', hbr', hrest, hch⟩ := (authChildren_succ P hle f pos).mp hauth
    obtain rfl : bl = bl' := Option.some.inj (hbl.symm.trans hbl')
    obtain rfl : br = br' := Option.some.inj (hbr.symm.trans hbr')
    set b := pos (Fin.last h) with hb
    have hchosen : subRoot P h (Nat.le_of_succ_le hle)
        (fun p => f (Fin.snoc p b)) = some (cond b br bl) := by
      rcases Bool.eq_false_or_eq_true b with hbv | hbv <;> rw [hbv] <;>
        first
        | exact hbl
        | exact hbr
    have hleaf : (fun p => f (Fin.snoc p b)) (Fin.init pos) = f pos := by
      show f (Fin.snoc (Fin.init pos) b) = f pos
      rw [hb, Fin.snoc_init_self]
    have ih := pathAux_of_subRoot P h (Nat.le_of_succ_le hle)
      (fun p => f (Fin.snoc p b)) (Fin.init pos) hchosen hrest
    rw [hleaf] at ih
    subst hch
    constructor
    · intro i
      induction i using Fin.lastCases with
      | last =>
          rw [← nodeAux_init P hle, Fin.init_snoc, Fin.snoc_last, ih.2, ← hb]
          rcases Bool.eq_false_or_eq_true b with hbv | hbv <;>
            simp [hbv, selectedChild, P.decode_canon]
      | cast j =>
          rw [← nodeAux_init P hle, Fin.init_snoc, Fin.snoc_castSucc]
          exact ih.1 j
    · rw [← Fin.succ_last]
      simp only [nodeAux, Fin.cases_succ, Fin.snoc_last]
      exact hcomp

/-- **Completeness.** If the tree is defined, the honest authentication data forms a
valid `Path` for the committed leaf, with the position bits as the side selectors. -/
theorem path_of_root (P : MerklePrimitives B E) {f : (Fin P.depth → Bool) → B}
    (pos : Fin P.depth → Bool) {rt : B} {children : Fin P.depth → E × E}
    (hroot : root P f = some rt)
    (hauth : authChildren P P.depth le_rfl f pos = some children) :
    Path P (f pos) rt children pos :=
  (pathAux_depth_iff P).mp (pathAux_of_subRoot P P.depth le_rfl f pos hroot hauth)

/-! ## Position binding -/

/-- **Position binding at subtree height, as an explicit reduction.** A valid path for a
leaf that is not the committed one at its position, against a defined subtree, computes a
collision of one height's compression: descend from the top and compare the path's raw
pair with the honest canonical pair; the first disagreement is the collision (both
compress to the running node), and full agreement forces the leaf, contradicting the
hypothesis. Computable, with the contradictions eliminated in dead branches. -/
def collisionOfWrongLeafAux [DecidableEq E] (P : MerklePrimitives B E) :
    (h : ℕ) → (hle : h ≤ P.depth) → (f : (Fin h → Bool) → B) → (leaf rt : B) →
    (children : Fin h → E × E) → (side : Fin h → Bool) →
    PathAux P h hle leaf rt children side → subRoot P h hle f = some rt →
    leaf ≠ f side → Collision P
  | 0, _, f, leaf, rt, _, side, hpath, hroot, hne =>
    absurd (by
      have hleaf : leaf = rt := Option.some.inj hpath.2
      have hfr : f (fun i => i.elim0) = rt := by simpa [subRoot] using hroot
      have hside : side = fun i => i.elim0 := funext fun i => i.elim0
      rw [hside, hfr, hleaf]) hne
  | h + 1, hle, f, leaf, rt, children, side, hpath, hroot, hne =>
    match hbl : subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p false)),
          hbr : subRoot P h (Nat.le_of_succ_le hle) (fun p => f (Fin.snoc p true)) with
    | some bl, some br =>
      if hcp : children (Fin.last h) = (P.canon bl, P.canon br) then
        collisionOfWrongLeafAux P h (Nat.le_of_succ_le hle)
          (fun p => f (Fin.snoc p (side (Fin.last h)))) leaf
          (cond (side (Fin.last h)) br bl) (Fin.init children) (Fin.init side)
          (by
            refine ⟨fun i => ?_, ?_⟩
            · rw [nodeAux_init P hle]
              exact hpath.1 (Fin.castSucc i)
            · rw [nodeAux_init P hle]
              have hstep := hpath.1 (Fin.last h)
              rw [hcp] at hstep
              rw [hstep]
              rcases Bool.eq_false_or_eq_true (side (Fin.last h)) with hbv | hbv <;>
                rw [hbv] <;> simp [selectedChild, P.decode_canon])
          (by
            rcases Bool.eq_false_or_eq_true (side (Fin.last h)) with hbv | hbv <;>
              rw [hbv] <;>
              first
              | exact hbl
              | exact hbr)
          (by
            intro heq
            apply hne
            have hfs : (fun p => f (Fin.snoc p (side (Fin.last h)))) (Fin.init side)
                = f side := by
              show f (Fin.snoc (Fin.init side) (side (Fin.last h))) = f side
              rw [Fin.snoc_init_self]
            rwa [hfs] at heq)
      else
        ⟨Fin.castLE hle (Fin.last h),
          { q₁ := children (Fin.last h)
            q₂ := (P.canon bl, P.canon br)
            ne := hcp
            output := rt
            eval₁ := by
              have hlast := hpath.2
              rw [← Fin.succ_last] at hlast
              simpa only [nodeAux, Fin.cases_succ] using hlast
            eval₂ := by
              have hroot' := hroot
              simp only [subRoot, hbl, hbr] at hroot'
              exact hroot' }⟩
    | none, _ => absurd (by simp [subRoot, hbl] at hroot) not_false
    | some _, none => absurd (by simp [subRoot, hbl, hbr] at hroot) not_false

/-- **Position binding, as an explicit reduction.** From a valid path that validates
`leaf` at position `side` against a defined tree over `f`, together with
`leaf ≠ f side`, compute a collision of one height's compression — a computable `def`
per the breaks-as-computed-data convention. The collision's queries live in the raw
encoding domain `E × E`, at the height the descent locates: the domain and granularity
the concrete collision bound counts. -/
def collisionOfWrongLeaf [DecidableEq E] (P : MerklePrimitives B E)
    {f : (Fin P.depth → Bool) → B} {leaf rt : B}
    {children : Fin P.depth → E × E} {side : Fin P.depth → Bool}
    (hpath : Path P leaf rt children side) (hroot : root P f = some rt)
    (hne : leaf ≠ f side) : Collision P :=
  collisionOfWrongLeafAux P P.depth le_rfl f leaf rt children side
    ((pathAux_depth_iff P).mpr hpath) hroot hne

end Zcash.Security.Ledger.Merkle

/-- The raw-encoding Merkle interface, re-exported at the ledger namespace for the
statement layer. -/
abbrev Zcash.Security.Ledger.MerklePrimitives (B E : Type*) :=
  Zcash.Security.Ledger.Merkle.MerklePrimitives B E
