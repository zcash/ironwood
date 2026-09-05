import Zcash.Circuits.Ecc.MulFixed.Certs.NullifierK
import Zcash.Circuits.Ecc.MulFixed.Certs.ValueCommitR
import Zcash.Circuits.Ecc.MulFixed.Certs.SpendAuthG
import Zcash.Circuits.Ecc.MulFixed.Certs.CommitIvkR
import Zcash.Circuits.Ecc.MulFixed.Certs.NoteCommitR
import Zcash.Circuits.Ecc.MulFixed.Certs.ValueCommitV
import Zcash.Circuits.Specs.SinsemillaGenerators
import Zcash.Circuits.Poseidon.Hash
import Zcash.Circuits.NoteCommit.MainTheorems
import Zcash.Security.Concrete.PallasGroup
import Zcash.Security.Ledger.Statement
import Zcash.Security.KeyBinding.Pool
import Zcash.Security.RedDSA.Basic

/-!
# The deployed pool's concrete ledger primitives

This module instantiates the abstract ledger `Primitives` and
`KeyBindingInterface` for the deployed pool over Pallas.  It supplies the
concrete `Encoding`, note/value commitments, nullifier derivation, Merkle
compression, and key binding used by the games-facing statement, with the
Sinsemilla domain points (`merkleQ`, `ivkQ`, `noteQ`) inlined as on-curve
constants.
-/

namespace Zcash.Security.Ledger.Pool

open Zcash.Circuits
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete

/-! ## Sinsemilla domain points

The `SinsemillaHashToPoint` initial points `Q(D) = GroupHash("z.cash:SinsemillaQ", D)`
(protocol spec §5.4.1.9) for the three deployed Orchard domains, inlined as affine
constants and proved on-curve.  The coordinates are the deployed values from
`zcash/orchard`'s `src/constants/sinsemilla.rs`.
-/

/-- `Q("z.cash:Orchard-MerkleCRH")` — `Q_MERKLE_CRH` in `zcash/orchard`. -/
def merkleQ : Point Fp :=
  { x := (9991206725476878888751475603038274618448000607209514551456795194094072219296 :
      Fp),
    y := (24209798415301550423396126020228723009317736024280831393239261884225294625378 :
      Fp) }

theorem merkleQ_onCurve : merkleQ.OnCurve := by
  show merkleQ.y ^ 2 = merkleQ.x ^ 3 + pallasB
  decide

/-- `Q("z.cash:Orchard-CommitIvk-M")` — `Q_COMMIT_IVK_M_GENERATOR` in `zcash/orchard`. -/
def ivkQ : Point Fp :=
  { x := (2593820817260930114322133467408868473290945477826616247349533151445648376562 :
      Fp),
    y := (12214744946019415453501880094709511126888074367290315326445800415816181472958 :
      Fp) }

theorem ivkQ_onCurve : ivkQ.OnCurve := by
  show ivkQ.y ^ 2 = ivkQ.x ^ 3 + pallasB
  decide

/-- `Q("z.cash:Orchard-NoteCommit-M")` — `Q_NOTE_COMMITMENT_M_GENERATOR` in `zcash/orchard`. -/
def noteQ : Point Fp :=
  { x := (10629404576683096409262958701336170057000067777256141967953463442979689100381 :
      Fp),
    y := (22898949290933268079297281211505753011910178734473470279111609228438645877859 :
      Fp) }

theorem noteQ_onCurve : noteQ.OnCurve := by
  show noteQ.y ^ 2 = noteQ.x ^ 3 + pallasB
  decide

abbrev Encoding := { n : ℕ // n < 2 ^ 255 }

def decode (e : Encoding) : Fp := (e.1 : Fp)

/-- Level-personalized Merkle compression of a raw child pair.  The escape branch is
`none`, not a totalized sentinel: definedness of every layer is recorded in
`Merkle.Path` (see `Merkle.Path.compress_isSome`), so a Sinsemilla exceptional branch
here can never masquerade as a genuine node value nor as a Merkle collision. -/
def merkleCompress (i : Fin 32) (children : Encoding × Encoding) : Option Fp :=
  (hashToPoint orchardGenerators.S merkleQ
    (merkleChunks i.1 children.1.1 children.2.1)).map Point.x

theorem merkleCompress_eq_of_hashToPoint {i : Fin 32} {children : Encoding × Encoding}
    {p : Point Fp}
    (h : hashToPoint orchardGenerators.S merkleQ
      (merkleChunks i.1 children.1.1 children.2.1) = some p) :
    merkleCompress i children = some p.x := by
  unfold merkleCompress
  rw [h]
  rfl

/-- The canonical 255-bit encoding of a node value: its canonical representative. -/
def canon (b : Fp) : Encoding :=
  ⟨b.val, lt_trans (ZMod.val_lt b)
    (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])⟩

theorem decode_canon (b : Fp) : decode (canon b) = b := ZMod.natCast_zmod_val b

def merkle : MerklePrimitives Fp Encoding where
  depth := 32
  decode := decode
  compress := merkleCompress
  canon := canon
  decode_canon := decode_canon

def extract (P : PallasGroup) : Fp := (PallasGroup.toPoint P).x

@[simp] theorem extract_ofPoint (P : Point Fp) (hP : P.Valid) :
    extract (PallasGroup.ofPoint P hP) = P.x := by
  simp [extract]

/-- `13` is a quadratic non-residue in the Pallas base field, so it is not a square. -/
theorem unc_thirteen_not_isSquare : ¬ IsSquare (13 : Fp) :=
  Zcash.Circuits.Ecc.MulFixed.Cert.Chain.thirteen_not_isSquare

/-- Protocol-spec Theorem 5.4.6 for the ledger pool: `Uncommitted^Orchard = 2` is not the
extracted `x`-coordinate of any Pallas group element. -/
theorem extract_ne_two (g : PallasGroup) : (PallasGroup.toPoint g).x ≠ 2 := by
  intro hx2
  rcases PallasGroup.toPoint_valid g with hCurve | hZero
  · -- On-curve case: `x = 2` forces `y² = 2³ + 5 = 13`, a non-residue.
    unfold Point.OnCurve at hCurve
    rw [hx2] at hCurve
    have h13 : (PallasGroup.toPoint g).y ^ 2 = (13 : Fp) := by
      rw [hCurve]; norm_num [pallasB]
    exact unc_thirteen_not_isSquare ⟨(PallasGroup.toPoint g).y, by rw [← h13]; ring⟩
  · -- Identity case: its affine encoding is `(0, 0)`, so `x = 0 ≠ 2`.
    rw [hZero] at hx2
    simp only [Point.zero_def] at hx2
    exact two_ne_zero hx2.symm

def randomizePublic (α : Fq) (ak : PallasGroup) : PallasGroup :=
  α • PallasGroup.ofPoint Ecc.MulFixed.Certs.spendAuthG.point
    (Or.inl Ecc.MulFixed.Certs.spendAuthG.onCurve) + ak

theorem toPoint_randomizePublic (α : Fq) (ak : PallasGroup) :
    PallasGroup.toPoint (randomizePublic α ak) =
      α.val • Ecc.MulFixed.Certs.spendAuthG.point + PallasGroup.toPoint ak := by
  simp [randomizePublic]

def deriveNullifier (nk rho psi : Fp) (cm : PallasGroup) : Fp :=
  (PallasGroup.toPoint cm +
    ((Poseidon.Hash.ConstantLength.value #v[nk, rho] + psi).val : Fq).val
      • Ecc.MulFixed.Certs.nullifierK.point).x

def intScalar (z : ℤ) : Fq := (z : Fq)

def valueCommit (z : ℤ) (r : Fq) : PallasGroup :=
  intScalar z • PallasGroup.ofPoint Ecc.MulFixed.Certs.valueCommitV.point
      (Or.inl Ecc.MulFixed.Certs.valueCommitV.onCurve)
    + r • PallasGroup.ofPoint Ecc.MulFixed.Certs.valueCommitR.point
      (Or.inl Ecc.MulFixed.Certs.valueCommitR.onCurve)

/-- The deployed value-commitment value base 𝒱^Orchard (§5.4.8.3,
<https://zips.z.cash/protocol/protocol.pdf#concretehomomorphiccommit>). -/
def valueCommitV : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.valueCommitV.point
    (Or.inl Ecc.MulFixed.Certs.valueCommitV.onCurve)

/-- The deployed value-commitment randomness base ℛ^Orchard (§5.4.8.3,
<https://zips.z.cash/protocol/protocol.pdf#concretehomomorphiccommit>). -/
def valueCommitR : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.valueCommitR.point
    (Or.inl Ecc.MulFixed.Certs.valueCommitR.onCurve)

/-- Deployed RedPallas binding verification with challenge hash `H`: RedDSA's Schnorr
equation at ℛ^Orchard (`valueCommitR`), byte encodings elided. Balance uses its
extractability —the binding signature as a signature of knowledge of `bsk`— not its
unforgeability. -/
def redPallasBindingVerify {MSG : Type*} (H : PallasGroup → PallasGroup → MSG → Fq) :
    PallasGroup → MSG → Zcash.Security.RedDSA.Sig Fq PallasGroup → Prop :=
  (Zcash.Security.RedDSA.Scheme.mk valueCommitR H).Verify

theorem toPoint_valueCommit (z : ℤ) (r : Fq) :
    PallasGroup.toPoint (valueCommit z r) =
      (intScalar z).val • Ecc.MulFixed.Certs.valueCommitV.point +
        r.val • Ecc.MulFixed.Certs.valueCommitR.point := by
  simp [valueCommit]

def notePoint (P : PallasGroup) : Point Fp := PallasGroup.toPoint P

def noteScalars (n : Note PallasGroup Fp Fp) : NoteCommit.NoteCommitScalars :=
  NoteCommit.noteScalars (notePoint n.gd) (notePoint n.pkd) (n.v : Fp) n.ρ n.ψ

def noteHash (n : Note PallasGroup Fp Fp) : Option (Point Fp) :=
  hashToPoint orchardGenerators.S noteQ (noteScalars n).chunks

/-- The deployed note commitment: the Sinsemilla hash of the note message, plus the
blinding term `rcm • NoteCommitR`.

The blinding addition is the complete group addition, matching both the protocol spec's
`SinsemillaCommit` (§5.4.8.4, complete addition since spec version 2021.2.16) and the
deployed `halo2_gadgets` `CommitDomain::commit`.  Completeness there is
soundness-relevant: an incomplete addition would let a prover choose `rcm` to force an
exceptional case.  The same applies to the `Commit^ivk` opening consumed by
`keyBinding`. -/
def noteCommit (rcm : Fq) (n : Note PallasGroup Fp Fp) : Option PallasGroup :=
  noteHash n >>= fun bp =>
    PallasGroup.ofPoint? (bp + rcm.val • Ecc.MulFixed.Certs.noteCommitR.point)

theorem noteCommit_eq_some_of_hash {rcm : Fq} {n : Note PallasGroup Fp Fp} {bp : Point Fp}
    {cm : PallasGroup}
    (hh : noteHash n = some bp)
    (hcm : PallasGroup.ofPoint? (bp + rcm.val • Ecc.MulFixed.Certs.noteCommitR.point) = some cm) :
    noteCommit rcm n = some cm := by
  simp [noteCommit, hh, hcm]

theorem noteCommit_eq_some_of_hashToPoint {rcm : Fq} {n : Note PallasGroup Fp Fp}
    {bp cm : Point Fp} (hbp : noteHash n = some bp)
    (hcm : cm = bp + rcm.val • Ecc.MulFixed.Certs.noteCommitR.point)
    (hvalid : cm.Valid) :
    noteCommit rcm n = some (PallasGroup.ofPoint cm hvalid) := by
  apply noteCommit_eq_some_of_hash hbp
  subst cm
  exact PallasGroup.ofPoint?_eq_some _ hvalid

/-- `Uncommitted^Orchard` (protocol spec §4.2.3): the padding value for tree positions
beyond the appended leaves.  `extract_ne_two` below is spec Theorem 5.4.6: it is not
the extracted coordinate of any Pallas group element. -/
def uncommitted : Fp := 2

variable {MSG SIG : Type*}

/-- The deployed pool's concrete primitives.  The spend-authorization and
binding-signature verification predicates are parameters: the Action circuit neither
constrains nor witnesses signatures, so every bridge statement holds for arbitrary
schemes; the concrete RedPallas instantiations compose downstream. -/
def primitives (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop) :
    Primitives Fq PallasGroup Fp Fp Fp Fp Fp Encoding MSG SIG where
  valueBound := 2 ^ 64
  vBalanceBound := 2 ^ 63
  emb := PallasGroup.embedFp
  emb_injective := PallasGroup.embedFp_injective
  extract := extract
  noteCommit := noteCommit
  deriveNullifier := deriveNullifier
  merkle := merkle
  uncommitted := uncommitted
  uncommitted_ne := extract_ne_two
  randomizePublic := randomizePublic
  valueCommit := valueCommit
  spendAuthVerify := spendAuthVerify
  bindingVerify := bindingVerify

def commitIvkHash (ak nk : Fp) : Option PallasGroup :=
  (hashToPoint orchardGenerators.S ivkQ
    (commitIvkChunks ak.val nk.val)).bind fun p => PallasGroup.ofPoint? p

theorem commitIvkHash_eq_some_of_hashToPoint {ak nk : Fp} {p : Point Fp}
    (h : hashToPoint orchardGenerators.S ivkQ
      (commitIvkChunks ak.val nk.val) = some p) (hp : p.Valid) :
    commitIvkHash ak nk = some (PallasGroup.ofPoint p hp) := by
  unfold commitIvkHash
  rw [h, Option.bind_some]
  exact PallasGroup.ofPoint?_eq_some p hp

/-- The deployed circuit's key-binding interface: the bare `Commit^ivk` opening
`Extract(hashPoint + rivk • CommitIvkR)` plus `ivk ≠ 0`.  As with `noteCommit`, the
blinding addition is the complete group addition, matching both §5.4.8.4 and the
deployed gadget. -/
def keyBinding : KeyBindingInterface (KeyBinding.Pool.Witness Fq PallasGroup Fp)
    PallasGroup Fp Fp :=
  KeyBinding.Pool.toInterface extract commitIvkHash
    (PallasGroup.ofPoint Ecc.MulFixed.Certs.commitIvkR.point
      (Or.inl Ecc.MulFixed.Certs.commitIvkR.onCurve))
    (fun P Q h => (PallasGroup.toPoint_x_eq_iff P Q).mp h)

end Zcash.Security.Ledger.Pool
