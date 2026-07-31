# Ironwood–Garden Action bridge

`Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean` is the
canonical dependency-free Action source. It imports only `Init.Prelude`.
`Int`, named `ActionGarden.Z`, is its only arithmetic carrier; `Nat` is used
only for structural recursion and indices. Base-field and scalar-field
behavior is expressed with named moduli and explicit modulo operations.

`Zcash.Circuits.Action.IronwoodGardenActionBridge` is the library entry point.
It imports the standalone specification and its correspondence proof, so
`lake build Zcash` checks both.

The review-facing API deliberately follows Garden:

- `Params` contains the three Sinsemilla domain points;
- `ActionInputs` contains exactly the inputs consumed by the output function;
- `FullActionInputs` adds `rcmOld` and the three validity flags;
- Merkle elements are explicit `(layer, sibling, isRight)` triples;
- `validActionInputs` is the seven-clause semantic input predicate;
- `orchardAction` is a total input-to-output function.

The standalone file contains no second `Core…` Action specification. The
proof-only `ProofCore` namespace lives in the Ironwood-dependent bridge file,
is not translated to Rocq, and exists only to decompose the circuit witness
relation into manageable lemmas.

## Lean bridge to Ironwood

`ActionGardenBridge.lean` imports Ironwood and maps `Fp`, `Fq`, Pallas points,
paths, inputs, and outputs to the explicit-integer model. It proves the
field/integer, group, Poseidon, Sinsemilla, message-packing, Merkle, ownership,
note-commitment, nullifier, randomized-key, and value-commitment
correspondences used by the two public capstones.

Its deployed-constant audit proves:

- equality of the complete 64-row Poseidon table;
- equality of the complete 1,024-row Sinsemilla generator table;
- finite-index accessor equality for both tables;
- equality of all three domain points and all six fixed bases.

The review-facing input theorem is:

```lean
validActionInputs_iff_exists_proverAssumptionsPost
```

It says that `ActionGarden.validActionInputs orchardParams (fullInput wit)`
holds exactly when there is an `ActionData` with the same public full input
that satisfies Ironwood's `ProverAssumptionsPost`. The existential completion
is necessary: `fullInput` intentionally erases five circuit-specific
fixed-base window arrays and five stored output fields.

The separate output theorem is:

```lean
proverAssumptionsPost_implies_gardenOrchardAction_output
```

Under `ProverAssumptionsPost`, it proves that the integer encoding of all five
stored Ironwood outputs is exactly
`ActionGarden.orchardAction orchardParams (gardenInput wit)`.

Check the complete Lean bridge using a disk-backed temporary directory:

```sh
TMPDIR=/home/fedora/Zcash/tmp/action-garden \
lake build \
  +Zcash.Circuits.Action.IronwoodGardenActionBridge.ActionGardenBridge
```

## Generated Lean-to-Rocq boundary

There is no hand-maintained Rocq body mirror. A Lean frontend elaborates the
supplied source, parses the same immutable byte snapshot without `.olean`
reuse, and emits a schema-versioned syntax representation; the closed Rocq
emitter then resolves and translates every supported body. Both Rocq files,
including the primitive-array storage declarations, are emitted directly—no
`.v.in` semantic template remains. The generator:

1. accepts only the restricted standalone Lean subset and consumes the whole
   file;
2. rejects axioms, theorem dependencies, type classes, notation, extra
   imports, unsupported syntax, and unresolved names;
3. accounts for all 119 Lean declarations in source order;
4. translates ordinary bodies and the audited representation lowerings for
   the 64 and 1,024-row constant tables;
5. stamps both generated files with the exact Lean SHA-256;
6. checks the committed complete source diff.

A body-only source change therefore changes the corresponding generated Rocq
body or is rejected before any output is written; updating only the source
hash cannot make a stale translation pass.

The generated constants use Rocq primitive arrays. Their signed-`Z` accessor
preserves Lean's behavior: negative indices select row zero and indices past
the end return the explicit fallback.

Generate or verify the committed artifacts:

```sh
TMPDIR=/home/fedora/Zcash/tmp/action-garden \
python3 Zcash/Circuits/Action/IronwoodGardenActionBridge/lean_to_rocq.py \
  Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean \
  ../garden/Garden/Orchard/IronwoodGardenActionBridge/action_garden_generated.v \
  --diff Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean-rocq.diff

TMPDIR=/home/fedora/Zcash/tmp/action-garden \
python3 Zcash/Circuits/Action/IronwoodGardenActionBridge/lean_to_rocq.py \
  Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean \
  ../garden/Garden/Orchard/IronwoodGardenActionBridge/action_garden_generated.v \
  --diff Zcash/Circuits/Action/IronwoodGardenActionBridge/ActionGarden.lean-rocq.diff \
  --check
```

Garden now needs five files:

- `action_garden_constants.v` and `action_garden_generated.v` are generated;
- `action_garden_bridge.v` proves the representation and arithmetic facts;
- `action_garden_poseidon_bridge.v` isolates the Poseidon correspondence;
- `action_garden_equivalence.v` proves the direct comparison with Garden's
  current Post-NU6.3 protocol and circuit theorem.

The Rocq output equality
`ActionGardenEquivalence.orchard_action_output_eq` is unconditional. The
theorems `orchard_action_output_of_action_statement` and
`native_valid_action_inputs_of_action_statement` then compose it directly
with Garden's native Post-NU6.3 `action_statement`. There is no alternate
NU6.2 semantics and no legacy Core Action layer on the Rocq side.

Garden's native validity predicate is indexed by the assignment `Γ` and reads
some ownership witnesses outside its protocol input record. The bridge keeps
that shape instead of manufacturing a misleading record-level iff. The
Lean-side theorem above is the exact record-level characterization at the
Ironwood witness boundary.

Garden's companion report is
`garden/docs/ironwood-garden-action-bridge.md`.
