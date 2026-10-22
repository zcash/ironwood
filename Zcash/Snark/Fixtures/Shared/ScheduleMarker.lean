import Zcash.Snark.Verifier.FiatShamir

/-!
# Re-encode captured Fiat–Shamir schedules

The exporter represents a completed squeeze by appending its challenge value as a synthetic
`.scalar` separator in the capture. Halo2 itself does not reabsorb that value. `deriveChallenges`
instead records halo2's challenge-domain marker before the squeeze.

`markerSchedule` converts the captured form to the marker form. Fixture checks then compare the
result with `deriveChallenges` using `native_decide`.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-- Convert one captured schedule step by dropping the synthetic challenge separator and appending
its marker. -/
def markerSchedule.go (prev : List (TranscriptElt F G) × F) (oldLen : ℕ) :
    List (List (TranscriptElt F G) × F) → List (List (TranscriptElt F G) × F)
  | [] => [prev]
  | e :: es =>
      prev :: markerSchedule.go (prev.1 ++ e.1.drop (oldLen + 1) ++ [.challenge], e.2) e.1.length es

/-- Convert an exporter-captured schedule to `deriveChallenges`'s marker encoding. -/
def markerSchedule : List (List (TranscriptElt F G) × F) → List (List (TranscriptElt F G) × F)
  | [] => []
  | e :: es => markerSchedule.go (e.1 ++ [.challenge], e.2) e.1.length es

end Zcash.Snark
