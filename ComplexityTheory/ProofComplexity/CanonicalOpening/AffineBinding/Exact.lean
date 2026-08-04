/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.AffineBinding

/-!
# Exactness of the four-coordinate affine binder

The finite search in `AffineBinding` is promoted here to the semantic
`ExactOpeningStep` interface. Every false affine claim and every committed
three-bit syndrome expose a false coordinate child.
-/

namespace ComplexityTheory
namespace CanonicalOpening
namespace FourCoordinateAffineBinding

/-- The propositional truth predicate underlying `claimTrue`. -/
def Claim.True (claim : Claim) : Prop :=
  claim.claimed = dot claim.linear claim.canonical

/-- The propositional truth predicate underlying `childTrue`. -/
def ChildClaim.True (child : ChildClaim) : Prop :=
  child.claimed = child.canonical

/--
The no-response affine binder is an exact opening step. The proof message is
fixed before the coordinate challenge, so exactness uses no response table.
-/
def exactStep : ExactOpeningStep Claim Syndrome Coordinate ChildClaim where
  parentTrue := Claim.True
  childTrue := ChildClaim.True
  honestProof := honestSyndrome
  step := run
  complete claim hTrue coordinate := by
    by_cases hNonzero : claim.linear ≠ 0
    · have hDecoded := decode_checksum claim.linear hNonzero claim.canonical
      rw [← hTrue] at hDecoded
      simp [run, hNonzero, honestSyndrome, hDecoded,
        ChildClaim.True, OpeningStepResult.PreservesTrue]
    · have hLinear : claim.linear = 0 := not_ne_iff.mp hNonzero
      have hClaimed : claim.claimed = 0 := by
        simpa [Claim.True, hLinear, dot] using hTrue
      simp [run, hNonzero, hClaimed, OpeningStepResult.PreservesTrue]
  falseDescent claim hFalse syndrome := by
    by_cases hNonzero : claim.linear ≠ 0
    · let decoded := decode claim.linear hNonzero syndrome claim.claimed
      have hDecodedValue : dot claim.linear decoded = claim.claimed :=
        dot_decode claim.linear hNonzero syndrome claim.claimed
      have hDifferent : decoded ≠ claim.canonical := by
        intro hEqual
        apply hFalse
        exact hDecodedValue.symm.trans (congrArg (dot claim.linear) hEqual)
      have hCoordinate : ∃ coordinate, decoded coordinate ≠ claim.canonical coordinate := by
        by_contra hNoCoordinate
        apply hDifferent
        funext coordinate
        by_contra hAtCoordinate
        exact hNoCoordinate ⟨coordinate, hAtCoordinate⟩
      obtain ⟨coordinate, hAtCoordinate⟩ := hCoordinate
      exact ⟨coordinate, by
        simp [run, hNonzero, decoded, ChildClaim.True,
          OpeningStepResult.ExposesFalse, hAtCoordinate]⟩
    · have hLinear : claim.linear = 0 := not_ne_iff.mp hNonzero
      have hClaimed : claim.claimed ≠ 0 := by
        intro hZero
        apply hFalse
        simp [Claim.True, hLinear, hZero, dot]
      exact ⟨0, by
        simp [run, hNonzero, hClaimed, OpeningStepResult.ExposesFalse]⟩

end FourCoordinateAffineBinding
end CanonicalOpening
end ComplexityTheory
