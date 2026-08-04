/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Step
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact opening by listing every slice contraction

The prover lists one claimed contraction per slice. A binding challenge checks
their weighted sum, while a localization challenge emits one slice claim. This
gives exact false descent, but the product barrier at the end shows why it
cannot provide square-log shrinkage with a square-root-size message.
-/

namespace ComplexityTheory
namespace LinearContractionOpening

open scoped BigOperators

/-- The weighted contraction of one finite family of slice values. -/
def value {Index Scalar : Type} [Fintype Index] [Semiring Scalar]
    (weight sliceValue : Index → Scalar) : Scalar :=
  ∑ index, weight index * sliceValue index

/-- A verifier either checks the aggregate binding equation or localizes a slice. -/
inductive Challenge (Index : Type) where
  /-- Check that the proof's weighted contraction equals the parent claim. -/
  | binding
  /-- Continue with the claimed value of one selected slice. -/
  | slice (index : Index)

/-- A child claims one canonical slice contraction. -/
structure ChildClaim (Index Scalar : Type) where
  /-- Identify the selected slice. -/
  index : Index
  /-- State the prover's claimed contraction of that slice. -/
  claimed : Scalar

/--
Execute the full-slice contraction protocol without reading the canonical
slice values. A localization challenge merely exposes a smaller claim; it does
not verify that child semantically.
-/
def step {Index Scalar : Type} [Fintype Index] [Semiring Scalar] [DecidableEq Scalar]
    (weight : Index → Scalar) (claimed : Scalar) (proof : Index → Scalar) :
    Challenge Index → OpeningStepResult (ChildClaim Index Scalar)
  | .binding => if claimed = value weight proof then .accept else .reject
  | .slice index => .child ⟨index, proof index⟩

/--
Listing every slice contraction is an exact recursive opening step. If the
binding equation passes for a false parent, at least one listed slice differs
from its canonical value and localization can expose it.
-/
def exactStep {Index Scalar : Type}
    [Fintype Index] [Semiring Scalar] [DecidableEq Scalar]
    (weight canonicalSlice : Index → Scalar) :
    ExactOpeningStep Scalar (Index → Scalar) (Challenge Index) (ChildClaim Index Scalar) where
  parentTrue claimed := claimed = value weight canonicalSlice
  childTrue child := child.claimed = canonicalSlice child.index
  honestProof _ := canonicalSlice
  step := step weight
  complete claimed hTrue challenge := by
    cases challenge with
    | binding => simp [step, hTrue, OpeningStepResult.PreservesTrue]
    | slice index => simp [step, OpeningStepResult.PreservesTrue]
  falseDescent claimed hFalse proof := by
    classical
    by_cases hBinding : claimed = value weight proof
    · have hMismatch : ∃ index, proof index ≠ canonicalSlice index := by
        by_contra hNoMismatch
        have hProof : proof = canonicalSlice := by
          funext index
          by_contra hDifferent
          exact hNoMismatch ⟨index, hDifferent⟩
        exact hFalse (by simpa [hProof] using hBinding)
      obtain ⟨index, hDifferent⟩ := hMismatch
      exact ⟨.slice index, by
        simp [step, OpeningStepResult.ExposesFalse, hDifferent]⟩
    · exact ⟨.binding, by
        simp [step, OpeningStepResult.ExposesFalse, hBinding]⟩

/--
If a parent is the product of its slice count and child mass, bounding both by
one budget bounds the parent by the square of that budget.
-/
theorem parentMass_le_budgetSquare
    {parentMass sliceCount childMass budget : Nat}
    (hShape : parentMass = sliceCount * childMass)
    (hMessage : sliceCount ≤ budget) (hChild : childMass ≤ budget) :
    parentMass ≤ budget ^ 2 := by
  simpa [hShape, pow_two] using Nat.mul_le_mul hMessage hChild

/--
At square-log scale, the naive full-slice protocol cannot simultaneously fit
its list of slice contractions and every child slice inside `2^(constant*m)`
once `m > 2*constant`.
-/
theorem squareLogMass_not_both_bounded
    {constant scale sliceCount childMass : Nat}
    (hScale : 2 * constant < scale)
    (hShape : 2 ^ (scale * scale) = sliceCount * childMass) :
    ¬(sliceCount ≤ 2 ^ (constant * scale) ∧
      childMass ≤ 2 ^ (constant * scale)) := by
  intro hBounds
  have hBound := parentMass_le_budgetSquare hShape hBounds.1 hBounds.2
  have hScalePositive : 0 < scale := lt_of_le_of_lt (Nat.zero_le _) hScale
  have hExponent : (constant * scale) * 2 < scale * scale := by
    calc
      (constant * scale) * 2 = (2 * constant) * scale := by ac_rfl
      _ < scale * scale := (Nat.mul_lt_mul_right hScalePositive).2 hScale
  have hStrict : (2 ^ (constant * scale)) ^ 2 < 2 ^ (scale * scale) := by
    rw [← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hExponent
  exact (Nat.not_lt_of_ge hBound) hStrict

end LinearContractionOpening
end ComplexityTheory
