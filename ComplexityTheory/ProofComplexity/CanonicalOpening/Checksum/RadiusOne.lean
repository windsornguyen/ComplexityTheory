/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum
import Mathlib.Data.Matrix.Mul

/-!
# Radius-one linear checksums

Hamming, *Error Detecting and Error Correcting Codes*, Bell System Technical
Journal 29(2), 1950, Section 3, pp. 150-154, derives the binary single-error
check-value count. This module proves its finite-field cardinality
generalization for the project's radius-one checksum definition.
-/

namespace ComplexityTheory
namespace CanonicalOpening

/-- The no-error case or one coordinate carrying a nonzero error value. -/
abbrev RadiusOneError (Column Scalar : Type) [Zero Scalar] :=
  Option (Column × { value : Scalar // value ≠ 0 })

/-- Interpret a radius-one error description as a word. -/
def radiusOneErrorWord
    {Column Scalar : Type} [Zero Scalar] [DecidableEq Column] :
    RadiusOneError Column Scalar → Column → Scalar
  | none => 0
  | some (column, value) => Pi.single column value

private theorem hammingDist_single_zero_le_one
    {Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [Zero Scalar] [DecidableEq Scalar]
    (column : Column) (value : Scalar) :
    hammingDist (Pi.single column value) (0 : Column → Scalar) ≤ 1 := by
  rw [hammingDist, Finset.card_le_one]
  intro first hFirst second hSecond
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hFirst hSecond
  have hFirstColumn : first = column := by
    by_contra hDifferent
    simp [hDifferent] at hFirst
  have hSecondColumn : second = column := by
    by_contra hDifferent
    simp [hDifferent] at hSecond
  exact hFirstColumn.trans hSecondColumn.symm

/-- Every represented radius-one error lies within distance one of zero. -/
theorem radiusOneErrorWord_nearZero
    {Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [Zero Scalar] [DecidableEq Scalar]
    (error : RadiusOneError Column Scalar) :
    hammingDist (radiusOneErrorWord error) (0 : Column → Scalar) ≤ 1 := by
  cases error with
  | none => simp [radiusOneErrorWord]
  | some error => exact hammingDist_single_zero_le_one error.1 error.2.1

/-- Distinct radius-one error descriptions denote distinct words. -/
theorem radiusOneErrorWord_injective
    {Column Scalar : Type}
    [DecidableEq Column] [Zero Scalar] :
    Function.Injective
      (radiusOneErrorWord : RadiusOneError Column Scalar → Column → Scalar) := by
  intro first second hWords
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second =>
          exfalso
          have hValue : (0 : Scalar) = second.2.1 := by
            simpa only [radiusOneErrorWord, Pi.zero_apply, Pi.single_eq_same]
              using congrFun hWords second.1
          exact second.2.2 hValue.symm
  | some first =>
      cases second with
      | none =>
          exfalso
          have hValue : first.2.1 = 0 := by
            simpa only [radiusOneErrorWord, Pi.single_eq_same, Pi.zero_apply]
              using congrFun hWords first.1
          exact first.2.2 hValue
      | some second =>
          have hColumn : first.1 = second.1 := by
            by_contra hDifferent
            have hValue : first.2.1 = 0 := by
              simpa only [radiusOneErrorWord, Pi.single_eq_same,
                Pi.single_eq_of_ne hDifferent] using congrFun hWords first.1
            exact first.2.2 hValue
          apply congrArg some
          apply Prod.ext hColumn
          apply Subtype.ext
          have hValue := congrFun hWords first.1
          simpa [radiusOneErrorWord, hColumn] using hValue

/-- Apply a linear checksum to a radius-one error word. -/
def radiusOneErrorSyndrome
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [Semiring Scalar]
    (matrix : Matrix Row Column Scalar) :
    RadiusOneError Column Scalar → Row → Scalar :=
  fun error => matrix.mulVec (radiusOneErrorWord error)

/-- Radius-one unique decoding makes the single-error syndrome map injective. -/
theorem radiusOneErrorSyndrome_injective
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column]
    [Field Scalar] [DecidableEq Scalar]
    (matrix : Matrix Row Column Scalar)
    (hUnique : IsUniqueDecodingChecksum 1 matrix.mulVec) :
    Function.Injective (radiusOneErrorSyndrome matrix) := by
  intro first second hSyndrome
  apply radiusOneErrorWord_injective
  by_contra hWordsDifferent
  exact hUnique 0 (radiusOneErrorWord first) (radiusOneErrorWord second)
    (radiusOneErrorWord_nearZero first) (radiusOneErrorWord_nearZero second)
    hWordsDifferent hSyndrome

/--
The radius-one Hamming bound: the zero error and every nonzero single-coordinate
error require distinct syndromes.
-/
theorem radiusOne_hammingBound
    {Row Column Scalar : Type}
    [Fintype Row] [Fintype Column]
    [Fintype Scalar] [Field Scalar] [DecidableEq Scalar]
    (matrix : Matrix Row Column Scalar)
    (hUnique : IsUniqueDecodingChecksum 1 matrix.mulVec) :
    1 + Fintype.card Column * (Fintype.card Scalar - 1) ≤
      Fintype.card Scalar ^ Fintype.card Row := by
  classical
  have hNonzeroCard :
      Fintype.card { value : Scalar // value ≠ 0 } = Fintype.card Scalar - 1 := by
    change Fintype.card { value : Scalar // value ∈ ({0} : Set Scalar)ᶜ } = _
    rw [Fintype.card_compl_set]
    simp
  have hCard := Fintype.card_le_of_injective (radiusOneErrorSyndrome matrix)
    (radiusOneErrorSyndrome_injective matrix hUnique)
  rw [show Fintype.card (RadiusOneError Column Scalar) =
      Fintype.card (Option (Column × { value : Scalar // value ≠ 0 })) by rfl,
    Fintype.card_option, Fintype.card_prod, hNonzeroCard,
    Fintype.card_fun] at hCard
  omega

/--
A radius-one checksum over a two-element field with `r` rows binds at most
`2^r - 1` input columns.
-/
theorem binaryRadiusOne_checksumLengthBound
    {Scalar : Type} [Fintype Scalar] [Field Scalar] [DecidableEq Scalar]
    {inputLength checksumLength : Nat}
    (hBinary : Fintype.card Scalar = 2)
    (matrix : Matrix (Fin checksumLength) (Fin inputLength) Scalar)
    (hUnique : IsUniqueDecodingChecksum 1 matrix.mulVec) :
    inputLength ≤ 2 ^ checksumLength - 1 := by
  have hBound := radiusOne_hammingBound matrix hUnique
  simp only [Fintype.card_fin, hBinary] at hBound
  omega

end CanonicalOpening
end ComplexityTheory
