/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum.RadiusOne

/-!
# Radius-one checksum classification

Hamming, *Error Detecting and Error Correcting Codes*, Bell System Technical
Journal 29(2), 1950, Section 3, pp. 150-154, uses nonzero, pairwise-distinct
binary check columns. This module proves the finite-field projective
generalization: scaled columns must be nonzero and pairwise distinct.
-/

namespace ComplexityTheory
namespace CanonicalOpening

private theorem exists_radiusOneErrorWord_eq
    {Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [Zero Scalar] [DecidableEq Scalar]
    (word : Column → Scalar) (hWeight : hammingNorm word ≤ 1) :
    ∃ error : RadiusOneError Column Scalar, radiusOneErrorWord error = word := by
  by_cases hZero : word = 0
  · exact ⟨none, by simp [radiusOneErrorWord, hZero]⟩
  · have hPositive : 0 < hammingNorm word := hammingNorm_pos_iff.mpr hZero
    have hCard : (Finset.univ.filter fun column => word column ≠ 0).card = 1 := by
      unfold hammingNorm at hWeight hPositive
      omega
    obtain ⟨column, hSupport⟩ := Finset.card_eq_one.mp hCard
    have hValue : word column ≠ 0 := by
      have : column ∈ Finset.univ.filter fun column => word column ≠ 0 := by
        simp [hSupport]
      simpa using this
    refine ⟨some (column, ⟨word column, hValue⟩), ?_⟩
    funext index
    by_cases hIndex : index = column
    · subst index
      simp [radiusOneErrorWord]
    · have hOutside : word index = 0 := by
        by_contra hNonzero
        have : index ∈ Finset.univ.filter fun column => word column ≠ 0 := by
          simpa using hNonzero
        rw [hSupport, Finset.mem_singleton] at this
        exact hIndex this
      simp [radiusOneErrorWord, hIndex, hOutside]

private theorem exists_radiusOneErrorFromCenter
    {Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [AddCommGroup Scalar] [DecidableEq Scalar]
    {center word : Column → Scalar}
    (hNear : hammingDist word center ≤ 1) :
    ∃ error : RadiusOneError Column Scalar,
      word = center + radiusOneErrorWord error := by
  have hWeight : hammingNorm (-center + word) ≤ 1 := by
    rw [← hammingDist_eq_hammingNorm center word, hammingDist_comm]
    exact hNear
  obtain ⟨error, hError⟩ := exists_radiusOneErrorWord_eq (-center + word) hWeight
  refine ⟨error, ?_⟩
  rw [hError]
  abel

/--
A linear checksum uniquely decodes radius one exactly when its syndromes
separate the no-error case and every nonzero single-coordinate error.
-/
theorem isUniqueDecodingChecksum_one_iff_radiusOneErrorSyndrome_injective
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column]
    [Field Scalar] [DecidableEq Scalar]
    (matrix : Matrix Row Column Scalar) :
    IsUniqueDecodingChecksum 1 matrix.mulVec ↔
      Function.Injective (radiusOneErrorSyndrome matrix) := by
  constructor
  · exact radiusOneErrorSyndrome_injective matrix
  · intro hSyndrome center first second hFirst hSecond hDifferent hChecksum
    obtain ⟨firstError, hFirstError⟩ := exists_radiusOneErrorFromCenter hFirst
    obtain ⟨secondError, hSecondError⟩ := exists_radiusOneErrorFromCenter hSecond
    have hErrorChecksum :
        radiusOneErrorSyndrome matrix firstError =
          radiusOneErrorSyndrome matrix secondError := by
      rw [hFirstError, hSecondError, Matrix.mulVec_add, Matrix.mulVec_add] at hChecksum
      exact add_left_cancel hChecksum
    have hErrors : firstError = secondError := hSyndrome hErrorChecksum
    apply hDifferent
    rw [hFirstError, hSecondError, hErrors]

/-- The syndrome of one nonzero coordinate error. -/
def singleErrorSyndrome
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [Semiring Scalar]
    (matrix : Matrix Row Column Scalar)
    (error : Column × { value : Scalar // value ≠ 0 }) : Row → Scalar :=
  radiusOneErrorSyndrome matrix (some error)

/-- A single-error syndrome is the corresponding nonzero multiple of a column. -/
@[simp] theorem singleErrorSyndrome_eq_smul_col
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [CommSemiring Scalar]
    (matrix : Matrix Row Column Scalar)
    (error : Column × { value : Scalar // value ≠ 0 }) :
    singleErrorSyndrome matrix error = error.2.1 • matrix.col error.1 := by
  simp [singleErrorSyndrome, radiusOneErrorSyndrome, radiusOneErrorWord]

/--
The projective column condition: every nonzero scaled column is nonzero, and no
two distinct coordinate-value pairs have the same scaled column.
-/
def HasProjectivelyDistinctColumns
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column] [Semiring Scalar]
    (matrix : Matrix Row Column Scalar) : Prop :=
  (∀ error, singleErrorSyndrome matrix error ≠ 0) ∧
    Function.Injective (singleErrorSyndrome matrix)

/-- Radius-one error syndromes are injective exactly under the projective condition. -/
theorem radiusOneErrorSyndrome_injective_iff_projectivelyDistinct
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column]
    [Field Scalar]
    (matrix : Matrix Row Column Scalar) :
    Function.Injective (radiusOneErrorSyndrome matrix) ↔
      HasProjectivelyDistinctColumns matrix := by
  classical
  constructor
  · intro hInjective
    constructor
    · intro error hZero
      have hEqual :
          radiusOneErrorSyndrome matrix (some error) =
            radiusOneErrorSyndrome matrix none := by
        simpa [singleErrorSyndrome, radiusOneErrorSyndrome, radiusOneErrorWord]
          using hZero
      exact Option.some_ne_none error (hInjective hEqual)
    · intro first second hEqual
      exact Option.some.inj (hInjective hEqual)
  · rintro ⟨hNonzero, hInjective⟩ first second hEqual
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some second =>
            exfalso
            apply hNonzero second
            simpa [singleErrorSyndrome, radiusOneErrorSyndrome, radiusOneErrorWord]
              using hEqual.symm
    | some first =>
        cases second with
        | none =>
            exfalso
            apply hNonzero first
            simpa [singleErrorSyndrome, radiusOneErrorSyndrome, radiusOneErrorWord]
              using hEqual
        | some second => exact congrArg some (hInjective hEqual)

/-- Radius-one linear unique decoding is equivalent to projective column separation. -/
theorem isUniqueDecodingChecksum_one_iff_projectivelyDistinct
    {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Column]
    [Field Scalar] [DecidableEq Scalar]
    (matrix : Matrix Row Column Scalar) :
    IsUniqueDecodingChecksum 1 matrix.mulVec ↔
      HasProjectivelyDistinctColumns matrix :=
  (isUniqueDecodingChecksum_one_iff_radiusOneErrorSyndrome_injective matrix).trans
    (radiusOneErrorSyndrome_injective_iff_projectivelyDistinct matrix)

end CanonicalOpening
end ComplexityTheory
