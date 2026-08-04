/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Locality barrier for linear unique-decoding checksums

A radius-one linear checksum must touch every input coordinate. Consequently,
if every checksum symbol is a sparse linear functional whose support is the
mass of its opening child, input mass is at most checksum length times child
mass. This covers the direct linear-syndrome/local-support grammar; it does not
cover a proximity protocol that produces a different compressed child.
-/

namespace ComplexityTheory
namespace CanonicalOpening

/-- The input coordinates used by one row of a linear checksum matrix. -/
def checksumRowSupport {Row Column Scalar : Type}
    [Fintype Column] [DecidableEq Scalar] [Zero Scalar]
    (matrix : Matrix Row Column Scalar) (row : Row) : Finset Column :=
  Finset.univ.filter fun column => matrix row column ≠ 0

/-- A nonzero singleton word has Hamming weight one. -/
@[simp] theorem hammingNorm_single_one
    {Column Scalar : Type}
    [Fintype Column] [DecidableEq Column]
    [DecidableEq Scalar] [NonAssocSemiring Scalar] [Nontrivial Scalar]
    (column : Column) :
    hammingNorm (Pi.single column (1 : Scalar) : Column → Scalar) = 1 := by
  rw [hammingNorm]
  change (Finset.univ.filter
    (fun index => (Pi.single column (1 : Scalar) : Column → Scalar) index ≠ 0)).card = 1
  have hSupport : Finset.univ.filter
      (fun index => (Pi.single column (1 : Scalar) : Column → Scalar) index ≠ 0) =
      {column} := by
    ext index
    by_cases hIndex : index = column
    · subst index
      simp
    · simp [Pi.single_apply, hIndex]
  rw [hSupport]
  simp

/--
Every column of a radius-one unique-decoding checksum matrix contains a
nonzero entry. Otherwise zero and the corresponding unit vector collide within
distance one of the zero word.
-/
theorem exists_nonzero_entry_of_radiusOneChecksum
    {Row Column Scalar : Type}
    [Fintype Column]
    [DecidableEq Scalar] [NonAssocSemiring Scalar] [Nontrivial Scalar]
    (matrix : Matrix Row Column Scalar)
    (hUnique : IsUniqueDecodingChecksum 1 matrix.mulVec)
    (column : Column) :
    ∃ row, matrix row column ≠ 0 := by
  classical
  by_contra hNoEntry
  have hColumnZero : ∀ row, matrix row column = 0 := by
    intro row
    by_contra hEntry
    exact hNoEntry ⟨row, hEntry⟩
  have hSameChecksum :
      matrix.mulVec (Pi.single column (1 : Scalar)) = matrix.mulVec 0 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_zero]
    funext row
    exact hColumnZero row
  have hDifferent : (Pi.single column (1 : Scalar) : Column → Scalar) ≠ 0 := by
    intro hZero
    have hAtColumn := congrFun hZero column
    simp at hAtColumn
  have hNear :
      hammingDist (Pi.single column (1 : Scalar)) (0 : Column → Scalar) ≤ 1 :=
    (hammingNorm_single_one column).le
  exact hUnique 0 (Pi.single column (1 : Scalar)) 0
    hNear (by simp) hDifferent hSameChecksum

/--
If every input coordinate occurs in some matrix row and every row support has
size at most `maxSupport`, then the input length is at most the number of rows
times `maxSupport`.
-/
theorem columnCard_le_rowCard_mul_maxSupport
    {Row Column Scalar : Type}
    [Fintype Row] [Fintype Column]
    [DecidableEq Scalar] [Zero Scalar]
    (matrix : Matrix Row Column Scalar)
    (hColumn : ∀ column, ∃ row, matrix row column ≠ 0)
    (maxSupport : Nat)
    (hRow : ∀ row, (checksumRowSupport matrix row).card ≤ maxSupport) :
    Fintype.card Column ≤ Fintype.card Row * maxSupport := by
  classical
  have hCovered :
      Finset.univ.biUnion (checksumRowSupport matrix) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro column
    obtain ⟨row, hEntry⟩ := hColumn column
    exact Finset.mem_biUnion.mpr ⟨row, Finset.mem_univ row, by
      simp [checksumRowSupport, hEntry]⟩
  calc
    Fintype.card Column =
        (Finset.univ.biUnion (checksumRowSupport matrix)).card := by
      rw [hCovered]
      simp
    _ ≤ Finset.univ.card * maxSupport :=
      Finset.card_biUnion_le_card_mul Finset.univ
        (checksumRowSupport matrix) maxSupport (fun row _ => hRow row)
    _ = Fintype.card Row * maxSupport := by simp

/--
A radius-one unique-decoding checksum with row support at most `maxSupport`
obeys the same checksum-length times child-mass incidence bound.
-/
theorem columnCard_le_rowCard_mul_maxSupport_of_radiusOneChecksum
    {Row Column Scalar : Type}
    [Fintype Row] [Fintype Column]
    [DecidableEq Scalar] [NonAssocSemiring Scalar] [Nontrivial Scalar]
    (matrix : Matrix Row Column Scalar)
    (hUnique : IsUniqueDecodingChecksum 1 matrix.mulVec)
    (maxSupport : Nat)
    (hRow : ∀ row, (checksumRowSupport matrix row).card ≤ maxSupport) :
    Fintype.card Column ≤ Fintype.card Row * maxSupport :=
  columnCard_le_rowCard_mul_maxSupport matrix
    (exists_nonzero_entry_of_radiusOneChecksum matrix hUnique) maxSupport hRow

/--
At square-log scale, a radius-one linear checksum cannot have both
`2^(C*m)` rows and row support at most `2^(C*m)` while covering
`2^(m^2)` input coordinates once `m > 2*C`.
-/
theorem squareLogChecksum_not_shortAndLocal
    {Row Column Scalar : Type}
    [Fintype Row] [Fintype Column]
    [DecidableEq Scalar] [NonAssocSemiring Scalar] [Nontrivial Scalar]
    (matrix : Matrix Row Column Scalar)
    (hUnique : IsUniqueDecodingChecksum 1 matrix.mulVec)
    {constant scale : Nat}
    (hScale : 2 * constant < scale)
    (hColumnCount : Fintype.card Column = 2 ^ (scale * scale))
    (hRowCount : Fintype.card Row ≤ 2 ^ (constant * scale))
    (hRowSupport : ∀ row,
      (checksumRowSupport matrix row).card ≤ 2 ^ (constant * scale)) : False := by
  have hIncidence := columnCard_le_rowCard_mul_maxSupport_of_radiusOneChecksum
    matrix hUnique (2 ^ (constant * scale)) hRowSupport
  have hBound :
      2 ^ (scale * scale) ≤ (2 ^ (constant * scale)) ^ 2 := by
    calc
      2 ^ (scale * scale) = Fintype.card Column := hColumnCount.symm
      _ ≤ Fintype.card Row * 2 ^ (constant * scale) := hIncidence
      _ ≤ 2 ^ (constant * scale) * 2 ^ (constant * scale) :=
        Nat.mul_le_mul_right _ hRowCount
      _ = (2 ^ (constant * scale)) ^ 2 := by rw [pow_two]
  have hScalePositive : 0 < scale := lt_of_le_of_lt (Nat.zero_le _) hScale
  have hExponent : (constant * scale) * 2 < scale * scale := by
    calc
      (constant * scale) * 2 = (2 * constant) * scale := by ac_rfl
      _ < scale * scale := (Nat.mul_lt_mul_right hScalePositive).2 hScale
  have hStrict : (2 ^ (constant * scale)) ^ 2 < 2 ^ (scale * scale) := by
    rw [← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hExponent
  exact (Nat.not_lt_of_ge hBound) hStrict

end CanonicalOpening
end ComplexityTheory
