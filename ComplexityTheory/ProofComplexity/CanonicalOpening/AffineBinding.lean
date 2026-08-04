/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum.Finite
import ComplexityTheory.ProofComplexity.CanonicalOpening.FiniteStrategy
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Exact affine binding of four binary coordinates

Three committed checksum bits plus one public nonzero affine equation uniquely
determine a four-bit word. A later public coordinate challenge therefore emits
one fixed child value; the prover sends no post-challenge response.

This finite primitive is exact but not asymptotically compressing: its message
has three bits for four coordinates. It assigns no execution or resource bound.
-/

namespace ComplexityTheory
namespace CanonicalOpening
namespace FourCoordinateAffineBinding

open scoped BigOperators

/-- The four block coordinates bound by the affine checksum. -/
abbrev Coordinate := Fin 4

/-- A four-coordinate word over the binary field. -/
abbrev Word := Coordinate → BinaryField

/-- The three field elements committed before the coordinate challenge. -/
abbrev Syndrome := Fin 3 → BinaryField

/-- The binary inner product of two four-coordinate words. -/
def dot (left right : Word) : BinaryField :=
  ∑ coordinate, left coordinate * right coordinate

/--
Select the first nonzero coordinate. The proof makes the final coordinate case
exhaustive rather than a default value.
-/
def firstSupport (word : Word) (_hNonzero : word ≠ 0) : Coordinate :=
  if word 0 = 1 then 0 else if word 1 = 1 then 1 else if word 2 = 1 then 2 else 3

/--
Choose an odd-weight vector paired nontrivially with `linear`. For odd parity
use the all-one word; for even parity delete one supported coordinate.
-/
def kernelVector (linear : Word) (hNonzero : linear ≠ 0) : Word :=
  if dot linear 1 = 1 then 1 else fun coordinate =>
    if coordinate = firstSupport linear hNonzero then 0 else 1

/-- Choose a supported kernel coordinate omitted from the three checksum rows. -/
def pivot (linear : Word) (hNonzero : linear ≠ 0) : Coordinate :=
  if dot linear 1 = 1 then 0
  else if firstSupport linear hNonzero = 0 then 1 else 0

/--
Encode a word using the three parity checks orthogonal to `kernelVector`.
`pivot.succAbove` enumerates the three nonpivot coordinates.
-/
def checksum (linear : Word) (hNonzero : linear ≠ 0) (word : Word) : Syndrome :=
  let kernel := kernelVector linear hNonzero
  let omitted := pivot linear hNonzero
  fun row =>
    word (omitted.succAbove row) +
      kernel (omitted.succAbove row) * word omitted

/-- Decode the unique word satisfying the supplied checksum and affine value. -/
def decode (linear : Word) (hNonzero : linear ≠ 0)
    (syndrome : Syndrome) (affineValue : BinaryField) : Word :=
  let kernel := kernelVector linear hNonzero
  let omitted := pivot linear hNonzero
  let omittedValue := affineValue +
    ∑ row, linear (omitted.succAbove row) * syndrome row
  Fin.insertNth omitted omittedValue fun row =>
    syndrome row + kernel (omitted.succAbove row) * omittedValue

/-- The chosen kernel has affine value one and Hamming weight at least three. -/
theorem kernelVector_spec :
    ∀ (linear : Word) (hNonzero : linear ≠ 0),
      dot linear (kernelVector linear hNonzero) = 1 ∧
        3 ≤ hammingNorm (kernelVector linear hNonzero) := by
  decide

/-- Every decoded word satisfies the public affine equation. -/
theorem dot_decode :
    ∀ (linear : Word) (hNonzero : linear ≠ 0) syndrome affineValue,
      dot linear (decode linear hNonzero syndrome affineValue) = affineValue := by
  decide

/-- Decoding preserves all three committed checksum symbols. -/
theorem checksum_decode :
    ∀ (linear : Word) (hNonzero : linear ≠ 0) syndrome affineValue,
      checksum linear hNonzero (decode linear hNonzero syndrome affineValue) = syndrome := by
  decide

/-- Encoding and decoding recover every word when given its affine value. -/
theorem decode_checksum :
    ∀ (linear : Word) (hNonzero : linear ≠ 0) word,
      decode linear hNonzero (checksum linear hNonzero word) (dot linear word) = word := by
  decide

/-- Exhaustive evaluation accepts every guarded three-bit checksum. -/
theorem check_checksum_isUnique :
    ∀ (linear : Word) (hNonzero : linear ≠ 0),
      checkUniqueDecodingChecksum 1 (checksum linear hNonzero) = true := by
  decide

/-- The three-bit checksum uniquely decodes through Hamming radius one. -/
theorem checksum_isUnique (linear : Word) (hNonzero : linear ≠ 0) :
    IsUniqueDecodingChecksum 1 (checksum linear hNonzero) :=
  (checkUniqueDecodingChecksum_eq_true_iff 1 (checksum linear hNonzero)).mp
    (check_checksum_isUnique linear hNonzero)

/-- A parent binds one canonical block word to one claimed affine value. -/
structure Claim where
  /-- The public linear functional applied to the block word. -/
  linear : Word
  /-- The canonical four block contractions. -/
  canonical : Word
  /-- The claimed value of the public linear functional. -/
  claimed : BinaryField
deriving Fintype

/-- Decide whether the claimed affine value is canonical. -/
def claimTrue (claim : Claim) : Bool :=
  claim.claimed == dot claim.linear claim.canonical

/-- A child compares one decoded coordinate with its canonical block value. -/
structure ChildClaim where
  /-- The canonical block value at the challenged coordinate. -/
  canonical : BinaryField
  /-- The value decoded from the prover's committed syndrome. -/
  claimed : BinaryField

/-- Decide whether a coordinate child is true. -/
def childTrue (child : ChildClaim) : Bool :=
  child.claimed == child.canonical

/--
Run the affine binder. A zero linear functional terminates immediately;
otherwise every challenge emits the coordinate of one globally decoded word.
-/
def run (claim : Claim) (syndrome : Syndrome) (coordinate : Coordinate) :
    OpeningStepResult ChildClaim :=
  if hNonzero : claim.linear ≠ 0 then
    .child ⟨claim.canonical coordinate,
      decode claim.linear hNonzero syndrome claim.claimed coordinate⟩
  else if claim.claimed = 0 then .accept else .reject

/-- Honest provers commit to the checksum of the canonical block word. -/
def honestSyndrome (claim : Claim) : Syndrome :=
  if hNonzero : claim.linear ≠ 0 then
    checksum claim.linear hNonzero claim.canonical
  else 0

set_option maxRecDepth 10000 in
/-- Exhaustive kernel evaluation finds no cheating strategy for any finite claim. -/
theorem checker_findsNoCheatingStrategy :
    ∀ claim,
      hasCheatingOneStepStrategy claimTrue childTrue run claim = false := by
  decide

end FourCoordinateAffineBinding
end CanonicalOpening
end ComplexityTheory
