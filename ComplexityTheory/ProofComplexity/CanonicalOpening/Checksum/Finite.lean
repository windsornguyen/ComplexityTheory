/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.ZMod.Basic

/-!
# Finite checksum synthesis over the binary field

This module exhaustively checks the smallest nontrivial unique-decoding
checksum instance. It retains both a surviving two-row matrix and a collision
certificate for every one-row candidate.
-/

namespace ComplexityTheory
namespace CanonicalOpening

/-- The two-element field used by the first finite checksum experiment. -/
abbrev BinaryField := ZMod 2

/-- Enumerate every binary linear checksum matrix satisfying the finite checker. -/
def binaryLinearChecksumCandidates
    (inputLength checksumLength radius : Nat) :
    Finset (Matrix (Fin checksumLength) (Fin inputLength) BinaryField) :=
  Finset.univ.filter fun matrix =>
    checkUniqueDecodingChecksum radius matrix.mulVec

/--
A two-row checksum that uniquely identifies every three-bit word within
Hamming radius one of a fixed center.
-/
def threeBitRadiusOneChecksum : Matrix (Fin 2) (Fin 3) BinaryField :=
  !![1, 1, 0; 0, 1, 1]

/-- The concrete two-row checksum passes exhaustive unique-decoding verification. -/
@[simp] theorem check_threeBitRadiusOneChecksum :
    checkUniqueDecodingChecksum 1 threeBitRadiusOneChecksum.mulVec = true := by
  decide

/-- The concrete two-row checksum has the radius-one unique-decoding property. -/
theorem threeBitRadiusOneChecksum_isUnique :
    IsUniqueDecodingChecksum 1 threeBitRadiusOneChecksum.mulVec :=
  (checkUniqueDecodingChecksum_eq_true_iff
    1 threeBitRadiusOneChecksum.mulVec).mp check_threeBitRadiusOneChecksum

/-- Exactly six binary two-row matrices solve the three-bit radius-one instance. -/
@[simp] theorem card_threeBitRadiusOneChecksums :
    (binaryLinearChecksumCandidates 3 2 1).card = 6 := by
  decide

/-- Every binary one-row checksum fails the three-bit radius-one checker. -/
theorem check_everyOneRowChecksum_fails :
    ∀ matrix : Matrix (Fin 1) (Fin 3) BinaryField,
      checkUniqueDecodingChecksum 1 matrix.mulVec = false := by
  decide

set_option maxSynthPendingDepth 20 in
/--
Every binary one-row checksum has an explicit collision between two distinct
words within radius one of a common center. This finite witness is the complete
obstruction detected by the exhaustive checker.
-/
theorem everyOneRowChecksum_hasCollision :
    ∀ matrix : Matrix (Fin 1) (Fin 3) BinaryField,
      ∃ center first second : Fin 3 → BinaryField,
        hammingDist first center ≤ 1 ∧
          hammingDist second center ≤ 1 ∧
            first ≠ second ∧ matrix.mulVec first = matrix.mulVec second := by
  decide

end CanonicalOpening
end ComplexityTheory
