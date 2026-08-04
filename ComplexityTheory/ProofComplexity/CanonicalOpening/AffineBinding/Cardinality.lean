/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.AffineBinding

/-!
# Cardinality barrier for deterministic affine binding

An affine equation on `n + 1` binary coordinates leaves `n` coordinates free.
Any deterministic no-response decoder representing every solution therefore
needs at least `2^n` messages, or at least `n` binary message coordinates.

The coverage hypothesis is essential. The theorem does not apply when only a
structured subset of solutions must be represented or when later interaction
supplies additional binding information.
-/

namespace ComplexityTheory
namespace CanonicalOpening
namespace AffineBinding

open scoped BigOperators

/--
Complete `n` free coordinates to one solution of a binary affine equation by
solving for the omitted pivot coordinate.
-/
def completeWord {n : Nat} (pivot : Fin (n + 1))
    (coefficient : Fin n → BinaryField) (affineValue : BinaryField)
    (free : Fin n → BinaryField) : Fin (n + 1) → BinaryField :=
  Fin.insertNth pivot
    (affineValue + ∑ index, coefficient index * free index) free

/-- Distinct assignments to the free coordinates produce distinct completed words. -/
theorem completeWord_injective {n : Nat} (pivot : Fin (n + 1))
    (coefficient : Fin n → BinaryField) (affineValue : BinaryField) :
    Function.Injective (completeWord pivot coefficient affineValue) := by
  intro first second hEqual
  funext index
  have hCoordinate := congrFun hEqual (pivot.succAbove index)
  simpa [completeWord] using hCoordinate

/--
If a finite message decoder represents every solution of one binary affine
equation on `n + 1` coordinates, its message space contains at least `2^n`
elements.
-/
theorem messageCardinality_ge_twoPow_freeCoordinates
    {n : Nat} {Message : Type} [Fintype Message]
    (pivot : Fin (n + 1)) (coefficient : Fin n → BinaryField)
    (affineValue : BinaryField)
    (decode : Message → Fin (n + 1) → BinaryField)
    (hCovers : ∀ free, ∃ message,
      decode message = completeWord pivot coefficient affineValue free) :
    2 ^ n ≤ Fintype.card Message := by
  classical
  let encode : (Fin n → BinaryField) → Message := fun free =>
    Classical.choose (hCovers free)
  have hEncode : ∀ free,
      decode (encode free) = completeWord pivot coefficient affineValue free := fun free =>
    Classical.choose_spec (hCovers free)
  have hInjective : Function.Injective encode := by
    intro first second hEqual
    apply completeWord_injective pivot coefficient affineValue
    calc
      completeWord pivot coefficient affineValue first = decode (encode first) :=
        (hEncode first).symm
      _ = decode (encode second) := congrArg decode hEqual
      _ = completeWord pivot coefficient affineValue second := hEncode second
  have hCard := Fintype.card_le_of_injective encode hInjective
  simpa using hCard

/--
A binary no-response binder representing every affine solution needs at least
one message bit per free coordinate.
-/
theorem binaryMessageLength_ge_freeCoordinates
    {n messageLength : Nat}
    (pivot : Fin (n + 1)) (coefficient : Fin n → BinaryField)
    (affineValue : BinaryField)
    (decode : (Fin messageLength → Bool) → Fin (n + 1) → BinaryField)
    (hCovers : ∀ free, ∃ message,
      decode message = completeWord pivot coefficient affineValue free) :
    n ≤ messageLength := by
  have hCard := messageCardinality_ge_twoPow_freeCoordinates
    pivot coefficient affineValue decode hCovers
  simp only [Fintype.card_pi_const, Fintype.card_bool] at hCard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hCard

end AffineBinding
end CanonicalOpening
end ComplexityTheory
