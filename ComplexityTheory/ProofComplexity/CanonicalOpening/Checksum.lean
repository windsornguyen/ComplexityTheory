/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.BigOperators

/-!
# Unique-decoding checksums

Chen, Hong, Kalai, and Xi, *Towards a Doubly Efficient IP = PSPACE*, ECCC
TR26-102, revision 1, June 19, 2026, Definition 6 and Proposition 1, p. 9
(PDF p. 11), use linear-code syndromes to bind words only within a prescribed
Hamming radius. This module states that local binding property using Mathlib's
Hamming distance and proves the kernel-distance criterion from their
proposition.
-/

namespace ComplexityTheory
namespace CanonicalOpening

/--
A checksum is `radius`-unique-decoding when it separates every two distinct
words lying within that Hamming radius of one common center. The definition does
not claim that a checksum is globally injective or that a word is near a center.
-/
def IsUniqueDecodingChecksum
    {Index Symbol Checksum : Type} [Fintype Index] [DecidableEq Symbol]
    (radius : Nat) (checksum : (Index → Symbol) → Checksum) : Prop :=
  ∀ center first second,
    hammingDist first center ≤ radius →
      hammingDist second center ≤ radius →
        first ≠ second → checksum first ≠ checksum second

/--
Exhaustively decide the unique-decoding property for finite checksum domains.
This is the trusted Lean-side checker for checksum candidates proposed by an
external enumerator; it does not search for a candidate itself.
-/
def checkUniqueDecodingChecksum
    {Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Symbol] [DecidableEq Symbol]
    [DecidableEq Checksum]
    (radius : Nat) (checksum : (Index → Symbol) → Checksum) : Bool :=
  letI : Decidable (IsUniqueDecodingChecksum radius checksum) := by
    unfold IsUniqueDecodingChecksum
    infer_instance
  decide (IsUniqueDecodingChecksum radius checksum)

/-- The finite checksum checker returns true exactly for unique-decoding maps. -/
@[simp] theorem checkUniqueDecodingChecksum_eq_true_iff
    {Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Symbol] [DecidableEq Symbol]
    [DecidableEq Checksum]
    (radius : Nat) (checksum : (Index → Symbol) → Checksum) :
    checkUniqueDecodingChecksum radius checksum = true ↔
      IsUniqueDecodingChecksum radius checksum := by
  simp [checkUniqueDecodingChecksum, IsUniqueDecodingChecksum]

/--
Two words with the same unique-decoding checksum are equal when one lies within
the decoding radius of the other. This is the binding half of the near-far
dichotomy; a separate proximity argument must establish the distance premise.
-/
theorem eq_of_checksum_eq_of_hammingDist_le
    {Index Symbol Checksum : Type} [Fintype Index] [DecidableEq Symbol]
    {radius : Nat} {checksum : (Index → Symbol) → Checksum}
    (hUnique : IsUniqueDecodingChecksum radius checksum)
    {canonical candidate : Index → Symbol}
    (hNear : hammingDist candidate canonical ≤ radius)
    (hChecksum : checksum candidate = checksum canonical) :
    candidate = canonical := by
  by_contra hDifferent
  exact hUnique canonical candidate canonical hNear (by simp) hDifferent hChecksum

/--
Distinct words with the same unique-decoding checksum must be farther apart
than the decoding radius. A checksum does not by itself prove which word is
canonical; it converts inconsistency into a distance obligation.
-/
theorem radius_lt_hammingDist_of_checksum_eq_of_ne
    {Index Symbol Checksum : Type} [Fintype Index] [DecidableEq Symbol]
    {radius : Nat} {checksum : (Index → Symbol) → Checksum}
    (hUnique : IsUniqueDecodingChecksum radius checksum)
    {canonical candidate : Index → Symbol}
    (hChecksum : checksum candidate = checksum canonical)
    (hDifferent : candidate ≠ canonical) :
    radius < hammingDist candidate canonical := by
  apply Nat.lt_of_not_ge
  intro hNear
  exact hDifferent (eq_of_checksum_eq_of_hammingDist_le hUnique hNear hChecksum)

/--
If every coordinate can be recovered exactly from a checksum alone, then the
checksum is injective. Thus a short syndrome needs an additional proximity or
interaction mechanism; it cannot serve as a lossless local oracle by itself.
-/
theorem checksum_injective_of_exactDecoder
    {Index Symbol Checksum : Type}
    (checksum : (Index → Symbol) → Checksum)
    (decoder : Checksum → Index → Symbol)
    (hExact : ∀ word index, decoder (checksum word) index = word index) :
    Function.Injective checksum := by
  intro first second hChecksum
  funext index
  rw [← hExact first index, ← hExact second index, hChecksum]

/-- Exact coordinate decoding forces the checksum space to contain every word. -/
theorem wordCard_le_checksumCard_of_exactDecoder
    {Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Symbol] [Fintype Checksum]
    (checksum : (Index → Symbol) → Checksum)
    (decoder : Checksum → Index → Symbol)
    (hExact : ∀ word index, decoder (checksum word) index = word index) :
    Fintype.card (Index → Symbol) ≤ Fintype.card Checksum :=
  Fintype.card_le_of_injective checksum
    (checksum_injective_of_exactDecoder checksum decoder hExact)

/--
No checksum of fewer binary coordinates can exactly recover every coordinate
of every longer binary word. This rules out checksum-only local opening before
any protocol-specific resource analysis.
-/
theorem no_exactDecoder_of_shortBinaryChecksum
    {inputLength checksumLength : Nat}
    (hShort : checksumLength < inputLength)
    (checksum : (Fin inputLength → Bool) → (Fin checksumLength → Bool)) :
    ¬∃ decoder : (Fin checksumLength → Bool) → Fin inputLength → Bool,
      ∀ word index, decoder (checksum word) index = word index := by
  rintro ⟨decoder, hExact⟩
  have hCard := wordCard_le_checksumCard_of_exactDecoder checksum decoder hExact
  simp only [Fintype.card_pi_const, Fintype.card_bool] at hCard
  exact (Nat.not_lt_of_ge hCard) (Nat.pow_lt_pow_right (by decide) hShort)

/--
An additive checksum is unique-decoding inside radius `radius` when every
nonzero kernel word has Hamming weight greater than `2 * radius`. This is the
syndrome binding argument of Chen, Hong, Kalai, and Xi, Proposition 1.
-/
theorem isUniqueDecodingChecksum_of_kernelDistance
    {Index Scalar Syndrome : Type}
    [Fintype Index] [DecidableEq Scalar]
    [AddCommGroup Scalar] [AddCommGroup Syndrome]
    (radius : Nat) (checksum : (Index → Scalar) →+ Syndrome)
    (hKernelDistance : ∀ word,
      checksum word = 0 → word ≠ 0 → 2 * radius < hammingNorm word) :
    IsUniqueDecodingChecksum radius checksum := by
  intro center first second hFirst hSecond hDifferent hSameChecksum
  let difference := -first + second
  have hDifferenceChecksum : checksum difference = 0 := by
    calc
      checksum difference = -checksum first + checksum second := by
        simp [difference]
      _ = 0 := neg_add_eq_zero.mpr hSameChecksum
  have hDifferenceNonzero : difference ≠ 0 := by
    intro hZero
    exact hDifferent (neg_add_eq_zero.mp hZero)
  have hCenterSecond : hammingDist center second ≤ radius := by
    simpa [hammingDist_comm] using hSecond
  have hDistance : hammingDist first second ≤ 2 * radius := by
    calc
      hammingDist first second ≤
          hammingDist first center + hammingDist center second :=
        hammingDist_triangle first center second
      _ ≤ radius + radius := Nat.add_le_add hFirst hCenterSecond
      _ = 2 * radius := by omega
  have hFar := hKernelDistance difference hDifferenceChecksum hDifferenceNonzero
  change 2 * radius < hammingNorm (-first + second) at hFar
  rw [← hammingDist_eq_hammingNorm first second] at hFar
  exact (Nat.not_lt_of_ge hDistance) hFar

end CanonicalOpening
end ComplexityTheory
