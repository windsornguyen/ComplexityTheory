/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.AffineBinding.Exact
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact affine opening from four tensor axes to two

This module instantiates the four-coordinate affine binder with the four block
contractions of a `2 x 2 x 2 x 2` tensor. A three-bit message is fixed before
one two-bit public challenge. Every nonterminal result contains a tensor with
exactly two active indices.

The theorem is semantic. In particular, the two-index function type does not
prove that a compiler copies four field elements instead of retaining a closure
over the parent tensor; an operational resource theorem must establish that
representation separately.
-/

namespace ComplexityTheory
namespace CanonicalOpening
namespace FourAxisAffine

open scoped BigOperators
open FourCoordinateAffineBinding

/-- One binary tensor axis. -/
abbrev Axis := Fin 2

/-- A four-axis binary tensor opening claim. -/
structure Open4 where
  /-- The canonical four-axis tensor. -/
  tensor : Axis → Axis → Axis → Axis → BinaryField
  /-- The public weight on the first axis. -/
  firstWeight : Axis → BinaryField
  /-- The public weight on the second axis. -/
  secondWeight : Axis → BinaryField
  /-- The public weight on the third axis. -/
  thirdWeight : Axis → BinaryField
  /-- The public weight on the fourth axis. -/
  fourthWeight : Axis → BinaryField
  /-- The claimed weighted contraction. -/
  claimed : BinaryField

/-- The outer two-axis coefficient vector, flattened lexicographically. -/
def outerWord (claim : Open4) : Word := fun coordinate =>
  let outer := finProdFinEquiv.symm coordinate
  claim.firstWeight outer.1 * claim.secondWeight outer.2

/-- The four canonical contractions of the inner two-axis slices. -/
def canonicalBlockWord (claim : Open4) : Word := fun coordinate =>
  let outer := finProdFinEquiv.symm coordinate
  ∑ third, ∑ fourth,
    claim.tensor outer.1 outer.2 third fourth *
      claim.thirdWeight third * claim.fourthWeight fourth

/-- The associated four-coordinate affine binding claim. -/
def Open4.toAffineClaim (claim : Open4) : FourCoordinateAffineBinding.Claim where
  linear := outerWord claim
  canonical := canonicalBlockWord claim
  claimed := claim.claimed

/-- A four-axis claim is true when its associated weighted contraction is canonical. -/
def Open4.True (claim : Open4) : Prop :=
  claim.toAffineClaim.True

/-- A two-axis tensor opening emitted by one outer-coordinate challenge. -/
structure Open2 where
  /-- The challenged two-axis tensor slice. -/
  tensor : Axis → Axis → BinaryField
  /-- The public weight on the first remaining axis. -/
  firstWeight : Axis → BinaryField
  /-- The public weight on the second remaining axis. -/
  secondWeight : Axis → BinaryField
  /-- The claimed weighted contraction of the slice. -/
  claimed : BinaryField

/-- A two-axis child is true when its weighted slice contraction is canonical. -/
def Open2.True (claim : Open2) : Prop :=
  claim.claimed = ∑ first, ∑ second,
    claim.tensor first second * claim.firstWeight first * claim.secondWeight second

/-- Construct the two-axis child selected by one flattened outer coordinate. -/
def child (parent : Open4) (coordinate : Coordinate) (claimed : BinaryField) : Open2 :=
  let outer := finProdFinEquiv.symm coordinate
  { tensor := fun third fourth => parent.tensor outer.1 outer.2 third fourth
    firstWeight := parent.thirdWeight
    secondWeight := parent.fourthWeight
    claimed }

/-- Child truth is exactly equality with the corresponding canonical block value. -/
theorem child_true_iff (parent : Open4) (coordinate : Coordinate)
    (claimed : BinaryField) :
    (child parent coordinate claimed).True ↔
      claimed = canonicalBlockWord parent coordinate := by
  rfl

/--
Execute the four-to-two fold by decoding one global block word and emitting the
challenged two-axis slice. The prover sends no post-challenge response.
-/
def step (parent : Open4) (syndrome : Syndrome) (coordinate : Coordinate) :
    OpeningStepResult Open2 :=
  if hNonzero : outerWord parent ≠ 0 then
    .child (child parent coordinate
      (decode (outerWord parent) hNonzero syndrome parent.claimed coordinate))
  else if parent.claimed = 0 then .accept else .reject

/-- The honest message is the checksum of the four canonical block contractions. -/
def honestSyndrome (parent : Open4) : Syndrome :=
  FourCoordinateAffineBinding.honestSyndrome parent.toAffineClaim

/-- The affine four-axis fold is an exact opening step with two-axis children. -/
def exactStep : ExactOpeningStep Open4 Syndrome Coordinate Open2 where
  parentTrue := Open4.True
  childTrue := Open2.True
  honestProof := honestSyndrome
  step := step
  complete parent hTrue coordinate := by
    by_cases hNonzero : outerWord parent ≠ 0
    · have hDecoded := decode_checksum (outerWord parent) hNonzero
        (canonicalBlockWord parent)
      change parent.claimed = dot (outerWord parent) (canonicalBlockWord parent) at hTrue
      rw [← hTrue] at hDecoded
      have hHonest : honestSyndrome parent =
          checksum (outerWord parent) hNonzero (canonicalBlockWord parent) := by
        simp [honestSyndrome, FourCoordinateAffineBinding.honestSyndrome,
          Open4.toAffineClaim, hNonzero]
      rw [hHonest]
      simp [step, hNonzero, hDecoded, child_true_iff,
        OpeningStepResult.PreservesTrue]
    · have hLinear : outerWord parent = 0 := not_ne_iff.mp hNonzero
      have hClaimed : parent.claimed = 0 := by
        change parent.claimed = dot (outerWord parent) (canonicalBlockWord parent) at hTrue
        simpa [hLinear, dot] using hTrue
      simp [step, hNonzero, hClaimed, OpeningStepResult.PreservesTrue]
  falseDescent parent hFalse syndrome := by
    by_cases hNonzero : outerWord parent ≠ 0
    · let decoded := decode (outerWord parent) hNonzero syndrome parent.claimed
      have hDecodedValue : dot (outerWord parent) decoded = parent.claimed :=
        dot_decode (outerWord parent) hNonzero syndrome parent.claimed
      have hDifferent : decoded ≠ canonicalBlockWord parent := by
        intro hEqual
        apply hFalse
        exact hDecodedValue.symm.trans (congrArg (dot (outerWord parent)) hEqual)
      have hCoordinate :
          ∃ coordinate, decoded coordinate ≠ canonicalBlockWord parent coordinate := by
        by_contra hNoCoordinate
        apply hDifferent
        funext coordinate
        by_contra hAtCoordinate
        exact hNoCoordinate ⟨coordinate, hAtCoordinate⟩
      obtain ⟨coordinate, hAtCoordinate⟩ := hCoordinate
      exact ⟨coordinate, by
        simp [step, hNonzero, decoded, child_true_iff,
          OpeningStepResult.ExposesFalse, hAtCoordinate]⟩
    · have hLinear : outerWord parent = 0 := not_ne_iff.mp hNonzero
      have hClaimed : parent.claimed ≠ 0 := by
        intro hZero
        apply hFalse
        simp [Open4.True, Open4.toAffineClaim, Claim.True, hLinear, hZero, dot]
      exact ⟨0, by
        simp [step, hNonzero, hClaimed, OpeningStepResult.ExposesFalse]⟩

end FourAxisAffine
end CanonicalOpening
end ComplexityTheory
