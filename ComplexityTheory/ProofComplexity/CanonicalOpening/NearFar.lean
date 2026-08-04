/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum
import ComplexityTheory.ProofComplexity.CanonicalOpening.Step

/-!
# Near-far opening semantics

This module isolates the semantic composition used by a checksum-bound
proximity argument. It does not construct a proximity protocol or assign
resource bounds to one.
-/

namespace ComplexityTheory
namespace CanonicalOpening

/-- Every valid object in one checksum fiber lies beyond the stated radius. -/
def IsFarFromGoodFiber
    {Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Symbol]
    (radius : Nat) (checksum : (Index → Symbol) → Checksum)
    (canonical : Index → Symbol) (good : (Index → Symbol) → Prop) : Prop :=
  ∀ candidate,
    checksum candidate = checksum canonical →
      good candidate → radius < hammingDist candidate canonical

/--
Unique decoding lifts invalidity of the canonical object to distance from every
valid object in its checksum fiber.
-/
theorem uniqueNear_invalid_implies_farFromGoodFiber
    {Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Symbol]
    {radius : Nat} {checksum : (Index → Symbol) → Checksum}
    (hUnique : IsUniqueDecodingChecksum radius checksum)
    (canonical : Index → Symbol) (good : (Index → Symbol) → Prop)
    (hCanonicalInvalid : ¬good canonical) :
    IsFarFromGoodFiber radius checksum canonical good := by
  intro candidate hChecksum hGood
  apply radius_lt_hammingDist_of_checksum_eq_of_ne hUnique hChecksum
  intro hEqual
  subst candidate
  exact hCanonicalInvalid hGood

/--
The semantic inputs to a near-far fold. The proximity step remains explicit: a
consumer must construct it and separately account for its resources.
-/
structure NearFarFold
    (Parent Proof Challenge ChildClaim Index Symbol Checksum : Type)
    [Fintype Index] [DecidableEq Symbol] where
  /-- Distance within which the checksum binds an object uniquely. -/
  radius : Nat
  /-- Bind an object to its checksum fiber. -/
  checksum : (Index → Symbol) → Checksum
  /-- Prove uniqueness inside the declared radius. -/
  uniqueChecksum : IsUniqueDecodingChecksum radius checksum
  /-- Return the canonical object determined by a parent claim. -/
  canonical : Parent → Index → Symbol
  /-- State the semantic truth condition for a parent claim. -/
  parentTrue : Parent → Prop
  /-- State the local property that a nearby object must satisfy. -/
  locallyValid : Parent → (Index → Symbol) → Prop
  /-- A parent is true exactly when its canonical object is locally valid. -/
  parentTrue_iff_canonicalValid :
    ∀ parent, parentTrue parent ↔ locallyValid parent (canonical parent)
  /-- Verify proximity to the locally valid part of the checksum fiber. -/
  proximityStep : ExactOpeningStep Parent Proof Challenge ChildClaim
  /--
  The proximity step accepts exactly when some locally valid object in the
  canonical checksum fiber is near the canonical object.
  -/
  proximityTruth : ∀ parent,
    proximityStep.parentTrue parent ↔
      ∃ candidate,
        checksum candidate = checksum (canonical parent) ∧
          locallyValid parent candidate ∧
            hammingDist candidate (canonical parent) ≤ radius

namespace NearFarFold

/-- A false parent is far from every locally valid object in its checksum fiber. -/
theorem falseParent_farFromGoodFiber
    {Parent Proof Challenge ChildClaim Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Symbol]
    (fold : NearFarFold Parent Proof Challenge ChildClaim Index Symbol Checksum)
    (parent : Parent) (hFalse : ¬fold.parentTrue parent) :
    IsFarFromGoodFiber fold.radius fold.checksum (fold.canonical parent)
      (fold.locallyValid parent) := by
  apply uniqueNear_invalid_implies_farFromGoodFiber fold.uniqueChecksum
  exact fun hValid => hFalse ((fold.parentTrue_iff_canonicalValid parent).mpr hValid)

/-- Parent truth is exactly the truth predicate checked by the proximity step. -/
theorem parentTrue_iff_proximityTrue
    {Parent Proof Challenge ChildClaim Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Symbol]
    (fold : NearFarFold Parent Proof Challenge ChildClaim Index Symbol Checksum)
    (parent : Parent) :
    fold.parentTrue parent ↔ fold.proximityStep.parentTrue parent := by
  rw [fold.proximityTruth]
  constructor
  · intro hTrue
    exact ⟨fold.canonical parent, rfl,
      (fold.parentTrue_iff_canonicalValid parent).mp hTrue, by simp⟩
  · rintro ⟨candidate, hChecksum, hValid, hNear⟩
    have hEqual := eq_of_checksum_eq_of_hammingDist_le
      fold.uniqueChecksum hNear hChecksum
    subst candidate
    exact (fold.parentTrue_iff_canonicalValid parent).mpr hValid

/-- Reinterpret the explicit proximity subgame as an exact step for the parent claim. -/
def exactStep
    {Parent Proof Challenge ChildClaim Index Symbol Checksum : Type}
    [Fintype Index] [DecidableEq Symbol]
    (fold : NearFarFold Parent Proof Challenge ChildClaim Index Symbol Checksum) :
    ExactOpeningStep Parent Proof Challenge ChildClaim where
  parentTrue := fold.parentTrue
  childTrue := fold.proximityStep.childTrue
  honestProof := fold.proximityStep.honestProof
  step := fold.proximityStep.step
  complete parent hTrue challenge :=
    fold.proximityStep.complete parent
      ((fold.parentTrue_iff_proximityTrue parent).mp hTrue) challenge
  falseDescent parent hFalse proof :=
    fold.proximityStep.falseDescent parent
      (fun hProximity => hFalse ((fold.parentTrue_iff_proximityTrue parent).mpr hProximity))
      proof

end NearFarFold
end CanonicalOpening
end ComplexityTheory
