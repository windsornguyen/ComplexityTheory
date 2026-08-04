/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.TwoQuery

/-!
# Resource accounting for canonical openings

This module fixes the resource categories that an opening theorem must charge
and proves their exact additive composition. A profile is only an accounting
value; it does not certify the operational cost of a Lean function.
-/

namespace ComplexityTheory

/-- A resource category charged by one canonical-opening protocol. -/
inductive OpeningResource where
  /-- Number of public-coin interaction rounds. -/
  | rounds
  /-- Bits sent by the prover, including the claimed answer. -/
  | proverMessageBits
  /-- Bits sampled or sent as public verifier challenges. -/
  | challengeBits
  /-- Verifier execution steps, including adaptive query computation. -/
  | verifierTime
  /-- Maximum verifier workspace in bits. -/
  | verifierWorkspaceBits
  /-- Steps used to compile the original verifier into the expanded game. -/
  | compilerTime
  /-- Steps used by public preprocessing before interaction. -/
  | preprocessingTime
  /-- Steps or queries used to access the original input. -/
  | inputAccess
  /-- Bits in inherited machine, field, code, and protocol descriptions. -/
  | inheritedDescriptionBits
  deriving DecidableEq

/-- Assign a natural-number cost to every opening resource category. -/
abbrev OpeningResourceProfile := OpeningResource → Nat

namespace OpeningResourceProfile

/-- The profile that charges no resources. -/
def zero : OpeningResourceProfile := fun _ => 0

/-- Add two resource profiles category by category. -/
def add (first second : OpeningResourceProfile) : OpeningResourceProfile :=
  fun resource => first resource + second resource

/-- Every category in `profile` is at most one common budget. -/
def Within (profile : OpeningResourceProfile) (budget : Nat) : Prop :=
  ∀ resource, profile resource ≤ budget

/-- The zero profile fits every natural-number budget. -/
theorem zero_within (budget : Nat) : zero.Within budget := by
  intro resource
  exact Nat.zero_le budget

/-- Adding profiles that fit separate budgets fits the sum of those budgets. -/
theorem Within.add {first second : OpeningResourceProfile}
    {firstBudget secondBudget : Nat}
    (hFirst : first.Within firstBudget) (hSecond : second.Within secondBudget) :
    (add first second).Within (firstBudget + secondBudget) := by
  intro resource
  exact Nat.add_le_add (hFirst resource) (hSecond resource)

end OpeningResourceProfile

namespace OneQueryVerifier

/--
Add the original verifier cost and the cost of opening its selected query.
`originalCost` must already charge query generation and answer handling.
-/
def expandedResourceProfile
    {OriginalRandom Query Answer : Type}
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (originalCost : OriginalRandom → OpeningResourceProfile)
    (openingCost : Query → OpeningResourceProfile)
    (randomness : OriginalRandom) : OpeningResourceProfile :=
  OpeningResourceProfile.add (originalCost randomness)
    (openingCost (verifier.query randomness))

/--
A uniform bound for the original verifier and every possible opening query
gives their additive bound for every expanded execution.
-/
theorem expandedResourceProfile_within
    {OriginalRandom Query Answer : Type}
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (originalCost : OriginalRandom → OpeningResourceProfile)
    (openingCost : Query → OpeningResourceProfile)
    {originalBudget openingBudget : Nat}
    (hOriginal : ∀ randomness, (originalCost randomness).Within originalBudget)
    (hOpening : ∀ query, (openingCost query).Within openingBudget) :
    ∀ randomness,
      (verifier.expandedResourceProfile originalCost openingCost randomness).Within
        (originalBudget + openingBudget) := by
  intro randomness
  exact (hOriginal randomness).add (hOpening (verifier.query randomness))

end OneQueryVerifier

namespace TwoQueryVerifier

/--
Add the original cost and both opening costs along an actual adaptive query
path. The first answer is explicit so the profile also covers cheating paths.
-/
def expandedResourceProfile
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (originalCost : OriginalRandom → OpeningResourceProfile)
    (firstOpeningCost : FirstQuery → OpeningResourceProfile)
    (secondOpeningCost : SecondQuery → OpeningResourceProfile)
    (randomness : OriginalRandom) (firstAnswer : FirstAnswer) : OpeningResourceProfile :=
  OpeningResourceProfile.add (originalCost randomness) <|
    OpeningResourceProfile.add (firstOpeningCost (verifier.firstQuery randomness))
      (secondOpeningCost (verifier.secondQuery randomness firstAnswer))

/--
Uniform bounds over every query give an additive bound for every adaptive
two-query execution, including paths induced by a noncanonical first answer.
-/
theorem expandedResourceProfile_within
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (originalCost : OriginalRandom → OpeningResourceProfile)
    (firstOpeningCost : FirstQuery → OpeningResourceProfile)
    (secondOpeningCost : SecondQuery → OpeningResourceProfile)
    {originalBudget firstBudget secondBudget : Nat}
    (hOriginal : ∀ randomness, (originalCost randomness).Within originalBudget)
    (hFirst : ∀ query, (firstOpeningCost query).Within firstBudget)
    (hSecond : ∀ query, (secondOpeningCost query).Within secondBudget) :
    ∀ randomness firstAnswer,
      (verifier.expandedResourceProfile originalCost firstOpeningCost secondOpeningCost
        randomness firstAnswer).Within
          (originalBudget + (firstBudget + secondBudget)) := by
  intro randomness firstAnswer
  exact (hOriginal randomness).add <|
    (hFirst (verifier.firstQuery randomness)).add
      (hSecond (verifier.secondQuery randomness firstAnswer))

end TwoQueryVerifier

end ComplexityTheory
