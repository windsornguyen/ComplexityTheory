/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Adaptive
import ComplexityTheory.ProofComplexity.CanonicalOpening.Resources

/-!
# Resource accounting along an adaptive opening transcript

This module adds the opening cost incurred along the actual adaptive strategy
path. Uniform per-query bounds therefore cover honest and adversarial paths.
The profiles remain accounting values: a separate implementation theorem must
show that an executable protocol realizes its declared profile.
-/

namespace ComplexityTheory
namespace AdaptiveOracleStrategy

/-- Count the oracle queries along the path selected by one strategy. -/
def queryCount {Query Answer Proof : Type} :
    {verifier : AdaptiveOracleVerifier Query Answer} →
      AdaptiveOracleStrategy Proof verifier → Nat
  | AdaptiveOracleVerifier.finish _, AdaptiveOracleStrategy.finish _ => 0
  | AdaptiveOracleVerifier.query _ _,
      AdaptiveOracleStrategy.query _ _ continuation => continuation.queryCount + 1

/-- Add the cost of opening every query along one adaptive strategy path. -/
def openingResourceProfile {Query Answer Proof : Type}
    (openingCost : Query → OpeningResourceProfile) :
    {verifier : AdaptiveOracleVerifier Query Answer} →
      AdaptiveOracleStrategy Proof verifier → OpeningResourceProfile
  | AdaptiveOracleVerifier.finish _, AdaptiveOracleStrategy.finish _ =>
      OpeningResourceProfile.zero
  | AdaptiveOracleVerifier.query oracleQuery _,
      AdaptiveOracleStrategy.query _ _ continuation =>
      OpeningResourceProfile.add (openingCost oracleQuery)
        (continuation.openingResourceProfile openingCost)

/--
A uniform per-query budget bounds every adaptive path by its actual query
count times that budget.
-/
theorem openingResourceProfile_within
    {Query Answer Proof : Type}
    (openingCost : Query → OpeningResourceProfile)
    {openingBudget : Nat}
    (hOpening : ∀ query, (openingCost query).Within openingBudget)
    {verifier : AdaptiveOracleVerifier Query Answer}
    (strategy : AdaptiveOracleStrategy Proof verifier) :
    (strategy.openingResourceProfile openingCost).Within
      (strategy.queryCount * openingBudget) := by
  induction strategy with
  | finish =>
      simpa [openingResourceProfile, queryCount] using
        OpeningResourceProfile.zero_within 0
  | query answer proof continuation inductionHypothesis =>
      simpa [openingResourceProfile, queryCount, Nat.add_mul, Nat.add_comm] using
        (hOpening _).add inductionHypothesis

/-- Add an original verifier profile to all openings on one strategy path. -/
def expandedResourceProfile {Query Answer Proof : Type}
    (originalCost : OpeningResourceProfile)
    (openingCost : Query → OpeningResourceProfile)
    {verifier : AdaptiveOracleVerifier Query Answer}
    (strategy : AdaptiveOracleStrategy Proof verifier) : OpeningResourceProfile :=
  OpeningResourceProfile.add originalCost
    (strategy.openingResourceProfile openingCost)

/--
Uniform original and per-query bounds give a pathwise additive bound for the
expanded verifier, including paths induced by noncanonical answers.
-/
theorem expandedResourceProfile_within
    {Query Answer Proof : Type}
    (originalCost : OpeningResourceProfile)
    (openingCost : Query → OpeningResourceProfile)
    {originalBudget openingBudget : Nat}
    (hOriginal : originalCost.Within originalBudget)
    (hOpening : ∀ query, (openingCost query).Within openingBudget)
    {verifier : AdaptiveOracleVerifier Query Answer}
    (strategy : AdaptiveOracleStrategy Proof verifier) :
    (strategy.expandedResourceProfile originalCost openingCost).Within
      (originalBudget + strategy.queryCount * openingBudget) :=
  hOriginal.add (strategy.openingResourceProfile_within openingCost hOpening)

end AdaptiveOracleStrategy
end ComplexityTheory
