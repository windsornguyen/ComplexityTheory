/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening

/-!
# Exact opening of two adaptive canonical oracle answers

This module tests semantic composition across the first adaptive boundary. The
second original query may depend on the first claimed answer, but neither answer
may depend on either later opening challenge. The types therefore model batched
opening after the original two-query transcript has been fixed.
-/

namespace ComplexityTheory

/--
A verifier making two original oracle queries, where the second query may
depend on the first returned answer.
-/
structure TwoQueryVerifier
    (OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type) where
  /-- Select the first query from the original verifier randomness. -/
  firstQuery : OriginalRandom → FirstQuery
  /-- Select the second query after receiving the first answer. -/
  secondQuery : OriginalRandom → FirstAnswer → SecondQuery
  /-- Decide whether the original verifier accepts both returned answers. -/
  accepts : OriginalRandom → FirstAnswer → SecondAnswer → Bool

/--
A two-query prover strategy that is independent of the later opening
challenges. The second answer and proof may depend on the first claimed answer,
as permitted by the original adaptive transcript.
-/
structure TwoQueryStrategy
    (OriginalRandom FirstAnswer SecondAnswer FirstProof SecondProof : Type) where
  /-- Claim the first answer after seeing the original verifier randomness. -/
  firstAnswer : OriginalRandom → FirstAnswer
  /-- Claim the second answer after fixing the first claimed answer. -/
  secondAnswer : OriginalRandom → FirstAnswer → SecondAnswer
  /-- Supply the proof opening the first claimed answer. -/
  firstProof : OriginalRandom → FirstProof
  /-- Supply the proof opening the second claimed answer. -/
  secondProof : OriginalRandom → FirstAnswer → SecondProof

namespace TwoQueryVerifier

/-- Run the original verifier on both canonical oracle answers. -/
def acceptsCanonical
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    {FirstProof FirstChallenge SecondProof SecondChallenge : Type}
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (firstOpening : ExactOpening
      FirstQuery FirstAnswer FirstProof FirstChallenge)
    (secondOpening : ExactOpening
      SecondQuery SecondAnswer SecondProof SecondChallenge)
    (randomness : OriginalRandom) : Bool :=
  let firstAnswer := firstOpening.canonicalAnswer (verifier.firstQuery randomness)
  let secondQuery := verifier.secondQuery randomness firstAnswer
  verifier.accepts randomness firstAnswer (secondOpening.canonicalAnswer secondQuery)

/--
Run the original verifier and both batched opening checks. The original query
path is fixed before either opening challenge is supplied.
-/
def acceptsExpanded
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    {FirstProof FirstChallenge SecondProof SecondChallenge : Type}
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (firstOpening : ExactOpening
      FirstQuery FirstAnswer FirstProof FirstChallenge)
    (secondOpening : ExactOpening
      SecondQuery SecondAnswer SecondProof SecondChallenge)
    (strategy : TwoQueryStrategy
      OriginalRandom FirstAnswer SecondAnswer FirstProof SecondProof)
    (randomness : OriginalRandom)
    (firstChallenge : FirstChallenge) (secondChallenge : SecondChallenge) : Bool :=
  let firstAnswer := strategy.firstAnswer randomness
  let secondAnswer := strategy.secondAnswer randomness firstAnswer
  verifier.accepts randomness firstAnswer secondAnswer &&
    (firstOpening.accepts (verifier.firstQuery randomness) firstAnswer
        (strategy.firstProof randomness) firstChallenge &&
      secondOpening.accepts (verifier.secondQuery randomness firstAnswer) secondAnswer
        (strategy.secondProof randomness firstAnswer) secondChallenge)

/-- The original verifier accepts both canonical answers for every random choice. -/
def AcceptsCanonical
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    {FirstProof FirstChallenge SecondProof SecondChallenge : Type}
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (firstOpening : ExactOpening
      FirstQuery FirstAnswer FirstProof FirstChallenge)
    (secondOpening : ExactOpening
      SecondQuery SecondAnswer SecondProof SecondChallenge) : Prop :=
  ∀ randomness, verifier.acceptsCanonical firstOpening secondOpening randomness = true

/--
Some challenge-independent strategy makes the expanded verifier accept every
original random choice and every pair of later opening challenges.
-/
def HasPerfectExpandedStrategy
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    {FirstProof FirstChallenge SecondProof SecondChallenge : Type}
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (firstOpening : ExactOpening
      FirstQuery FirstAnswer FirstProof FirstChallenge)
    (secondOpening : ExactOpening
      SecondQuery SecondAnswer SecondProof SecondChallenge) : Prop :=
  ∃ strategy : TwoQueryStrategy
      OriginalRandom FirstAnswer SecondAnswer FirstProof SecondProof,
    ∀ randomness firstChallenge secondChallenge,
      verifier.acceptsExpanded firstOpening secondOpening strategy randomness
        firstChallenge secondChallenge = true

/--
Exact batched opening preserves perfect acceptance across two adaptive queries.
The proof first forces the initial answer to be canonical, then forces the
answer to the resulting second query to be canonical.
-/
theorem hasPerfectExpandedStrategy_iff_acceptsCanonical
    {OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer : Type}
    {FirstProof FirstChallenge SecondProof SecondChallenge : Type}
    [Nonempty FirstChallenge] [Nonempty SecondChallenge]
    (verifier : TwoQueryVerifier
      OriginalRandom FirstQuery FirstAnswer SecondQuery SecondAnswer)
    (firstOpening : ExactOpening
      FirstQuery FirstAnswer FirstProof FirstChallenge)
    (secondOpening : ExactOpening
      SecondQuery SecondAnswer SecondProof SecondChallenge) :
    verifier.HasPerfectExpandedStrategy firstOpening secondOpening ↔
      verifier.AcceptsCanonical firstOpening secondOpening := by
  constructor
  · rintro ⟨strategy, hPerfect⟩ randomness
    have hFirst : strategy.firstAnswer randomness =
        firstOpening.canonicalAnswer (verifier.firstQuery randomness) := by
      by_contra hFalse
      obtain ⟨firstChallenge, hRejects⟩ := firstOpening.falseClaimRejected
        (verifier.firstQuery randomness) (strategy.firstAnswer randomness) hFalse
        (strategy.firstProof randomness)
      obtain ⟨secondChallenge⟩ := ‹Nonempty SecondChallenge›
      have hAll := hPerfect randomness firstChallenge secondChallenge
      simp [acceptsExpanded, hRejects] at hAll
    have hSecond : strategy.secondAnswer randomness (strategy.firstAnswer randomness) =
        secondOpening.canonicalAnswer
          (verifier.secondQuery randomness (strategy.firstAnswer randomness)) := by
      by_contra hFalse
      obtain ⟨secondChallenge, hRejects⟩ := secondOpening.falseClaimRejected
        (verifier.secondQuery randomness (strategy.firstAnswer randomness))
        (strategy.secondAnswer randomness (strategy.firstAnswer randomness)) hFalse
        (strategy.secondProof randomness (strategy.firstAnswer randomness))
      obtain ⟨firstChallenge⟩ := ‹Nonempty FirstChallenge›
      have hAll := hPerfect randomness firstChallenge secondChallenge
      simp [acceptsExpanded, hRejects] at hAll
    obtain ⟨firstChallenge⟩ := ‹Nonempty FirstChallenge›
    obtain ⟨secondChallenge⟩ := ‹Nonempty SecondChallenge›
    have hParts :
        verifier.accepts randomness (strategy.firstAnswer randomness)
            (strategy.secondAnswer randomness (strategy.firstAnswer randomness)) = true ∧
          firstOpening.accepts (verifier.firstQuery randomness)
              (strategy.firstAnswer randomness) (strategy.firstProof randomness)
              firstChallenge = true ∧
            secondOpening.accepts
              (verifier.secondQuery randomness (strategy.firstAnswer randomness))
              (strategy.secondAnswer randomness (strategy.firstAnswer randomness))
              (strategy.secondProof randomness (strategy.firstAnswer randomness))
              secondChallenge = true := by
      simpa [acceptsExpanded] using hPerfect randomness firstChallenge secondChallenge
    have hSecondCanonical :
        strategy.secondAnswer randomness
            (firstOpening.canonicalAnswer (verifier.firstQuery randomness)) =
          secondOpening.canonicalAnswer (verifier.secondQuery randomness
            (firstOpening.canonicalAnswer (verifier.firstQuery randomness))) := by
      simpa [hFirst] using hSecond
    simpa [acceptsCanonical, hFirst, hSecondCanonical] using hParts.1
  · intro hCanonical
    let strategy : TwoQueryStrategy
        OriginalRandom FirstAnswer SecondAnswer FirstProof SecondProof :=
      { firstAnswer := fun randomness =>
          firstOpening.canonicalAnswer (verifier.firstQuery randomness)
        secondAnswer := fun randomness firstAnswer =>
          secondOpening.canonicalAnswer (verifier.secondQuery randomness firstAnswer)
        firstProof := fun randomness =>
          firstOpening.honestProof (verifier.firstQuery randomness)
        secondProof := fun randomness firstAnswer =>
          secondOpening.honestProof (verifier.secondQuery randomness firstAnswer) }
    refine ⟨strategy, ?_⟩
    intro randomness firstChallenge secondChallenge
    have hOriginal : verifier.accepts
        randomness (strategy.firstAnswer randomness)
          (strategy.secondAnswer randomness (strategy.firstAnswer randomness)) = true := by
      simpa [acceptsCanonical, strategy] using hCanonical randomness
    simp [acceptsExpanded, strategy, hOriginal, firstOpening.complete,
      secondOpening.complete]

end TwoQueryVerifier

end ComplexityTheory
