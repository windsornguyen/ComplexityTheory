/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.Data.Bool.Basic

/-!
# Exact opening of one canonical oracle answer

This module isolates the semantic composition step needed by canonical
de-oraclization. The original verifier chooses one query before a separate
public opening challenge is sampled. An exact opening accepts an honest proof
for the canonical answer and exposes a rejecting challenge for every proof of
any other answer.

The declarations below do not certify computability, runtime, communication,
or workspace. Those resource obligations must be supplied before an opening
protocol can be used in a complexity-theoretic construction.
-/

namespace ComplexityTheory

/--
An exact public-coin protocol for opening one canonical query answer.

`honestProof` makes completeness constructive. `falseClaimRejected` gives
pointwise soundness: after any proof of a false answer, at least one public
challenge rejects it. This structure alone makes no efficiency claim.
-/
structure ExactOpening (Query Answer Proof Challenge : Type) where
  /-- Return the unique answer that the opening protocol is meant to certify. -/
  canonicalAnswer : Query → Answer
  /-- Construct the proof message for the canonical answer to a query. -/
  honestProof : Query → Proof
  /-- Decide whether one claimed answer, proof, and public challenge are accepted. -/
  accepts : Query → Answer → Proof → Challenge → Bool
  /-- Every public challenge accepts the proof of the canonical answer. -/
  complete : ∀ query challenge,
    accepts query (canonicalAnswer query) (honestProof query) challenge = true
  /-- Every proof of a noncanonical answer has a rejecting public challenge. -/
  falseClaimRejected : ∀ query answer,
    answer ≠ canonicalAnswer query →
      ∀ proof, ∃ challenge, accepts query answer proof challenge = false

/--
A verifier whose original public randomness fixes one oracle query and whose
decision uses the returned answer. The opening challenge is absent from this
type, so it cannot alter the original query or decision rule.
-/
structure OneQueryVerifier (OriginalRandom Query Answer : Type) where
  /-- Select the original verifier's oracle query from its public randomness. -/
  query : OriginalRandom → Query
  /-- Decide whether the original verifier accepts the returned answer. -/
  accepts : OriginalRandom → Answer → Bool

/--
A prover strategy after the original verifier randomness is public. It supplies
one claimed oracle answer and the proof message used to open that answer.
-/
structure OneQueryStrategy (OriginalRandom Answer Proof : Type) where
  /-- Claim an answer after seeing the original verifier randomness. -/
  answer : OriginalRandom → Answer
  /-- Supply the opening proof after seeing the original verifier randomness. -/
  proof : OriginalRandom → Proof

namespace OneQueryVerifier

/-- Run the original verifier on the canonical oracle answer. -/
def acceptsCanonical {OriginalRandom Query Answer Proof Challenge : Type}
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge)
    (randomness : OriginalRandom) : Bool :=
  verifier.accepts randomness (opening.canonicalAnswer (verifier.query randomness))

/--
Run the original verifier and the separate opening check. Both checks must
accept, and the opening challenge cannot affect the original query.
-/
def acceptsExpanded {OriginalRandom Query Answer Proof Challenge : Type}
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge)
    (strategy : OneQueryStrategy OriginalRandom Answer Proof)
    (randomness : OriginalRandom) (challenge : Challenge) : Bool :=
  verifier.accepts randomness (strategy.answer randomness) &&
    opening.accepts (verifier.query randomness) (strategy.answer randomness)
      (strategy.proof randomness) challenge

/-- The original verifier accepts its canonical answer for every random choice. -/
def AcceptsCanonical {OriginalRandom Query Answer Proof Challenge : Type}
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge) : Prop :=
  ∀ randomness, verifier.acceptsCanonical opening randomness = true

/--
Some prover strategy makes the expanded verifier accept every original random
choice and every later opening challenge.
-/
def HasPerfectExpandedStrategy {OriginalRandom Query Answer Proof Challenge : Type}
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge) : Prop :=
  ∃ strategy : OneQueryStrategy OriginalRandom Answer Proof,
    ∀ randomness challenge,
      verifier.acceptsExpanded opening strategy randomness challenge = true

/--
Exact opening preserves perfect acceptance for one query. Informally, a prover
cannot make every challenge accept a false answer, while the constructive
honest proof opens the canonical answer for every challenge.
-/
theorem hasPerfectExpandedStrategy_iff_acceptsCanonical
    {OriginalRandom Query Answer Proof Challenge : Type}
    [Nonempty Challenge]
    (verifier : OneQueryVerifier OriginalRandom Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge) :
    verifier.HasPerfectExpandedStrategy opening ↔ verifier.AcceptsCanonical opening := by
  constructor
  · rintro ⟨strategy, hPerfect⟩ randomness
    have hExpanded := hPerfect randomness
    have hAnswer : strategy.answer randomness =
        opening.canonicalAnswer (verifier.query randomness) := by
      by_contra hFalse
      obtain ⟨challenge, hRejects⟩ := opening.falseClaimRejected
        (verifier.query randomness) (strategy.answer randomness) hFalse
        (strategy.proof randomness)
      have hParts :
          verifier.accepts randomness (strategy.answer randomness) = true ∧
            opening.accepts (verifier.query randomness) (strategy.answer randomness)
              (strategy.proof randomness) challenge = true := by
        simpa [acceptsExpanded] using hExpanded challenge
      have hAccepts := hParts.2
      rw [hRejects] at hAccepts
      contradiction
    obtain ⟨challenge⟩ := ‹Nonempty Challenge›
    have hParts :
        verifier.accepts randomness (strategy.answer randomness) = true ∧
          opening.accepts (verifier.query randomness) (strategy.answer randomness)
            (strategy.proof randomness) challenge = true := by
      simpa [acceptsExpanded] using hExpanded challenge
    have hOriginal := hParts.1
    simpa [acceptsCanonical, hAnswer] using hOriginal
  · intro hCanonical
    let strategy : OneQueryStrategy OriginalRandom Answer Proof :=
      { answer := fun randomness => opening.canonicalAnswer (verifier.query randomness)
        proof := fun randomness => opening.honestProof (verifier.query randomness) }
    refine ⟨strategy, ?_⟩
    intro randomness challenge
    have hOriginal : verifier.accepts randomness
        (opening.canonicalAnswer (verifier.query randomness)) = true := by
      simpa [acceptsCanonical] using hCanonical randomness
    simpa [acceptsExpanded, strategy] using And.intro
      hOriginal (opening.complete (verifier.query randomness) challenge)

end OneQueryVerifier

end ComplexityTheory
