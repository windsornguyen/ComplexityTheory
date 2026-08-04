/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening

/-!
# Exact opening of a well-founded adaptive oracle transcript

This module generalizes exact opening from one or two queries to every
well-founded adaptive oracle verifier. Every realized query path terminates,
although an infinite answer type may give a node infinitely many continuations.
The strategy fixes each original answer and its opening proof before the later
public opening challenges are supplied. Its type therefore excludes
challenge-dependent answers by construction.

The result is semantic: exact opening preserves perfect acceptance. It does
not bound the size of the query tree or any computational resource.
-/

namespace ComplexityTheory

/--
A well-founded oracle verifier. Each returned answer selects the remainder of
the adaptive query tree; a leaf records the verifier's final decision.
-/
inductive AdaptiveOracleVerifier (Query Answer : Type) where
  /-- End the transcript with one Boolean decision. -/
  | finish (accepts : Bool)
  /-- Ask one query, then continue according to its returned answer. -/
  | query (query : Query) (next : Answer → AdaptiveOracleVerifier Query Answer)

/--
A challenge-independent prover strategy for one well-founded oracle verifier. The
continuation is indexed by the claimed answer, so it follows exactly the
original verifier path induced by that answer.
-/
inductive AdaptiveOracleStrategy {Query Answer : Type} (Proof : Type) :
    AdaptiveOracleVerifier Query Answer → Type where
  /-- Supply no message after the verifier has finished. -/
  | finish (accepts : Bool) : AdaptiveOracleStrategy Proof (.finish accepts)
  /-- Commit one answer and proof, then commit the induced continuation. -/
  | query {query next} (answer : Answer) (proof : Proof)
      (continuation : AdaptiveOracleStrategy Proof (next answer)) :
      AdaptiveOracleStrategy Proof (.query query next)

namespace AdaptiveOracleVerifier

/-- Follow an adaptive verifier using the canonical answer to every query. -/
def acceptsCanonical {Query Answer : Type}
    (canonicalAnswer : Query → Answer) :
    AdaptiveOracleVerifier Query Answer → Bool
  | AdaptiveOracleVerifier.finish accepts => accepts
  | AdaptiveOracleVerifier.query oracleQuery next =>
      acceptsCanonical canonicalAnswer (next (canonicalAnswer oracleQuery))

end AdaptiveOracleVerifier

namespace AdaptiveOracleStrategy

/--
Check every claimed answer along one strategy. Challenge `n` checks the
`n`th query, after the complete original query path has already been fixed.
-/
def acceptsExpanded {Query Answer Proof Challenge : Type}
    (opening : ExactOpening Query Answer Proof Challenge) :
    {verifier : AdaptiveOracleVerifier Query Answer} →
      AdaptiveOracleStrategy Proof verifier → (Nat → Challenge) → Bool
  | AdaptiveOracleVerifier.finish _, AdaptiveOracleStrategy.finish accepts, _ => accepts
  | AdaptiveOracleVerifier.query oracleQuery _,
      AdaptiveOracleStrategy.query answer proof continuation, challenges =>
      opening.accepts oracleQuery answer proof (challenges 0) &&
        continuation.acceptsExpanded opening (fun index => challenges (index + 1))

end AdaptiveOracleStrategy

namespace AdaptiveOracleVerifier

/--
Some challenge-independent strategy makes every sequence of later opening
challenges accept.
-/
def HasPerfectExpandedStrategy {Query Answer Proof Challenge : Type}
    (verifier : AdaptiveOracleVerifier Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge) : Prop :=
  ∃ strategy : AdaptiveOracleStrategy Proof verifier,
    ∀ challenges, strategy.acceptsExpanded opening challenges = true

/-- Add one first challenge in front of an infinite challenge sequence. -/
private def prependChallenge {Challenge : Type}
    (first : Challenge) (rest : Nat → Challenge) : Nat → Challenge
  | 0 => first
  | index + 1 => rest index

/--
Exact opening preserves perfect acceptance for every well-founded adaptive
query verifier. Informally, perfect expanded acceptance forces each committed
answer to be canonical; completeness supplies the converse honest strategy.
-/
theorem hasPerfectExpandedStrategy_iff_acceptsCanonical
    {Query Answer Proof Challenge : Type} [Nonempty Challenge]
    (verifier : AdaptiveOracleVerifier Query Answer)
    (opening : ExactOpening Query Answer Proof Challenge) :
    verifier.HasPerfectExpandedStrategy opening ↔
      verifier.acceptsCanonical opening.canonicalAnswer = true := by
  induction verifier with
  | finish accepts =>
      constructor
      · rintro ⟨strategy, hPerfect⟩
        cases strategy
        obtain ⟨challenge⟩ := ‹Nonempty Challenge›
        simpa [AdaptiveOracleStrategy.acceptsExpanded, acceptsCanonical] using
          hPerfect (fun _ => challenge)
      · intro hCanonical
        refine ⟨.finish accepts, ?_⟩
        intro challenges
        simpa [AdaptiveOracleStrategy.acceptsExpanded, acceptsCanonical] using hCanonical
  | query query next inductionHypothesis =>
      constructor
      · rintro ⟨strategy, hPerfect⟩
        cases strategy with
        | query answer proof continuation =>
            have hAnswer : answer = opening.canonicalAnswer query := by
              by_contra hFalse
              obtain ⟨rejectingChallenge, hRejects⟩ :=
                opening.falseClaimRejected query answer hFalse proof
              obtain ⟨laterChallenge⟩ := ‹Nonempty Challenge›
              have hAll := hPerfect
                (prependChallenge rejectingChallenge (fun _ => laterChallenge))
              simp [AdaptiveOracleStrategy.acceptsExpanded, prependChallenge,
                hRejects] at hAll
            have hContinuation :
                (next answer).HasPerfectExpandedStrategy opening := by
              refine ⟨continuation, ?_⟩
              intro laterChallenges
              obtain ⟨firstChallenge⟩ := ‹Nonempty Challenge›
              have hParts :
                  opening.accepts query answer proof firstChallenge = true ∧
                    continuation.acceptsExpanded opening laterChallenges = true := by
                simpa [AdaptiveOracleStrategy.acceptsExpanded, prependChallenge] using
                  hPerfect (prependChallenge firstChallenge laterChallenges)
              exact hParts.2
            have hCanonicalContinuation :=
              (inductionHypothesis answer).mp hContinuation
            simpa [acceptsCanonical, hAnswer] using hCanonicalContinuation
      · intro hCanonical
        have hCanonicalContinuation :
            (next (opening.canonicalAnswer query)).acceptsCanonical
                opening.canonicalAnswer = true := by
          simpa [acceptsCanonical] using hCanonical
        obtain ⟨continuation, hContinuation⟩ :=
          (inductionHypothesis (opening.canonicalAnswer query)).mpr
            hCanonicalContinuation
        refine ⟨.query (opening.canonicalAnswer query) (opening.honestProof query)
          continuation, ?_⟩
        intro challenges
        have hLater := hContinuation (fun index => challenges (index + 1))
        simp [AdaptiveOracleStrategy.acceptsExpanded, opening.complete, hLater]

end AdaptiveOracleVerifier

end ComplexityTheory
