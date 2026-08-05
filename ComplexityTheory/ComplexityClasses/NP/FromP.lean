/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ComplexityClasses.NP
import ComplexityTheory.Computability.PairFirstComposition.Correctness

/-!
# Polynomial time is contained in nondeterministic polynomial time

Arora and Barak, *Computational Complexity: A Modern Approach*, January 2007
web draft, Claim 2.3, p. 41 (PDF p. 57), prove `P ⊆ NP` by using an empty
certificate and letting the verifier run the original decider.

The verifier ignores an empty certificate and runs the original decider. The
pair-first wrapper proves that the complete encoded instance-certificate pair
is parsed and charged before the decider runs, making the inclusion
unconditional in the library's concrete multitape-machine model.
-/

namespace ComplexityTheory

namespace PolyTimeDecider

/-- Ignore the witness and run an existing decider on the instance. -/
def ignoresWitness {problem : DecisionProblem}
    (decider : PolyTimeDecider problem) : BooleanRelation :=
  fun input _ => decider.decide input

/-- A pair-input certificate turns an existing decider into an `NP` verifier. -/
def toPolynomialWitnessVerifier {problem : DecisionProblem}
    (decider : PolyTimeDecider problem)
    (computesOnPairs : PolyTimeComputable BitString.pairEncoding.encode
      Computability.encodeBool decider.ignoresWitness.onPair) :
    PolynomialWitnessVerifier problem where
  accepts := decider.ignoresWitness
  witnessCoefficient := 0
  witnessDegree := 0
  sound input _ hAccepts := (decider.correct input).1 hAccepts
  complete input hMember :=
    ⟨[], by simp, (decider.correct input).2 hMember⟩
  computesInPolyTime := computesOnPairs

end PolyTimeDecider

/--
Every certified Boolean function can run after the certified first projection.
This is the exact specialization of generic polynomial-time TM2 composition
needed for `P ⊆ NP`.
-/
def PairFirstCompositionPrinciple : Prop :=
  ∀ {function : BooleanFunction},
    PolyTimeComputable id Computability.encodeBool function →
      Nonempty (PolyTimeComputable BitString.pairEncoding.encode
        Computability.encodeBool (fun pair => function pair.1))

/-- The certified wrapper discharges pair-first composition for every source machine. -/
theorem pairFirstCompositionPrinciple : PairFirstCompositionPrinciple := by
  intro function certificate
  exact ⟨PolyTimeComputable.PairFirstComposition.computesInPolyTime certificate⟩

namespace ComplexityClass

/-- The explicit pair-first composition principle implies the standard inclusion. -/
theorem p_subset_np_of_pairFirstCompositionPrinciple
    (hComposition : PairFirstCompositionPrinciple) : P ⊆ NP := by
  intro problem hProblemInP
  obtain ⟨decider⟩ := hProblemInP
  obtain ⟨computesOnPairs⟩ := hComposition decider.computesInPolyTime
  have verifierCertificate : PolyTimeComputable BitString.pairEncoding.encode
      Computability.encodeBool decider.ignoresWitness.onPair := by
    change PolyTimeComputable BitString.pairEncoding.encode
      Computability.encodeBool (fun pair => decider.decide pair.1)
    exact computesOnPairs
  exact ⟨decider.toPolynomialWitnessVerifier verifierCertificate⟩

/-- Every polynomial-time binary decision problem has an empty-witness `NP` verifier. -/
theorem p_subset_np : P ⊆ NP :=
  p_subset_np_of_pairFirstCompositionPrinciple pairFirstCompositionPrinciple

end ComplexityClass
end ComplexityTheory
