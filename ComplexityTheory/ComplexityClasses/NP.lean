/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ComplexityClasses.P

/-!
# Nondeterministic polynomial time

Arora and Barak, *Computational Complexity: A Modern Approach*, January 2007
web draft, Definition 2.1, p. 40 (PDF p. 56), define `NP` by a polynomial-time
verifier and a polynomial-length binary certificate.

Definition 2.1 writes the certificate length as exactly `p(|x|)`. This module
uses the conventional at-most bound `c * (|x| + 1)^d`. The verifier receives a
typed instance-witness pair whose complete canonical self-delimiting encoding
determines the machine clock. No nondeterministic-machine equivalence is
assumed here.
-/

namespace ComplexityTheory

/-- A binary verifier relation takes an instance and a proposed witness. -/
abbrev BooleanRelation := BitString → BitString → Bool

namespace BooleanRelation

/-- Evaluate a binary relation on one typed instance-witness pair. -/
def onPair (relation : BooleanRelation) : BitString × BitString → Bool :=
  fun pair => relation pair.1 pair.2

/-- Pair evaluation exposes the original relation without an encoding convention. -/
@[simp] theorem onPair_apply (relation : BooleanRelation) (input witness : BitString) :
    relation.onPair (input, witness) = relation input witness :=
  rfl

end BooleanRelation

/--
A conventional polynomial-time witness verifier for one binary language.

The verifier accepts exactly the yes-instances that have a witness within the
displayed monomial bound. Its computation certificate charges the complete
self-delimiting code of the typed instance-witness pair.
-/
structure PolynomialWitnessVerifier (problem : DecisionProblem) where
  /-- Decide whether one witness certifies one input. -/
  accepts : BooleanRelation
  /-- Constant multiplier in the witness-length bound. -/
  witnessCoefficient : Nat
  /-- Degree of the witness-length bound. -/
  witnessDegree : Nat
  /-- Every accepted witness certifies a language member. -/
  sound : ∀ input witness, accepts input witness = true → input ∈ problem
  /-- Every language member has an accepted polynomially bounded witness. -/
  complete : ∀ input, input ∈ problem →
    ∃ witness,
      witness.length ≤ witnessCoefficient * (input.length + 1) ^ witnessDegree ∧
        accepts input witness = true
  /-- A finite multitape machine evaluates the complete encoded verifier in polynomial time. -/
  computesInPolyTime :
    PolyTimeComputable BitString.pairEncoding.encode
      Computability.encodeBool accepts.onPair

namespace DecisionProblem

/-- A binary decision problem lies in `NP` when it has a polynomial witness verifier. -/
def IsInNP (problem : DecisionProblem) : Prop :=
  Nonempty (PolynomialWitnessVerifier problem)

end DecisionProblem

namespace ComplexityClass

/-- `NP` is the set of binary languages with polynomially bounded, polynomial-time witnesses. -/
def NP : Set DecisionProblem :=
  {problem | problem.IsInNP}

/-- Membership in `NP` is exactly the existence of a polynomial witness verifier. -/
theorem mem_NP_iff (problem : DecisionProblem) :
    problem ∈ NP ↔ problem.IsInNP :=
  Iff.rfl

end ComplexityClass
end ComplexityTheory
