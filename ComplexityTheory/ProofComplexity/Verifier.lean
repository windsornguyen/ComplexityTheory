/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.ProofSystem

/-!
# Boolean tautology verifiers and tagged normalization

Cook and Reckhow, *The Relative Efficiency of Propositional Proof Systems*,
Journal of Symbolic Logic 44(1), 1979, Definition 1.3, p. 37 (PDF p. 3), use
total proof maps. Their discussion on p. 39 (PDF p. 5) maps malformed proofs to
a fixed tautology. This module gives a Boolean-valued relational view and that
normalization, without claiming code generation or a polynomial runtime.
-/

namespace ComplexityTheory

namespace BooleanFormula

/-- The constant-true formula is the canonical output for rejected proof strings. -/
@[simp] theorem isTautology_tru : BooleanFormula.tru.IsTautology := by
  simp [IsTautology, Satisfies, eval]

end BooleanFormula

/--
A Boolean-valued proof verifier with semantic soundness and completeness. The
type records acceptance decisions but does not itself certify computability.
-/
structure TautologyVerifier where
  /-- Decide whether `proof` is accepted as a proof of `formula`. -/
  accepts : BitString → BooleanFormula → Bool
  /-- Every accepted formula is a tautology. -/
  sound : ∀ proof formula, accepts proof formula = true → formula.IsTautology
  /-- Every tautology has an accepted proof. -/
  complete : ∀ formula, formula.IsTautology → ∃ proof, accepts proof formula = true

namespace TautologyVerifier

/-- Pair a proof with the canonical binary encoding of its claimed formula. -/
def tag (proof : BitString) (formula : BooleanFormula) : BitString :=
  BitString.pair proof (BooleanFormulaCode.encode formula)

/--
Interpret a tagged proof as a total proof-map output. Malformed tags, malformed
formula codes, and rejected claims all return the fixed tautology `true`.
-/
def taggedOutput (verifier : TautologyVerifier) (input : BitString) : BooleanFormula :=
  match BitString.unpair? input with
  | none => .tru
  | some (proof, formulaBits) =>
      match BooleanFormulaCode.decode? formulaBits with
      | none => .tru
      | some formula => if verifier.accepts proof formula then formula else .tru

/-- Every output of tagged normalization is a tautology. -/
theorem taggedOutput_isTautology (verifier : TautologyVerifier) (input : BitString) :
    (verifier.taggedOutput input).IsTautology := by
  unfold taggedOutput
  split
  · simp
  · split
    · simp
    · split
      · exact verifier.sound _ _ (by assumption)
      · simp

/-- An accepted proof-formula pair survives tagged normalization exactly. -/
@[simp] theorem taggedOutput_tag_of_accepts (verifier : TautologyVerifier)
    (proof : BitString) (formula : BooleanFormula)
    (hAccepts : verifier.accepts proof formula = true) :
    verifier.taggedOutput (tag proof formula) = formula := by
  simp [taggedOutput, tag, hAccepts]

/-- Convert a Boolean verifier into its total tagged proof-map representation. -/
def toProofSystem (verifier : TautologyVerifier) : TautologyProofSystem where
  produce := verifier.taggedOutput
  sound := verifier.taggedOutput_isTautology
  complete formula hTautology := by
    obtain ⟨proof, hAccepts⟩ := verifier.complete formula hTautology
    exact ⟨tag proof formula, verifier.taggedOutput_tag_of_accepts proof formula hAccepts⟩

end TautologyVerifier

namespace TautologyProofSystem

/-- View equality with a functional proof-map output as a Boolean verifier. -/
def toVerifier (system : TautologyProofSystem) : TautologyVerifier where
  accepts proof formula := decide (system.produce proof = formula)
  sound proof formula hAccepts := by
    apply system.isTautology_of_proves
    change system.produce proof = formula
    exact of_decide_eq_true hAccepts
  complete formula hTautology := by
    obtain ⟨proof, hProof⟩ := system.complete formula hTautology
    exact ⟨proof, by simp [hProof]⟩

/-- The equality verifier accepts exactly the system's relational proofs. -/
@[simp] theorem toVerifier_accepts_iff (system : TautologyProofSystem)
    (proof : BitString) (formula : BooleanFormula) :
    system.toVerifier.accepts proof formula = true ↔ system.Proves proof formula := by
  simp [toVerifier, Proves]

/-- Tagged normalization makes every proof carry its claimed output formula. -/
def normalized (system : TautologyProofSystem) : TautologyProofSystem :=
  system.toVerifier.toProofSystem

/-- A source proof translates to its tagged normalized proof without changing output. -/
@[simp] theorem normalized_produce_tag (system : TautologyProofSystem) (proof : BitString) :
    system.normalized.produce
        (TautologyVerifier.tag proof (system.produce proof)) =
      system.produce proof := by
  apply TautologyVerifier.taggedOutput_tag_of_accepts
  simp [toVerifier]

end TautologyProofSystem

end ComplexityTheory
