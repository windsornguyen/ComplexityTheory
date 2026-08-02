/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.FormulaPadding

/-!
# Semantic tautology proof systems

Cook and Reckhow, *The Relative Efficiency of Propositional Proof Systems*,
Journal of Symbolic Logic 44(1), 1979, Definition 1.3, p. 37 (PDF p. 3), define
a proof system as a polynomial-time computable surjection onto a language.

This module isolates the surjection and proof-length layer. It deliberately
does not claim polynomial-time computability; a later machine model will add
that independent requirement to obtain a Cook-Reckhow system.
-/

namespace ComplexityTheory

/-- A tautology bundled with the semantic proof that every assignment satisfies it. -/
abbrev Tautology := { formula : BooleanFormula // formula.IsTautology }

/--
The semantic core of a proof system for `TAUT`: every proof string produces a
tautology, and every tautology is produced by at least one proof string.
-/
structure TautologyProofSystem where
  /-- Return the formula named by a proof string. -/
  produce : BitString → BooleanFormula
  /-- Every output formula is a tautology. -/
  sound : ∀ proof, (produce proof).IsTautology
  /-- Every tautology occurs as an output. -/
  complete : ∀ formula, formula.IsTautology → ∃ proof, produce proof = formula

namespace TautologyProofSystem

/-- A string is a proof of `formula` when the proof map returns that formula. -/
def Proves (system : TautologyProofSystem) (proof : BitString)
    (formula : BooleanFormula) : Prop :=
  system.produce proof = formula

/-- Every accepted proof proves a tautology, restating system soundness relationally. -/
theorem isTautology_of_proves (system : TautologyProofSystem)
    {proof : BitString} {formula : BooleanFormula} (hProof : system.Proves proof formula) :
    formula.IsTautology := by
  rw [← hProof]
  exact system.sound proof

/-- Completeness supplies at least one proof of each bundled tautology. -/
theorem exists_proof (system : TautologyProofSystem) (tautology : Tautology) :
    ∃ proof, system.Proves proof tautology.1 :=
  system.complete tautology.1 tautology.2

/-- Every tautology has some proof length at which a proof exists. -/
theorem exists_proof_length (system : TautologyProofSystem) (tautology : Tautology) :
    ∃ length, ∃ proof, proof.length = length ∧ system.Proves proof tautology.1 := by
  obtain ⟨proof, hProof⟩ := system.exists_proof tautology
  exact ⟨proof.length, proof, rfl, hProof⟩

/--
The minimum bit length of a proof of a tautology. This is noncomputable because
the semantic structure does not yet provide a proof-search algorithm.
-/
noncomputable def proofCost (system : TautologyProofSystem) (tautology : Tautology) : Nat :=
  by
    classical
    exact Nat.find (system.exists_proof_length tautology)

/-- A proof attaining `proofCost` exists for every tautology. -/
theorem exists_proof_of_length_proofCost
    (system : TautologyProofSystem) (tautology : Tautology) :
    ∃ proof, proof.length = system.proofCost tautology ∧
      system.Proves proof tautology.1 := by
  classical
  exact Nat.find_spec (system.exists_proof_length tautology)

/-- No proof of a tautology is shorter than its declared minimum proof cost. -/
theorem proofCost_le_length (system : TautologyProofSystem) (tautology : Tautology)
    {proof : BitString} (hProof : system.Proves proof tautology.1) :
    system.proofCost tautology ≤ proof.length := by
  classical
  exact Nat.find_min' (system.exists_proof_length tautology) ⟨proof, rfl, hProof⟩

end TautologyProofSystem

end ComplexityTheory
