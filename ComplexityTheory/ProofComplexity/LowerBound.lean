/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.Verifier

/-!
# Elementary proof lower bounds

This module records the extensional-collapse regression theorem from the
project's proof audit. A semantic biconditional between tautologicity and the
absence of short proofs does not create self-reference; soundness reduces it to
the conjunction of those two properties.
-/

namespace ComplexityTheory

namespace TautologyProofSystem

/--
`formula` has no proof of length at most `bound`. Equivalently, every proof of
the formula contains strictly more than `bound` bits.
-/
def NoProofAtMost (system : TautologyProofSystem) (bound : Nat)
    (formula : BooleanFormula) : Prop :=
  ∀ proof, system.Proves proof formula → bound < proof.length

/--
For a tautology, excluding proofs through `bound` is exactly a strict lower
bound on its minimum proof cost.
-/
theorem noProofAtMost_iff_proofCost (system : TautologyProofSystem)
    (tautology : Tautology) (bound : Nat) :
    system.NoProofAtMost bound tautology.1 ↔
      bound < system.proofCost tautology := by
  constructor
  · intro hNoProof
    obtain ⟨proof, hLength, hProof⟩ :=
      system.exists_proof_of_length_proofCost tautology
    simpa [hLength] using hNoProof proof hProof
  · intro hCost proof hProof
    exact hCost.trans_le (system.proofCost_le_length tautology hProof)

/--
The audited SRC condition is equivalent to directly asserting both a tautology
and its proof lower bound. This theorem prevents that condition from being
mistaken for an intensional diagonal construction.
-/
theorem src_extensional_collapse (system : TautologyProofSystem)
    (formula : BooleanFormula) (bound : Nat) :
    (formula.IsTautology ↔ system.NoProofAtMost bound formula) ↔
      formula.IsTautology ∧ system.NoProofAtMost bound formula := by
  constructor
  · intro hEquiv
    have hNoProof : system.NoProofAtMost bound formula := by
      intro proof hProof
      exact hEquiv.mp (system.isTautology_of_proves hProof) proof hProof
    exact ⟨hEquiv.mpr hNoProof, hNoProof⟩
  · rintro ⟨hTautology, hNoProof⟩
    exact iff_of_true hTautology hNoProof

/--
The lower-bound conjunct from `src_extensional_collapse` immediately exceeds
`bound` in the system's minimum-proof measure.
-/
theorem src_quantitative_lower_bound (system : TautologyProofSystem)
    (tautology : Tautology) (bound : Nat)
    (hNoProof : system.NoProofAtMost bound tautology.1) :
    bound < system.proofCost tautology :=
  (system.noProofAtMost_iff_proofCost tautology bound).mp hNoProof

end TautologyProofSystem

end ComplexityTheory
