/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.Tautology
import ComplexityTheory.ProofComplexity.Jump

/-!
# The canonical proof system induced by a tautology decider

A correct tautology decider turns each encoded tautology into its own proof and
maps every other string to `true`. This is the structural part of the theorem
that a polynomial-time TAUT decider yields a linearly bounded p-optimal proof
system. No runtime claim is made in this module.
-/

namespace ComplexityTheory

namespace TautologyDecider

/--
Interpret a proof string as a formula code accepted by the decider. Malformed
codes and rejected formulas return the fixed tautology `true`.
-/
def output (decider : TautologyDecider) (proof : BitString) : BooleanFormula :=
  match BooleanFormulaCode.decode? proof with
  | none => .tru
  | some formula => if decider.decide formula then formula else .tru

/-- Every output of the decider-induced map is a tautology. -/
theorem output_isTautology (decider : TautologyDecider) (proof : BitString) :
    (decider.output proof).IsTautology := by
  unfold output
  split
  · simp
  · split
    · exact (decider.correct _).mp (by assumption)
    · simp

/-- A tautology's canonical formula code is returned unchanged. -/
@[simp] theorem output_encode (decider : TautologyDecider) (tautology : Tautology) :
    decider.output (BooleanFormulaCode.encode tautology.1) = tautology.1 := by
  simp [output, (decider.correct tautology.1).mpr tautology.2]

/-- The correct decider induces a sound and complete semantic proof system. -/
def proofSystem (decider : TautologyDecider) : TautologyProofSystem where
  produce := decider.output
  sound := decider.output_isTautology
  complete formula hTautology := by
    let tautology : Tautology := ⟨formula, hTautology⟩
    exact ⟨BooleanFormulaCode.encode formula, decider.output_encode tautology⟩

/--
Every tautology has a proof whose length is exactly its canonical encoded
length, establishing the structural linear bound with constant one.
-/
theorem exists_proof_of_length_encode (decider : TautologyDecider)
    (tautology : Tautology) :
    ∃ proof, proof.length = (BooleanFormulaCode.encode tautology.1).length ∧
      decider.proofSystem.Proves proof tautology.1 := by
  exact ⟨BooleanFormulaCode.encode tautology.1, rfl, decider.output_encode tautology⟩

/--
Translate any source proof by encoding its output formula. Correctness of the
decider makes this an output-preserving translation into the canonical system.
-/
def translationFrom (decider : TautologyDecider) (source : TautologyProofSystem) :
    ProofTranslation source decider.proofSystem where
  translate proof := BooleanFormulaCode.encode (source.produce proof)
  preserves proof := by
    let tautology : Tautology := ⟨source.produce proof, source.sound proof⟩
    exact decider.output_encode tautology

/-- The decider-induced system admits a translation from every semantic proof system. -/
theorem hasTranslationFrom (decider : TautologyDecider)
    (source : TautologyProofSystem) :
    decider.proofSystem.HasTranslationFrom source :=
  ⟨decider.translationFrom source⟩

end TautologyDecider

end ComplexityTheory
