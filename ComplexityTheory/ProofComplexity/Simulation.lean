/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.LowerBound

/-!
# Semantic kernels for proof-system simulation

Krajíček, *The Cook-Reckhow Definition*, 2019, Definition 2.1, p. 5,
distinguishes polynomially length-bounded simulation from polynomial-time
proof translation. This module isolates their semantic kernels. Polynomial
growth and runtime constraints are added separately rather than inferred from
the existence of a Lean function.

Lean already provides identity functions and function composition. The
`ProofTranslation.refl` and `ProofTranslation.comp` declarations below lift
those generic operations into the project-specific translation structure by
supplying the required output-preservation proofs.
-/

namespace ComplexityTheory

/--
A proof translation from `source` to `target` preserves the formula produced
by every source proof. No computability or runtime property is included.
-/
structure ProofTranslation (source target : TautologyProofSystem) where
  /-- Map each source proof string to a target proof string. -/
  translate : BitString → BitString
  /-- Translation preserves the formula proved. -/
  preserves : ∀ proof, target.produce (translate proof) = source.produce proof

namespace ProofTranslation

/--
Lift Lean's identity function to an output-preserving proof translation. This
packages a generic operation; it does not define a new translation algorithm.
-/
def refl (system : TautologyProofSystem) : ProofTranslation system system where
  translate := id
  preserves := by simp

/--
Lift function composition to output-preserving proof translations. The proof
shows that the two component preservation certificates compose.
-/
def comp {first middle last : TautologyProofSystem}
    (later : ProofTranslation middle last)
    (earlier : ProofTranslation first middle) : ProofTranslation first last where
  translate := later.translate ∘ earlier.translate
  preserves proof := by
    rw [Function.comp_apply, later.preserves, earlier.preserves]

end ProofTranslation

namespace TautologyProofSystem

/--
`target` simulates `source` within `overhead` when each source proof has a
target proof of the same formula whose length respects that bound.
-/
def LengthSimulatesWith (target source : TautologyProofSystem)
    (overhead : Nat → Nat) : Prop :=
  ∀ sourceProof, ∃ targetProof,
    target.Proves targetProof (source.produce sourceProof) ∧
      targetProof.length ≤ overhead sourceProof.length

/--
Bounded length simulation is equivalent to bounding the target's minimum proof
cost for every source output. This removes the existential target proof.
-/
theorem lengthSimulatesWith_iff_proofCost
    (target source : TautologyProofSystem) (overhead : Nat → Nat) :
    target.LengthSimulatesWith source overhead ↔
      ∀ sourceProof,
        target.proofCost ⟨source.produce sourceProof, source.sound sourceProof⟩ ≤
          overhead sourceProof.length := by
  constructor
  · intro hSimulation sourceProof
    obtain ⟨targetProof, hProof, hLength⟩ := hSimulation sourceProof
    exact (target.proofCost_le_length
      ⟨source.produce sourceProof, source.sound sourceProof⟩ hProof).trans hLength
  · intro hCost sourceProof
    let tautology : Tautology :=
      ⟨source.produce sourceProof, source.sound sourceProof⟩
    obtain ⟨targetProof, hLength, hProof⟩ :=
      target.exists_proof_of_length_proofCost tautology
    exact ⟨targetProof, hProof, hLength.trans_le (hCost sourceProof)⟩

/-- The identity overhead witnesses bounded length simulation of a system by itself. -/
theorem lengthSimulatesWith_refl (system : TautologyProofSystem) :
    system.LengthSimulatesWith system id := by
  intro proof
  exact ⟨proof, rfl, le_rfl⟩

/-- A translation packages the output-preservation condition used by p-simulation. -/
def HasTranslationFrom (target source : TautologyProofSystem) : Prop :=
  Nonempty (ProofTranslation source target)

/-- Every proof system has an identity translation. -/
theorem hasTranslationFrom_refl (system : TautologyProofSystem) :
    system.HasTranslationFrom system :=
  ⟨ProofTranslation.refl system⟩

/-- Output-preserving translations compose transitively. -/
theorem hasTranslationFrom_trans {first middle last : TautologyProofSystem}
    (hLater : last.HasTranslationFrom middle)
    (hEarlier : middle.HasTranslationFrom first) :
    last.HasTranslationFrom first := by
  obtain ⟨later⟩ := hLater
  obtain ⟨earlier⟩ := hEarlier
  exact ⟨later.comp earlier⟩

end TautologyProofSystem

end ComplexityTheory
