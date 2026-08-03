/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.ConditionalIdentity.Output

/-!
# Correctness of conditional identity

This module composes the verified copying, source-simulation, restoration, and
output phases. The resulting certificate computes the original input exactly
when the source decider accepts and the declared rejection output otherwise.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Mathlib.Computability.StateTransition`, structure
`StateTransition.EvalsToInTime` and definition `EvalsToInTime.trans`, supplies
the bounded-evaluation relation and composition operation used below.
-/

namespace ComplexityTheory

namespace PolyTimeComputable

namespace ConditionalIdentity

variable {predicate : BitString → Bool}

/-- Identify the wrapper's output-stack alphabet with external Boolean bits. -/
def outputAlphabet
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) :
    (machine certificate rejectionOutput).Γ
      (machine certificate rejectionOutput).k₁ ≃ Bool :=
  Equiv.refl Bool

/--
The inverse output-alphabet equivalence encodes each external Boolean bit
unchanged, connecting external bits to internal machine stack symbols.
-/
@[simp]
theorem outputAlphabet_invFun
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (bit : Bool) :
    (outputAlphabet certificate rejectionOutput).invFun bit = bit := rfl

/--
The inverse output-alphabet equivalence encodes each Boolean bit unchanged.
This is the pointwise equation used to normalize output lists.
-/
@[simp]
theorem outputAlphabet_symm_apply
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (bit : Bool) :
    (outputAlphabet certificate rejectionOutput).symm bit = bit := rfl

/--
Mapping the inverse output equivalence over a bitstring is the identity. This
turns a halted wrapper stack into its declared external output.
-/
@[simp]
theorem map_outputAlphabet_symm
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput bits : BitString) :
    bits.map (outputAlphabet certificate rejectionOutput).symm = bits := by
  induction bits with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, outputAlphabet_symm_apply, inductionHypothesis]
      rfl

/--
Mathlib's generic initial configuration equals the wrapper's first copying
configuration. This bridge lets `evaluatesPreprocessing` start its copying
proof from `Turing.initList`.
-/
theorem initList_eq_copyConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (input : List (certificate.tm.Γ certificate.tm.k₀)) :
    Turing.initList (machine certificate rejectionOutput) input =
      copyConfiguration certificate rejectionOutput input [] none := by
  change Turing.TM2.Cfg.mk _ _ _ = Turing.TM2.Cfg.mk _ _ _
  rw [Turing.TM2.Cfg.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext stack
  cases stack <;>
    simp [Turing.initList, wrapperStacks, machine, initialState]

/--
Copy and restore a Boolean input before entering the source machine. The source
receives its original internal encoding, and the wrapper retains the exact
external input as backup.
-/
def evaluatesPreprocessing
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput input : BitString) :
    StateTransition.EvalsToInTime (machine certificate rejectionOutput).step
      (Turing.initList (machine certificate rejectionOutput)
        (input.map certificate.inputAlphabet.invFun))
      (some (embeddedConfiguration certificate rejectionOutput
        (Turing.initList certificate.tm
          (input.map certificate.inputAlphabet.invFun)) input))
      (input.length + 1 + (input.length + 1)) := by
  let internalInput := input.map certificate.inputAlphabet.invFun
  have copyEvaluation :=
    evaluatesCopyPhase certificate rejectionOutput internalInput [] none
  have restoreEvaluation :=
    evaluatesRestorePhase certificate rejectionOutput [] internalInput.reverse [] none
  have combinedEvaluation := StateTransition.EvalsToInTime.trans
    (machine certificate rejectionOutput).step
    (internalInput.length + 1) (internalInput.reverse.length + 1)
    _ _ _ copyEvaluation restoreEvaluation
  convert combinedEvaluation using 1
  · rw [initList_eq_copyConfiguration]
    rfl
  · simp [internalInput, List.map_reverse]
  · simp [internalInput]

/--
Run the certified source decider inside the wrapper without changing its clock
or the saved input.
-/
def evaluatesDecision
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput input : BitString) :
    StateTransition.EvalsToInTime (machine certificate rejectionOutput).step
      (embeddedConfiguration certificate rejectionOutput
        (Turing.initList certificate.tm
          (input.map certificate.inputAlphabet.invFun)) input)
      (some (embeddedConfiguration certificate rejectionOutput
        (Turing.haltList certificate.tm
          [certificate.outputAlphabet.invFun (predicate input)]) input))
      (certificate.time.eval input.length) := by
  apply embeddedEvaluation certificate rejectionOutput input
  simpa [Turing.TM2OutputsInTime, Computability.encodeBool] using
    certificate.outputsFun input

/--
The complete wrapper computes conditional identity within the source clock
plus `3n + 4` steps for an input of length `n`.
-/
def evaluatesConditionalIdentity
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput input : BitString) :
    StateTransition.EvalsToInTime (machine certificate rejectionOutput).step
      (Turing.initList (machine certificate rejectionOutput)
        (input.map certificate.inputAlphabet.invFun))
      (some (Turing.haltList (machine certificate rejectionOutput)
        (if predicate input then input else rejectionOutput)))
      (certificate.time.eval input.length + 3 * input.length + 4) := by
  have preprocessing := evaluatesPreprocessing certificate rejectionOutput input
  have decision := evaluatesDecision certificate rejectionOutput input
  have preprocessingAndDecision := StateTransition.EvalsToInTime.trans
    (machine certificate rejectionOutput).step
    (input.length + 1 + (input.length + 1))
    (certificate.time.eval input.length)
    _ _ _ preprocessing decision
  have output := evaluatesOutputPhase certificate rejectionOutput input (predicate input)
  have completeEvaluation := StateTransition.EvalsToInTime.trans
    (machine certificate rejectionOutput).step
    (certificate.time.eval input.length +
      (input.length + 1 + (input.length + 1)))
    (input.length + 2)
    _ _ _ preprocessingAndDecision output
  exact {
    toEvalsTo := completeEvaluation.toEvalsTo
    steps_le_m := completeEvaluation.steps_le_m.trans (by omega)
  }

end ConditionalIdentity

variable {predicate : BitString → Bool}

/--
Certify conditional identity as polynomial-time: return the original input when
`predicate` holds, and return `rejectionOutput` otherwise. The clock is the source
decider's polynomial plus the wrapper overhead `3n + 4`.
-/
noncomputable def conditionalIdentity
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) :
    PolyTimeComputable id id
      (fun input => if predicate input then input else rejectionOutput) where
  tm := ConditionalIdentity.machine certificate rejectionOutput
  inputAlphabet := certificate.inputAlphabet
  outputAlphabet := ConditionalIdentity.outputAlphabet certificate rejectionOutput
  time := certificate.time + 3 * Polynomial.X + 4
  outputsFun input := by
    unfold Turing.TM2OutputsInTime
    convert ConditionalIdentity.evaluatesConditionalIdentity
      certificate rejectionOutput input using 1 <;>
      simp [Polynomial.eval_add, Polynomial.eval_mul]
    all_goals rfl

end PolyTimeComputable

end ComplexityTheory
