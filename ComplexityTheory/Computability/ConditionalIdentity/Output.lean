/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.ConditionalIdentity.Simulation

/-!
# Output selection for conditional identity

After the source decider halts, the wrapper returns the saved input when the
decision bit is true. When it is false, the wrapper clears the saved input and
writes the declared rejection output.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Mathlib.Computability.TuringMachine.Computable`, definitions
`Turing.haltList` and `Turing.FinTM2.step`, and
`Mathlib.Computability.TuringMachine.StackTuringMachine`, definitions
`Turing.TM2.step` and `Turing.TM2.stepAux`, supply the configurations and
transition semantics specialized below.
-/

namespace ComplexityTheory

namespace PolyTimeComputable

namespace ConditionalIdentity

variable {predicate : BitString → Bool}

/--
The canonical halted configuration has no next label. Output proofs use this
to enter the wrapper's decision-reading phase.
-/
@[simp]
theorem haltList_label (source : Turing.FinTM2)
    (output : List (source.Γ source.k₁)) :
    (Turing.haltList source output).l = none := rfl

/--
The canonical halted configuration resets to the machine's initial state. This
identifies the wrapper state before output selection.
-/
@[simp]
theorem haltList_state (source : Turing.FinTM2)
    (output : List (source.Γ source.k₁)) :
    (Turing.haltList source output).var = source.initialState := rfl

/--
The designated output stack of `Turing.haltList` contains exactly its output.
This exposes the source decider's Boolean decision bit.
-/
@[simp]
theorem haltList_outputStack (source : Turing.FinTM2)
    (output : List (source.Γ source.k₁)) :
    (Turing.haltList source output).stk source.k₁ = output := by
  simp [Turing.haltList]

/--
Replacing the output stack of `Turing.haltList` yields another canonical halted
configuration. Output proofs use this to normalize stack updates.
-/
@[simp]
theorem update_haltList_outputStack (source : Turing.FinTM2)
    (output replacement : List (source.Γ source.k₁)) :
    Function.update (Turing.haltList source output).stk source.k₁ replacement =
      (Turing.haltList source replacement).stk := by
  funext stack
  by_cases h : stack = source.k₁
  · subst stack
    simp
  · simp [Turing.haltList, h]

/--
Embedding an empty-output source halt with a Boolean backup equals the wrapper's
canonical halt on that backup. This is the accepting branch's output invariant.
-/
theorem wrapperStacks_haltList
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput backup : BitString) :
    wrapperStacks certificate.tm (Turing.haltList certificate.tm []).stk [] backup =
      (Turing.haltList (machine certificate rejectionOutput) backup).stk := by
  funext stack
  cases stack with
  | source sourceStack =>
      simp only [wrapperStacks]
      by_cases h : sourceStack = certificate.tm.k₁
      · subst sourceStack
        simp [Turing.haltList, machine]
      · simp [Turing.haltList, machine, h]
  | temporary => simp [wrapperStacks, Turing.haltList, machine]
  | backup => simp [wrapperStacks, Turing.haltList, machine]

/-- Configuration while deleting the rejected input copy. -/
def clearingConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput remaining : BitString) (flag : Bool) :
    (machine certificate rejectionOutput).Cfg where
  l := some .clearBackup
  var := { initialState certificate.tm with flag }
  stk := wrapperStacks certificate.tm (Turing.haltList certificate.tm []).stk [] remaining

/-- An accepting decision halts immediately with the saved input. -/
theorem step_acceptingOutput
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput backup : BitString) :
    (machine certificate rejectionOutput).step
        (embeddedConfiguration certificate rejectionOutput
          (Turing.haltList certificate.tm
            [certificate.outputAlphabet.invFun true]) backup) =
      some (Turing.haltList (machine certificate rejectionOutput) backup) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [embeddedConfiguration]
  simp only [haltList_label, haltList_state, embeddedLabel]
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program, readDecisionStatement]
  simp only [wrapperStacks_source, haltList_outputStack, List.head?_cons, List.tail_cons]
  simp only [update_source_wrapperStacks, update_haltList_outputStack]
  simp [resetAndHalt, initialState]
  congr
  simpa [Turing.haltList] using wrapperStacks_haltList certificate rejectionOutput backup

/-- A rejecting decision enters the backup-clearing loop. -/
theorem step_rejectingOutput
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput backup : BitString) :
    (machine certificate rejectionOutput).step
        (embeddedConfiguration certificate rejectionOutput
          (Turing.haltList certificate.tm
            [certificate.outputAlphabet.invFun false]) backup) =
      some (clearingConfiguration certificate rejectionOutput backup false) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [embeddedConfiguration]
  simp only [haltList_label, haltList_state, embeddedLabel]
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program, readDecisionStatement]
  simp only [wrapperStacks_source, haltList_outputStack, List.head?_cons, List.tail_cons]
  simp only [update_source_wrapperStacks, update_haltList_outputStack]
  simp [clearingConfiguration]
  congr

/-- One nonempty clearing step deletes the backup's head. -/
theorem step_clearingConfiguration_cons
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (head : Bool) (remaining : BitString) (flag : Bool) :
    (machine certificate rejectionOutput).step
        (clearingConfiguration certificate rejectionOutput (head :: remaining) flag) =
      some (clearingConfiguration certificate rejectionOutput remaining true) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    clearBackupStatement, clearingConfiguration]
  simp only [wrapperStacks_backup, List.head?_cons, List.tail_cons]
  simp only [update_backup_wrapperStacks]
  congr

/-- Pushing a bit list prefixes its reversal to the backup stack. -/
theorem stepAux_pushReversedBits (source : Turing.FinTM2)
    (bits : BitString)
    (next : Turing.TM2.Stmt (Alphabet source) (Label source) (State source))
    (state : State source) (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup : BitString) :
    Turing.TM2.stepAux (pushReversedBits source bits next) state
        (wrapperStacks source sourceStacks temporary backup) =
      Turing.TM2.stepAux next state
        (wrapperStacks source sourceStacks temporary (bits.reverseAux backup)) := by
  induction bits generalizing backup with
  | nil => rfl
  | cons head bits inductionHypothesis =>
      simp only [pushReversedBits, Turing.TM2.stepAux]
      rw [update_backup_wrapperStacks]
      simpa [List.reverseAux] using inductionHypothesis (head :: backup)

/-- An empty backup is replaced by the declared rejection output before halting. -/
theorem step_clearingConfiguration_nil
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (flag : Bool) :
    (machine certificate rejectionOutput).step
        (clearingConfiguration certificate rejectionOutput [] flag) =
      some (Turing.haltList (machine certificate rejectionOutput) rejectionOutput) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    clearBackupStatement, clearingConfiguration]
  simp only [wrapperStacks_backup, List.head?, List.tail]
  simp only [Option.isSome_none, update_backup_wrapperStacks, cond_false]
  -- Reverse before pushing so the LIFO backup stack exposes the declared order.
  rw [stepAux_pushReversedBits]
  simp [resetAndHalt, initialState, Turing.haltList]
  congr
  simpa [Turing.haltList] using wrapperStacks_haltList certificate rejectionOutput rejectionOutput

end ConditionalIdentity

end PolyTimeComputable

end ComplexityTheory
