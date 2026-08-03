/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.ConditionalIdentity

/-!
# Input-copying phase for conditional identity

The conditional-identity wrapper first reverses the source input onto a
temporary stack, then restores the source input while producing an external
Boolean backup. This module names the phase configurations used to state the
exact single-step transition equations.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Mathlib.Computability.TuringMachine.Computable`, definition `Turing.initList`,
supplies the canonical source-machine input configuration specialized below.
The same version's `Mathlib.Computability.StateTransition`, structure
`StateTransition.EvalsToInTime` and definition `EvalsToInTime.trans`, supplies
the bounded-evaluation relation and composition operation used by the phase
proof.
-/

namespace ComplexityTheory

namespace PolyTimeComputable

namespace ConditionalIdentity

variable {predicate : BitString → Bool}

/-- Combine source stacks with the wrapper's temporary and backup stacks. -/
def wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup : BitString) :
    ∀ stack, List (Alphabet source stack)
  | .source stack => sourceStacks stack
  | .temporary => temporary
  | .backup => backup

/--
Selecting a source index returns that source stack. Copying proofs use this to
reduce wrapper transitions to the source configuration.
-/
@[simp]
theorem wrapperStacks_source (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup : BitString) (stack : source.K) :
    wrapperStacks source sourceStacks temporary backup (.source stack) = sourceStacks stack := rfl

/--
Selecting the temporary index returns its scratch stack. This exposes the
reversing phase's storage to transition proofs.
-/
@[simp]
theorem wrapperStacks_temporary (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup : BitString) :
    wrapperStacks source sourceStacks temporary backup .temporary = temporary := rfl

/--
Selecting the backup index returns the saved Boolean input. Output proofs use
this equation to show that accepted inputs remain unchanged.
-/
@[simp]
theorem wrapperStacks_backup (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup : BitString) :
    wrapperStacks source sourceStacks temporary backup .backup = backup := rfl

/--
The designated stack of `Turing.initList` contains exactly its input. This
identifies the first symbol consumed by the wrapper.
-/
@[simp]
theorem initList_inputStack (source : Turing.FinTM2)
    (input : List (source.Γ source.k₀)) :
    (Turing.initList source input).stk source.k₀ = input := by
  simp [Turing.initList]

/--
Replacing the input stack of `Turing.initList` yields another canonical input
configuration. Restoration proofs use this to name their intermediate states.
-/
@[simp]
theorem update_initList_inputStack (source : Turing.FinTM2)
    (input replacement : List (source.Γ source.k₀)) :
    Function.update (Turing.initList source input).stk source.k₀ replacement =
      (Turing.initList source replacement).stk := by
  funext stack
  by_cases h : stack = source.k₀
  · subst stack
    simp
  · simp [Turing.initList, h]

/--
Updating a wrapped source stack changes only that source stack. Embedded source
transitions use this equation without disturbing temporary or backup storage.
-/
@[simp]
theorem update_source_wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup : BitString)
    (stack : source.K) (value : List (source.Γ stack)) :
    Function.update (wrapperStacks source sourceStacks temporary backup) (.source stack) value =
      wrapperStacks source (Function.update sourceStacks stack value) temporary backup := by
  funext wrapperStack
  cases wrapperStack with
  | source other =>
      by_cases h : other = stack
      · subst other
        simp
      · simp [h]
  | temporary => simp
  | backup => simp

/--
Updating temporary storage leaves source stacks and the backup unchanged. This
is the stack invariant of the input-reversal phase.
-/
@[simp]
theorem update_temporary_wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary value : List (source.Γ source.k₀)) (backup : BitString) :
    Function.update (wrapperStacks source sourceStacks temporary backup) .temporary value =
      wrapperStacks source sourceStacks value backup := by
  funext wrapperStack
  cases wrapperStack <;> simp [wrapperStacks]

/--
Updating the backup leaves source stacks and temporary storage unchanged. This
isolates saved-input and rejection-output updates.
-/
@[simp]
theorem update_backup_wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (temporary : List (source.Γ source.k₀)) (backup value : BitString) :
    Function.update (wrapperStacks source sourceStacks temporary backup) .backup value =
      wrapperStacks source sourceStacks temporary value := by
  funext wrapperStack
  cases wrapperStack <;> simp [wrapperStacks]

/-- Configuration while reversing the remaining source input. -/
def copyConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (remaining temporary : List (certificate.tm.Γ certificate.tm.k₀))
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate rejectionOutput).Cfg where
  l := some .copyToTemporary
  var := { initialState certificate.tm with bufferedInput }
  stk := wrapperStacks certificate.tm
    (Turing.initList certificate.tm remaining).stk temporary []

/-- Configuration while restoring the source input and constructing its backup. -/
def restoreConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (restored temporary : List (certificate.tm.Γ certificate.tm.k₀))
    (backup : BitString)
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate rejectionOutput).Cfg where
  l := some .restoreInput
  var := { initialState certificate.tm with bufferedInput }
  stk := wrapperStacks certificate.tm
    (Turing.initList certificate.tm restored).stk temporary backup

/-- One nonempty reversing step moves the input head onto the temporary stack. -/
theorem step_copyConfiguration_cons
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (head : certificate.tm.Γ certificate.tm.k₀)
    (remaining temporary : List (certificate.tm.Γ certificate.tm.k₀))
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate rejectionOutput).step
        (copyConfiguration certificate rejectionOutput
          (head :: remaining) temporary bufferedInput) =
      some (copyConfiguration certificate rejectionOutput
        remaining (head :: temporary) (some head)) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  -- Frame lemmas keep the untouched source, temporary, and backup stacks abstract.
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    copyToTemporaryStatement, copyConfiguration]
  simp only [wrapperStacks_source, initList_inputStack]
  simp only [List.head?_cons, List.tail_cons]
  simp
  congr

/-- An empty source input transfers control to the restoring phase. -/
theorem step_copyConfiguration_nil
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (temporary : List (certificate.tm.Γ certificate.tm.k₀))
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate rejectionOutput).step
        (copyConfiguration certificate rejectionOutput [] temporary bufferedInput) =
      some (restoreConfiguration certificate rejectionOutput [] temporary [] none) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    copyToTemporaryStatement, copyConfiguration]
  simp only [wrapperStacks_source, initList_inputStack]
  simp only [List.head?, List.tail]
  simp only [restoreConfiguration]
  simp
  congr

/--
One nonempty restoring step returns a symbol to the source input and writes its
external Boolean value to the backup.
-/
theorem step_restoreConfiguration_cons
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (restored : List (certificate.tm.Γ certificate.tm.k₀))
    (head : certificate.tm.Γ certificate.tm.k₀)
    (temporary : List (certificate.tm.Γ certificate.tm.k₀)) (backup : BitString)
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate rejectionOutput).step (restoreConfiguration certificate rejectionOutput
        restored (head :: temporary) backup bufferedInput) =
      some (restoreConfiguration certificate rejectionOutput (head :: restored) temporary
        (certificate.inputAlphabet head :: backup) (some head)) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    restoreInputStatement, restoreConfiguration]
  simp only [wrapperStacks_temporary]
  simp only [List.head?_cons, List.tail_cons]
  simp
  congr

/-- Package one verified transition as an exact one-step evaluation bound. -/
def oneStepEvaluation
    {state : Type} {transition : state → Option state} {start finish : state}
    (step_eq : transition start = some finish) :
  StateTransition.EvalsToInTime transition start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    change transition start = some finish
    exact step_eq
  steps_le_m := le_rfl

/--
The copying phase consumes every source-input symbol and reverses it onto the
temporary stack. It transfers control to restoration within
`input.length + 1` steps; the certificate states an upper bound, not equality.
-/
def evaluatesCopyPhase
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (input temporary : List (certificate.tm.Γ certificate.tm.k₀))
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    StateTransition.EvalsToInTime (machine certificate rejectionOutput).step
      (copyConfiguration certificate rejectionOutput input temporary bufferedInput)
      (some (restoreConfiguration certificate rejectionOutput []
        (input.reverseAux temporary) [] none))
      (input.length + 1) := by
  induction input generalizing temporary bufferedInput with
  | nil =>
      simpa using oneStepEvaluation
        (step_copyConfiguration_nil certificate rejectionOutput temporary bufferedInput)
  | cons head remaining inductionHypothesis =>
      have firstStep := oneStepEvaluation
        (step_copyConfiguration_cons certificate rejectionOutput head remaining temporary
          bufferedInput)
      have remainingSteps := inductionHypothesis (head :: temporary) (some head)
      simpa [List.reverseAux] using StateTransition.EvalsToInTime.trans
        (machine certificate rejectionOutput).step 1 (remaining.length + 1)
        (copyConfiguration certificate rejectionOutput (head :: remaining) temporary bufferedInput)
        (copyConfiguration certificate rejectionOutput remaining (head :: temporary) (some head))
        (some (restoreConfiguration certificate rejectionOutput []
          (remaining.reverseAux (head :: temporary)) [] none))
        firstStep remainingSteps

end ConditionalIdentity

end PolyTimeComputable

end ComplexityTheory
