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

end ConditionalIdentity

end PolyTimeComputable

end ComplexityTheory
