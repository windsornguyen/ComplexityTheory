/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.ConditionalIdentity.Copy

/-!
# Source-machine simulation for conditional identity

The conditional-identity wrapper executes each nonhalting source-machine step
without changing its source stacks or state semantics. Source halting becomes
the wrapper's decision-reading phase, which chooses either the saved input or
the declared rejection output.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Mathlib.Computability.TuringMachine.StackTuringMachine`, definitions
`Turing.TM2.stepAux` and `Turing.TM2.step`, and
`Mathlib.Computability.TuringMachine.Computable`, definition
`Turing.FinTM2.step`, supply the transition semantics simulated below.
The same version's `Mathlib.Computability.StateTransition`, structure
`StateTransition.EvalsToInTime` and definition `EvalsToInTime.trans`, supplies
the bounded-evaluation relation and composition operation used here.
-/

namespace ComplexityTheory

namespace PolyTimeComputable

namespace ConditionalIdentity

variable {predicate : BitString → Bool}

/-- Map a source label to its wrapper label, sending source halt to postprocessing. -/
def embeddedLabel (source : Turing.FinTM2) : Option source.Λ → Option (Label source)
  | some label => some (.source label)
  | none => some .readDecision

/--
Embed a source configuration with empty temporary storage and an untouched
Boolean backup. The source label, state, and stacks retain their meanings.
-/
def embeddedSourceConfiguration (source : Turing.FinTM2)
    (sourceConfiguration : source.Cfg)
    (backup : BitString) :
    Turing.TM2.Cfg (Alphabet source) (Label source) (State source) where
  l := embeddedLabel source sourceConfiguration.l
  var := { initialState source with sourceState := sourceConfiguration.var }
  stk := wrapperStacks source sourceConfiguration.stk [] backup

/-- The source configuration embedded in this certificate's concrete wrapper. -/
def embeddedConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (sourceConfiguration : certificate.tm.Cfg)
    (backup : BitString) : (machine certificate rejectionOutput).Cfg where
  l := embeddedLabel certificate.tm sourceConfiguration.l
  var := { initialState certificate.tm with sourceState := sourceConfiguration.var }
  stk := wrapperStacks certificate.tm sourceConfiguration.stk [] backup

/-- An empty temporary stack transfers restoration to the embedded source machine. -/
theorem step_restoreConfiguration_nil
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (restored : List (certificate.tm.Γ certificate.tm.k₀))
    (backup : BitString)
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate rejectionOutput).step
        (restoreConfiguration certificate rejectionOutput restored [] backup bufferedInput) =
      some (embeddedConfiguration certificate rejectionOutput
        (Turing.initList certificate.tm restored) backup) := by
  change Turing.TM2.step (program certificate rejectionOutput) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    restoreInputStatement, restoreConfiguration]
  simp only [wrapperStacks_temporary, List.head?, List.tail]
  simp [embeddedConfiguration, embeddedLabel, Turing.initList, initialState]
  congr

/--
Embedding commutes with the execution of one source statement. In particular,
a source `halt` becomes the wrapper's `readDecision` label.
-/
theorem stepAux_embedStatement (source : Turing.FinTM2)
    (statement : Turing.TM2.Stmt source.Γ source.Λ source.σ)
    (sourceState : source.σ) (sourceStacks : ∀ stack, List (source.Γ stack))
    (backup : BitString) :
    Turing.TM2.stepAux (embedStatement source statement)
        { initialState source with sourceState := sourceState }
        (wrapperStacks source sourceStacks [] backup) =
      embeddedSourceConfiguration source
        (Turing.TM2.stepAux statement sourceState sourceStacks) backup := by
  induction statement generalizing sourceState sourceStacks with
  | push stack value next inductionHypothesis =>
      simp [embedStatement, Turing.TM2.stepAux, inductionHypothesis]
  | peek stack update next inductionHypothesis =>
      simp [embedStatement, Turing.TM2.stepAux, inductionHypothesis]
  | pop stack update next inductionHypothesis =>
      simp [embedStatement, Turing.TM2.stepAux, inductionHypothesis]
  | load update next inductionHypothesis =>
      simp [embedStatement, Turing.TM2.stepAux, inductionHypothesis]
  | branch condition accept reject acceptHypothesis rejectHypothesis =>
      cases hcondition : condition sourceState <;>
        simp [embedStatement, Turing.TM2.stepAux, hcondition,
          acceptHypothesis, rejectHypothesis]
  | goto next =>
      simp [embedStatement, Turing.TM2.stepAux, embeddedSourceConfiguration, embeddedLabel]
  | halt =>
      simp [embedStatement, Turing.TM2.stepAux, embeddedSourceConfiguration, embeddedLabel]

/-- One nonhalting source-machine transition is one wrapper transition. -/
theorem step_embeddedConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (sourceConfiguration nextConfiguration : certificate.tm.Cfg)
    (backup : BitString)
    (step_eq : certificate.tm.step sourceConfiguration = some nextConfiguration) :
    (machine certificate rejectionOutput).step
        (embeddedConfiguration certificate rejectionOutput sourceConfiguration backup) =
      some (embeddedConfiguration certificate rejectionOutput nextConfiguration backup) := by
  cases sourceConfiguration with
  | mk sourceLabel sourceState sourceStacks =>
      cases sourceLabel with
      | none =>
          -- A halted source has no successor, contradicting the supplied nonhalting step.
          simp [Turing.FinTM2.step, Turing.TM2.step] at step_eq
      | some sourceLabel =>
          -- Both machines now execute the same statement tree under the embedding.
          change some (Turing.TM2.stepAux (certificate.tm.m sourceLabel)
            sourceState sourceStacks) = some nextConfiguration at step_eq
          injection step_eq with stepAux_eq
          subst nextConfiguration
          change some (Turing.TM2.stepAux
            (embedStatement certificate.tm (certificate.tm.m sourceLabel))
            { initialState certificate.tm with sourceState := sourceState }
            (wrapperStacks certificate.tm sourceStacks [] backup)) = _
          rw [stepAux_embedStatement]
          rfl

@[simp]
private theorem iterate_optionTransition_none {state : Type}
    (transition : state → Option state) (steps : ℕ) :
    (flip Option.bind transition)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      change (flip Option.bind transition)^[steps] none = none
      exact inductionHypothesis

/--
An exact source evaluation lifts to an exact wrapper evaluation with the same
number of steps while the saved Boolean input remains untouched.
-/
theorem iterate_embeddedConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (backup : BitString) (steps : ℕ)
    (start finish : certificate.tm.Cfg)
    (sourceEvaluation :
      (flip Option.bind certificate.tm.step)^[steps] (some start) = some finish) :
    (flip Option.bind (machine certificate rejectionOutput).step)^[steps]
        (some (embeddedConfiguration certificate rejectionOutput start backup)) =
      some (embeddedConfiguration certificate rejectionOutput finish backup) := by
  induction steps generalizing start finish with
  | zero =>
      simp only [Function.iterate_zero_apply] at sourceEvaluation ⊢
      injection sourceEvaluation with configuration_eq
      subst finish
      rfl
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply] at sourceEvaluation ⊢
      change (flip Option.bind certificate.tm.step)^[steps]
        (certificate.tm.step start) = some finish at sourceEvaluation
      change (flip Option.bind (machine certificate rejectionOutput).step)^[steps]
        ((machine certificate rejectionOutput).step
          (embeddedConfiguration certificate rejectionOutput start backup)) = _
      cases hstep : certificate.tm.step start with
      | none =>
          -- Exact evaluation to `finish` rules out an early source halt.
          rw [hstep, iterate_optionTransition_none] at sourceEvaluation
          contradiction
      | some next =>
          rw [hstep] at sourceEvaluation
          rw [step_embeddedConfiguration certificate rejectionOutput start next backup hstep]
          exact inductionHypothesis next finish sourceEvaluation

/-- Lift a bounded source evaluation without increasing its stated upper bound. -/
def embeddedEvaluation
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (backup : BitString) (bound : ℕ)
    (start finish : certificate.tm.Cfg)
    (sourceEvaluation : StateTransition.EvalsToInTime certificate.tm.step
      start (some finish) bound) :
    StateTransition.EvalsToInTime (machine certificate rejectionOutput).step
      (embeddedConfiguration certificate rejectionOutput start backup)
      (some (embeddedConfiguration certificate rejectionOutput finish backup)) bound where
  steps := sourceEvaluation.steps
  evals_in_steps := iterate_embeddedConfiguration certificate rejectionOutput backup
    sourceEvaluation.steps start finish sourceEvaluation.evals_in_steps
  steps_le_m := sourceEvaluation.steps_le_m

/--
The restoration phase returns every temporary symbol to the source input and
builds its external Boolean backup. The final extra step enters source code.
-/
def evaluatesRestorePhase
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) (restored temporary : List (certificate.tm.Γ certificate.tm.k₀))
    (backup : BitString)
    (bufferedInput : Option (certificate.tm.Γ certificate.tm.k₀)) :
    StateTransition.EvalsToInTime (machine certificate rejectionOutput).step
      (restoreConfiguration certificate rejectionOutput restored temporary backup bufferedInput)
      (some (embeddedConfiguration certificate rejectionOutput
        (Turing.initList certificate.tm (temporary.reverseAux restored))
        ((temporary.map certificate.inputAlphabet).reverseAux backup)))
      (temporary.length + 1) := by
  induction temporary generalizing restored backup bufferedInput with
  | nil =>
      simpa using oneStepEvaluation
        (step_restoreConfiguration_nil certificate rejectionOutput restored backup bufferedInput)
  | cons head temporary inductionHypothesis =>
      have firstStep := oneStepEvaluation
        (step_restoreConfiguration_cons certificate rejectionOutput restored head temporary backup
          bufferedInput)
      have remainingSteps := inductionHypothesis (head :: restored)
        (certificate.inputAlphabet head :: backup) (some head)
      simpa [List.reverseAux] using StateTransition.EvalsToInTime.trans
        (machine certificate rejectionOutput).step 1 (temporary.length + 1)
        (restoreConfiguration certificate rejectionOutput restored (head :: temporary) backup
          bufferedInput)
        (restoreConfiguration certificate rejectionOutput (head :: restored) temporary
          (certificate.inputAlphabet head :: backup) (some head))
        (some (embeddedConfiguration certificate rejectionOutput
          (Turing.initList certificate.tm (temporary.reverseAux (head :: restored)))
          ((temporary.map certificate.inputAlphabet).reverseAux
            (certificate.inputAlphabet head :: backup))))
        firstStep remainingSteps

end ConditionalIdentity

end PolyTimeComputable

end ComplexityTheory
