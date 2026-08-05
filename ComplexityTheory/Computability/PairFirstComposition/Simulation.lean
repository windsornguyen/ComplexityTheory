/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition.Transitions

/-!
# Source simulation for pair-first composition

Once the parser restores the first component, the wrapper executes each source
statement with identical source state and stacks. One source step costs one
wrapper step, and source halting becomes wrapper halting without postprocessing.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- Embedding commutes with the execution of one source statement. -/
theorem stepAux_embedStatement
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (statement : Turing.TM2.Stmt certificate.tm.Γ certificate.tm.Λ certificate.tm.σ)
    (sourceState : certificate.tm.σ)
    (sourceStacks : ∀ stack, List (certificate.tm.Γ stack)) :
    Turing.TM2.stepAux (embedStatement certificate.tm statement)
        { initialState certificate.tm with sourceState }
        (wrapperStacks certificate.tm sourceStacks []) =
      embeddedConfiguration certificate
        (Turing.TM2.stepAux statement sourceState sourceStacks) := by
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
      cases hCondition : condition sourceState <;>
        simp [embedStatement, Turing.TM2.stepAux, hCondition,
          acceptHypothesis, rejectHypothesis]
  | goto next =>
      simp [embedStatement, Turing.TM2.stepAux, embeddedConfiguration, embeddedLabel]
      rfl
  | halt =>
      simp [embedStatement, Turing.TM2.stepAux, embeddedConfiguration, embeddedLabel]
      rfl

/-- One nonhalting source transition is one wrapper transition. -/
theorem step_embeddedConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (sourceConfiguration nextConfiguration : certificate.tm.Cfg)
    (step_eq : certificate.tm.step sourceConfiguration = some nextConfiguration) :
    (machine certificate).step (embeddedConfiguration certificate sourceConfiguration) =
      some (embeddedConfiguration certificate nextConfiguration) := by
  cases sourceConfiguration with
  | mk sourceLabel sourceState sourceStacks =>
      cases sourceLabel with
      | none =>
          simp [Turing.FinTM2.step, Turing.TM2.step] at step_eq
      | some sourceLabel =>
          change some (Turing.TM2.stepAux (certificate.tm.m sourceLabel)
            sourceState sourceStacks) = some nextConfiguration at step_eq
          injection step_eq with stepAux_eq
          subst nextConfiguration
          change some (Turing.TM2.stepAux
            (embedStatement certificate.tm (certificate.tm.m sourceLabel))
            { initialState certificate.tm with sourceState }
            (wrapperStacks certificate.tm sourceStacks [])) = _
          rw [stepAux_embedStatement]
          rfl

private theorem iterate_optionTransition_none {state : Type}
    (transition : state → Option state) (steps : Nat) :
    (flip Option.bind transition)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact inductionHypothesis

/-- An exact source evaluation lifts with the same number of steps. -/
theorem iterate_embeddedConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (steps : Nat) (start finish : certificate.tm.Cfg)
    (sourceEvaluation :
      (flip Option.bind certificate.tm.step)^[steps] (some start) = some finish) :
    (flip Option.bind (machine certificate).step)^[steps]
        (some (embeddedConfiguration certificate start)) =
      some (embeddedConfiguration certificate finish) := by
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
      change (flip Option.bind (machine certificate).step)^[steps]
        ((machine certificate).step (embeddedConfiguration certificate start)) = _
      cases hStep : certificate.tm.step start with
      | none =>
          rw [hStep, iterate_optionTransition_none] at sourceEvaluation
          contradiction
      | some next =>
          rw [hStep] at sourceEvaluation
          rw [step_embeddedConfiguration certificate start next hStep]
          exact inductionHypothesis next finish sourceEvaluation

/-- Lift a bounded source evaluation without increasing its upper bound. -/
def embeddedEvaluation
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (bound : Nat) (start finish : certificate.tm.Cfg)
    (sourceEvaluation : StateTransition.EvalsToInTime certificate.tm.step
      start (some finish) bound) :
    StateTransition.EvalsToInTime (machine certificate).step
      (embeddedConfiguration certificate start)
      (some (embeddedConfiguration certificate finish)) bound where
  steps := sourceEvaluation.steps
  evals_in_steps := iterate_embeddedConfiguration certificate sourceEvaluation.steps
    start finish sourceEvaluation.evals_in_steps
  steps_le_m := sourceEvaluation.steps_le_m

/-- Embedding a source halt configuration is exactly wrapper halt. -/
theorem embedded_haltList
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (output : List (certificate.tm.Γ certificate.tm.k₁)) :
    embeddedConfiguration certificate (Turing.haltList certificate.tm output) =
      Turing.haltList (machine certificate) output := by
  simp only [embeddedConfiguration, embeddedLabel, Turing.haltList]
  congr
  funext stack
  cases stack with
  | source sourceStack =>
      by_cases h : sourceStack = certificate.tm.k₁
      · subst sourceStack
        simp [wrapperStacks, machine]
      · simp [wrapperStacks, machine, h]
  | reverse => simp [wrapperStacks, machine]

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
