/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.TwoStackInterpreter

/-!
# Program-length charges for two-stack interpretation

The typed interpreter treats instruction lookup as one transition. This module
adds a conservative clock: before every source transition, it charges one step
per bit of the canonical program code, followed by one execution step. The
resulting exact transition cost is therefore `programCodeLength + 1`.

The delay is executable and its accounting is proved below. It models a full
linear scan but does not yet implement that scan bit by bit, so it is a cost
specification rather than a polynomial-time universal-machine certificate.
-/

namespace ComplexityTheory
namespace SyntacticDiagonal
namespace TwoStackChargedInterpreter

/-- Charge one scan step per program-code bit and one step for execution. -/
def transitionCharge (program : TwoStackMachine.Program) : Nat :=
  (TwoStackMachine.ProgramCode.encode program).length + 1

/-- A semantic interpreter state together with its remaining scan charge. -/
structure State where
  /-- The underlying typed program and runtime configuration. -/
  semantic : TwoStackInterpreter.State
  /-- Number of scan steps remaining before the next source transition. -/
  remaining : Nat

/-- Begin with a full program-length scan charge. -/
def initial (program : TwoStackMachine.Program) (input : BitString) : State :=
  ⟨TwoStackInterpreter.initial program input,
    (TwoStackMachine.ProgramCode.encode program).length⟩

/--
Consume one scan charge, or execute one source transition when the charge is
zero and reset the charge for the following transition.
-/
def step : State → State
  | ⟨semantic, 0⟩ =>
      ⟨TwoStackInterpreter.step semantic,
        (TwoStackMachine.ProgramCode.encode semantic.program).length⟩
  | ⟨semantic, remaining + 1⟩ => ⟨semantic, remaining⟩

/-- Observe exactly the output of the underlying semantic interpreter. -/
def output (state : State) : Option BitString :=
  TwoStackInterpreter.output state.semantic

/-- Interpret typed programs while charging their canonical encoded length. -/
def machine : ClockedTranslationMachine TwoStackMachine.Program where
  Configuration := State
  indexEncoding := TwoStackMachine.ProgramCode.encoding
  eq_indexEncoding_encode_of_decode_eq_some :=
    TwoStackMachine.ProgramCode.eq_encode_of_decode?_eq_some
  initial := initial
  step := step
  output := output

/-- Exactly `remaining` delay steps preserve the semantic state and exhaust the charge. -/
@[simp] theorem iterate_step_remaining (semantic : TwoStackInterpreter.State)
    (remaining : Nat) :
    (step^[remaining]) ⟨semantic, remaining⟩ = ⟨semantic, 0⟩ := by
  induction remaining with
  | zero => simp
  | succ remaining inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      simpa [step] using inductionHypothesis

/-- The transition after an exhausted delay executes one source transition. -/
theorem step_after_program_scan (semantic : TwoStackInterpreter.State) :
    step ((step^[(TwoStackMachine.ProgramCode.encode semantic.program).length])
      ⟨semantic, (TwoStackMachine.ProgramCode.encode semantic.program).length⟩) =
      ⟨TwoStackInterpreter.step semantic,
        (TwoStackMachine.ProgramCode.encode semantic.program).length⟩ := by
  rw [iterate_step_remaining]
  rfl

/-- Exhausting a delay under a running state preserves the remaining clock exactly. -/
theorem machine_runFrom_delay (allowance remaining : Nat)
    (semantic : TwoStackInterpreter.State)
    (hNoOutput : TwoStackInterpreter.output semantic = none) :
    machine.runFrom (remaining + allowance) ⟨semantic, remaining⟩ =
      machine.runFrom allowance ⟨semantic, 0⟩ := by
  induction remaining with
  | zero => simp
  | succ remaining inductionHypothesis =>
      simpa [ClockedTranslationMachine.runFrom, machine, output, step, hNoOutput,
        Nat.succ_add] using inductionHypothesis

/-- One charged transition equals one underlying program transition. -/
theorem machine_runFrom_transition (allowance : Nat)
    (program : TwoStackMachine.Program)
    (configuration : TwoStackMachine.Configuration program)
    (label : program.Label) (hRunning : configuration.control = .running label) :
    machine.runFrom (transitionCharge program + allowance)
        ⟨⟨program, configuration⟩,
          (TwoStackMachine.ProgramCode.encode program).length⟩ =
      machine.runFrom allowance
        ⟨TwoStackInterpreter.step ⟨program, configuration⟩,
          (TwoStackMachine.ProgramCode.encode program).length⟩ := by
  have hOutput : TwoStackInterpreter.output ⟨program, configuration⟩ = none := by
    simp [TwoStackInterpreter.output, TwoStackMachine.output, hRunning]
  rw [show transitionCharge program + allowance =
    (TwoStackMachine.ProgramCode.encode program).length + (allowance + 1) by
      simp [transitionCharge]
      omega]
  rw [machine_runFrom_delay (allowance + 1) _ _ hOutput]
  simp [ClockedTranslationMachine.runFrom, machine, output, step, hOutput]

end TwoStackChargedInterpreter
end SyntacticDiagonal
end ComplexityTheory
