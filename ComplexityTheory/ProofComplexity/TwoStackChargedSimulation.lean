/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.TwoStackChargedInterpreter

/-!
# Simulation overhead of charged two-stack interpretation

For a fixed program `P`, the charged interpreter simulates `t` typed program
transitions in exactly `transitionCharge P * t` charged transitions. The
multiplier is independent of the input, so it is a constant for each indexed
translator. This module proves exact execution equality before lifting it to
the `ComputesWithin` contract used by clocked diagonalization.

The theorem concerns the executable charge specification. It does not claim
that a bit-level interpreter implements each charged transition in constant
time; that remains the next refinement boundary.
-/

namespace ComplexityTheory
namespace SyntacticDiagonal
namespace TwoStackChargedInterpreter

/-- Multiplying the typed allowance by the program charge preserves bounded execution. -/
theorem machine_runFrom_eq_typed (allowance : Nat)
    (semantic : TwoStackInterpreter.State) :
    machine.runFrom (transitionCharge semantic.program * allowance)
        ⟨semantic, (TwoStackMachine.ProgramCode.encode semantic.program).length⟩ =
      TwoStackInterpreter.machine.runFrom allowance semantic := by
  induction allowance generalizing semantic with
  | zero => rfl
  | succ allowance inductionHypothesis =>
      rcases semantic with ⟨program, configuration⟩
      cases hControl : configuration.control with
      | halted =>
          generalize transitionCharge program * (allowance + 1) = chargedAllowance
          cases chargedAllowance <;>
            simp [ClockedTranslationMachine.runFrom, machine, output,
              TwoStackInterpreter.machine, TwoStackInterpreter.output,
              TwoStackMachine.output, hControl]
      | running label =>
          rw [Nat.mul_succ, Nat.add_comm]
          rw [machine_runFrom_transition
            (transitionCharge program * allowance) program configuration label hControl]
          rw [TwoStackInterpreter.machine_runFrom_running
            allowance program configuration label hControl]
          simpa [TwoStackInterpreter.step] using
            inductionHypothesis (TwoStackInterpreter.step ⟨program, configuration⟩)

/-- Charged and typed interpreters return the same result under the multiplied allowance. -/
theorem machine_runFor_eq_typed (allowance : Nat)
    (program : TwoStackMachine.Program) (input : BitString) :
    machine.runFor (transitionCharge program * allowance) program input =
      TwoStackInterpreter.machine.runFor allowance program input := by
  simpa [ClockedTranslationMachine.runFor, machine, initial,
    TwoStackInterpreter.machine, TwoStackInterpreter.initial] using
      machine_runFrom_eq_typed allowance (TwoStackInterpreter.initial program input)

/-- Every typed clock certificate lifts through the exact program-dependent charge. -/
theorem computesWithin_of_typed {clock : Nat → Nat}
    {program : TwoStackMachine.Program} {translation : BitString → BitString}
    (hComputes : TwoStackInterpreter.machine.ComputesWithin clock program translation) :
    machine.ComputesWithin
      (fun inputLength => transitionCharge program * clock inputLength)
      program translation := by
  intro input
  rw [machine_runFor_eq_typed]
  exact hComputes input

end TwoStackChargedInterpreter
end SyntacticDiagonal
end ComplexityTheory
