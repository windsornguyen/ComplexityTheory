/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.TwoStackMachine.ProgramEncoding
import ComplexityTheory.ProofComplexity.ClockedDiagonal

/-!
# Two-stack instance of the clocked translation machine

This module packages each typed two-stack program with its dependent runtime
configuration, producing the common state type required by
`ClockedTranslationMachine`. One interpreter transition is definitionally one
transition of the selected program.

This is a semantic machine adapter, not yet a bit-level universal interpreter.
The program is already decoded, and instruction lookup is one transition.
Consequently the instance makes the fixed-clock diagonal theorem executable
for two-stack programs but does not yet establish a polynomial simulation
over encoded program-and-input pairs.
-/

namespace ComplexityTheory
namespace SyntacticDiagonal
namespace TwoStackInterpreter

/-- A program packaged with a configuration whose control type belongs to it. -/
structure State where
  /-- The fixed two-stack program interpreted by this state. -/
  program : TwoStackMachine.Program
  /-- The program-dependent runtime configuration. -/
  configuration : TwoStackMachine.Configuration program

/-- Initialize a typed program with the input on its primary stack. -/
def initial (program : TwoStackMachine.Program) (input : BitString) : State :=
  ⟨program, TwoStackMachine.initialConfiguration program input⟩

/-- Execute exactly one transition of the packaged program. -/
def step : State → State
  | ⟨program, configuration⟩ =>
      ⟨program, TwoStackMachine.step program configuration⟩

/-- Return the packaged program's primary stack exactly after it halts. -/
def output : State → Option BitString
  | ⟨_, configuration⟩ => TwoStackMachine.output configuration

/--
Interpret typed two-stack programs under the generic clocked-machine contract.
The canonical program codec makes every accepted index payload unique.
-/
def machine : ClockedTranslationMachine TwoStackMachine.Program where
  Configuration := State
  indexEncoding := TwoStackMachine.ProgramCode.encoding
  eq_indexEncoding_encode_of_decode_eq_some :=
    TwoStackMachine.ProgramCode.eq_encode_of_decode?_eq_some
  initial := initial
  step := step
  output := output

/-- A running state consumes one clock unit and performs one program transition. -/
@[simp] theorem machine_runFrom_running (allowance : Nat)
    (program : TwoStackMachine.Program)
    (configuration : TwoStackMachine.Configuration program)
    (label : program.Label) (hRunning : configuration.control = .running label) :
    machine.runFrom (allowance + 1) ⟨program, configuration⟩ =
      machine.runFrom allowance
        ⟨program, TwoStackMachine.step program configuration⟩ := by
  simp [ClockedTranslationMachine.runFrom, machine, output, step,
    TwoStackMachine.output, hRunning]

/-- A halted state returns its primary stack without consuming another transition. -/
@[simp] theorem machine_runFrom_halted (allowance : Nat)
    (program : TwoStackMachine.Program)
    (configuration : TwoStackMachine.Configuration program)
    (hHalted : configuration.control = .halted) :
    machine.runFrom allowance ⟨program, configuration⟩ = some configuration.primary := by
  cases allowance <;>
    simp [ClockedTranslationMachine.runFrom, machine, output,
      TwoStackMachine.output, hHalted]

/-- A program whose initial instruction halts returns its unchanged input in one transition. -/
@[simp] theorem machine_runFor_one_of_initial_halt
    (program : TwoStackMachine.Program) (input : BitString)
    (hHalt : program.instruction program.initial = .halt) :
    machine.runFor 1 program input = some input := by
  simp [ClockedTranslationMachine.runFor, ClockedTranslationMachine.runFrom,
    machine, initial, step, output, TwoStackMachine.output, TwoStackMachine.step,
    hHalt, TwoStackMachine.executeInstruction, TwoStackMachine.initialConfiguration]

end TwoStackInterpreter
end SyntacticDiagonal
end ComplexityTheory
