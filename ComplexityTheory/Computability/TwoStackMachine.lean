/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.BinaryString

/-!
# Finite-control binary two-stack machines

This module defines the concrete program syntax that will underlie the
clocked universal translator. A program has finitely many control labels and
two Boolean stacks. Each transition halts, pushes one bit, or pops one bit and
branches on the result.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Turing.TM2.Stmt` in
`Mathlib.Computability.TuringMachine.StackTuringMachine`, supplies the general
stack-machine model that motivates these instructions. The syntax here fixes
two stacks, a Boolean alphabet, and labels of type `Fin n` so every jump target
is valid by construction. This module does not yet claim universality or a
simulation overhead.

The head of each bitstring is the top of its stack. Input begins on the primary
stack, the auxiliary stack begins empty, and a halted machine returns the
primary stack.
-/

namespace ComplexityTheory
namespace TwoStackMachine

/-- Select one of the machine's two Boolean stacks. -/
inductive Stack
  /-- The input and output stack. -/
  | primary
  /-- The work stack used for reversible traversal and temporary storage. -/
  | auxiliary
  deriving DecidableEq

/--
One finite-control instruction. Every continuation is a value of `Label`, so
an instruction cannot jump outside its program's control-label type.
-/
inductive Instruction (Label : Type)
  /-- Halt and expose the primary stack as output. -/
  | halt
  /-- Push one Boolean value and continue at `next`. -/
  | push (stack : Stack) (bit : Bool) (next : Label)
  /-- Pop and branch separately for an empty stack, `false`, or `true`. -/
  | pop (stack : Stack) (onEmpty onFalse onTrue : Label)

/--
A finite program assigns one instruction to every valid control label and
designates one of those labels as initial. The `initial` field makes a program
with zero labels unrepresentable.
-/
structure Program where
  /-- Number of control labels in the program. -/
  labelCount : Nat
  /-- The first instruction executed on every input. -/
  initial : Fin labelCount
  /-- The instruction associated with each valid control label. -/
  instruction : Fin labelCount → Instruction (Fin labelCount)

namespace Program

/-- The finite control-label type belonging to `program`. -/
abbrev Label (program : Program) := Fin program.labelCount

end Program

/-- A machine is either running at a valid control label or halted. -/
inductive Control (Label : Type)
  /-- Continue by executing the instruction at this label. -/
  | running (label : Label)
  /-- Stop; no further instruction may execute. -/
  | halted

/--
The complete runtime state for one program. The dependent control type makes
an invalid program counter unrepresentable.
-/
structure Configuration (program : Program) where
  /-- Current finite-control status. -/
  control : Control program.Label
  /-- Input, output, and primary work data. -/
  primary : BitString
  /-- Secondary work data. -/
  auxiliary : BitString

namespace Configuration

/-- Read the selected stack without changing the configuration. -/
def readStack {program : Program} (configuration : Configuration program) :
    Stack → BitString
  | .primary => configuration.primary
  | .auxiliary => configuration.auxiliary

/-- Replace exactly the selected stack and preserve all other machine state. -/
def writeStack {program : Program} (configuration : Configuration program)
    (stack : Stack) (bits : BitString) : Configuration program :=
  match stack with
  | .primary => { configuration with primary := bits }
  | .auxiliary => { configuration with auxiliary := bits }

/-- Writing a stack changes the value subsequently read from that stack. -/
@[simp] theorem readStack_writeStack_same {program : Program}
    (configuration : Configuration program) (stack : Stack) (bits : BitString) :
    (configuration.writeStack stack bits).readStack stack = bits := by
  cases stack <;> rfl

/-- Writing one stack preserves the other stack exactly. -/
@[simp] theorem readStack_writeStack_other {program : Program}
    (configuration : Configuration program) (stack : Stack) (bits : BitString) :
    (configuration.writeStack stack bits).readStack
      (match stack with | .primary => .auxiliary | .auxiliary => .primary) =
      configuration.readStack
        (match stack with | .primary => .auxiliary | .auxiliary => .primary) := by
  cases stack <;> rfl

end Configuration

/--
Execute one instruction against a running configuration. `pop` leaves an
empty stack unchanged; a nonempty pop removes exactly its head bit.
-/
def executeInstruction {program : Program}
    (instruction : Instruction program.Label)
    (configuration : Configuration program) : Configuration program :=
  match instruction with
  | .halt => { configuration with control := .halted }
  | .push stack bit next =>
      let updated := configuration.writeStack stack (bit :: configuration.readStack stack)
      { updated with control := .running next }
  | .pop stack onEmpty onFalse onTrue =>
      match configuration.readStack stack with
      | [] => { configuration with control := .running onEmpty }
      | bit :: remaining =>
          let updated := configuration.writeStack stack remaining
          let next := if bit then onTrue else onFalse
          { updated with control := .running next }

/--
Advance one machine transition. Halted configurations are fixed points;
running configurations execute the instruction at their valid control label.
-/
def step (program : Program) (configuration : Configuration program) :
    Configuration program :=
  match configuration.control with
  | .halted => configuration
  | .running label => executeInstruction (program.instruction label) configuration

/-- Place the complete input on the primary stack and enter the initial label. -/
def initialConfiguration (program : Program) (input : BitString) : Configuration program where
  control := .running program.initial
  primary := input
  auxiliary := []

/-- Return the primary stack exactly when the machine has halted. -/
def output {program : Program} (configuration : Configuration program) : Option BitString :=
  match configuration.control with
  | .running _ => none
  | .halted => some configuration.primary

/-- Initial configurations are running and therefore have no output yet. -/
@[simp] theorem output_initialConfiguration (program : Program) (input : BitString) :
    output (initialConfiguration program input) = none :=
  rfl

/-- A halted configuration remains unchanged by every subsequent step. -/
theorem step_eq_self_of_halted (program : Program) (configuration : Configuration program)
    (hHalted : configuration.control = .halted) :
    step program configuration = configuration := by
  simp [step, hHalted]

end TwoStackMachine
end ComplexityTheory
