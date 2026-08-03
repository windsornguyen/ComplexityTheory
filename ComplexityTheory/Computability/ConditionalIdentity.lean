/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PolyTime

/-!
# Conditional identity machines

Given a certified Boolean decider and a declared rejection output, this module
constructs a finite multitape machine that returns its input when the decider
accepts and returns that output when the decider rejects. The wrapper copies the
input before running the source machine because a `FinTM2` computation may
consume every input stack.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Mathlib.Computability.TuringMachine.Computable`, records generic polynomial-
time TM2 composition only as a `proof_wanted` introduced by
leanprover-community/mathlib4#7172. Conditional identity additionally needs the
original input after the decider halts, so ordinary function composition would
not establish the construction defined here.
-/

namespace ComplexityTheory

namespace PolyTimeComputable

namespace ConditionalIdentity

/-- Reuse the source machine's finite stack-index certificate. -/
local instance sourceStackFintype (source : Turing.FinTM2) : Fintype source.K :=
  source.kFin

/-- Reuse the source machine's finite control-label certificate. -/
local instance sourceLabelFintype (source : Turing.FinTM2) : Fintype source.Λ :=
  source.ΛFin

/-- Reuse the source machine's finite internal-state certificate. -/
local instance sourceStateFintype (source : Turing.FinTM2) : Fintype source.σ :=
  source.σFin

/-- Reuse the source machine's finite input-alphabet certificate. -/
local instance sourceInputAlphabetFintype (source : Turing.FinTM2) :
    Fintype (source.Γ source.k₀) :=
  source.Γk₀Fin

/-- Stack indices for the wrapped source machine and its two copying stacks. -/
inductive Stack (source : Turing.FinTM2) where
  /-- A stack belonging to the source decider. -/
  | source (stack : source.K)
  /-- Temporary storage used while restoring the source input's order. -/
  | temporary
  /-- The untouched input copy and final output stack. -/
  | backup
  deriving DecidableEq, Fintype

/-- Each source stack retains its alphabet; both new stacks store input symbols. -/
abbrev Alphabet (source : Turing.FinTM2) : Stack source → Type
  | .source stack => source.Γ stack
  | .temporary => source.Γ source.k₀
  | .backup => Bool

/-- Control labels for copying, running the source decider, and selecting output. -/
inductive Label (source : Turing.FinTM2) where
  /-- Reverse the source input onto the temporary stack. -/
  | copyToTemporary
  /-- Restore the source input while producing its backup. -/
  | restoreInput
  /-- Execute one of the source machine's labels. -/
  | source (label : source.Λ)
  /-- Read the source decider's Boolean output. -/
  | readDecision
  /-- Remove a rejected input copy before writing the declared rejection output. -/
  | clearBackup
  deriving Fintype

/--
Finite wrapper state containing the source state, one buffered input symbol,
and the Boolean flag used by postprocessing branches.
-/
structure State (source : Turing.FinTM2) where
  /-- Internal state of the embedded source machine. -/
  sourceState : source.σ
  /-- Symbol most recently popped while copying the input. -/
  bufferedInput : Option (source.Γ source.k₀)
  /-- Decision bit or stack-nonemptiness flag for the current phase. -/
  flag : Bool
  deriving Fintype

/-- The wrapper starts with the source's initial state and empty scratch fields. -/
def initialState (source : Turing.FinTM2) : State source where
  sourceState := source.initialState
  bufferedInput := none
  flag := false

/--
Embed a source statement into the wrapper. Source stack operations and state
updates are preserved exactly; source halting transfers control to the output
selection phase instead of halting the wrapper.
-/
def embedStatement (source : Turing.FinTM2) :
    Turing.TM2.Stmt source.Γ source.Λ source.σ →
      Turing.TM2.Stmt (Alphabet source) (Label source) (State source)
  | .push stack value next =>
      .push (.source stack) (fun state => value state.sourceState)
        (embedStatement source next)
  | .peek stack update next =>
      .peek (.source stack)
        (fun state symbol => { state with sourceState := update state.sourceState symbol })
        (embedStatement source next)
  | .pop stack update next =>
      .pop (.source stack)
        (fun state symbol => { state with sourceState := update state.sourceState symbol })
        (embedStatement source next)
  | .load update next =>
      .load (fun state => { state with sourceState := update state.sourceState })
        (embedStatement source next)
  | .branch condition accept reject =>
      .branch (fun state => condition state.sourceState)
        (embedStatement source accept) (embedStatement source reject)
  | .goto next => .goto (fun state => .source (next state.sourceState))
  | .halt => .goto (fun _ => .readDecision)

/-- Push the supplied bits in order onto an initially empty backup stack. -/
def pushReversedBits (source : Turing.FinTM2) :
    BitString → Turing.TM2.Stmt (Alphabet source) (Label source) (State source) →
      Turing.TM2.Stmt (Alphabet source) (Label source) (State source)
  | [], next => next
  | bit :: bits, next =>
      .push .backup (fun _ => bit) (pushReversedBits source bits next)

/-- Reset scratch state before producing the exact `haltList` configuration. -/
def resetAndHalt (source : Turing.FinTM2) :
    Turing.TM2.Stmt (Alphabet source) (Label source) (State source) :=
  .load (fun _ => initialState source) .halt

end ConditionalIdentity

end PolyTimeComputable

end ComplexityTheory
