/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PolyTime

/-!
# Conditional identity machines

Given a certified Boolean decider and a declared rejection output, this module
defines a finite multitape wrapper intended to return its input when the decider
accepts and that output when the decider rejects. A `FinTM2` computation may
consume every input stack, so the wrapper first copies the input. This module
defines the machine only; subsequent phase modules prove its execution contract.

The wrapper's control flow is:

```text
copyToTemporary -> restoreInput -> source -> readDecision
                                           | true  -> halt with input
                                           | false -> clearBackup -> halt with rejection output
```

Every `bufferedInput.getD` occurs inside the branch guarded by
`bufferedInput.isSome`. Mathlib statements require total symbol functions, but
the branch semantics make the supplied default unreachable; the phase
transition theorems verify that invariant.

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
  -- Source halt cannot halt the wrapper: output selection still owns the final result.
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

variable {predicate : BitString → Bool}

/--
Transfer control to another wrapper label without changing machine data. This
single combinator keeps Mathlib's low-level `goto` constructor out of the phase
definitions below.
-/
private abbrev continueAt {source : Turing.FinTM2} (label : Label source) :
    Turing.TM2.Stmt (Alphabet source) (Label source) (State source) :=
  .goto fun _ => label

/--
Move one source-input symbol to temporary storage, or begin restoration once
the source input is empty. Repeating this statement reverses the input.
-/
def copyToTemporaryStatement
    (certificate : PolyTimeComputable id Computability.encodeBool predicate) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm)
      (State certificate.tm) :=
  -- The first reversal lets the restoration pass recover the original input order.
  .pop (.source certificate.tm.k₀)
    (fun state symbol => { state with bufferedInput := symbol })
    (.branch (fun state => state.bufferedInput.isSome)
      (.push .temporary
        (fun state => state.bufferedInput.getD
          (certificate.inputAlphabet.invFun false))
        (continueAt .copyToTemporary))
      (continueAt .restoreInput))

/--
Move one temporary symbol back to the source input while recording its Boolean
value on the backup stack, or start the source decider when restoration ends.
-/
def restoreInputStatement
    (certificate : PolyTimeComputable id Computability.encodeBool predicate) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm)
      (State certificate.tm) :=
  -- Both pushes use the same buffered symbol, keeping source input and backup aligned.
  .pop .temporary
    (fun state symbol => { state with bufferedInput := symbol })
    (.branch (fun state => state.bufferedInput.isSome)
      (.push (.source certificate.tm.k₀)
        (fun state => state.bufferedInput.getD
          (certificate.inputAlphabet.invFun false))
        (.push .backup
          (fun state => certificate.inputAlphabet
            (state.bufferedInput.getD (certificate.inputAlphabet.invFun false)))
          (continueAt .restoreInput)))
      (continueAt (.source certificate.tm.main)))

/--
Read the source decider's Boolean result. Acceptance halts with the saved input;
rejection transfers control to the explicit backup-replacement phase.
-/
def readDecisionStatement
    (certificate : PolyTimeComputable id Computability.encodeBool predicate) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm)
      (State certificate.tm) :=
  -- Certified source executions produce one bit; `none` is unreachable on this path.
  .pop (.source certificate.tm.k₁)
    (fun state symbol => { state with
      flag := (symbol.map certificate.outputAlphabet).getD false })
    (.branch (fun state => state.flag)
      (resetAndHalt certificate.tm)
      (continueAt .clearBackup))

/--
Delete one saved-input bit per iteration. Once the backup is empty, write the
declared rejection output and halt in the canonical final configuration.
-/
def clearBackupStatement
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm)
      (State certificate.tm) :=
  -- `flag` is true exactly when `pop` removed a bit, so only an empty stack exits.
  .pop .backup (fun state symbol => { state with flag := symbol.isSome })
    (.branch (fun state => state.flag)
      (continueAt .clearBackup)
      (pushReversedBits certificate.tm rejectionOutput.reverse
        (resetAndHalt certificate.tm)))

/--
The wrapper program copies the input, executes the source decider, and returns
the copy on acceptance. Rejection explicitly clears the copy and writes
`rejectionOutput`.
-/
def program
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) :
    Label certificate.tm →
      Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm)
        (State certificate.tm)
  | .copyToTemporary => copyToTemporaryStatement certificate
  | .restoreInput => restoreInputStatement certificate
  | .source label => embedStatement certificate.tm (certificate.tm.m label)
  | .readDecision => readDecisionStatement certificate
  | .clearBackup => clearBackupStatement certificate rejectionOutput

/-- The finite multitape wrapper computing conditional identity. -/
def machine
    (certificate : PolyTimeComputable id Computability.encodeBool predicate)
    (rejectionOutput : BitString) : Turing.FinTM2 where
  K := Stack certificate.tm
  k₀ := .source certificate.tm.k₀
  k₁ := .backup
  Γ := Alphabet certificate.tm
  Λ := Label certificate.tm
  main := .copyToTemporary
  σ := State certificate.tm
  initialState := initialState certificate.tm
  Γk₀Fin := by simpa [Alphabet] using certificate.tm.Γk₀Fin
  m := program certificate rejectionOutput

end ConditionalIdentity

end PolyTimeComputable

end ComplexityTheory
