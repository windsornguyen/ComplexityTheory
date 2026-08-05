/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PolyTime

/-!
# Pair-first polynomial-time composition machine

This finite wrapper decodes the first component of the canonical Arora--Barak
pair, restores that bit string as the input of an arbitrary certified source
machine, and then simulates the source. The wrapper charges the complete pair,
including the ignored second component.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

/-- Reuse the source certificate's finite stack index. -/
local instance sourceStackFintype (source : Turing.FinTM2) : Fintype source.K :=
  source.kFin

/-- Reuse the source certificate's finite program labels. -/
local instance sourceLabelFintype (source : Turing.FinTM2) : Fintype source.Λ :=
  source.ΛFin

/-- Reuse the source certificate's finite machine state. -/
local instance sourceStateFintype (source : Turing.FinTM2) : Fintype source.σ :=
  source.σFin

/-- Reuse the finite alphabet on the source input stack. -/
local instance sourceInputAlphabetFintype (source : Turing.FinTM2) :
    Fintype (source.Γ source.k₀) :=
  source.Γk₀Fin

/-- Source-machine stacks plus reversal scratch for the decoded first component. -/
inductive Stack (source : Turing.FinTM2) where
  | source (stack : source.K)
  | reverse
  deriving DecidableEq, Fintype

/-- Source stacks retain their alphabets; scratch stores source-input symbols. -/
abbrev Alphabet (source : Turing.FinTM2) : Stack source → Type
  | .source stack => source.Γ stack
  | .reverse => source.Γ source.k₀

/-- Pair decoding phases followed by the embedded source-machine labels. -/
inductive Label (source : Turing.FinTM2) where
  | readFirst
  | readSecond
  | clearSecond
  | restoreInput
  | source (label : source.Λ)
  deriving Fintype

/-- Finite wrapper state for source simulation and two buffered pair symbols. -/
structure State (source : Turing.FinTM2) where
  /-- State of the embedded source machine. -/
  sourceState : source.σ
  /-- First symbol buffered by the current parser transition. -/
  first : Option (source.Γ source.k₀)
  /-- Second symbol buffered for duplicate-or-delimiter recognition. -/
  second : Option (source.Γ source.k₀)
  deriving Fintype

/-- Reset parsing buffers while restoring the source's initial state. -/
def initialState (source : Turing.FinTM2) : State source :=
  ⟨source.initialState, none, none⟩

variable {function : BitString → Bool}

/-- Both buffered symbols exist and decode to the same bit. -/
def isDuplicate (certificate : PolyTimeComputable id Computability.encodeBool function) :
    State certificate.tm → Bool
  | ⟨_, some first, some second⟩ =>
      certificate.inputAlphabet first == certificate.inputAlphabet second
  | _ => false

/-- The buffered symbols decode to the reserved `01` delimiter. -/
def isDelimiter (certificate : PolyTimeComputable id Computability.encodeBool function) :
    State certificate.tm → Bool
  | ⟨_, some first, some second⟩ =>
      !certificate.inputAlphabet first && certificate.inputAlphabet second
  | _ => false

/-- Read the first buffered symbol on the branch where it is present. -/
def firstSymbol (certificate : PolyTimeComputable id Computability.encodeBool function) :
    State certificate.tm → certificate.tm.Γ certificate.tm.k₀
  | ⟨_, some first, _⟩ => first
  | _ => certificate.inputAlphabet.invFun false

private abbrev continueAt {source : Turing.FinTM2} (label : Label source) :
    Turing.TM2.Stmt (Alphabet source) (Label source) (State source) :=
  .goto fun _ => label

private abbrev resetAt (source : Turing.FinTM2) (label : Label source) :
    Turing.TM2.Stmt (Alphabet source) (Label source) (State source) :=
  .load (fun _ => initialState source) (continueAt label)

/-- Embed one source statement; source halt is wrapper halt. -/
def embedStatement (source : Turing.FinTM2) :
    Turing.TM2.Stmt source.Γ source.Λ source.σ →
      Turing.TM2.Stmt (Alphabet source) (Label source) (State source)
  | .push stack value next =>
      .push (.source stack) (fun state => value state.sourceState) (embedStatement source next)
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
  | .halt => .halt

/-- Read the first symbol of a duplicated bit or delimiter. -/
def readFirstStatement
    (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm) (State certificate.tm) :=
  .pop (.source certificate.tm.k₀)
    (fun state symbol => { state with first := symbol, second := none })
    (continueAt .readSecond)

/-- Decode a duplicated bit, recognize the delimiter, or reject malformed input. -/
def readSecondStatement
    (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm) (State certificate.tm) :=
  .pop (.source certificate.tm.k₀) (fun state symbol => { state with second := symbol })
    (.branch (isDuplicate certificate)
      (.push .reverse (firstSymbol certificate) (resetAt certificate.tm .readFirst))
      (.branch (isDelimiter certificate) (resetAt certificate.tm .clearSecond) .halt))

/-- Consume every symbol of the ignored second component. -/
def clearSecondStatement
    (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm) (State certificate.tm) :=
  .pop (.source certificate.tm.k₀)
    (fun state symbol => { state with first := symbol, second := none })
    (.branch (fun state => state.first.isSome)
      (resetAt certificate.tm .clearSecond) (resetAt certificate.tm .restoreInput))

/-- Restore the decoded first component, then enter the source machine. -/
def restoreInputStatement
    (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm) (State certificate.tm) :=
  .pop .reverse (fun state symbol => { state with first := symbol, second := none })
    (.branch (fun state => state.first.isSome)
      (.push (.source certificate.tm.k₀) (firstSymbol certificate)
        (resetAt certificate.tm .restoreInput))
      (resetAt certificate.tm (.source certificate.tm.main)))

/-- Dispatch pair decoding and source simulation. -/
def program (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Label certificate.tm →
      Turing.TM2.Stmt (Alphabet certificate.tm) (Label certificate.tm) (State certificate.tm)
  | .readFirst => readFirstStatement certificate
  | .readSecond => readSecondStatement certificate
  | .clearSecond => clearSecondStatement certificate
  | .restoreInput => restoreInputStatement certificate
  | .source label => embedStatement certificate.tm (certificate.tm.m label)

/-- The finite wrapper computing `function` on the first component of a pair. -/
def machine (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Turing.FinTM2 where
  K := Stack certificate.tm
  k₀ := .source certificate.tm.k₀
  k₁ := .source certificate.tm.k₁
  Γ := Alphabet certificate.tm
  Λ := Label certificate.tm
  main := .readFirst
  σ := State certificate.tm
  initialState := initialState certificate.tm
  Γk₀Fin := by simpa [Alphabet] using certificate.tm.Γk₀Fin
  m := program certificate

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
