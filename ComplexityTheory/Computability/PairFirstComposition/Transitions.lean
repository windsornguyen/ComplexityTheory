/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition.Stacks

/-!
# Pair-first composition parser transitions

These equations cover canonical duplicated bits, the reserved `01` delimiter,
complete witness consumption, and restoration of the decoded first component.
Malformed pair codes deliberately receive no semantic theorem.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- Represent one external bit in the source machine's input alphabet. -/
def inputSymbol
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (bit : Bool) : certificate.tm.Γ certificate.tm.k₀ :=
  certificate.inputAlphabet.invFun bit

/-- Reading the first symbol buffers it and advances to second-symbol reading. -/
theorem step_readFirst_cons
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (head : certificate.tm.Γ certificate.tm.k₀)
    (remaining reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .readFirst (initialState certificate.tm)
          (head :: remaining) reverse) =
      some (configuration certificate .readSecond
        { initialState certificate.tm with first := some head }
        remaining reverse) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    readFirstStatement, configuration]
  simp only [wrapperStacks_source, initList_inputStack,
    List.head?_cons, List.tail_cons]
  simp [update_initList_inputStack]
  congr

/-- A duplicated encoded bit emits one decoded symbol onto reversal scratch. -/
theorem step_readSecond_duplicate
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (bit : Bool) (remaining reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .readSecond
          { initialState certificate.tm with first := some (inputSymbol certificate bit) }
          (inputSymbol certificate bit :: remaining) reverse) =
      some (configuration certificate .readFirst (initialState certificate.tm)
        remaining (inputSymbol certificate bit :: reverse)) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    readSecondStatement, configuration]
  simp only [wrapperStacks_source, initList_inputStack,
    List.head?_cons, List.tail_cons]
  cases bit <;>
    simp [isDuplicate, isDelimiter, firstSymbol, inputSymbol, initialState,
      update_initList_inputStack] <;> congr

/-- The reserved encoded `01` pair transfers control to witness clearing. -/
theorem step_readSecond_delimiter
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (second reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .readSecond
          { initialState certificate.tm with first := some (inputSymbol certificate false) }
          (inputSymbol certificate true :: second) reverse) =
      some (configuration certificate .clearSecond (initialState certificate.tm)
        second reverse) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    readSecondStatement, configuration]
  simp only [wrapperStacks_source, initList_inputStack,
    List.head?_cons, List.tail_cons]
  simp [isDuplicate, isDelimiter, inputSymbol, initialState,
    update_initList_inputStack]
  congr

/-- Witness clearing consumes one source-alphabet symbol. -/
theorem step_clearSecond_cons
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (head : certificate.tm.Γ certificate.tm.k₀)
    (remaining reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .clearSecond (initialState certificate.tm)
          (head :: remaining) reverse) =
      some (configuration certificate .clearSecond (initialState certificate.tm)
        remaining reverse) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    clearSecondStatement, configuration]
  simp only [wrapperStacks_source, initList_inputStack,
    List.head?_cons, List.tail_cons]
  simp [initialState, update_initList_inputStack]
  congr

/-- Empty witness input advances to first-component restoration. -/
theorem step_clearSecond_nil
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .clearSecond (initialState certificate.tm) [] reverse) =
      some (configuration certificate .restoreInput (initialState certificate.tm) [] reverse) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    clearSecondStatement, configuration]
  simp only [wrapperStacks_source, initList_inputStack,
    List.head?, List.tail]
  simp [initialState, update_initList_inputStack]
  congr

/-- Restoration moves one scratch symbol back onto the source input stack. -/
theorem step_restoreInput_cons
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (restored : List (certificate.tm.Γ certificate.tm.k₀))
    (head : certificate.tm.Γ certificate.tm.k₀)
    (remaining : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .restoreInput (initialState certificate.tm)
          restored (head :: remaining)) =
      some (configuration certificate .restoreInput (initialState certificate.tm)
        (head :: restored) remaining) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    restoreInputStatement, configuration]
  simp only [wrapperStacks_reverse, List.head?_cons, List.tail_cons]
  simp [firstSymbol, initialState, initList_inputStack,
    update_initList_inputStack]
  congr

/-- Empty scratch enters the source machine with the restored canonical input. -/
theorem step_restoreInput_nil
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (restored : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).step
        (configuration certificate .restoreInput (initialState certificate.tm) restored []) =
      some (embeddedConfiguration certificate (Turing.initList certificate.tm restored)) := by
  change Turing.TM2.step (program certificate) _ = _
  simp only [Turing.TM2.step, Turing.TM2.stepAux, program,
    restoreInputStatement, configuration]
  simp only [wrapperStacks_reverse, List.head?, List.tail]
  simp [embeddedConfiguration, embeddedLabel, Turing.initList, initialState]
  congr

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
