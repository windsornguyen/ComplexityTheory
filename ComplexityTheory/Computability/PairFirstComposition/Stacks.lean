/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition

/-!
# Stack frames for pair-first composition

The wrapper preserves every source stack and adds one reversal stack for the
decoded first component. These equations isolate the dependent stack updates
used by the parser and by the embedded source-machine simulation.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- Combine all source stacks with reversal scratch. -/
def wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (reverse : List (source.Γ source.k₀)) :
    ∀ stack, List (Alphabet source stack)
  | .source stack => sourceStacks stack
  | .reverse => reverse

/-- Selecting a source index returns the corresponding source stack. -/
@[simp] theorem wrapperStacks_source (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (reverse : List (source.Γ source.k₀)) (stack : source.K) :
    wrapperStacks source sourceStacks reverse (.source stack) = sourceStacks stack :=
  rfl

/-- Selecting reversal scratch returns the decoded prefix in reverse order. -/
@[simp] theorem wrapperStacks_reverse (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (reverse : List (source.Γ source.k₀)) :
    wrapperStacks source sourceStacks reverse .reverse = reverse :=
  rfl

/-- The designated stack of `Turing.initList` contains exactly its input. -/
theorem initList_inputStack (source : Turing.FinTM2)
    (input : List (source.Γ source.k₀)) :
    (Turing.initList source input).stk source.k₀ = input := by
  simp [Turing.initList]

/-- Replacing the input stack of an initial configuration preserves its frame. -/
theorem update_initList_inputStack (source : Turing.FinTM2)
    (input replacement : List (source.Γ source.k₀)) :
    Function.update (Turing.initList source input).stk source.k₀ replacement =
      (Turing.initList source replacement).stk := by
  funext stack
  by_cases h : stack = source.k₀
  · subst stack
    simp [Turing.initList]
  · simp [Turing.initList, h]

/-- Updating one wrapped source stack changes no other wrapper stack. -/
@[simp] theorem update_source_wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (reverse : List (source.Γ source.k₀)) (stack : source.K)
    (value : List (source.Γ stack)) :
    Function.update (wrapperStacks source sourceStacks reverse) (.source stack) value =
      wrapperStacks source (Function.update sourceStacks stack value) reverse := by
  funext wrapperStack
  cases wrapperStack with
  | source other =>
      by_cases h : other = stack
      · subst other
        simp
      · simp [h]
  | reverse => simp

/-- Updating reversal scratch preserves all source stacks. -/
@[simp] theorem update_reverse_wrapperStacks (source : Turing.FinTM2)
    (sourceStacks : ∀ stack, List (source.Γ stack))
    (reverse value : List (source.Γ source.k₀)) :
    Function.update (wrapperStacks source sourceStacks reverse) .reverse value =
      wrapperStacks source sourceStacks value := by
  funext wrapperStack
  cases wrapperStack <;> simp [wrapperStacks]

/-- A displayed parser configuration with canonical untouched source stacks. -/
def configuration
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (label : Label certificate.tm) (state : State certificate.tm)
    (input reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    (machine certificate).Cfg where
  l := some label
  var := state
  stk := wrapperStacks certificate.tm (Turing.initList certificate.tm input).stk reverse

/-- Map source labels into wrapper labels while preserving source halting. -/
def embeddedLabel (source : Turing.FinTM2) : Option source.Λ → Option (Label source)
  | some label => some (.source label)
  | none => none

/-- Embed a source configuration with empty reversal scratch and cleared buffers. -/
def embeddedConfiguration
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (sourceConfiguration : certificate.tm.Cfg) : (machine certificate).Cfg where
  l := embeddedLabel certificate.tm sourceConfiguration.l
  var := { initialState certificate.tm with sourceState := sourceConfiguration.var }
  stk := wrapperStacks certificate.tm sourceConfiguration.stk []

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
