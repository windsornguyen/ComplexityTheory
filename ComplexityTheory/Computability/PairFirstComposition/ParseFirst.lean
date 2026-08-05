/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition.Simulation

/-!
# First-component parsing for pair-first composition

The source input alphabet is only equivalent to `Bool`, so canonical pair bits
must first be transported through that equivalence. This phase proves the exact
trace that decodes duplicated first-component bits through the `01` delimiter.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- Encode external bits in the source machine's designated input alphabet. -/
def encodedBits
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (bits : BitString) : List (certificate.tm.Γ certificate.tm.k₀) :=
  bits.map certificate.inputAlphabet.invFun

/-- Package one verified transition with its unit upper bound. -/
def oneStepEvaluation
    {state : Type} {transition : state → Option state} {start finish : state}
    (step_eq : transition start = some finish) :
    StateTransition.EvalsToInTime transition start (some finish) 1 where
  steps := 1
  evals_in_steps := step_eq
  steps_le_m := le_rfl

/-- Increase an execution bound without changing the certified trace. -/
def weakenEvaluation
    {state : Type} {transition : state → Option state} {start : state}
    {finish : Option state} {firstBound secondBound : Nat}
    (evaluation : StateTransition.EvalsToInTime transition start finish firstBound)
    (hBound : firstBound ≤ secondBound) :
    StateTransition.EvalsToInTime transition start finish secondBound where
  toEvalsTo := evaluation.toEvalsTo
  steps_le_m := evaluation.steps_le_m.trans hBound

/-- Reading the first pair component reaches witness clearing. -/
def evaluatesReadFirst
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (first second : BitString)
    (reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    StateTransition.EvalsToInTime (machine certificate).step
      (configuration certificate .readFirst (initialState certificate.tm)
        (encodedBits certificate (BitString.pair first second)) reverse)
      (some (configuration certificate .clearSecond (initialState certificate.tm)
        (encodedBits certificate second)
        ((encodedBits certificate first).reverseAux reverse)))
      (2 * first.length + 2) := by
  induction first generalizing reverse with
  | nil =>
      have firstStep := oneStepEvaluation
        (step_readFirst_cons certificate (inputSymbol certificate false)
          (inputSymbol certificate true :: encodedBits certificate second) reverse)
      have secondStep := oneStepEvaluation
        (step_readSecond_delimiter certificate (encodedBits certificate second) reverse)
      simpa [encodedBits, inputSymbol] using StateTransition.EvalsToInTime.trans
        (machine certificate).step 1 1
        (configuration certificate .readFirst (initialState certificate.tm)
          (inputSymbol certificate false :: inputSymbol certificate true ::
            encodedBits certificate second) reverse)
        (configuration certificate .readSecond
          { initialState certificate.tm with first := some (inputSymbol certificate false) }
          (inputSymbol certificate true :: encodedBits certificate second) reverse)
        (some (configuration certificate .clearSecond (initialState certificate.tm)
          (encodedBits certificate second) reverse))
        firstStep secondStep
  | cons bit remaining inductionHypothesis =>
      have firstStep := oneStepEvaluation
        (step_readFirst_cons certificate (inputSymbol certificate bit)
          (inputSymbol certificate bit ::
            encodedBits certificate (BitString.pair remaining second)) reverse)
      have secondStep := oneStepEvaluation
        (step_readSecond_duplicate certificate bit
          (encodedBits certificate (BitString.pair remaining second)) reverse)
      have firstTwo := StateTransition.EvalsToInTime.trans
        (machine certificate).step 1 1
        (configuration certificate .readFirst (initialState certificate.tm)
          (inputSymbol certificate bit :: inputSymbol certificate bit ::
            encodedBits certificate (BitString.pair remaining second)) reverse)
        (configuration certificate .readSecond
          { initialState certificate.tm with first := some (inputSymbol certificate bit) }
          (inputSymbol certificate bit ::
            encodedBits certificate (BitString.pair remaining second)) reverse)
        (some (configuration certificate .readFirst (initialState certificate.tm)
          (encodedBits certificate (BitString.pair remaining second))
          (inputSymbol certificate bit :: reverse)))
        firstStep secondStep
      have remainingSteps := inductionHypothesis (inputSymbol certificate bit :: reverse)
      have combined := StateTransition.EvalsToInTime.trans (machine certificate).step
        2 (2 * remaining.length + 2)
        (configuration certificate .readFirst (initialState certificate.tm)
          (encodedBits certificate (BitString.pair (bit :: remaining) second)) reverse)
        (configuration certificate .readFirst (initialState certificate.tm)
          (encodedBits certificate (BitString.pair remaining second))
          (inputSymbol certificate bit :: reverse))
        (some (configuration certificate .clearSecond (initialState certificate.tm)
          (encodedBits certificate second)
          ((encodedBits certificate remaining).reverseAux
            (inputSymbol certificate bit :: reverse))))
        (by simpa [encodedBits, inputSymbol] using firstTwo) remainingSteps
      simpa [encodedBits, inputSymbol, List.reverseAux] using weakenEvaluation combined
        (secondBound := 2 * (bit :: remaining).length + 2) (by simp; omega)

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
