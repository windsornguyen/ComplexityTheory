/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition.ParseFirst

/-!
# Complete canonical-pair parsing

After locating the delimiter, the wrapper consumes the complete witness and
restores the decoded first component as the source input. The resulting bound
charges every symbol of the canonical pair, including the ignored witness.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- Witness clearing consumes the complete encoded second component. -/
def evaluatesClearSecond
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (second : BitString)
    (reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    StateTransition.EvalsToInTime (machine certificate).step
      (configuration certificate .clearSecond (initialState certificate.tm)
        (encodedBits certificate second) reverse)
      (some (configuration certificate .restoreInput (initialState certificate.tm) [] reverse))
      (second.length + 1) := by
  induction second with
  | nil =>
      simpa [encodedBits] using oneStepEvaluation
        (step_clearSecond_nil certificate reverse)
  | cons bit remaining inductionHypothesis =>
      have firstStep := oneStepEvaluation
        (step_clearSecond_cons certificate (inputSymbol certificate bit)
          (encodedBits certificate remaining) reverse)
      simpa [encodedBits, inputSymbol] using StateTransition.EvalsToInTime.trans
        (machine certificate).step 1 (remaining.length + 1)
        (configuration certificate .clearSecond (initialState certificate.tm)
          (inputSymbol certificate bit :: encodedBits certificate remaining) reverse)
        (configuration certificate .clearSecond (initialState certificate.tm)
          (encodedBits certificate remaining) reverse)
        (some (configuration certificate .restoreInput (initialState certificate.tm) [] reverse))
        firstStep inductionHypothesis

/-- Restoration moves every scratch symbol onto the source input stack. -/
def evaluatesRestoreInput
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (restored reverse : List (certificate.tm.Γ certificate.tm.k₀)) :
    StateTransition.EvalsToInTime (machine certificate).step
      (configuration certificate .restoreInput (initialState certificate.tm) restored reverse)
      (some (embeddedConfiguration certificate
        (Turing.initList certificate.tm (reverse.reverseAux restored))))
      (reverse.length + 1) := by
  induction reverse generalizing restored with
  | nil =>
      simpa using oneStepEvaluation (step_restoreInput_nil certificate restored)
  | cons head remaining inductionHypothesis =>
      have firstStep := oneStepEvaluation
        (step_restoreInput_cons certificate restored head remaining)
      have remainingSteps := inductionHypothesis (head :: restored)
      simpa [List.reverseAux] using StateTransition.EvalsToInTime.trans
        (machine certificate).step 1 (remaining.length + 1)
        (configuration certificate .restoreInput (initialState certificate.tm)
          restored (head :: remaining))
        (configuration certificate .restoreInput (initialState certificate.tm)
          (head :: restored) remaining)
        (some (embeddedConfiguration certificate
          (Turing.initList certificate.tm (remaining.reverseAux (head :: restored)))))
        firstStep remainingSteps

/-- Canonical parsing enters the source machine on exactly the first component. -/
def evaluatesCanonicalPairParsing
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (first second : BitString) :
    StateTransition.EvalsToInTime (machine certificate).step
      (configuration certificate .readFirst (initialState certificate.tm)
        (encodedBits certificate (BitString.pair first second)) [])
      (some (embeddedConfiguration certificate
        (Turing.initList certificate.tm (encodedBits certificate first))))
      (3 * first.length + second.length + 4) := by
  have readSteps := evaluatesReadFirst certificate first second []
  have clearSteps := evaluatesClearSecond certificate second
    ((encodedBits certificate first).reverseAux [])
  have restoreSteps := evaluatesRestoreInput certificate []
    ((encodedBits certificate first).reverseAux [])
  have readThenClear := StateTransition.EvalsToInTime.trans (machine certificate).step
    (2 * first.length + 2) (second.length + 1)
    (configuration certificate .readFirst (initialState certificate.tm)
      (encodedBits certificate (BitString.pair first second)) [])
    (configuration certificate .clearSecond (initialState certificate.tm)
      (encodedBits certificate second) ((encodedBits certificate first).reverseAux []))
    (some (configuration certificate .restoreInput (initialState certificate.tm) []
      ((encodedBits certificate first).reverseAux [])))
    readSteps clearSteps
  have combined := StateTransition.EvalsToInTime.trans (machine certificate).step
    (second.length + 1 + (2 * first.length + 2))
    (((encodedBits certificate first).reverseAux []).length + 1)
    (configuration certificate .readFirst (initialState certificate.tm)
      (encodedBits certificate (BitString.pair first second)) [])
    (configuration certificate .restoreInput (initialState certificate.tm) []
      ((encodedBits certificate first).reverseAux []))
    (some (embeddedConfiguration certificate (Turing.initList certificate.tm
      (((encodedBits certificate first).reverseAux []).reverseAux []))))
    readThenClear restoreSteps
  simpa [encodedBits] using weakenEvaluation combined
    (secondBound := 3 * first.length + second.length + 4) (by
      simp [encodedBits]
      omega)

/-- Parsing time is at most twice the complete canonical pair length. -/
theorem parsingTime_le_twice_pair_length (first second : BitString) :
    3 * first.length + second.length + 4 ≤
      2 * (BitString.pair first second).length := by
  rw [BitString.length_pair]
  omega

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
