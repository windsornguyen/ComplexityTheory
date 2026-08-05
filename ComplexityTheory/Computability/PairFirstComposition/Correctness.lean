/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition.Clock

/-!
# Polynomial-time correctness of pair-first composition

The wrapper parses the complete canonical pair, restores the first component,
and then runs the supplied source certificate. This discharges the specialized
composition obligation needed for the textbook proof that `P` is contained in
`NP`.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- Mathlib initialization agrees with the displayed parser configuration. -/
theorem initList_machine
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (input : List (certificate.tm.Γ certificate.tm.k₀)) :
    Turing.initList (machine certificate) input =
      configuration certificate .readFirst (initialState certificate.tm) input [] := by
  simp only [machine, initialState, Turing.initList, configuration,
    eq_mpr_eq_cast]
  congr
  funext stack
  cases stack with
  | source sourceStack =>
      by_cases h : sourceStack = certificate.tm.k₀
      · subst sourceStack
        simp [wrapperStacks]
      · simp [wrapperStacks, h]
  | reverse => simp [wrapperStacks]

/-- The wrapper computes the source function on the first pair component. -/
noncomputable def computesInPolyTime
    (certificate : PolyTimeComputable id Computability.encodeBool function) :
    PolyTimeComputable BitString.pairEncoding.encode Computability.encodeBool
      (fun pair : BitString × BitString => function pair.1) where
  tm := machine certificate
  inputAlphabet := certificate.inputAlphabet
  outputAlphabet := certificate.outputAlphabet
  time := compositionClock certificate
  outputsFun pair := by
    obtain ⟨first, second⟩ := pair
    unfold Turing.TM2OutputsInTime
    change StateTransition.EvalsToInTime (machine certificate).step
      (Turing.initList (machine certificate)
        (encodedBits certificate (BitString.pair first second)))
      (some (Turing.haltList (machine certificate)
        (List.map certificate.outputAlphabet.invFun
          (Computability.encodeBool (function first)))))
      ((compositionClock certificate).eval (BitString.pair first second).length)
    rw [initList_machine]
    have parsingSteps := evaluatesCanonicalPairParsing certificate first second
    have sourceEvaluation : StateTransition.EvalsToInTime certificate.tm.step
        (Turing.initList certificate.tm (encodedBits certificate first))
        (some (Turing.haltList certificate.tm
          (List.map certificate.outputAlphabet.invFun
            (Computability.encodeBool (function first)))))
        (certificate.time.eval first.length) := by
      have sourceCertificate := certificate.outputsFun first
      unfold Turing.TM2OutputsInTime at sourceCertificate
      simpa [encodedBits] using sourceCertificate
    have sourceSteps := embeddedEvaluation certificate (certificate.time.eval first.length)
      (Turing.initList certificate.tm (encodedBits certificate first))
      (Turing.haltList certificate.tm
        (List.map certificate.outputAlphabet.invFun
          (Computability.encodeBool (function first))))
      sourceEvaluation
    rw [embedded_haltList] at sourceSteps
    have combined := StateTransition.EvalsToInTime.trans (machine certificate).step
      (3 * first.length + second.length + 4) (certificate.time.eval first.length)
      (configuration certificate .readFirst (initialState certificate.tm)
        (encodedBits certificate (BitString.pair first second)) [])
      (embeddedConfiguration certificate
        (Turing.initList certificate.tm (encodedBits certificate first)))
      (some (Turing.haltList (machine certificate)
        (List.map certificate.outputAlphabet.invFun
          (Computability.encodeBool (function first)))))
      parsingSteps sourceSteps
    exact weakenEvaluation combined (totalExecutionTime_le_clock certificate first second)

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
