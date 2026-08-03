/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.BinaryString
import Mathlib.Computability.TuringMachine.Computable

/-!
# Polynomial-time computation certificates

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Turing.TM2ComputableInPolyTime` in
`Mathlib.Computability.TuringMachine.Computable`, defines the finite multitape
machine and polynomial-clock certificate reused here.

In that version, generic polynomial-time TM2 composition is recorded only as
a `proof_wanted`, introduced by leanprover-community/mathlib4#7172. The
transport below neither assumes nor replaces that missing construction.

This module names the Mathlib TM2 certificate used throughout
ComplexityTheory and provides representation-preserving transport. Transport
does not compose or modify machines: it reuses one execution certificate when
the old and new semantic functions have identical encoded inputs and outputs.
-/

namespace ComplexityTheory

/--
A certificate that `function` is computed by a Mathlib finite multitape Turing
machine within a polynomial number of steps under the supplied encodings.
-/
abbrev PolyTimeComputable {input output : Type}
    (encodeInput : input → BitString) (encodeOutput : output → BitString)
    (function : input → output) :=
  Turing.TM2ComputableInPolyTime encodeInput encodeOutput function

namespace PolyTimeComputable

/--
Reuse a polynomial-time machine certificate under a new semantic
interpretation whose encoded inputs and outputs are pointwise unchanged. The
returned certificate contains the original machine and polynomial clock; only
the types used to describe its tape contents differ.
-/
def transport
    {sourceInput targetInput sourceOutput targetOutput : Type}
    {encodeSourceInput : sourceInput → BitString}
    {encodeTargetInput : targetInput → BitString}
    {encodeSourceOutput : sourceOutput → BitString}
    {encodeTargetOutput : targetOutput → BitString}
    {sourceFunction : sourceInput → sourceOutput}
    {targetFunction : targetInput → targetOutput}
    (certificate :
      PolyTimeComputable encodeSourceInput encodeSourceOutput sourceFunction)
    (mapInput : targetInput → sourceInput)
    (inputEncoding_eq : ∀ input,
      encodeSourceInput (mapInput input) = encodeTargetInput input)
    (outputEncoding_eq : ∀ input,
      encodeSourceOutput (sourceFunction (mapInput input)) =
        encodeTargetOutput (targetFunction input)) :
    PolyTimeComputable encodeTargetInput encodeTargetOutput targetFunction where
  toTM2ComputableAux := certificate.toTM2ComputableAux
  time := certificate.time
  outputsFun input := by
    simpa only [inputEncoding_eq input, outputEncoding_eq input] using
      certificate.outputsFun (mapInput input)

end PolyTimeComputable

end ComplexityTheory
