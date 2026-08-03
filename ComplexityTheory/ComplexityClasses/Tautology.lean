/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ComplexityClasses.P
import ComplexityTheory.Foundations.Tautology

/-!
# Polynomial-time deciders for tautology

This module connects the canonical binary tautology language to semantic
formula decisions. It deliberately preserves the distinction between the
source machine certificate and the projected semantic decider.
-/

namespace ComplexityTheory

namespace PolyTimeDecider

/--
A certified polynomial-time decider for the binary tautology language induces
a correct semantic decider on formulas by deciding each canonical formula
code. The source `PolyTimeDecider` retains the runtime certificate; this
projection asserts only semantic correctness.
-/
def toTautologyDecider (decider : PolyTimeDecider tautologyLanguage) :
    TautologyDecider where
  decide formula := decider.decide (BooleanFormulaCode.encode formula)
  correct formula := by
    rw [decider.correct]
    exact encode_mem_tautologyLanguage formula

/--
The binary-language machine also computes the projected formula decision under
the canonical formula encoding. No machine composition occurs: the transported
certificate receives exactly the same input bits and emits the same Boolean
encoding as the source certificate.
-/
def toTautologyDeciderComputesInPolyTime
    (decider : PolyTimeDecider tautologyLanguage) :
    PolyTimeComputable BooleanFormulaCode.encode Computability.encodeBool
      decider.toTautologyDecider.decide :=
  PolyTimeComputable.transport decider.computesInPolyTime
    BooleanFormulaCode.encode (fun _ => rfl) (fun _ => rfl)

/-- The projected formula decision is the source decider applied to the canonical code. -/
@[simp] theorem toTautologyDecider_decide
    (decider : PolyTimeDecider tautologyLanguage) (formula : BooleanFormula) :
    decider.toTautologyDecider.decide formula =
      decider.decide (BooleanFormulaCode.encode formula) :=
  rfl

end PolyTimeDecider

end ComplexityTheory
