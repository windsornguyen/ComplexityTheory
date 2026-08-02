/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.FormulaEncoding
import ComplexityTheory.Foundations.DecisionProblem

/-!
# The propositional tautology language

Arora and Barak, *Computational Complexity: A Modern Approach*, January 2007
web draft, Example 2.23, p. 57 (PDF p. 73), define `TAUTOLOGY` as the Boolean
formulas satisfied by every assignment. Here the language contains their exact
canonical binary encodings, so malformed strings are not instances.
-/

namespace ComplexityTheory

/--
The semantic set of Boolean tautologies. A formula belongs exactly when every
assignment makes it true.
-/
def tautologyInstances : Set BooleanFormula :=
  {formula | formula.IsTautology}

/--
The binary language of canonical tautology codes. Only exact outputs of
`BooleanFormulaCode.encode` are members; malformed and trailing data are
excluded from the language.
-/
def tautologyLanguage : DecisionProblem :=
  BooleanFormulaCode.encoding.decisionProblem tautologyInstances

/--
A canonical formula code belongs to `tautologyLanguage` exactly when the
formula is a tautology.
-/
@[simp] theorem encode_mem_tautologyLanguage (formula : BooleanFormula) :
    BooleanFormulaCode.encode formula ∈ tautologyLanguage ↔ formula.IsTautology := by
  change BooleanFormulaCode.encoding.encode formula ∈
      BooleanFormulaCode.encoding.decisionProblem tautologyInstances ↔
    formula ∈ tautologyInstances
  exact BinaryEncoding.encode_mem_decisionProblem
    BooleanFormulaCode.encoding tautologyInstances formula

/--
A string rejected by the exact formula decoder cannot belong to the tautology
language. This makes malformed-input rejection explicit at the language
boundary.
-/
theorem not_mem_tautologyLanguage_of_decode_eq_none {bits : BitString}
    (hdecode : BooleanFormulaCode.decode? bits = none) :
    bits ∉ tautologyLanguage := by
  intro hmem
  change bits ∈ BooleanFormulaCode.encoding.encode '' tautologyInstances at hmem
  obtain ⟨formula, _, hencode⟩ := hmem
  subst bits
  change BooleanFormulaCode.decode? (BooleanFormulaCode.encode formula) = none at hdecode
  simp at hdecode

/-- A canonical formula code followed by nonempty trailing data is not a TAUT instance. -/
theorem encode_append_not_mem_tautologyLanguage
    (formula : BooleanFormula) {suffix : BitString} (hsuffix : suffix ≠ []) :
    BooleanFormulaCode.encode formula ++ suffix ∉ tautologyLanguage :=
  not_mem_tautologyLanguage_of_decode_eq_none
    (BooleanFormulaCode.decode?_encode_append_eq_none formula hsuffix)

/--
A Boolean-valued decision procedure that agrees extensionally with semantic
tautologicity. This structure records correctness but no machine or runtime
certificate.
-/
structure TautologyDecider where
  /-- Return the proposed tautology decision. -/
  decide : BooleanFormula → Bool
  /-- The decision is true exactly for tautologies. -/
  correct : ∀ formula, decide formula = true ↔ formula.IsTautology

end ComplexityTheory
