/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.FormulaEncoding

/-!
# Prefix restrictions of Boolean formulas

A binary prefix fixes variables `x_0, ..., x_(k-1)` while leaving every later
variable free. Restriction preserves evaluation under the corresponding
assignment and never enlarges the canonical binary representation.
-/

namespace ComplexityTheory

namespace BooleanAssignment

/--
Override an assignment with a finite prefix. Index `i` receives the `i`th
prefix bit when present and otherwise keeps the original assignment value.
-/
def withPrefix (fixed : BitString) (assignment : BooleanAssignment) :
    BooleanAssignment := fun index =>
  match fixed[index]? with
  | some value => value
  | none => assignment index

end BooleanAssignment

namespace BooleanFormula

/-- Convert one truth value into the corresponding constant formula. -/
def ofBool : Bool → BooleanFormula
  | false => .fls
  | true => .tru

/--
Fix every variable whose index occurs in `prefix`. The formula tree keeps the
same shape; only assigned variable leaves become Boolean constants.
-/
def restrictPrefix (fixed : BitString) : BooleanFormula → BooleanFormula
  | .var index =>
      match fixed[index]? with
      | some value => ofBool value
      | none => .var index
  | .tru => .tru
  | .fls => .fls
  | .neg formula => .neg (restrictPrefix fixed formula)
  | .conj left right => .conj (restrictPrefix fixed left) (restrictPrefix fixed right)
  | .disj left right => .disj (restrictPrefix fixed left) (restrictPrefix fixed right)

/-- Evaluating a Boolean constant returns the truth value used to construct it. -/
@[simp] theorem eval_ofBool (assignment : BooleanAssignment) (value : Bool) :
    eval assignment (ofBool value) = value := by
  cases value <;> rfl

/--
Evaluation after syntactic restriction equals evaluation under the overridden
assignment. This is the semantic contract used by SAT self-reduction.
-/
@[simp] theorem eval_restrictPrefix (fixed : BitString)
    (assignment : BooleanAssignment) (formula : BooleanFormula) :
    eval assignment (restrictPrefix fixed formula) =
      eval (BooleanAssignment.withPrefix fixed assignment) formula := by
  induction formula with
  | var index =>
      cases h : fixed[index]? with
      | none => simp [restrictPrefix, BooleanAssignment.withPrefix, h, eval]
      | some value => cases value <;> simp [restrictPrefix, BooleanAssignment.withPrefix, h, eval]
  | tru => rfl
  | fls => rfl
  | neg formula ih => simp [restrictPrefix, eval, ih]
  | conj left right ihLeft ihRight => simp [restrictPrefix, eval, ihLeft, ihRight]
  | disj left right ihLeft ihRight => simp [restrictPrefix, eval, ihLeft, ihRight]

/-- Restriction changes variable leaves into constants without changing tree size. -/
@[simp] theorem size_restrictPrefix (fixed : BitString) (formula : BooleanFormula) :
    size (restrictPrefix fixed formula) = size formula := by
  induction formula with
  | var index =>
      cases h : fixed[index]? with
      | none => simp [restrictPrefix, h, size]
      | some value => cases value <;> simp [restrictPrefix, h, ofBool, size]
  | tru => rfl
  | fls => rfl
  | neg formula ih => simp [restrictPrefix, size, ih]
  | conj left right ihLeft ihRight => simp [restrictPrefix, size, ihLeft, ihRight]
  | disj left right ihLeft ihRight => simp [restrictPrefix, size, ihLeft, ihRight]

/--
A restricted formula is satisfiable exactly when the original formula is true
under some assignment extending the fixed prefix.
-/
theorem isSatisfiable_restrictPrefix_iff (fixed : BitString) (formula : BooleanFormula) :
    IsSatisfiable (restrictPrefix fixed formula) ↔
      ∃ assignment, Satisfies (BooleanAssignment.withPrefix fixed assignment) formula := by
  simp [IsSatisfiable, Satisfies]

end BooleanFormula

namespace BooleanFormulaCode

/--
Prefix restriction never enlarges the canonical formula code. This guarantees
that a restricted formula can be padded back to its original encoded width.
-/
theorem length_encode_restrictPrefix_le (fixed : BitString) : ∀ formula : BooleanFormula,
    (encode (formula.restrictPrefix fixed)).length ≤ (encode formula).length := by
  intro formula
  rw [length_encode, length_encode, BooleanFormula.size_restrictPrefix]
  induction formula with
  | var index =>
      cases h : fixed[index]? with
      | none => simp [BooleanFormula.restrictPrefix, h, tokens, Token.codeLength]
      | some value =>
          cases value <;>
            simp [BooleanFormula.restrictPrefix, h, tokens, Token.codeLength,
              BooleanFormula.ofBool]
  | tru => simp [BooleanFormula.restrictPrefix]
  | fls => simp [BooleanFormula.restrictPrefix]
  | neg formula ih => simpa [BooleanFormula.restrictPrefix, tokens] using ih
  | conj left right ihLeft ihRight =>
      simp only [BooleanFormula.restrictPrefix, tokens, List.map_append, List.sum_append]
      omega
  | disj left right ihLeft ihRight =>
      simp only [BooleanFormula.restrictPrefix, tokens, List.map_append, List.sum_append]
      omega

end BooleanFormulaCode

end ComplexityTheory
