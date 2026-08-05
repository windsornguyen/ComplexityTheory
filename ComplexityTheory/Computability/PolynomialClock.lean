/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PolyTime
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Explicit exponents for polynomial machine clocks

Mathlib's polynomial-time machine certificate carries a concrete polynomial
clock. This module converts that clock into one positive natural exponent and
one fixed coefficient while retaining a proved pointwise running-time bound.
-/

namespace ComplexityTheory
namespace PolynomialClock

/-- A positive monomial exponent strictly above the clock's natural degree. -/
def exponent (clock : Polynomial Nat) : Nat :=
  clock.natDegree + 1

/-- The sum of the clock coefficients, obtained by evaluating at one. -/
def coefficient (clock : Polynomial Nat) : Nat :=
  clock.eval 1

/-- Every extracted clock exponent is positive. -/
theorem exponent_pos (clock : Polynomial Nat) :
    0 < exponent clock := by
  simp [exponent]

/-- The clock's natural degree is strictly below its extracted exponent. -/
theorem natDegree_lt_exponent (clock : Polynomial Nat) :
    clock.natDegree < exponent clock := by
  simp [exponent]

/--
The extracted coefficient and exponent bound the polynomial clock pointwise.

Every natural coefficient is nonnegative. Each supported monomial is bounded
by `(inputLength + 1)^exponent`, and summing its coefficient pays exactly the
fixed factor `clock.eval 1`.
-/
theorem eval_le_coefficient_mul_pow (clock : Polynomial Nat) (inputLength : Nat) :
    clock.eval inputLength ≤
      coefficient clock * (inputLength + 1) ^ exponent clock := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    ∑ degree ∈ clock.support, clock.coeff degree * inputLength ^ degree ≤
        ∑ degree ∈ clock.support,
          clock.coeff degree * (inputLength + 1) ^ exponent clock := by
      apply Finset.sum_le_sum
      intro degree hDegree
      apply Nat.mul_le_mul_left
      exact (Nat.pow_le_pow_left (Nat.le_succ inputLength) degree).trans
        (Nat.pow_le_pow_right (Nat.succ_pos inputLength)
          ((clock.le_natDegree_of_mem_supp degree hDegree).trans
            (Nat.le_of_lt (natDegree_lt_exponent clock))))
    _ = coefficient clock * (inputLength + 1) ^ exponent clock := by
      rw [← Finset.sum_mul]
      simp [coefficient, Polynomial.eval_eq_sum, Polynomial.sum_def]

end PolynomialClock
end ComplexityTheory
