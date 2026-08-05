/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.PairFirstComposition.Parsing
import ComplexityTheory.Computability.PolynomialClock

/-!
# Polynomial clock for pair-first composition

The wrapper pays linear time to parse the complete pair, then runs the source
on the shorter first component. One explicit polynomial in the complete pair
length dominates both costs.
-/

namespace ComplexityTheory
namespace PolyTimeComputable
namespace PairFirstComposition

variable {function : BitString → Bool}

/-- A full-input clock covering pair parsing followed by source execution. -/
noncomputable def compositionClock
    (certificate : PolyTimeComputable id Computability.encodeBool function) :
    Polynomial Nat :=
  2 * Polynomial.X +
    Polynomial.C (PolynomialClock.coefficient certificate.time) *
      (Polynomial.X + 1) ^ PolynomialClock.exponent certificate.time

/-- The source clock on the first component is bounded by the full-pair monomial. -/
theorem sourceTime_le_pairMonomial
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (first second : BitString) :
    certificate.time.eval first.length ≤
      PolynomialClock.coefficient certificate.time *
        ((BitString.pair first second).length + 1) ^
          PolynomialClock.exponent certificate.time := by
  have firstLength_le_pairLength : first.length ≤ (BitString.pair first second).length := by
    rw [BitString.length_pair]
    omega
  calc
    certificate.time.eval first.length ≤
        PolynomialClock.coefficient certificate.time *
          (first.length + 1) ^ PolynomialClock.exponent certificate.time :=
      PolynomialClock.eval_le_coefficient_mul_pow certificate.time first.length
    _ ≤ PolynomialClock.coefficient certificate.time *
          ((BitString.pair first second).length + 1) ^
            PolynomialClock.exponent certificate.time := by
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_left (Nat.add_le_add_right firstLength_le_pairLength 1) _

/-- Parsing plus source execution fits the displayed composition clock. -/
theorem totalExecutionTime_le_clock
    (certificate : PolyTimeComputable id Computability.encodeBool function)
    (first second : BitString) :
    certificate.time.eval first.length +
        (3 * first.length + second.length + 4) ≤
      (compositionClock certificate).eval (BitString.pair first second).length := by
  have sourceBound := sourceTime_le_pairMonomial certificate first second
  have parsingBound := parsingTime_le_twice_pair_length first second
  simp only [compositionClock, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow]
  omega

end PairFirstComposition
end PolyTimeComputable
end ComplexityTheory
