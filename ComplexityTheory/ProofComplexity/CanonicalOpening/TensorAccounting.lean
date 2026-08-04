/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.LocalSliceBarrier

/-!
# Accounting barrier for unbatched tensor opening

This module isolates a no-go result for the audited winner-compiler certificate.
If each of `t` sequential tensor-axis rounds multiplies the cost exponent by at
least two, then the final exponent cannot fit below the parent exponent `t`.
This does not rule out a different compiler or a batched protocol.
-/

namespace ComplexityTheory
namespace CanonicalOpening

private theorem rounds_le_twoPow (rounds : Nat) : rounds ≤ 2 ^ rounds := by
  induction rounds with
  | zero => simp
  | succ rounds inductionHypothesis =>
      calc
        rounds + 1 ≤ 2 ^ rounds + 1 := Nat.add_le_add_right inductionHypothesis 1
        _ ≤ 2 ^ rounds + 2 ^ rounds := Nat.add_le_add_left Nat.one_le_two_pow _
        _ = 2 ^ (rounds + 1) := by rw [Nat.pow_succ]; omega

/--
An exponent amplified by at least two in every sequential round is never
smaller than the number of rounds.
-/
theorem unbatchedTensorOpening_not_clockClosing
    {amplification rounds : Nat} (hAmplification : 2 ≤ amplification) :
    ¬amplification ^ rounds < rounds := by
  have hPower : 2 ^ rounds ≤ amplification ^ rounds :=
    Nat.pow_le_pow_left hAmplification rounds
  exact Nat.not_lt_of_ge (le_trans (rounds_le_twoPow rounds) hPower)

/--
For axis length greater than one, the unbatched winner cost
`axisLength^(amplification^rounds)` is not below the parent mass
`axisLength^rounds` when `amplification ≥ 2`.
-/
theorem unbatchedTensorOpening_winnerCost_not_lt_parentMass
    {axisLength amplification rounds : Nat}
    (hAxisLength : 1 < axisLength) (hAmplification : 2 ≤ amplification) :
    ¬axisLength ^ (amplification ^ rounds) < axisLength ^ rounds := by
  intro hCost
  have hExponent : amplification ^ rounds < rounds :=
    (Nat.pow_lt_pow_iff_right hAxisLength).mp hCost
  exact unbatchedTensorOpening_not_clockClosing hAmplification hExponent

end CanonicalOpening
end ComplexityTheory
