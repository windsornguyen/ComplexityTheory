/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.Data.Nat.Basic

/-!
# Product barrier for repeated local-slice opening

This module covers the restricted grammar in which every round selects one of
`branching` uniform slices and carries the selected slice forward unchanged.
It does not cover checksum, polynomial, or proximity arguments that identify a
different compressed child.
-/

namespace ComplexityTheory
namespace CanonicalOpening

/--
After `rounds` uniform localizations, the parent mass is the number of possible
challenge paths times the remaining child mass. Bounding both branching and
child mass by one budget bounds the parent by `budget^(rounds + 1)`.
-/
theorem repeatedLocalSlice_parentMass_le_budgetPower
    {parentMass branching rounds childMass budget : Nat}
    (hShape : parentMass = branching ^ rounds * childMass)
    (hBranching : branching ≤ budget) (hChild : childMass ≤ budget) :
    parentMass ≤ budget ^ (rounds + 1) := by
  rw [hShape]
  calc
    branching ^ rounds * childMass ≤ budget ^ rounds * budget :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hBranching rounds) hChild
    _ = budget ^ (rounds + 1) := by
      rw [← Nat.pow_succ, Nat.succ_eq_add_one]

/--
For parent mass `2^(m^2)` and per-round budget `2^(C*m)`, repeated uniform
localization cannot bound both branching and final child mass by the budget
when `C * (rounds + 1) < m`. In particular, any fixed round count fails for all
sufficiently large `m`.
-/
theorem squareLogMass_not_boundedBy_constantRoundLocalSlices
    {constant scale rounds branching childMass : Nat}
    (hRounds : constant * (rounds + 1) < scale)
    (hShape : 2 ^ (scale * scale) = branching ^ rounds * childMass) :
    ¬(branching ≤ 2 ^ (constant * scale) ∧
      childMass ≤ 2 ^ (constant * scale)) := by
  intro hBounds
  have hBound := repeatedLocalSlice_parentMass_le_budgetPower
    hShape hBounds.1 hBounds.2
  have hScalePositive : 0 < scale := lt_of_le_of_lt (Nat.zero_le _) hRounds
  have hExponent : (constant * scale) * (rounds + 1) < scale * scale := by
    calc
      (constant * scale) * (rounds + 1) =
          (constant * (rounds + 1)) * scale := by ac_rfl
      _ < scale * scale := (Nat.mul_lt_mul_right hScalePositive).2 hRounds
  have hStrict :
      (2 ^ (constant * scale)) ^ (rounds + 1) < 2 ^ (scale * scale) := by
    rw [← Nat.pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hExponent
  exact (Nat.not_lt_of_ge hBound) hStrict

end CanonicalOpening
end ComplexityTheory
