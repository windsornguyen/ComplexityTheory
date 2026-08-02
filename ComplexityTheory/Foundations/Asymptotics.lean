/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic notation

The Big-O convention from Arora and Barak, *Computational Complexity: A Modern
Approach*, January 2007 web draft, Definition 1.2, p. 14 (PDF p. 30), expressed
using Mathlib's canonical filter-based asymptotic relation.
-/

namespace ComplexityTheory

open Asymptotics Filter

/--
A natural-number resource bound indexed by input length. For example,
`cost n` may be the maximum number of machine steps on inputs of length `n`.
-/
abbrev CostFunction := Nat → Nat

namespace CostFunction

/--
View a natural-number cost function as real-valued. This preserves every value
while making Mathlib's norm-based asymptotic relations available.
-/
def toReal (cost : CostFunction) : Nat → Real :=
  fun inputLength ↦ cost inputLength

/--
`cost` is eventually bounded by a positive constant multiple of `bound`.
Formally, one constant works for every input length beyond one threshold;
informally, `bound` controls the long-run growth of `cost`.

This is Big-O as defined by Arora and Barak (January 2007 web draft,
Definition 1.2, p. 14; PDF p. 30).
-/
def IsEventuallyBoundedBy (cost bound : CostFunction) : Prop :=
  ∃ constant : Real, 0 < constant ∧ ∃ threshold : Nat,
    ∀ inputLength ≥ threshold,
      (cost inputLength : Real) ≤ constant * (bound inputLength : Real)

/--
Mathlib's Big-O relation at `atTop` is equivalent to the textbook predicate
`IsEventuallyBoundedBy`. This bridge lets later proofs use Mathlib's Big-O
calculus while retaining explicit constants and thresholds when needed.
-/
theorem isBigO_iff_eventuallyBoundedBy (cost bound : CostFunction) :
    toReal cost =O[atTop] toReal bound ↔ IsEventuallyBoundedBy cost bound := by
  simp only [Asymptotics.isBigO_iff', Filter.eventually_atTop, Real.norm_natCast,
    toReal, IsEventuallyBoundedBy]

end CostFunction

end ComplexityTheory
