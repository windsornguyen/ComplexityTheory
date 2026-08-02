/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.DecisionProblem
import Mathlib.Computability.TuringMachine.Computable

/-!
# Deterministic polynomial time

Arora and Barak, *Computational Complexity: A Modern Approach*, January 2007
web draft, Definitions 1.19-1.20, p. 27 (PDF p. 43), define `DTIME` and the
class `P`. This module uses Mathlib's certified finite multitape Turing machines
and polynomial clocks to state the binary-language version directly.
-/

namespace ComplexityTheory

namespace BooleanFunction

/--
`function` decides `problem` when it returns true exactly on the language's
yes-instances. This is semantic correctness, independent of running time.
-/
def Decides (function : BooleanFunction) (problem : DecisionProblem) : Prop :=
  ∀ input, function input = true ↔ input ∈ problem

/-- Every Boolean function decides the language containing exactly its true inputs. -/
theorem decides_language (function : BooleanFunction) :
    function.Decides function.language :=
  fun input => (function.mem_language input).symm

end BooleanFunction

/--
A deterministic polynomial-time decider packages its Boolean function,
semantic correctness, and a Mathlib Turing-machine execution certificate.
-/
structure PolyTimeDecider (problem : DecisionProblem) where
  /-- The Boolean decision function. -/
  decide : BooleanFunction
  /-- The function accepts exactly the language's members. -/
  correct : decide.Decides problem
  /-- A finite multitape machine computes the decision within a polynomial clock. -/
  computesInPolyTime :
    Turing.TM2ComputableInPolyTime id Computability.encodeBool decide

namespace DecisionProblem

/-- A binary decision problem lies in `P` when it has a certified polynomial-time decider. -/
def IsInP (problem : DecisionProblem) : Prop :=
  Nonempty (PolyTimeDecider problem)

end DecisionProblem

namespace BooleanFunction

/--
A polynomial-time machine certificate places the function's accepted language
in `P`. The semantic correctness proof is supplied by `decides_language`.
-/
theorem language_isInP (function : BooleanFunction)
    (computesInPolyTime :
      Turing.TM2ComputableInPolyTime id Computability.encodeBool function) :
    function.language.IsInP :=
  ⟨{
    decide := function
    correct := function.decides_language
    computesInPolyTime
  }⟩

end BooleanFunction

namespace ComplexityClass

/--
`P` is the set of binary decision problems decidable by deterministic Turing
machines within a polynomial number of Mathlib TM2 steps.
-/
def P : Set DecisionProblem :=
  {problem | problem.IsInP}

/-- Membership in `P` is exactly certified deterministic polynomial-time decidability. -/
theorem mem_P_iff (problem : DecisionProblem) :
    problem ∈ P ↔ problem.IsInP :=
  Iff.rfl

end ComplexityClass

end ComplexityTheory
