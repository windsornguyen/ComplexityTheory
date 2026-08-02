/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Boolean formulas

Tree syntax and semantics for Boolean formulas. Formula size counts tree nodes,
so repeated subformulas are counted repeatedly rather than shared as in a
Boolean circuit.
-/

namespace ComplexityTheory

/--
A total assignment maps every natural-number variable index to a truth value.
It is the environment in which Boolean formulas receive their meaning.
-/
abbrev BooleanAssignment := Nat → Bool

/--
Two assignments agree on a finite set when they give every variable in that
set the same value. Differences outside the set are deliberately ignored.
-/
def BooleanAssignment.AgreeOn (indices : Finset Nat)
    (first second : BooleanAssignment) : Prop :=
  ∀ index ∈ indices, first index = second index

/--
A Boolean formula represented as a tree of variables, constants, and logical
connectives. The explicit syntax lets later algorithms inspect and transform
formulas rather than treating them as opaque Boolean functions.
-/
inductive BooleanFormula where
  /-- The variable `x_i`. -/
  | var (i : Nat)
  /-- The constant true. -/
  | tru
  /-- The constant false. -/
  | fls
  /-- Negation. -/
  | neg (formula : BooleanFormula)
  /-- Conjunction. -/
  | conj (left right : BooleanFormula)
  /-- Disjunction. -/
  | disj (left right : BooleanFormula)
  deriving DecidableEq, Repr

namespace BooleanFormula

/--
Evaluate a Boolean formula under an assignment. This supplies the semantics
used by satisfiability and tautology.
-/
def eval (assignment : BooleanAssignment) : BooleanFormula → Bool
  | var i => assignment i
  | tru => true
  | fls => false
  | neg formula => !(eval assignment formula)
  | conj left right => eval assignment left && eval assignment right
  | disj left right => eval assignment left || eval assignment right

/--
The number of nodes in a formula tree. This is the formula-size measure used
by later resource bounds.
-/
def size : BooleanFormula → Nat
  | var _ | tru | fls => 1
  | neg formula => size formula + 1
  | conj left right | disj left right => size left + size right + 1

/--
The finite set of variables occurring in a formula. Variables outside this set
cannot affect evaluation.
-/
def vars : BooleanFormula → Finset Nat
  | var i => {i}
  | tru | fls => ∅
  | neg formula => vars formula
  | conj left right | disj left right => vars left ∪ vars right

/--
An assignment satisfies a formula exactly when evaluation returns true; in
plain language, the assignment makes the formula true.
-/
def Satisfies (assignment : BooleanAssignment) (formula : BooleanFormula) : Prop :=
  eval assignment formula = true

/--
A formula is satisfiable when some assignment satisfies it. Such an assignment
is a witness to satisfiability.
-/
def IsSatisfiable (formula : BooleanFormula) : Prop :=
  ∃ assignment, Satisfies assignment formula

/--
A formula is a tautology when every assignment satisfies it; its truth does
not depend on how its variables are assigned.
-/
def IsTautology (formula : BooleanFormula) : Prop :=
  ∀ assignment, Satisfies assignment formula

/--
Every formula tree contains at least one node. There is no empty formula.
-/
theorem one_le_size (formula : BooleanFormula) : 1 ≤ size formula := by
  cases formula <;> simp [size]

/--
Assignments that agree on every variable occurring in a formula evaluate it
identically. In plain language, variables absent from the formula do not
matter.
-/
theorem eval_eq_of_agree : ∀ (formula : BooleanFormula) {first second : BooleanAssignment},
    BooleanAssignment.AgreeOn (vars formula) first second →
      eval first formula = eval second formula := by
  intro formula
  induction formula with
  | var i =>
      intro first second agree
      exact agree i (Finset.mem_singleton_self i)
  | tru =>
      intros
      rfl
  | fls =>
      intros
      rfl
  | neg formula ih =>
      intro first second agree
      simp only [eval, ih agree]
  | conj left right ihLeft ihRight =>
      intro first second agree
      have agreeLeft : BooleanAssignment.AgreeOn (vars left) first second :=
        fun i hi ↦ agree i (Finset.mem_union_left _ hi)
      have agreeRight : BooleanAssignment.AgreeOn (vars right) first second :=
        fun i hi ↦ agree i (Finset.mem_union_right _ hi)
      simp only [eval, ihLeft agreeLeft, ihRight agreeRight]
  | disj left right ihLeft ihRight =>
      intro first second agree
      have agreeLeft : BooleanAssignment.AgreeOn (vars left) first second :=
        fun i hi ↦ agree i (Finset.mem_union_left _ hi)
      have agreeRight : BooleanAssignment.AgreeOn (vars right) first second :=
        fun i hi ↦ agree i (Finset.mem_union_right _ hi)
      simp only [eval, ihLeft agreeLeft, ihRight agreeRight]

end BooleanFormula

end ComplexityTheory
