/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.BinaryString
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Computability.Language
import Mathlib.Data.Set.BoolIndicator

/-!
# Decision problems and languages

The identification of Boolean functions with languages from Arora and Barak,
*Computational Complexity: A Modern Approach*, January 2007 web draft,
Section 1.1.2, p. 13 (PDF p. 29), together with its independent-set example.
-/

namespace ComplexityTheory

/--
A binary language is a set of bitstrings, interpreted as the yes-instances of
a decision problem.
-/
abbrev DecisionProblem := Language Bool

/-- A Boolean function gives one yes-or-no answer for every binary input. -/
abbrev BooleanFunction := BitString → Bool

namespace BooleanFunction

/--
The language accepted by a Boolean function contains exactly the inputs on
which it returns true.
-/
def language (f : BooleanFunction) : DecisionProblem :=
  {x | f x = true}

/-- Membership in a function's language is the same proposition as the function returning true. -/
@[simp] theorem mem_language (f : BooleanFunction) (x : BitString) :
    x ∈ f.language ↔ f x = true :=
  Iff.rfl

end BooleanFunction

/--
Boolean functions and binary decision problems are extensionally equivalent.
This formalizes the convention that computing a Boolean function means
deciding its language.
-/
noncomputable def booleanFunctionEquivDecisionProblem :
    BooleanFunction ≃ DecisionProblem where
  toFun := BooleanFunction.language
  invFun := Set.boolIndicator
  left_inv f := by
    funext x
    cases h : f x <;> simp [BooleanFunction.language, Set.boolIndicator, h]
  right_inv language := by
    ext x
    exact (Set.mem_iff_boolIndicator language x).symm

namespace BinaryEncoding

/--
Encode semantic yes-instances as a binary decision problem. This separates the
mathematical predicate on objects from its concrete input representation.
-/
def decisionProblem {α : Type*} (encoding : BinaryEncoding α) (instances : Set α) :
    DecisionProblem :=
  encoding.encode '' instances

/-- A canonical code is accepted exactly when the object it encodes is a yes-instance. -/
@[simp] theorem encode_mem_decisionProblem {α : Type*} (encoding : BinaryEncoding α)
    (instances : Set α) (input : α) :
    encoding.encode input ∈ encoding.decisionProblem instances ↔ input ∈ instances := by
  constructor
  · rintro ⟨other, hother, hencode⟩
    exact encoding.encode_injective hencode ▸ hother
  · intro hinput
    exact ⟨input, hinput, rfl⟩

end BinaryEncoding

/-- A finite labeled graph records its vertex count and uses `Fin n` as the concrete vertex type. -/
abbrev FiniteSimpleGraph := Σ n : Nat, SimpleGraph (Fin n)

/-- An independent-set input pairs a finite graph with the requested minimum cardinality. -/
abbrev IndependentSetInput := FiniteSimpleGraph × Nat

/--
`graph` contains an independent vertex set with at least `minimumSize`
vertices. This names the semantic graph predicate independently of encoding.
-/
def ContainsIndependentSet {n : Nat} (graph : SimpleGraph (Fin n))
    (minimumSize : Nat) : Prop :=
  ∃ vertices : Finset (Fin n),
    minimumSize ≤ vertices.card ∧ graph.IsIndepSet vertices

/--
An independent-set input is a yes-instance when the graph contains an
independent vertex set at least as large as the requested bound.
-/
def independentSetInstances : Set IndependentSetInput :=
  {input | match input with
    | (⟨_, graph⟩, minimumSize) => ContainsIndependentSet graph minimumSize}

/-- The bundled independent-set predicate reduces to its familiar graph-theoretic statement. -/
@[simp] theorem mem_independentSetInstances (n k : Nat) (G : SimpleGraph (Fin n)) :
    (⟨n, G⟩, k) ∈ independentSetInstances ↔
      ∃ vertices : Finset (Fin n), k ≤ vertices.card ∧ G.IsIndepSet vertices :=
  Iff.rfl

/-- The independent-set language consists of canonical codes of semantic yes-instances. -/
def independentSetLanguage (encoding : BinaryEncoding IndependentSetInput) : DecisionProblem :=
  encoding.decisionProblem independentSetInstances

/--
An encoded graph instance is accepted exactly when it has a sufficiently large
independent set.
-/
@[simp] theorem encode_mem_independentSetLanguage
    (encoding : BinaryEncoding IndependentSetInput) (n k : Nat) (G : SimpleGraph (Fin n)) :
    encoding.encode (⟨n, G⟩, k) ∈ independentSetLanguage encoding ↔
      ∃ vertices : Finset (Fin n), k ≤ vertices.card ∧ G.IsIndepSet vertices := by
  simp [independentSetLanguage]

end ComplexityTheory
