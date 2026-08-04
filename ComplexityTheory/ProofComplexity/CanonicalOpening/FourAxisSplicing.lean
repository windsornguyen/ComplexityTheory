/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Checksum.Finite
import ComplexityTheory.ProofComplexity.CanonicalOpening.FiniteStrategy
import Mathlib.Tactic.DeriveFintype

/-!
# A four-axis response-splicing counterexample

This finite experiment groups a `2 x 2 x 2 x 2` binary tensor into four
two-axis block contractions. A global branch checks a three-symbol Hamming
syndrome and the claimed top contraction. Local branches open individual
blocks. Because the two branches do not bind their responses to one common
word, a false claim has a perfect spliced strategy.

The result refutes only this separated-response grammar. It does not refute a
protocol with a binding commitment or a genuine proximity test. Robert W.
Hamming, "Error Detecting and Error Correcting Codes," *Bell System Technical
Journal* 29(2), 1950, Section 3, pp. 150--154, supplies the checksum pattern.
-/

namespace ComplexityTheory
namespace CanonicalOpening
namespace FourAxisSplicing

open scoped BigOperators

/-- One pair of binary tensor axes, encoded lexicographically. -/
abbrev PairIndex := Fin 4

/-- A four-axis binary tensor, represented as two paired axes. -/
abbrev Tensor := PairIndex → PairIndex → BinaryField

/-- The four contractions obtained after summing over the inner axis pair. -/
abbrev BlockWord := PairIndex → BinaryField

/-- The three-symbol syndrome committed before the verifier challenge. -/
abbrev Syndrome := Fin 3 → BinaryField

/-- Contract one two-axis block of a four-axis tensor. -/
def blockContraction (tensor : Tensor) (block : PairIndex) : BinaryField :=
  ∑ inner, tensor block inner

/-- Materialize the four canonical block contractions. -/
def blockWord (tensor : Tensor) : BlockWord :=
  blockContraction tensor

/-- Contract all four axes by summing the canonical block word. -/
def tensorContraction (tensor : Tensor) : BinaryField :=
  ∑ block, blockWord tensor block

/--
The first four nonzero binary Hamming columns. Its kernel contains the odd
word `(1, 1, 1, 0)`, which drives the finite counterexample.
-/
def checksumMatrix : Matrix (Fin 3) PairIndex BinaryField :=
  !![1, 0, 1, 0; 0, 1, 1, 0; 0, 0, 0, 1]

/-- The concrete checksum uniquely binds every word within Hamming radius one. -/
theorem checksumMatrix_isUnique :
    IsUniqueDecodingChecksum 1 checksumMatrix.mulVec :=
  (checkUniqueDecodingChecksum_eq_true_iff 1 checksumMatrix.mulVec).mp (by decide)

/-- A parent claims the total contraction of one canonical four-axis tensor. -/
structure Parent where
  /-- The canonical tensor being opened. -/
  tensor : Tensor
  /-- The prover's claimed top contraction. -/
  claimed : BinaryField

/-- Decide whether a parent carries the canonical total contraction. -/
def parentTrue (parent : Parent) : Bool :=
  parent.claimed == tensorContraction parent.tensor

/-- A child claims one canonical two-axis block contraction. -/
structure ChildClaim where
  /-- The canonical tensor inherited from the parent. -/
  tensor : Tensor
  /-- The outer axis pair selecting the child block. -/
  block : PairIndex
  /-- The claimed contraction of the selected inner axis pair. -/
  claimed : BinaryField

/-- Decide whether a child carries its canonical block contraction. -/
def childTrue (child : ChildClaim) : Bool :=
  child.claimed == blockContraction child.tensor child.block

/--
A prover commits to one syndrome, but may answer the global audit and local
openings with different block words. This is a strategy object, not one
transmitted message.
-/
structure Strategy where
  /-- The syndrome fixed before the challenge. -/
  commitment : Syndrome
  /-- The word used to satisfy the global checksum and top-value audit. -/
  globalResponse : BlockWord
  /-- The independently chosen answers used by local openings. -/
  localResponse : BlockWord
deriving Fintype

/-- Enumerate the five global-or-block challenges used by the finite checker. -/
local instance : Fintype (GlobalLocalChallenge PairIndex) :=
  derive_fintype% GlobalLocalChallenge PairIndex

/-- View the concrete prover as a generic separated-response strategy. -/
def Strategy.toSeparated (strategy : Strategy) :
    SeparatedResponseStrategy Syndrome BlockWord PairIndex BinaryField where
  commitment := strategy.commitment
  globalResponse := strategy.globalResponse
  localResponse := strategy.localResponse

/-- The global branch checks the committed syndrome and claimed top value. -/
def globalStep (parent : Parent) (commitment : Syndrome) (response : BlockWord) :
    OpeningStepResult ChildClaim :=
  if checksumMatrix.mulVec response = commitment ∧
      ∑ block, response block = parent.claimed then .accept else .reject

/-- A local branch emits one two-axis claim without binding it to the global word. -/
def openingStep (parent : Parent) (_commitment : Syndrome)
    (block : PairIndex) (response : BinaryField) : OpeningStepResult ChildClaim :=
  .child ⟨parent.tensor, block, response⟩

/-- Execute the separated global-or-local challenge. -/
def run (parent : Parent) (strategy : Strategy) :
    GlobalLocalChallenge PairIndex → OpeningStepResult ChildClaim :=
  strategy.toSeparated.run (globalStep parent) (openingStep parent)

/-- The all-zero tensor with the false claimed contraction one. -/
def falseParent : Parent :=
  ⟨fun _ _ => 0, 1⟩

/-- The odd checksum-kernel word used only on the global branch. -/
def kernelWord : BlockWord :=
  ![1, 1, 1, 0]

/-- The global response has the same checksum as the canonical zero word. -/
@[simp] theorem checksum_kernelWord : checksumMatrix.mulVec kernelWord = 0 := by
  decide

/-- The global response has the falsely claimed total contraction one. -/
@[simp] theorem sum_kernelWord : ∑ block, kernelWord block = 1 := by
  decide

/-- A spliced strategy uses the kernel word globally and canonical zeros locally. -/
def cheatingStrategy : Strategy where
  commitment := 0
  globalResponse := kernelWord
  localResponse := 0

/-- The selected parent claim is false. -/
@[simp] theorem falseParent_isFalse : parentTrue falseParent = false := by
  decide

/-- The explicit spliced strategy survives every global and local challenge. -/
theorem cheatingStrategy_isPerfect :
    IsPerfectOneStepStrategy childTrue (run falseParent) cheatingStrategy := by
  apply (SeparatedResponseStrategy.safeForEveryChallenge_iff
    childTrue (globalStep falseParent) (openingStep falseParent)
    cheatingStrategy.toSeparated).2
  decide

set_option maxRecDepth 10000 in
/-- Exhaustive evaluation confirms that the false parent admits a perfect strategy. -/
@[simp] theorem checker_findsCheatingStrategy :
    hasCheatingOneStepStrategy parentTrue childTrue run falseParent = true := by
  decide

end FourAxisSplicing
end CanonicalOpening
end ComplexityTheory
