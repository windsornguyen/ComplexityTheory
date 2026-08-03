/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.Simulation

/-!
# The semantic kernel of indexed diagonalization

This module isolates the output contradiction behind a syntactic diagonal
proof-system construction. It does not assert that the indexed translation
family is enumerable, computable, or clock bounded. Those independent
obligations belong to later machine-level formalizations.

The construction has three visibly different input paths:

```text
false :: proof       -> source output
true :: encodedIndex -> wrapped source output from that indexed translation
malformed input      -> explicit rejection tautology
```

On the distinguished input carrying an index's own code, translation
correctness would equate an output with its fixed-point-free wrapping. The
final theorem packages exactly that contradiction and nothing stronger.
-/

namespace ComplexityTheory
namespace SyntacticDiagonal

/--
A syntactic wrapper preserves tautologies while changing every formula. The
first field protects proof-system soundness; the second creates the diagonal
output mismatch.
-/
structure TautologyWrapper where
  /-- Transform a formula into a syntactically different formula. -/
  wrap : BooleanFormula → BooleanFormula
  /-- Wrapping a tautology produces another tautology. -/
  preservesTautology : ∀ formula, formula.IsTautology → (wrap formula).IsTautology
  /-- No formula is a syntactic fixed point of the wrapper. -/
  fixedPointFree : ∀ formula, wrap formula ≠ formula

/--
Conjoining `true` preserves semantic truth while strictly increasing formula
size, so it supplies a concrete fixed-point-free tautology wrapper.
-/
def conjoinTrueWrapper : TautologyWrapper where
  wrap formula := .conj formula .tru
  preservesTautology formula hTautology assignment := by
    simpa [BooleanFormula.Satisfies, BooleanFormula.eval] using hTautology assignment
  fixedPointFree formula equality := by
    -- Syntactic equality is impossible because conjunction strictly increases size.
    have sizeEquality := congrArg BooleanFormula.size equality
    simp only [BooleanFormula.size] at sizeEquality
    omega

/--
An indexed family packages candidate proof-string translations with an exact
binary index codec. Canonical encodings round-trip, and every successful
decoding identifies the payload as that canonical encoding.
-/
structure IndexedTranslationFamily (Index : Type) where
  /-- The proof-string translation named by an index. -/
  translate : Index → BitString → BitString
  /-- Encode an index as the payload of a diagonal proof string. -/
  encodeIndex : Index → BitString
  /-- Decode an index payload, rejecting malformed payloads with `none`. -/
  decodeIndex : BitString → Option Index
  /-- The decoder recovers every encoded index exactly. -/
  decode_encode : ∀ index, decodeIndex (encodeIndex index) = some index
  /-- Every accepted payload is the canonical encoding of its decoded index. -/
  eq_encode_of_decode_eq_some : ∀ {payload index},
    decodeIndex payload = some index → payload = encodeIndex index

/--
The distinguished proof string for `index` is a true tag followed by its
encoded index. This is the input on which the indexed candidate is defeated.
-/
def diagonalInput {Index : Type} (family : IndexedTranslationFamily Index)
    (index : Index) : BitString :=
  true :: family.encodeIndex index

/--
Construct the semantic indexed diagonal system over `source`. False-tagged
inputs retain all source proofs. A valid true-tagged index wraps the source
output obtained from that indexed candidate; empty or invalid inputs return
the explicitly supplied rejected-proof output.
-/
def indexedDiagonalSystem {Index : Type} (source : TautologyProofSystem)
    (wrapper : TautologyWrapper) (family : IndexedTranslationFamily Index)
    (rejection : Tautology) : TautologyProofSystem where
  produce input :=
    match input with
    | [] => rejection.1
    | false :: proof => source.produce proof
    | true :: payload =>
        match family.decodeIndex payload with
        | none => rejection.1
        | some index => wrapper.wrap (source.produce (family.translate index input))
  sound input := by
    cases input with
    | nil => exact rejection.2
    | cons tag payload =>
        cases tag with
        -- Ordinary proofs delegate soundness directly to the source system.
        | false => exact source.sound payload
        | true =>
            cases hDecode : family.decodeIndex payload with
            -- Malformed indexed proofs take the explicit rejection path.
            | none => simpa [hDecode] using rejection.2
            | some index =>
                -- A valid indexed proof is sound because wrapping preserves tautologies.
                simpa [hDecode] using wrapper.preservesTautology
                  (source.produce (family.translate index (true :: payload)))
                  (source.sound (family.translate index (true :: payload)))
  complete formula hTautology := by
    obtain ⟨proof, hProof⟩ := source.complete formula hTautology
    -- The false tag embeds every source proof, so the wrapped system remains surjective.
    exact ⟨false :: proof, hProof⟩

/-- False-tagged inputs reproduce the corresponding source output exactly. -/
@[simp] theorem indexedDiagonalSystem_produce_ordinary {Index : Type}
    (source : TautologyProofSystem) (wrapper : TautologyWrapper)
    (family : IndexedTranslationFamily Index) (rejection : Tautology)
    (proof : BitString) :
    (indexedDiagonalSystem source wrapper family rejection).produce (false :: proof) =
      source.produce proof :=
  rfl

/-- A noncanonical true-tagged index takes the explicit rejection path. -/
@[simp] theorem indexedDiagonalSystem_produce_noncanonical {Index : Type}
    (source : TautologyProofSystem) (wrapper : TautologyWrapper)
    (family : IndexedTranslationFamily Index) (rejection : Tautology)
    (payload : BitString)
    (hNoncanonical : ∀ index, payload ≠ family.encodeIndex index) :
    (indexedDiagonalSystem source wrapper family rejection).produce (true :: payload) =
      rejection.1 := by
  unfold indexedDiagonalSystem
  cases hDecode : family.decodeIndex payload with
  | none => simp [hDecode]
  | some index => exact (hNoncanonical index (family.eq_encode_of_decode_eq_some hDecode)).elim

/--
The distinguished input for an index produces the wrapped output of that
index's candidate translation. This is the defining diagonal equation.
-/
@[simp] theorem indexedDiagonalSystem_produce_diagonal {Index : Type}
    (source : TautologyProofSystem) (wrapper : TautologyWrapper)
    (family : IndexedTranslationFamily Index) (rejection : Tautology)
    (index : Index) :
    (indexedDiagonalSystem source wrapper family rejection).produce
        (diagonalInput family index) =
      wrapper.wrap (source.produce (family.translate index (diagonalInput family index))) := by
  simp [indexedDiagonalSystem, diagonalInput, family.decode_encode]

/--
The candidate named by `index` cannot preserve the output of its distinguished
input from the diagonal system into `source`.
-/
theorem indexedTranslationFails {Index : Type} (source : TautologyProofSystem)
    (wrapper : TautologyWrapper) (family : IndexedTranslationFamily Index)
    (rejection : Tautology) (index : Index) :
    source.produce (family.translate index (diagonalInput family index)) ≠
      (indexedDiagonalSystem source wrapper family rejection).produce
        (diagonalInput family index) := by
  rw [indexedDiagonalSystem_produce_diagonal]
  exact (wrapper.fixedPointFree _).symm

/--
If the indexed family contains the function underlying every translation from
the diagonal system into `source`, then `source` has no such translation. This
is an extensional semantic result and makes no computability claim.
-/
theorem not_hasTranslationFrom_of_coversAllTranslations {Index : Type}
    (source : TautologyProofSystem) (wrapper : TautologyWrapper)
    (family : IndexedTranslationFamily Index) (rejection : Tautology)
    (covers : ∀ candidate : ProofTranslation
        (indexedDiagonalSystem source wrapper family rejection) source,
      ∃ index, candidate.translate = family.translate index) :
    ¬source.HasTranslationFrom (indexedDiagonalSystem source wrapper family rejection) := by
  rintro ⟨candidate⟩
  -- Coverage assigns the candidate's translation function its own diagonal index.
  obtain ⟨index, hIndex⟩ := covers candidate
  apply indexedTranslationFails source wrapper family rejection index
  rw [← hIndex]
  -- Translation correctness at that index's distinguished input closes the contradiction.
  exact candidate.preserves (diagonalInput family index)

end SyntacticDiagonal
end ComplexityTheory
