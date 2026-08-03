/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.Diagonal

/-!
# Clock-bounded indexed diagonalization

This module adds the runtime boundary omitted by the semantic indexed
diagonal construction. A machine supplies an initial configuration, one
transition, and a halted-output observer. `runFor` is derived by structural
recursion on its allowance, so the bound denotes actual machine transitions.
`ComputesWithin` states that one index returns a translation's exact output
before the allowance determined by the input length.

```text
clock input.length
        |
        v
runFor allowance index input
        | some proof             | none
        v                        v
translated proof           explicit timeout proof
```

The timeout proof is an explicit parameter because the diagonal proof map is
total. It is not used when `ComputesWithin` holds.

Mathlib contributors, *Mathlib*, 2026, v4.32.1,
`Nat.Partrec.Code.evaln` in `Mathlib.Computability.PartrecCode` bounds
intermediate natural-number values rather than execution steps. The discussion
in `Mathlib.Computability.TuringMachine.ToPartrec` says its code interpreter is
polynomial-time but does not prove that bound. Consequently, this module states
the clocked-machine contract without claiming that the pinned Mathlib source
already supplies its polynomial-time instantiation.
-/

namespace ComplexityTheory
namespace SyntacticDiagonal

/--
A clocked translation machine gives every indexed program a common
configuration type and deterministic one-step semantics. It does not assume
universality or any bound on the overhead of interpreting an index.
-/
structure ClockedTranslationMachine (Index : Type) where
  /-- Runtime configurations shared by all indexed programs. -/
  Configuration : Type
  /-- The exact binary representation used for program indices. -/
  indexEncoding : BinaryEncoding Index
  /-- Every accepted index payload is its decoded index's canonical encoding. -/
  eq_indexEncoding_encode_of_decode_eq_some : ∀ {payload index},
    indexEncoding.decode payload = some index → payload = indexEncoding.encode index
  /-- Construct the initial configuration for an indexed program and input. -/
  initial : Index → BitString → Configuration
  /-- Advance one deterministic machine transition. -/
  step : Configuration → Configuration
  /-- Return the translated proof exactly when the configuration has halted. -/
  output : Configuration → Option BitString

namespace ClockedTranslationMachine

/--
Run a configuration for at most `allowance` transitions. A halted
configuration returns immediately; exhausting the allowance while still
running returns `none`.
-/
def runFrom {Index : Type} (machine : ClockedTranslationMachine Index) :
    Nat → machine.Configuration → Option BitString
  | 0, configuration => machine.output configuration
  | allowance + 1, configuration =>
      match machine.output configuration with
      | some proof => some proof
      | none => machine.runFrom allowance (machine.step configuration)

/-- Initialize an indexed program and run it for at most the supplied transitions. -/
def runFor {Index : Type} (machine : ClockedTranslationMachine Index)
    (allowance : Nat) (index : Index) (input : BitString) : Option BitString :=
  machine.runFrom allowance (machine.initial index input)

/--
`index` computes `translation` within `clock` when every input returns the
exact translated proof under the allowance determined by its length. In plain
language, this is the no-timeout correctness certificate for one program.
-/
def ComputesWithin {Index : Type} (machine : ClockedTranslationMachine Index)
    (clock : Nat → Nat) (index : Index) (translation : BitString → BitString) : Prop :=
  ∀ input, machine.runFor (clock input.length) index input = some (translation input)

/--
Totalize a clocked machine into the family consumed by semantic
diagonalization. Successful runs return their output; timeouts return the
declared `timeoutProof`. The index codec is preserved exactly.
-/
def toIndexedFamily {Index : Type} (machine : ClockedTranslationMachine Index)
    (clock : Nat → Nat) (timeoutProof : BitString) : IndexedTranslationFamily Index where
  translate index input :=
    match machine.runFor (clock input.length) index input with
    | some proof => proof
    | none => timeoutProof
  encodeIndex := machine.indexEncoding.encode
  decodeIndex := machine.indexEncoding.decode
  decode_encode := machine.indexEncoding.decode_encode
  eq_encode_of_decode_eq_some := machine.eq_indexEncoding_encode_of_decode_eq_some

/-- A successful clocked run becomes the corresponding totalized translation output. -/
@[simp]
theorem toIndexedFamily_translate_of_success {Index : Type}
    (machine : ClockedTranslationMachine Index) (clock : Nat → Nat)
    (timeoutProof : BitString) (index : Index) (input output : BitString)
    (hRun : machine.runFor (clock input.length) index input = some output) :
    (machine.toIndexedFamily clock timeoutProof).translate index input = output := by
  simp [toIndexedFamily, hRun]

/-- A timed-out run takes the declared, visible timeout branch. -/
@[simp]
theorem toIndexedFamily_translate_of_timeout {Index : Type}
    (machine : ClockedTranslationMachine Index) (clock : Nat → Nat)
    (timeoutProof : BitString) (index : Index) (input : BitString)
    (hRun : machine.runFor (clock input.length) index input = none) :
    (machine.toIndexedFamily clock timeoutProof).translate index input = timeoutProof := by
  simp [toIndexedFamily, hRun]

/--
If an index computes a translation within the clock, totalization preserves
that translation as a function. Thus the timeout branch cannot alter any
input covered by the certificate.
-/
theorem toIndexedFamily_translate_eq_of_computesWithin {Index : Type}
    (machine : ClockedTranslationMachine Index) (clock : Nat → Nat)
    (timeoutProof : BitString) (index : Index) (translation : BitString → BitString)
    (hComputes : machine.ComputesWithin clock index translation) :
    (machine.toIndexedFamily clock timeoutProof).translate index = translation := by
  funext input
  exact machine.toIndexedFamily_translate_of_success clock timeoutProof index input
    (translation input) (hComputes input)

end ClockedTranslationMachine

/--
Build the semantic diagonal system from a clocked machine. Ordinary proofs
retain the source range, while indexed proofs run only for the declared clock
before the explicit timeout branch is selected.
-/
def clockedDiagonalSystem {Index : Type} (source : TautologyProofSystem)
    (wrapper : TautologyWrapper) (machine : ClockedTranslationMachine Index)
    (clock : Nat → Nat) (timeoutProof : BitString) (rejection : Tautology) :
    TautologyProofSystem :=
  indexedDiagonalSystem source wrapper (machine.toIndexedFamily clock timeoutProof) rejection

/--
No output-preserving translation from the clocked diagonal system into
`source` can be computed by `index` within the declared clock. Evaluating that
candidate on its own indexed input would equate an output with its
fixed-point-free wrapping.
-/
theorem proofTranslation_not_computedWithin {Index : Type}
    (source : TautologyProofSystem) (wrapper : TautologyWrapper)
    (machine : ClockedTranslationMachine Index) (clock : Nat → Nat)
    (timeoutProof : BitString) (rejection : Tautology)
    (candidate : ProofTranslation
      (clockedDiagonalSystem source wrapper machine clock timeoutProof rejection) source)
    (index : Index) :
    ¬machine.ComputesWithin clock index candidate.translate := by
  intro hComputes
  let family := machine.toIndexedFamily clock timeoutProof
  have hTranslation : family.translate index = candidate.translate :=
    machine.toIndexedFamily_translate_eq_of_computesWithin
      clock timeoutProof index candidate.translate hComputes
  apply indexedTranslationFails source wrapper family rejection index
  rw [hTranslation]
  simpa [clockedDiagonalSystem, family] using
    candidate.preserves (diagonalInput family index)

/--
There is no proof translation into `source` whose function is represented by
any machine index within the fixed clock. This is the clock-bounded semantic
jump theorem; it does not yet assert that the constructed proof map itself is
polynomial-time.
-/
theorem not_exists_translation_computedWithin {Index : Type}
    (source : TautologyProofSystem) (wrapper : TautologyWrapper)
    (machine : ClockedTranslationMachine Index) (clock : Nat → Nat)
    (timeoutProof : BitString) (rejection : Tautology) :
    ¬∃ candidate : ProofTranslation
        (clockedDiagonalSystem source wrapper machine clock timeoutProof rejection) source,
      ∃ index, machine.ComputesWithin clock index candidate.translate := by
  rintro ⟨candidate, index, hComputes⟩
  exact proofTranslation_not_computedWithin source wrapper machine clock timeoutProof
    rejection candidate index hComputes

end SyntacticDiagonal
end ComplexityTheory
