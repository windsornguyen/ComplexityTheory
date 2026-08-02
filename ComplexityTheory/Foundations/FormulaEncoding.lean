/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.FormulaEncoding.Stream

/-!
# Canonical binary encoding of Boolean formulas

A formula is serialized as a self-delimiting token count followed by its
postfix tokens. The count frames the stream, stack reconstruction validates its
shape, and exact decoding rejects every trailing bit.
-/

namespace ComplexityTheory

namespace BooleanFormulaCode

/--
Decode exactly `count` token prefixes and return the unused suffix. Failure
means the bitstring ended early or contained a malformed token.
-/
def decodeTokens? : Nat → BitString → Option (List Token × BitString)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (token, rest) ← Token.decodePrefix? bits
      let (stream, suffix) ← decodeTokens? count rest
      some (token :: stream, suffix)

/--
Canonically encode a Boolean formula. The token-count prefix makes the
variable-length postfix payload self-delimiting inside a larger bitstring.
-/
def encode (formula : BooleanFormula) : BitString :=
  NatPrefixCode.encode (tokens formula).length ++
    (tokens formula).flatMap Token.encode

/--
Decode one complete formula prefix and return the unused suffix. Both token
syntax and postfix stack shape are validated before a formula is returned.
-/
def decodePrefix? (bits : BitString) : Option (BooleanFormula × BitString) := do
  let (count, rest) ← NatPrefixCode.decodePrefix? bits
  let (stream, suffix) ← decodeTokens? count rest
  let formula ← build? stream
  some (formula, suffix)

/--
Decode exactly one Boolean formula. A valid prefix followed by any additional
bit is rejected rather than silently truncating the input.
-/
def decode? (bits : BitString) : Option BooleanFormula :=
  match decodePrefix? bits with
  | some (formula, []) => some formula
  | _ => none

/--
Fixed-count token decoding reverses concatenated token encodings without
consuming a caller-provided suffix.
-/
@[simp] theorem decodeTokens?_flatMap_encode_append
    (stream : List Token) (suffix : BitString) :
    decodeTokens? stream.length (stream.flatMap Token.encode ++ suffix) =
      some (stream, suffix) := by
  induction stream with
  | nil => simp [decodeTokens?]
  | cons token stream ih =>
      simp [decodeTokens?, ih, List.append_assoc]

/--
Prefix decoding reverses formula encoding and preserves the supplied suffix.
This is the compositional round-trip property of the whole wire format.
-/
@[simp] theorem decodePrefix?_encode_append
    (formula : BooleanFormula) (suffix : BitString) :
    decodePrefix? (encode formula ++ suffix) = some (formula, suffix) := by
  unfold decodePrefix?
  simp only [encode, List.append_assoc, NatPrefixCode.decodePrefix?_encode_append]
  dsimp
  rw [decodeTokens?_flatMap_encode_append]
  dsimp
  rw [build?_tokens]
  rfl

/-- Every Boolean formula survives an exact encode-decode round trip. -/
@[simp] theorem decode?_encode (formula : BooleanFormula) :
    decode? (encode formula) = some formula := by
  unfold decode?
  rw [show encode formula = encode formula ++ [] by simp, decodePrefix?_encode_append]

/-- Canonical formula encodings are injective, so one code names at most one formula. -/
theorem encode_injective : Function.Injective encode := by
  intro left right heq
  have hleft := decode?_encode left
  have hright := decode?_encode right
  rw [heq] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

/--
Exact decoding rejects nonempty trailing data after a canonical formula code.
This distinguishes one complete object from a valid prefix of a larger input.
-/
theorem decode?_encode_append_eq_none
    (formula : BooleanFormula) {suffix : BitString} (hsuffix : suffix ≠ []) :
    decode? (encode formula ++ suffix) = none := by
  unfold decode?
  rw [decodePrefix?_encode_append]
  simp [hsuffix]

/--
The exact code length is the framed node count plus every encoded token cost.
This equation exposes all representation overhead for later runtime bounds.
-/
@[simp] theorem length_encode (formula : BooleanFormula) :
    (encode formula).length =
      formula.size + 1 + ((tokens formula).map Token.codeLength).sum := by
  simp [encode, List.length_flatMap]

/-- The formula codec satisfies Mathlib's reusable binary-encoding interface. -/
def encoding : BinaryEncoding BooleanFormula where
  encode := encode
  decode := decode?
  decode_encode := decode?_encode

end BooleanFormulaCode

end ComplexityTheory
