/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.BinaryString

/-!
# Self-delimiting natural-number encoding

A terminated-unary prefix code for natural numbers. It extends Mathlib's unary
encoding with one false terminator, allowing a decoder to recover one number
and leave the remaining bits untouched.
-/

namespace ComplexityTheory

namespace NatPrefixCode

/--
Encode `value` as `value` true bits followed by one false terminator. The
terminator makes the code self-delimiting inside a larger bitstring.
-/
def encode (value : Nat) : BitString :=
  Computability.unaryEncodeNat value ++ [false]

/--
Decode one terminated-unary prefix and return the unused suffix. A bitstring
containing only true bits is malformed because it has no terminator.
-/
def decodePrefix? : BitString → Option (Nat × BitString)
  | [] => none
  | false :: suffix => some (0, suffix)
  | true :: bits => do
      let (value, suffix) ← decodePrefix? bits
      some (value + 1, suffix)

/--
Decode exactly one natural number. Unlike `decodePrefix?`, this rejects every
nonempty trailing suffix.
-/
def decode? (bits : BitString) : Option Nat :=
  match decodePrefix? bits with
  | some (value, []) => some value
  | _ => none

/--
An encoded natural occupies exactly one bit per unary unit plus its terminator.
This equation is the accounting rule used by larger encodings.
-/
@[simp] theorem length_encode (value : Nat) :
    (encode value).length = value + 1 := by
  have unaryLength : (Computability.unaryEncodeNat value).length = value := by
    simpa [Computability.unaryDecodeNat] using
      Computability.unary_decode_encode_nat value
  simp [encode, unaryLength]

/--
Prefix decoding reverses encoding without consuming a caller-provided suffix.
This is the compositional round-trip property needed by token decoders.
-/
@[simp] theorem decodePrefix?_encode_append (value : Nat) (suffix : BitString) :
    decodePrefix? (encode value ++ suffix) = some (value, suffix) := by
  induction value with
  | zero => simp [encode, Computability.unaryEncodeNat, decodePrefix?]
  | succ value ih =>
      simp only [encode, Computability.unaryEncodeNat, List.cons_append, decodePrefix?]
      rw [show decodePrefix? (Computability.unaryEncodeNat value ++ [false] ++ suffix) =
        some (value, suffix) by simpa [encode] using ih]
      rfl

/--
Every successful prefix decoding identifies the bits it consumed as the
canonical encoding of the returned natural number. The unconsumed suffix is
preserved exactly.
-/
theorem eq_encode_append_of_decodePrefix?_eq_some
    {bits : BitString} {value : Nat} {suffix : BitString}
    (hdecode : decodePrefix? bits = some (value, suffix)) :
    bits = encode value ++ suffix := by
  induction bits generalizing value suffix with
  | nil => simp [decodePrefix?] at hdecode
  | cons bit bits ih =>
    cases bit with
    | false =>
      simp only [decodePrefix?] at hdecode
      cases hdecode
      rfl
    | true =>
      simp only [decodePrefix?] at hdecode
      cases hrest : decodePrefix? bits with
      | none => simp [hrest] at hdecode
      | some result =>
        rcases result with ⟨restValue, restSuffix⟩
        simp only [hrest] at hdecode
        rcases hdecode with ⟨rfl, rfl⟩
        rw [ih hrest]
        simp [encode, Computability.unaryEncodeNat, List.append_assoc]

/--
Exact decoding reverses canonical encoding. In plain language, every natural
number survives an encode-decode round trip.
-/
@[simp] theorem decode?_encode (value : Nat) :
    decode? (encode value) = some value := by
  unfold decode?
  rw [show encode value = encode value ++ [] by simp, decodePrefix?_encode_append]

/--
A nonempty suffix makes an otherwise canonical code invalid for exact
decoding. This prevents two adjacent objects from being mistaken for one.
-/
theorem decode?_encode_append_eq_none (value : Nat)
    {suffix : BitString} (hsuffix : suffix ≠ []) :
    decode? (encode value ++ suffix) = none := by
  unfold decode?
  rw [decodePrefix?_encode_append]
  simp [hsuffix]

/--
An unterminated run of true bits is rejected. The decoder therefore fails
closed on truncated codes rather than inventing a value.
-/
@[simp] theorem decodePrefix?_unaryEncodeNat (value : Nat) :
    decodePrefix? (Computability.unaryEncodeNat value) = none := by
  induction value with
  | zero => rfl
  | succ value ih => simp [Computability.unaryEncodeNat, decodePrefix?, ih]

/-- The terminated-unary functions form a Mathlib-compatible binary encoding. -/
def encoding : BinaryEncoding Nat where
  encode := encode
  decode := decode?
  decode_encode := decode?_encode

/-- Canonical terminated-unary encodings are unambiguous. -/
theorem encode_injective : Function.Injective encode :=
  encoding.encode_injective

end NatPrefixCode

end ComplexityTheory
