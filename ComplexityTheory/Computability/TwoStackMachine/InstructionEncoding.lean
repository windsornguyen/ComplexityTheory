/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.TwoStackMachine
import ComplexityTheory.Foundations.NatEncoding

/-!
# Binary encoding of two-stack instructions

This module gives canonical prefix codes for the fields of a binary two-stack
instruction. Successful decoding identifies the exact bits consumed, so the
later program decoder cannot accept aliases for the same instruction.

The two-bit instruction tags are `00` for halt, `01` for push, and `10` for
pop; `11` is reserved and rejected. Stack selectors occupy one bit. Control
labels use the self-delimiting natural-number code and are accepted only when
their value is below the program's declared label count.
-/

namespace ComplexityTheory
namespace TwoStackMachine
namespace StackCode

/-- Encode the primary stack as `0` and the auxiliary stack as `1`. -/
def encode : Stack → Bool
  | .primary => false
  | .auxiliary => true

/-- Decode the unique stack represented by one bit. -/
def decode : Bool → Stack
  | false => .primary
  | true => .auxiliary

/-- The one-bit stack code round-trips exactly. -/
@[simp] theorem decode_encode (stack : Stack) : decode (encode stack) = stack := by
  cases stack <;> rfl

end StackCode

namespace LabelCode

/-- Encode a valid control label by its self-delimiting natural value. -/
def encode {labelCount : Nat} (label : Fin labelCount) : BitString :=
  NatPrefixCode.encode label.val

/--
Decode one control-label prefix. Values outside the declared label range are
malformed and are rejected instead of being reduced modulo `labelCount`.
-/
def decodePrefix? (labelCount : Nat) (bits : BitString) :
    Option (Fin labelCount × BitString) := do
  let (value, suffix) ← NatPrefixCode.decodePrefix? bits
  if hValid : value < labelCount then
    some (⟨value, hValid⟩, suffix)
  else
    none

/-- No control label can be decoded from an empty bitstring. -/
@[simp] theorem decodePrefix?_empty (labelCount : Nat) : decodePrefix? labelCount [] = none := rfl

/-- Decoding a valid encoded label recovers it and preserves the supplied suffix. -/
@[simp] theorem decodePrefix?_encode_append {labelCount : Nat}
    (label : Fin labelCount) (suffix : BitString) :
    decodePrefix? labelCount (encode label ++ suffix) = some (label, suffix) := by
  simp [decodePrefix?, encode, label.isLt]

/-- A natural value outside the label range is rejected rather than wrapped. -/
theorem decodePrefix?_outOfRange {labelCount value : Nat}
    (hInvalid : labelCount ≤ value) (suffix : BitString) :
    decodePrefix? labelCount (NatPrefixCode.encode value ++ suffix) = none := by
  simp [decodePrefix?, Nat.not_lt.mpr hInvalid]

end LabelCode

namespace InstructionCode

/--
Encode one instruction as a prefix-free constructor tag followed by its stack,
bit, and valid-label fields in constructor order.
-/
def encode {labelCount : Nat} : Instruction (Fin labelCount) → BitString
  | .halt => [false, false]
  | .push stack bit next =>
      [false, true, StackCode.encode stack, bit] ++ LabelCode.encode next
  | .pop stack onEmpty onFalse onTrue =>
      [true, false, StackCode.encode stack] ++ LabelCode.encode onEmpty ++
        LabelCode.encode onFalse ++ LabelCode.encode onTrue

/-- The exact number of bits occupied by one encoded instruction. -/
def codeLength {labelCount : Nat} : Instruction (Fin labelCount) → Nat
  | .halt => 2
  | .push _ _ next => next.val + 5
  | .pop _ onEmpty onFalse onTrue =>
      onEmpty.val + onFalse.val + onTrue.val + 6

/-- The declared instruction-code cost equals its encoded length exactly. -/
@[simp] theorem length_encode {labelCount : Nat}
    (instruction : Instruction (Fin labelCount)) :
    (encode instruction).length = codeLength instruction := by
  cases instruction <;> simp [encode, codeLength, LabelCode.encode]
  omega

/--
Decode one instruction prefix and return its unused suffix. Truncated fields,
the reserved `11` tag, and out-of-range labels are rejected.
-/
def decodePrefix? (labelCount : Nat) : BitString →
    Option (Instruction (Fin labelCount) × BitString)
  | false :: false :: suffix => some (.halt, suffix)
  | false :: true :: stackBit :: bit :: bits => do
      let (next, suffix) ← LabelCode.decodePrefix? labelCount bits
      some (.push (StackCode.decode stackBit) bit next, suffix)
  | true :: false :: stackBit :: bits => do
      let (onEmpty, afterEmpty) ← LabelCode.decodePrefix? labelCount bits
      let (onFalse, afterFalse) ← LabelCode.decodePrefix? labelCount afterEmpty
      let (onTrue, suffix) ← LabelCode.decodePrefix? labelCount afterFalse
      some (.pop (StackCode.decode stackBit) onEmpty onFalse onTrue, suffix)
  | _ => none

/-- Encoded instructions decode exactly without consuming a supplied suffix. -/
@[simp] theorem decodePrefix?_encode_append {labelCount : Nat}
    (instruction : Instruction (Fin labelCount)) (suffix : BitString) :
    decodePrefix? labelCount (encode instruction ++ suffix) =
      some (instruction, suffix) := by
  cases instruction with
  | halt => rfl
  | push stack bit next => cases stack <;> simp [encode, decodePrefix?]
  | pop stack onEmpty onFalse onTrue =>
      cases stack <;> simp [encode, decodePrefix?, List.append_assoc]

/-- Distinct instructions have distinct canonical encodings. -/
theorem encode_injective {labelCount : Nat} :
    Function.Injective (encode (labelCount := labelCount)) := by
  intro first second hencode
  have hdecode := congrArg (decodePrefix? labelCount) hencode
  have hfirst : decodePrefix? labelCount (encode first) = some (first, []) := by
    simpa using decodePrefix?_encode_append first []
  have hsecond : decodePrefix? labelCount (encode second) = some (second, []) := by
    simpa using decodePrefix?_encode_append second []
  rw [hfirst, hsecond] at hdecode
  exact congrArg Prod.fst (Option.some.inj hdecode)

/-- The reserved `11` constructor tag is rejected for every suffix. -/
@[simp] theorem decodePrefix?_reserved (labelCount : Nat) (suffix : BitString) :
    decodePrefix? labelCount (true :: true :: suffix) = none := rfl

/-- An empty bitstring contains no complete instruction tag. -/
@[simp] theorem decodePrefix?_empty (labelCount : Nat) : decodePrefix? labelCount [] = none := by
  rfl

/-- One tag bit is insufficient for every instruction constructor. -/
@[simp] theorem decodePrefix?_oneBit (labelCount : Nat) (bit : Bool) :
    decodePrefix? labelCount [bit] = none := by
  cases bit <;> rfl

/-- A push code without its continuation label is rejected. -/
@[simp] theorem decodePrefix?_truncatedPush
    (labelCount : Nat) (stackBit bit : Bool) :
    decodePrefix? labelCount [false, true, stackBit, bit] = none := by
  simp [decodePrefix?]

/-- A pop code without its first branch label is rejected. -/
@[simp] theorem decodePrefix?_truncatedPop (labelCount : Nat) (stackBit : Bool) :
    decodePrefix? labelCount [true, false, stackBit] = none := by
  simp [decodePrefix?]

/-- A pop code ending after its empty-stack label is rejected. -/
@[simp] theorem decodePrefix?_truncatedPopAfterEmpty {labelCount : Nat}
    (stackBit : Bool) (onEmpty : Fin labelCount) :
    decodePrefix? labelCount
      (true :: false :: stackBit :: LabelCode.encode onEmpty) = none := by
  have hempty : LabelCode.decodePrefix? labelCount (LabelCode.encode onEmpty) =
      some (onEmpty, []) := by
    simpa using LabelCode.decodePrefix?_encode_append onEmpty []
  simp only [decodePrefix?]
  rw [hempty]
  rfl

/-- A pop code ending after its false-bit label is rejected. -/
@[simp] theorem decodePrefix?_truncatedPopAfterFalse {labelCount : Nat}
    (stackBit : Bool) (onEmpty onFalse : Fin labelCount) :
    decodePrefix? labelCount
      (true :: false :: stackBit ::
        (LabelCode.encode onEmpty ++ LabelCode.encode onFalse)) = none := by
  have hempty := LabelCode.decodePrefix?_encode_append onEmpty (LabelCode.encode onFalse)
  have hfalse : LabelCode.decodePrefix? labelCount (LabelCode.encode onFalse) =
      some (onFalse, []) := by
    simpa using LabelCode.decodePrefix?_encode_append onFalse []
  simp only [decodePrefix?]
  simp only [hempty, Option.bind_eq_bind, Option.bind_some, hfalse]
  rfl

end InstructionCode
end TwoStackMachine
end ComplexityTheory
