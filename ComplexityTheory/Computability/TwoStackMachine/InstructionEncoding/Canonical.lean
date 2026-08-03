/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.TwoStackMachine.InstructionEncoding

/-!
# Canonical decoding of two-stack instructions

The executable instruction codec proves that every encoded instruction
round-trips. This module proves the converse: every prefix accepted by the
decoder is exactly the canonical encoding of its result followed by the
reported suffix. Complete program decoding uses this theorem to rule out
alternative codes for the same instruction table.
-/

namespace ComplexityTheory
namespace TwoStackMachine

namespace StackCode

/-- Encoding the stack selected by a bit recovers that bit. -/
@[simp] theorem encode_decode (bit : Bool) : encode (decode bit) = bit := by
  cases bit <;> rfl

end StackCode

namespace LabelCode

/--
Every successfully decoded label prefix is its canonical encoding followed by
the returned suffix. In particular, the decoder admits no out-of-range alias.
-/
theorem eq_encode_append_of_decodePrefix?_eq_some
    {labelCount : Nat} {bits : BitString} {label : Fin labelCount}
    {suffix : BitString}
    (hdecode : decodePrefix? labelCount bits = some (label, suffix)) :
    bits = encode label ++ suffix := by
  simp only [decodePrefix?] at hdecode
  cases hvalue : NatPrefixCode.decodePrefix? bits with
  | none => simp [hvalue] at hdecode
  | some result =>
      rcases result with ⟨value, rest⟩
      simp only [hvalue, Option.bind_eq_bind, Option.bind_some,
        Option.dite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
        exists_and_right] at hdecode
      rcases hdecode with ⟨⟨_, rfl⟩, rfl⟩
      exact NatPrefixCode.eq_encode_append_of_decodePrefix?_eq_some hvalue

end LabelCode

namespace InstructionCode

/--
Every successful instruction decoding identifies exactly its canonical prefix.
This is the compositional invariant used by the complete program decoder.
-/
theorem eq_encode_append_of_decodePrefix?_eq_some
    {labelCount : Nat} {bits : BitString}
    {instruction : Instruction (Fin labelCount)} {suffix : BitString}
    (hdecode : decodePrefix? labelCount bits = some (instruction, suffix)) :
    bits = encode instruction ++ suffix := by
  match bits with
  | false :: false :: rest =>
      simp only [decodePrefix?] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      rfl
  | false :: true :: stackBit :: bit :: rest =>
      simp only [decodePrefix?] at hdecode
      cases hnext : LabelCode.decodePrefix? labelCount rest with
      | none => simp [hnext] at hdecode
      | some result =>
          rcases result with ⟨next, nextSuffix⟩
          simp only [hnext] at hdecode
          rcases hdecode with ⟨rfl, rfl⟩
          rw [LabelCode.eq_encode_append_of_decodePrefix?_eq_some hnext]
          cases stackBit <;> rfl
  | true :: false :: stackBit :: rest =>
      simp only [decodePrefix?] at hdecode
      cases hempty : LabelCode.decodePrefix? labelCount rest with
      | none => simp [hempty] at hdecode
      | some emptyResult =>
          rcases emptyResult with ⟨onEmpty, afterEmpty⟩
          simp only [hempty, Option.bind_eq_bind, Option.bind_some] at hdecode
          cases hfalse : LabelCode.decodePrefix? labelCount afterEmpty with
          | none => simp [hfalse] at hdecode
          | some falseResult =>
              rcases falseResult with ⟨onFalse, afterFalse⟩
              simp only [hfalse, Option.bind_some] at hdecode
              cases htrue : LabelCode.decodePrefix? labelCount afterFalse with
              | none => simp [htrue] at hdecode
              | some trueResult =>
                  rcases trueResult with ⟨onTrue, finalSuffix⟩
                  simp only [htrue, Option.bind_some, Option.some.injEq,
                    Prod.mk.injEq] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  rw [LabelCode.eq_encode_append_of_decodePrefix?_eq_some hempty]
                  rw [LabelCode.eq_encode_append_of_decodePrefix?_eq_some hfalse]
                  rw [LabelCode.eq_encode_append_of_decodePrefix?_eq_some htrue]
                  cases stackBit <;> simp [encode, List.append_assoc]
  | [] => simp [decodePrefix?] at hdecode
  | _ :: [] => simp [decodePrefix?] at hdecode
  | false :: true :: [] => simp [decodePrefix?] at hdecode
  | false :: true :: _ :: [] => simp [decodePrefix?] at hdecode
  | true :: false :: [] => simp [decodePrefix?] at hdecode
  | true :: true :: _ => simp [decodePrefix?] at hdecode

end InstructionCode

end TwoStackMachine
end ComplexityTheory
