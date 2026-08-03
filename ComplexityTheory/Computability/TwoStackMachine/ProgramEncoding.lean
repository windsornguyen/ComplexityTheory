/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Computability.TwoStackMachine.InstructionEncoding.Canonical
import Mathlib.Data.Vector.Basic

/-!
# Canonical binary encoding of two-stack programs

A program code contains its self-delimiting label count, its initial label,
and one instruction for every label in order. The count therefore frames the
instruction table without a second length field.

The decoder rejects zero-label programs through the initial-label check,
out-of-range labels through the instruction decoder, truncated tables, and
every trailing bit in exact mode. Its converse theorem proves that every
accepted code is canonical.
-/

namespace ComplexityTheory
namespace TwoStackMachine

namespace InstructionTableCode

/-- Encode a fixed-length instruction table in increasing label order. -/
def encode {labelCount count : Nat}
    (table : List.Vector (Instruction (Fin labelCount)) count) : BitString :=
  table.toList.flatMap InstructionCode.encode

/-- The encoded table length is the sum of its instruction-code lengths. -/
@[simp] theorem length_encode {labelCount count : Nat}
    (table : List.Vector (Instruction (Fin labelCount)) count) :
    (encode table).length = (table.toList.map InstructionCode.codeLength).sum := by
  simp [encode]

/-- Decode exactly `count` instructions while preserving the unused suffix. -/
def decodePrefix? (labelCount : Nat) : (count : Nat) → BitString →
    Option (List.Vector (Instruction (Fin labelCount)) count × BitString)
  | 0, bits => some (List.Vector.nil, bits)
  | count + 1, bits => do
      let (instruction, rest) ← InstructionCode.decodePrefix? labelCount bits
      let (table, suffix) ← decodePrefix? labelCount count rest
      some (instruction ::ᵥ table, suffix)

/-- A canonical instruction table decodes without consuming a supplied suffix. -/
@[simp] theorem decodePrefix?_encode_append {labelCount count : Nat}
    (table : List.Vector (Instruction (Fin labelCount)) count) (suffix : BitString) :
    decodePrefix? labelCount count (encode table ++ suffix) = some (table, suffix) := by
  induction table using List.Vector.inductionOn with
  | nil => rfl
  | cons ih =>
      rename_i instruction table
      simp only [encode, List.Vector.toList_cons, List.flatMap_cons,
        List.append_assoc, decodePrefix?,
        InstructionCode.decodePrefix?_encode_append, Option.bind_eq_bind,
        Option.bind_some]
      change (decodePrefix? labelCount _ (encode table ++ suffix)).bind
        (fun result => some (instruction ::ᵥ result.1, result.2)) =
        some (instruction ::ᵥ table, suffix)
      rw [ih]
      rfl

/-- Every successfully decoded table prefix is its canonical ordered encoding. -/
theorem eq_encode_append_of_decodePrefix?_eq_some
    {labelCount count : Nat} {bits : BitString}
    {table : List.Vector (Instruction (Fin labelCount)) count} {suffix : BitString}
    (hdecode : decodePrefix? labelCount count bits = some (table, suffix)) :
    bits = encode table ++ suffix := by
  induction count generalizing bits with
  | zero =>
      simp only [decodePrefix?, Option.some.injEq, Prod.mk.injEq] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      rfl
  | succ count ih =>
      simp only [decodePrefix?] at hdecode
      cases hinstruction : InstructionCode.decodePrefix? labelCount bits with
      | none => simp [hinstruction] at hdecode
      | some instructionResult =>
          rcases instructionResult with ⟨instruction, rest⟩
          simp only [hinstruction, Option.bind_eq_bind, Option.bind_some] at hdecode
          cases htable : decodePrefix? labelCount count rest with
          | none => simp [htable] at hdecode
          | some tableResult =>
              rcases tableResult with ⟨remainingTable, finalSuffix⟩
              simp only [htable, Option.bind_some, Option.some.injEq,
                Prod.mk.injEq] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              rw [InstructionCode.eq_encode_append_of_decodePrefix?_eq_some hinstruction]
              rw [ih htable]
              simp [encode]

end InstructionTableCode

namespace ProgramCode

/--
Encode a complete program as its label count, initial label, and ordered
instruction table. Function-valued tables are enumerated extensionally.
-/
def encode (program : Program) : BitString :=
  NatPrefixCode.encode program.labelCount ++ LabelCode.encode program.initial ++
    InstructionTableCode.encode (List.Vector.ofFn program.instruction)

/-- Program-code length is exactly the sum of its framed fields. -/
@[simp] theorem length_encode (program : Program) :
    (encode program).length = program.labelCount + 1 + (program.initial.val + 1) +
      ((List.Vector.ofFn program.instruction).toList.map InstructionCode.codeLength).sum := by
  simp [encode, LabelCode.encode, Nat.add_assoc]

/-- Decode one complete program prefix and return its unused suffix. -/
def decodePrefix? (bits : BitString) : Option (Program × BitString) := do
  let (labelCount, afterCount) ← NatPrefixCode.decodePrefix? bits
  let (initial, afterInitial) ← LabelCode.decodePrefix? labelCount afterCount
  let (table, suffix) ←
    InstructionTableCode.decodePrefix? labelCount labelCount afterInitial
  some ({ labelCount, initial, instruction := table.get }, suffix)

/-- A code declaring zero control labels cannot supply a valid initial label. -/
@[simp] theorem decodePrefix?_zeroLabelCount (suffix : BitString) :
    decodePrefix? (NatPrefixCode.encode 0 ++ suffix) = none := by
  simp [decodePrefix?, LabelCode.decodePrefix?]

/-- Encoding then prefix-decoding recovers the program and preserves the suffix. -/
@[simp] theorem decodePrefix?_encode_append (program : Program) (suffix : BitString) :
    decodePrefix? (encode program ++ suffix) = some (program, suffix) := by
  rcases program with ⟨labelCount, initial, instruction⟩
  have htable : (List.Vector.ofFn instruction).get = instruction := by
    funext label
    exact List.Vector.get_ofFn instruction label
  simp [decodePrefix?, encode, List.append_assoc, htable]

/-- Every successfully decoded program prefix is its canonical encoding. -/
theorem eq_encode_append_of_decodePrefix?_eq_some
    {bits : BitString} {program : Program} {suffix : BitString}
    (hdecode : decodePrefix? bits = some (program, suffix)) :
    bits = encode program ++ suffix := by
  simp only [decodePrefix?] at hdecode
  cases hcount : NatPrefixCode.decodePrefix? bits with
  | none => simp [hcount] at hdecode
  | some countResult =>
      rcases countResult with ⟨labelCount, afterCount⟩
      simp only [hcount, Option.bind_eq_bind, Option.bind_some] at hdecode
      cases hinitial : LabelCode.decodePrefix? labelCount afterCount with
      | none => simp [hinitial] at hdecode
      | some initialResult =>
          rcases initialResult with ⟨initial, afterInitial⟩
          simp only [hinitial, Option.bind_some] at hdecode
          cases htable : InstructionTableCode.decodePrefix?
              labelCount labelCount afterInitial with
          | none => simp [htable] at hdecode
          | some tableResult =>
              rcases tableResult with ⟨table, finalSuffix⟩
              simp only [htable, Option.bind_some, Option.some.injEq,
                Prod.mk.injEq] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              rw [NatPrefixCode.eq_encode_append_of_decodePrefix?_eq_some hcount]
              rw [LabelCode.eq_encode_append_of_decodePrefix?_eq_some hinitial]
              rw [InstructionTableCode.eq_encode_append_of_decodePrefix?_eq_some htable]
              simp [encode, List.Vector.ofFn_get, List.append_assoc]

/-- Decode exactly one program, rejecting every nonempty trailing suffix. -/
def decode? (bits : BitString) : Option Program :=
  match decodePrefix? bits with
  | some (program, []) => some program
  | _ => none

/-- Exact decoding reverses the canonical program encoding. -/
@[simp] theorem decode?_encode (program : Program) : decode? (encode program) = some program := by
  unfold decode?
  rw [show encode program = encode program ++ [] by simp, decodePrefix?_encode_append]

/-- Exact decoding rejects a canonical program followed by any additional bit. -/
theorem decode?_encode_append_eq_none (program : Program)
    {suffix : BitString} (hsuffix : suffix ≠ []) :
    decode? (encode program ++ suffix) = none := by
  unfold decode?
  rw [decodePrefix?_encode_append]
  simp [hsuffix]

/-- The program functions form a Mathlib-compatible binary encoding. -/
def encoding : BinaryEncoding Program where
  encode := encode
  decode := decode?
  decode_encode := decode?_encode

/-- Canonical program encodings are injective. -/
theorem encode_injective : Function.Injective encode :=
  encoding.encode_injective

end ProgramCode

end TwoStackMachine
end ComplexityTheory
