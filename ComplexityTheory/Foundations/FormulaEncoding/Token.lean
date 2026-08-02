/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.BooleanFormula
import ComplexityTheory.Foundations.NatEncoding

/-!
# Boolean-formula encoding tokens

Six three-bit tags represent the nodes of a Boolean formula in a postfix
stream. Variable tokens carry a self-delimiting natural-number index; the two
unused tags are rejected so later formats can assign them deliberately.
-/

namespace ComplexityTheory

namespace BooleanFormulaCode

/--
A proof-free instruction in a postfix Boolean-formula stream. Leaves push a
formula, while connectives consume their operands from a formula stack.
-/
inductive Token where
  /-- Push the variable with the given index. -/
  | var (index : Nat)
  /-- Push the constant true. -/
  | tru
  /-- Push the constant false. -/
  | fls
  /-- Negate the top formula. -/
  | neg
  /-- Conjoin the top two formulas. -/
  | conj
  /-- Disjoin the top two formulas. -/
  | disj
  deriving DecidableEq, Repr

namespace Token

/--
Serialize one token. Tags `110` and `111` remain reserved, while a variable's
`000` tag is followed by its self-delimiting index.
-/
def encode : Token → BitString
  | .var index => [false, false, false] ++ NatPrefixCode.encode index
  | .tru => [false, false, true]
  | .fls => [false, true, false]
  | .neg => [false, true, true]
  | .conj => [true, false, false]
  | .disj => [true, false, true]

/--
Parse one token prefix and return the unused suffix. Truncated tags, reserved
tags, and unterminated variable indices are rejected.
-/
def decodePrefix? : BitString → Option (Token × BitString)
  | false :: false :: false :: bits => do
      let (index, suffix) ← NatPrefixCode.decodePrefix? bits
      some (.var index, suffix)
  | false :: false :: true :: suffix => some (.tru, suffix)
  | false :: true :: false :: suffix => some (.fls, suffix)
  | false :: true :: true :: suffix => some (.neg, suffix)
  | true :: false :: false :: suffix => some (.conj, suffix)
  | true :: false :: true :: suffix => some (.disj, suffix)
  | _ => none

/--
The exact number of encoded bits in a token. Variable cost includes its index;
every other token occupies only its three-bit tag.
-/
def codeLength : Token → Nat
  | .var index => index + 4
  | _ => 3

/--
Apply one postfix token to a formula stack. Connectives fail on stack
underflow, so malformed streams cannot manufacture missing operands.
-/
def apply? : Token → List BooleanFormula → Option (List BooleanFormula)
  | .var index, stack => some (.var index :: stack)
  | .tru, stack => some (.tru :: stack)
  | .fls, stack => some (.fls :: stack)
  | .neg, formula :: stack => some (.neg formula :: stack)
  | .conj, right :: left :: stack => some (.conj left right :: stack)
  | .disj, right :: left :: stack => some (.disj left right :: stack)
  | _, _ => none

/-- The declared token cost equals its encoded length exactly. -/
@[simp] theorem length_encode (token : Token) :
    token.encode.length = token.codeLength := by
  cases token <;> simp [encode, codeLength]

/--
Decoding an encoded token recovers that token without consuming a supplied
suffix. This is the token-level round-trip used by the stream decoder.
-/
@[simp] theorem decodePrefix?_encode_append (token : Token) (suffix : BitString) :
    decodePrefix? (token.encode ++ suffix) = some (token, suffix) := by
  cases token <;> simp [encode, decodePrefix?]

/-- Reserved tag `110` is rejected rather than assigned an accidental meaning. -/
@[simp] theorem decodePrefix?_reserved₀ (suffix : BitString) :
    decodePrefix? (true :: true :: false :: suffix) = none := by
  rfl

/-- Reserved tag `111` is rejected rather than assigned an accidental meaning. -/
@[simp] theorem decodePrefix?_reserved₁ (suffix : BitString) :
    decodePrefix? (true :: true :: true :: suffix) = none := by
  rfl

end Token

end BooleanFormulaCode

end ComplexityTheory
