/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.FormulaRestriction

/-!
# Fixed-width Boolean-formula codes

A canonical formula code can be extended to any larger width with false bits.
The formula's self-delimiting prefix identifies the payload, while the decoder
rejects every padding suffix containing a true bit.
-/

namespace ComplexityTheory

namespace BitString

/-- Convert a list of known length into the corresponding fixed-length string. -/
def toFixed {width : Nat} (bits : BitString) (hLength : bits.length = width) :
    FixedBitString width := fun index => bits.get (Fin.cast hLength.symm index)

/-- Converting a list to fixed length and back preserves every bit. -/
@[simp] theorem ofFn_toFixed {width : Nat} (bits : BitString)
    (hLength : bits.length = width) :
    List.ofFn (toFixed bits hLength) = bits := by
  apply List.ext_get
  · simp [hLength]
  · intro index hLeft hRight
    simp [toFixed]

/-- Append false bits until `bits` reaches `width`; callers prove it already fits. -/
def zeroPadList (width : Nat) (bits : BitString) : BitString :=
  bits ++ List.replicate (width - bits.length) false

/-- Zero padding reaches the requested width exactly when the payload fits. -/
theorem length_zeroPadList {width : Nat} {bits : BitString}
    (hFits : bits.length ≤ width) :
    (zeroPadList width bits).length = width := by
  simp [zeroPadList]
  omega

/-- Embed a fitting variable-length string into an exact-width binary string. -/
def zeroPad (width : Nat) (bits : BitString) (hFits : bits.length ≤ width) :
    FixedBitString width :=
  toFixed (zeroPadList width bits) (length_zeroPadList hFits)

/-- Reading an exact-width zero-padded string recovers its explicit list form. -/
@[simp] theorem ofFn_zeroPad (width : Nat) (bits : BitString)
    (hFits : bits.length ≤ width) :
    List.ofFn (zeroPad width bits hFits) = zeroPadList width bits := by
  simp [zeroPad]

end BitString

namespace BooleanFormulaCode

/--
Decode a formula followed only by false padding. A noncanonical formula prefix
or any true padding bit makes the entire fixed-width representation invalid.
-/
def decodePadded? (bits : BitString) : Option BooleanFormula := do
  let (formula, padding) ← decodePrefix? bits
  if padding.all (!·) then some formula else none

/--
Padding-aware decoding exposes its complete suffix policy after a canonical
formula prefix: all-false padding succeeds and every other suffix fails.
-/
theorem decodePadded?_encode_append (formula : BooleanFormula) (padding : BitString) :
    decodePadded? (encode formula ++ padding) =
      if padding.all (!·) then some formula else none := by
  simp [decodePadded?]

/-- Encode a formula at an exact width, given evidence that its code fits. -/
def pad (width : Nat) (formula : BooleanFormula)
    (hFits : (encode formula).length ≤ width) : FixedBitString width :=
  BitString.zeroPad width (encode formula) hFits

/-- Exact-width decoding is padding-aware decoding of the underlying bit list. -/
def decodeFixed? {width : Nat} (bits : FixedBitString width) : Option BooleanFormula :=
  decodePadded? (List.ofFn bits)

/--
A fixed-width string represents a satisfiable formula when padding-aware
decoding succeeds and the decoded formula has a satisfying assignment.
-/
def IsSatisfiableCode {width : Nat} (bits : FixedBitString width) : Prop :=
  ∃ formula, decodeFixed? bits = some formula ∧ formula.IsSatisfiable

/-- Every fitting formula survives exact-width padding and decoding. -/
@[simp] theorem decodeFixed?_pad (width : Nat) (formula : BooleanFormula)
    (hFits : (encode formula).length ≤ width) :
    decodeFixed? (pad width formula hFits) = some formula := by
  simp [decodeFixed?, pad, BitString.zeroPadList, decodePadded?_encode_append]

/-- Padding preserves whether the encoded formula is satisfiable. -/
@[simp] theorem isSatisfiableCode_pad_iff (width : Nat) (formula : BooleanFormula)
    (hFits : (encode formula).length ≤ width) :
    IsSatisfiableCode (pad width formula hFits) ↔ formula.IsSatisfiable := by
  simp [IsSatisfiableCode]

/--
Restrict a formula and return its code at the original ambient width. Code
nonexpansion proves the constructor is total for every fitting source formula.
-/
def restrictPad (width : Nat) (formula : BooleanFormula)
    (hFits : (encode formula).length ≤ width) (fixed : BitString) :
    FixedBitString width :=
  pad width (formula.restrictPrefix fixed)
    (length_encode_restrictPrefix_le fixed formula |>.trans hFits)

/-- Decoding a restricted padded code recovers exactly the restricted formula. -/
@[simp] theorem decodeFixed?_restrictPad (width : Nat) (formula : BooleanFormula)
    (hFits : (encode formula).length ≤ width) (fixed : BitString) :
    decodeFixed? (restrictPad width formula hFits fixed) =
      some (formula.restrictPrefix fixed) := by
  simp [restrictPad]

/--
The restricted fixed-width code is satisfiable exactly when the original
formula has a satisfying assignment extending the fixed variable prefix.
-/
theorem isSatisfiableCode_restrictPad_iff (width : Nat) (formula : BooleanFormula)
    (hFits : (encode formula).length ≤ width) (fixed : BitString) :
    IsSatisfiableCode (restrictPad width formula hFits fixed) ↔
      ∃ assignment, BooleanFormula.Satisfies
        (BooleanAssignment.withPrefix fixed assignment) formula := by
  simp [IsSatisfiableCode, BooleanFormula.isSatisfiable_restrictPrefix_iff]

end BooleanFormulaCode

end ComplexityTheory
