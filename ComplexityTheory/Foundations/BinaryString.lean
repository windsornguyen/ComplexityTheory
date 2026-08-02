/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.Computability.Encoding
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Order

/-!
# Binary strings and encodings

The string and pair conventions from Arora and Barak, *Computational
Complexity: A Modern Approach*, January 2007 web draft, Section 1.1.1,
pp. 12-13 (PDF pp. 28-29), made explicit as decodable Lean functions.
-/

namespace ComplexityTheory

/-- A finite binary string, corresponding to `{0, 1}*`, and the library's basic input format. -/
abbrev BitString := List Bool

/-- A binary string of length `n`, corresponding to `{0, 1}^n`, with length enforced by its type. -/
abbrev FixedBitString (n : Nat) := Fin n → Bool

/--
An explicit binary representation bundles serialization with a partial decoder
that reverses every canonical code.
-/
abbrev BinaryEncoding (α : Type*) := Computability.Encoding α Bool

/--
Every binary string has a unique length and fixed-length representation. This
equivalence moves between variable-length inputs and length-indexed arguments.
-/
def bitStringEquivSigma : BitString ≃ Σ n, FixedBitString n :=
  List.equivSigmaTuple

/-- There are exactly `2^n` binary strings of length `n`, fixing the finite search-space size. -/
theorem card_fixedBitString (n : Nat) :
  Fintype.card (FixedBitString n) = 2 ^ n := by
  simp [FixedBitString]

namespace BitString

/-- Duplicate every bit so the pattern `01` remains available as an unambiguous delimiter. -/
def duplicate : BitString → BitString
  | [] => []
  | b :: bits => b :: b :: duplicate bits

/-- Decode identical bit pairs, rejecting mismatched pairs and odd-length input. -/
def unduplicate? : BitString → Option BitString
  | [] => some []
  | false :: false :: bits => do
      let decoded ← unduplicate? bits
      return false :: decoded
  | true :: true :: bits => do
      let decoded ← unduplicate? bits
      return true :: decoded
  | _ => none

/-- Duplication followed by unduplication recovers the original bitstring. -/
@[simp] theorem unduplicate?_duplicate (bits : BitString) :
    unduplicate? (duplicate bits) = some bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [duplicate, unduplicate?, ih]

/-- Duplication doubles length exactly, providing its later encoding-cost equation. -/
@[simp] theorem length_duplicate (bits : BitString) :
    (duplicate bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp [duplicate, ih]
    omega

/--
Encode a pair as in Arora and Barak: double the first string, append `01` as a
delimiter, then append the second string unchanged. The decoder can therefore
find the boundary without receiving either component length separately.
-/
def pair (x y : BitString) : BitString :=
  duplicate x ++ [false, true] ++ y

/-- Pairing with an empty first component begins immediately with the delimiter. -/
@[simp] theorem pair_nil (y : BitString) :
    pair [] y = false :: true :: y := by
  rfl

/-- Pairing exposes a duplicated head bit, supporting structural proofs over the first component. -/
@[simp] theorem pair_cons (b : Bool) (x y : BitString) :
    pair (b :: x) y = b :: b :: pair x y := by
  simp [pair, duplicate, List.append_assoc]

/-- Decode a pair, rejecting malformed doubled bits or a missing delimiter instead of guessing. -/
def unpair? : BitString → Option (BitString × BitString)
  | false :: true :: bits => some ([], bits)
  | false :: false :: bits => do
      let (first, second) ← unpair? bits
      return (false :: first, second)
  | true :: true :: bits => do
      let (first, second) ← unpair? bits
      return (true :: first, second)
  | _ => none

/-- Pair decoding reverses every canonical pair encoding. -/
@[simp] theorem unpair?_pair (x y : BitString) :
    unpair? (pair x y) = some (x, y) := by
  induction x with
  | nil => simp [unpair?]
  | cons b x ih => cases b <;> simp [unpair?, ih]

/-- Pair encoding has linear size with an exact two-bit delimiter overhead. -/
@[simp] theorem length_pair (x y : BitString) :
    (pair x y).length = 2 * x.length + 2 + y.length := by
  simp [pair]
  omega

/-- Pair encoding is injective, so one code cannot name two different pairs. -/
theorem pair_inj {x₁ x₂ y₁ y₂ : BitString} (h : pair x₁ y₁ = pair x₂ y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hsome : some (x₁, y₁) = some (x₂, y₂) := by
    simpa using congrArg unpair? h
  have hp : (x₁, y₁) = (x₂, y₂) := Option.some.inj hsome
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- The pair functions satisfy Mathlib's reusable `Encoding` interface. -/
def pairEncoding : BinaryEncoding (BitString × BitString) where
  encode xy := pair xy.1 xy.2
  decode := unpair?
  decode_encode := by
    rintro ⟨x, y⟩
    exact unpair?_pair x y

end BitString

namespace BinaryEncoding

/--
Encode a product by encoding each component and then applying the canonical
bitstring pair encoding.
Letting `aCode = ea.encode a` and `bCode = eb.encode b`, the result is
`duplicate aCode ++ 01 ++ bCode`.
This named layer keeps component serialization separate from pair framing.
The decoder can therefore reverse the two stages independently.
This is the encoder used by `prod` below.
-/
def encodeProd {α β : Type*} (ea : BinaryEncoding α) (eb : BinaryEncoding β) :
    α × β → BitString
  | (a, b) => BitString.pair (ea.encode a) (eb.encode b)

/--
Decode the outer bitstring pair, then decode both component representations.
Failure at any stage rejects the entire product code instead of inventing a
component value.
-/
def decodeProd? {α β : Type*} (ea : BinaryEncoding α) (eb : BinaryEncoding β)
    (bits : BitString) : Option (α × β) :=
  match BitString.unpair? bits with
  | none => none
  | some (aCode, bCode) =>
      match ea.decode aCode, eb.decode bCode with
      | some a, some b => some (a, b)
      | _, _ => none

/-- Compose component serialization and pair framing into one binary encoding. -/
def prod {α β : Type*} (ea : BinaryEncoding α) (eb : BinaryEncoding β) :
    BinaryEncoding (α × β) where
  encode := encodeProd ea eb
  decode := decodeProd? ea eb
  decode_encode := by
    rintro ⟨a, b⟩
    simp [encodeProd, decodeProd?]

/-- The composed pair encoding has the exact first-code doubling and delimiter cost. -/
@[simp] theorem length_prod_encode {α β : Type*}
    (ea : BinaryEncoding α) (eb : BinaryEncoding β) (a : α) (b : β) :
    ((prod ea eb).encode (a, b)).length =
      2 * (ea.encode a).length + 2 + (eb.encode b).length := by
  simp [prod, encodeProd]

end BinaryEncoding

end ComplexityTheory
