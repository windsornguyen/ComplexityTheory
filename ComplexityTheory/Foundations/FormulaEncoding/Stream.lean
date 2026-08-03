/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.Foundations.FormulaEncoding.Token

/-!
# Postfix Boolean-formula streams

Boolean formulas compile to a flat postfix token stream. A small stack machine
reconstructs the tree without a recursive bit-level parser, and the stream has
exactly one token for every formula node.
-/

namespace ComplexityTheory

namespace BooleanFormulaCode

/--
Compile a formula tree to its canonical postfix token stream. Children precede
their connective, so a left-to-right stack machine can rebuild the tree.
-/
def tokens : BooleanFormula → List Token
  | .var index => [.var index]
  | .tru => [.tru]
  | .fls => [.fls]
  | .neg formula => tokens formula ++ [.neg]
  | .conj left right => tokens left ++ tokens right ++ [.conj]
  | .disj left right => tokens left ++ tokens right ++ [.disj]

/--
Execute a postfix token stream from an initial formula stack. Evaluation stops
with `none` as soon as a token cannot consume the required operands.
-/
def run? : List Token → List BooleanFormula → Option (List BooleanFormula)
  | [], stack => some stack
  | token :: stream, stack => do
      let next ← token.apply? stack
      run? stream next

/--
Reconstruct exactly one formula from a complete token stream. Empty streams,
stack underflow, and leftover formulas are all rejected.
-/
def build? (stream : List Token) : Option BooleanFormula := do
  let stack ← run? stream []
  match stack with
  | [formula] => some formula
  | _ => none

/--
Running concatenated streams is sequential stack execution. This composition
law lets structural proofs reason about each formula subtree independently.
-/
theorem run?_append (first second : List Token) (stack : List BooleanFormula) :
    run? (first ++ second) stack = (run? first stack).bind (run? second) := by
  induction first generalizing stack with
  | nil => simp [run?]
  | cons token first ih =>
      simp only [List.cons_append, run?]
      cases happly : token.apply? stack with
      | none => simp
      | some next => simp [ih]

/--
Executing a formula's postfix tokens pushes exactly that formula onto any
existing stack. This is the central semantic invariant of the stream format.
-/
@[simp] theorem run?_tokens (formula : BooleanFormula) (stack : List BooleanFormula) :
    run? (tokens formula) stack = some (formula :: stack) := by
  induction formula generalizing stack with
  | var index => simp [tokens, run?, Token.apply?]
  | tru => simp [tokens, run?, Token.apply?]
  | fls => simp [tokens, run?, Token.apply?]
  | neg formula ih =>
      rw [tokens, run?_append, ih]
      simp [run?, Token.apply?]
  | conj left right ihLeft ihRight =>
      rw [tokens, run?_append, run?_append, ihLeft]
      simp only [Option.bind_some]
      rw [ihRight]
      simp [run?, Token.apply?]
  | disj left right ihLeft ihRight =>
      rw [tokens, run?_append, run?_append, ihLeft]
      simp only [Option.bind_some]
      rw [ihRight]
      simp [run?, Token.apply?]

/-- Building from a formula's canonical token stream recovers that formula. -/
@[simp] theorem build?_tokens (formula : BooleanFormula) :
    build? (tokens formula) = some formula := by
  simp [build?]

/-- The canonical token stream represented by a top-first formula stack. -/
private def stackTokenStream (stack : List BooleanFormula) : List Token :=
  stack.reverse.flatMap tokens

/-- One successful token instruction appends that token to the represented stream. -/
private theorem stackTokenStream_apply?_eq_append
    (token : Token) (stack next : List BooleanFormula)
    (happly : token.apply? stack = some next) :
    stackTokenStream next = stackTokenStream stack ++ [token] := by
  cases token with
  | var index =>
    simp only [Token.apply?, Option.some.injEq] at happly
    subst next
    simp [stackTokenStream, tokens]
  | tru =>
    simp only [Token.apply?, Option.some.injEq] at happly
    subst next
    simp [stackTokenStream, tokens]
  | fls =>
    simp only [Token.apply?, Option.some.injEq] at happly
    subst next
    simp [stackTokenStream, tokens]
  | neg =>
    cases stack with
    | nil => simp [Token.apply?] at happly
    | cons formula stack =>
      simp only [Token.apply?, Option.some.injEq] at happly
      subst next
      simp [stackTokenStream, tokens, List.append_assoc]
  | conj =>
    cases stack with
    | nil => simp [Token.apply?] at happly
    | cons right stack =>
      cases stack with
      | nil => simp [Token.apply?] at happly
      | cons left stack =>
        simp only [Token.apply?, Option.some.injEq] at happly
        subst next
        simp [stackTokenStream, tokens, List.append_assoc]
  | disj =>
    cases stack with
    | nil => simp [Token.apply?] at happly
    | cons right stack =>
      cases stack with
      | nil => simp [Token.apply?] at happly
      | cons left stack =>
        simp only [Token.apply?, Option.some.injEq] at happly
        subst next
        simp [stackTokenStream, tokens, List.append_assoc]

/-- Successful stack execution preserves the exact token stream represented by the stack. -/
private theorem stackTokenStream_eq_append_of_run?_eq_some
    (stream : List Token) (stack result : List BooleanFormula)
    (hrun : run? stream stack = some result) :
    stackTokenStream result = stackTokenStream stack ++ stream := by
  induction stream generalizing stack with
  | nil =>
    simp only [run?, Option.some.injEq] at hrun
    subst result
    simp
  | cons token stream ih =>
    simp only [run?] at hrun
    cases happly : token.apply? stack with
    | none => simp [happly] at hrun
    | some next =>
      simp only [happly] at hrun
      calc
        stackTokenStream result = stackTokenStream next ++ stream := ih next hrun
        _ = (stackTokenStream stack ++ [token]) ++ stream := by
          rw [stackTokenStream_apply?_eq_append token stack next happly]
        _ = stackTokenStream stack ++ (token :: stream) := by
          simp [List.append_assoc]

/--
If a complete postfix stream builds `formula`, then it is exactly that
formula's canonical token stream. Successful reconstruction therefore cannot
identify two distinct serialized trees.
-/
theorem eq_tokens_of_build?_eq_some
    {stream : List Token} {formula : BooleanFormula}
    (hbuild : build? stream = some formula) :
    stream = tokens formula := by
  unfold build? at hbuild
  cases hrun : run? stream [] with
  | none => simp [hrun] at hbuild
  | some stack =>
    simp only [hrun] at hbuild
    match stack with
    | [result] =>
      cases hbuild
      have hinvariant :=
        stackTokenStream_eq_append_of_run?_eq_some stream [] [formula] hrun
      simpa [stackTokenStream] using hinvariant.symm
    | [] => simp at hbuild
    | _ :: _ :: _ => simp at hbuild

/--
The postfix stream contains exactly one token per formula-tree node. Token
count and syntactic formula size therefore coincide.
-/
@[simp] theorem length_tokens (formula : BooleanFormula) :
    (tokens formula).length = formula.size := by
  induction formula with
  | var index => simp [tokens, BooleanFormula.size]
  | tru => simp [tokens, BooleanFormula.size]
  | fls => simp [tokens, BooleanFormula.size]
  | neg formula ih => simp [tokens, BooleanFormula.size, ih]
  | conj left right ihLeft ihRight =>
      simp [tokens, BooleanFormula.size, ihLeft, ihRight]
      omega
  | disj left right ihLeft ihRight =>
      simp [tokens, BooleanFormula.size, ihLeft, ihRight]
      omega

end BooleanFormulaCode

end ComplexityTheory
