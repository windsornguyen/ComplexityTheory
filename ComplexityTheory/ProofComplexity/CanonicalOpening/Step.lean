/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

/-!
# Recursive exact-opening steps

An opening step may reject, finish successfully, or emit a smaller child claim.
The semantic contract separates preservation of true claims from exposure of a
false child. It deliberately contains no resource assertion.
-/

namespace ComplexityTheory

/-- The result of one recursive opening challenge. -/
inductive OpeningStepResult (ChildClaim : Type) where
  /-- Reject the current proof message. -/
  | reject
  /-- Finish this branch successfully without a child claim. -/
  | accept
  /-- Continue verification with a smaller child claim. -/
  | child (claim : ChildClaim)

namespace OpeningStepResult

/--
A result is valid for a true parent when it accepts immediately or emits a true
child. Rejection is invalid on the honest path.
-/
def PreservesTrue {ChildClaim : Type} (childTrue : ChildClaim → Prop) :
    OpeningStepResult ChildClaim → Prop
  | .reject => False
  | .accept => True
  | .child claim => childTrue claim

/--
A result exposes a false parent when it rejects or emits a false child.
Immediate acceptance does not expose an error.
-/
def ExposesFalse {ChildClaim : Type} (childTrue : ChildClaim → Prop) :
    OpeningStepResult ChildClaim → Prop
  | .reject => True
  | .accept => False
  | .child claim => ¬childTrue claim

end OpeningStepResult

/--
One exact public-coin reduction from a parent claim to a smaller child claim.
Completeness is constructive. Pointwise false descent permits the rejecting
challenge to depend on the adversarial proof message.
-/
structure ExactOpeningStep (ParentClaim Proof Challenge ChildClaim : Type) where
  /-- State the semantic truth condition for a parent claim. -/
  parentTrue : ParentClaim → Prop
  /-- State the semantic truth condition for an emitted child claim. -/
  childTrue : ChildClaim → Prop
  /-- Construct the proof message used for a true parent claim. -/
  honestProof : ParentClaim → Proof
  /-- Execute one verifier challenge. -/
  step : ParentClaim → Proof → Challenge → OpeningStepResult ChildClaim
  /-- Every challenge preserves a true parent under the honest proof. -/
  complete : ∀ parent,
    parentTrue parent →
      ∀ challenge,
        (step parent (honestProof parent) challenge).PreservesTrue childTrue
  /-- Every proof of a false parent has a rejecting or false-child challenge. -/
  falseDescent : ∀ parent,
    ¬parentTrue parent →
      ∀ proof,
        ∃ challenge, (step parent proof challenge).ExposesFalse childTrue

end ComplexityTheory
