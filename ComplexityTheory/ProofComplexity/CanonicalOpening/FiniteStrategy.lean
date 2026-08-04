/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CanonicalOpening.Step
import Mathlib.Data.Fintype.Basic

/-!
# Exhaustive checking for finite opening steps

This module turns a finite one-step protocol into an executable search for a
perfect prover strategy. A concrete protocol should retain the discovered proof
as a separate checked certificate.
-/

namespace ComplexityTheory
namespace OpeningStepResult

/-- A result is safe for the prover when it accepts or emits a true child. -/
def isSafe {ChildClaim : Type} (childTrue : ChildClaim → Bool) :
    OpeningStepResult ChildClaim → Bool
  | OpeningStepResult.reject => false
  | OpeningStepResult.accept => true
  | OpeningStepResult.child claim => childTrue claim

end OpeningStepResult

namespace CanonicalOpening

/-- A verifier either audits one global response or opens one local response. -/
inductive GlobalLocalChallenge (Index : Type) where
  /-- Audit the response intended to establish the global relation. -/
  | global
  /-- Open the response at one challenged local index. -/
  | opening (index : Index)

/--
A one-round strategy commits before the challenge, then supplies separate
global and local responses. The local response function is semantic strategy
state, not a claim that its entire table is transmitted.
-/
structure SeparatedResponseStrategy
    (Commitment GlobalResponse Index LocalResponse : Type) where
  /-- The message fixed before the verifier reveals its challenge. -/
  commitment : Commitment
  /-- The response used on the global audit branch. -/
  globalResponse : GlobalResponse
  /-- The response used at each local opening branch. -/
  localResponse : Index → LocalResponse

namespace SeparatedResponseStrategy

/-- Run the branch selected by a global-or-local challenge. -/
def run
    {Commitment GlobalResponse Index LocalResponse ChildClaim : Type}
    (global : Commitment → GlobalResponse → OpeningStepResult ChildClaim)
    (localStep : Commitment → Index → LocalResponse → OpeningStepResult ChildClaim)
    (strategy : SeparatedResponseStrategy Commitment GlobalResponse Index LocalResponse) :
    GlobalLocalChallenge Index → OpeningStepResult ChildClaim
  | .global => global strategy.commitment strategy.globalResponse
  | .opening index => localStep strategy.commitment index (strategy.localResponse index)

/--
A separated strategy survives every challenge exactly when its global response
and every independently selectable local response are safe. This equivalence
is the response-splicing seam that a real commitment mechanism must close.
-/
theorem safeForEveryChallenge_iff
    {Commitment GlobalResponse Index LocalResponse ChildClaim : Type}
    (childTrue : ChildClaim → Bool)
    (global : Commitment → GlobalResponse → OpeningStepResult ChildClaim)
    (localStep : Commitment → Index → LocalResponse → OpeningStepResult ChildClaim)
    (strategy : SeparatedResponseStrategy Commitment GlobalResponse Index LocalResponse) :
    (∀ challenge, (strategy.run global localStep challenge).isSafe childTrue = true) ↔
      (global strategy.commitment strategy.globalResponse).isSafe childTrue = true ∧
        ∀ index,
          (localStep strategy.commitment index (strategy.localResponse index)).isSafe childTrue =
            true := by
  constructor
  · intro hSafe
    exact ⟨hSafe .global, fun index => hSafe (.opening index)⟩
  · rintro ⟨hGlobal, hLocal⟩ challenge
    cases challenge with
    | global => exact hGlobal
    | opening index => exact hLocal index

end SeparatedResponseStrategy

/--
One fixed proof survives every challenge without rejection or a false child.
This proposition states the semantic contract before finite enumeration.
-/
def IsPerfectOneStepStrategy
    {Proof Challenge ChildClaim : Type}
    (childTrue : ChildClaim → Bool)
    (run : Proof → Challenge → OpeningStepResult ChildClaim)
    (proof : Proof) : Prop :=
  ∀ challenge, (run proof challenge).isSafe childTrue = true

/-- Some challenge-independent proof is safe for every challenge. -/
def HasPerfectOneStepStrategy
    {Proof Challenge ChildClaim : Type}
    (childTrue : ChildClaim → Bool)
    (run : Proof → Challenge → OpeningStepResult ChildClaim) : Prop :=
  ∃ proof, IsPerfectOneStepStrategy childTrue run proof

/-- Exhaustively decide whether a perfect one-step proof exists. -/
def hasPerfectOneStepStrategy
    {Proof Challenge ChildClaim : Type}
    [Fintype Proof] [Fintype Challenge]
    (childTrue : ChildClaim → Bool)
    (run : Proof → Challenge → OpeningStepResult ChildClaim) : Bool :=
  letI : Decidable (∃ proof, ∀ challenge,
      (run proof challenge).isSafe childTrue = true) := by infer_instance
  decide (∃ proof, ∀ challenge,
    (run proof challenge).isSafe childTrue = true)

/-- The finite checker returns true exactly when a perfect proof exists. -/
@[simp] theorem hasPerfectOneStepStrategy_eq_true_iff
    {Proof Challenge ChildClaim : Type}
    [Fintype Proof] [Fintype Challenge]
    (childTrue : ChildClaim → Bool)
    (run : Proof → Challenge → OpeningStepResult ChildClaim) :
    hasPerfectOneStepStrategy childTrue run = true ↔
      HasPerfectOneStepStrategy childTrue run := by
  simp [hasPerfectOneStepStrategy, HasPerfectOneStepStrategy,
    IsPerfectOneStepStrategy]

/--
A proof cheats on one parent when that parent is false but the proof is safe
for every challenge.
-/
def IsCheatingOneStepStrategy
    {Parent Proof Challenge ChildClaim : Type}
    (parentTrue : Parent → Bool) (childTrue : ChildClaim → Bool)
    (run : Parent → Proof → Challenge → OpeningStepResult ChildClaim)
    (parent : Parent) (proof : Proof) : Prop :=
  parentTrue parent = false ∧
    IsPerfectOneStepStrategy childTrue (run parent) proof

/-- A false parent has some proof that cheats on every challenge. -/
def HasCheatingOneStepStrategy
    {Parent Proof Challenge ChildClaim : Type}
    (parentTrue : Parent → Bool) (childTrue : ChildClaim → Bool)
    (run : Parent → Proof → Challenge → OpeningStepResult ChildClaim)
    (parent : Parent) : Prop :=
  ∃ proof, IsCheatingOneStepStrategy parentTrue childTrue run parent proof

/--
Exhaustively detect a false parent admitting a proof that survives every
challenge. A true result is a complete finite cheating certificate.
-/
def hasCheatingOneStepStrategy
    {Parent Proof Challenge ChildClaim : Type}
    [Fintype Proof] [Fintype Challenge]
    (parentTrue : Parent → Bool) (childTrue : ChildClaim → Bool)
    (run : Parent → Proof → Challenge → OpeningStepResult ChildClaim)
    (parent : Parent) : Bool :=
  !parentTrue parent && hasPerfectOneStepStrategy childTrue (run parent)

/-- The cheating checker exposes both the false parent and its perfect proof. -/
@[simp] theorem hasCheatingOneStepStrategy_eq_true_iff
    {Parent Proof Challenge ChildClaim : Type}
    [Fintype Proof] [Fintype Challenge]
    (parentTrue : Parent → Bool) (childTrue : ChildClaim → Bool)
    (run : Parent → Proof → Challenge → OpeningStepResult ChildClaim)
    (parent : Parent) :
    hasCheatingOneStepStrategy parentTrue childTrue run parent = true ↔
      HasCheatingOneStepStrategy parentTrue childTrue run parent := by
  simp [hasCheatingOneStepStrategy, HasCheatingOneStepStrategy,
    IsCheatingOneStepStrategy, HasPerfectOneStepStrategy,
    IsPerfectOneStepStrategy]

end CanonicalOpening
end ComplexityTheory
