/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import Mathlib.Computability.TuringMachine.Computable
import ComplexityTheory.ProofComplexity.Simulation

/-!
# Cook-Reckhow proof systems

Cook and Reckhow, *The Relative Efficiency of Propositional Proof Systems*,
Journal of Symbolic Logic 44(1), 1979, Definitions 1.3 and 1.5, pp. 37-38
(PDF pp. 3-4), define polynomial-time proof maps and p-simulation.

This module reuses Mathlib's `Turing.TM2ComputableInPolyTime` certificate,
which bundles a finite multitape machine, a polynomial clock, and a proof that
the machine computes the declared function within that clock.
-/

namespace ComplexityTheory

/--
A certificate that `function` is computed by a Mathlib finite multitape Turing
machine within a polynomial number of steps under the supplied encodings.
-/
abbrev PolyTimeComputable {input output : Type}
    (encodeInput : input → BitString) (encodeOutput : output → BitString)
    (function : input → output) :=
  Turing.TM2ComputableInPolyTime encodeInput encodeOutput function

/--
A Cook-Reckhow system is a sound and complete tautology proof map together
with a certified polynomial-time Turing machine computing that map.
-/
structure CookReckhowSystem extends TautologyProofSystem where
  /-- The machine and polynomial clock computing `produce` on binary proofs. -/
  computesInPolyTime :
    PolyTimeComputable id BooleanFormulaCode.encode toTautologyProofSystem.produce

/--
A proof translation equipped with a certified polynomial-time Turing machine.
This is the data witnessing p-simulation.
-/
structure PolyTimeProofTranslation (source target : TautologyProofSystem)
    extends ProofTranslation source target where
  /-- The machine and polynomial clock computing the translator. -/
  computesInPolyTime : PolyTimeComputable id id toProofTranslation.translate

namespace PolyTimeProofTranslation

/-- Identity translation is polynomial-time under the binary-string encoding. -/
noncomputable def refl (system : TautologyProofSystem) :
    PolyTimeProofTranslation system system where
  toProofTranslation := ProofTranslation.refl system
  computesInPolyTime :=
    Turing.idComputableInPolyTime (fun bits : BitString => bits)

end PolyTimeProofTranslation

namespace TautologyProofSystem

/--
`target` simulates `source` when one polynomial bounds the target proof length
needed for every source proof, following Krajíček (2019), Definition 2.1, p. 5.
-/
def Simulates (target source : TautologyProofSystem) : Prop :=
  ∃ bound : Polynomial Nat,
    target.LengthSimulatesWith source (fun length => bound.eval length)

/-- Every proof system simulates itself with the polynomial `n`. -/
theorem simulates_refl (system : TautologyProofSystem) : system.Simulates system := by
  refine ⟨Polynomial.X, ?_⟩
  intro proof
  exact ⟨proof, rfl, by simp⟩

end TautologyProofSystem

namespace CookReckhowSystem

/--
`target` p-simulates `source` when both are Cook-Reckhow systems and a
certified polynomial-time translator preserves every produced formula.
-/
def PSimulates (target source : CookReckhowSystem) : Prop :=
  Nonempty (PolyTimeProofTranslation source.toTautologyProofSystem
    target.toTautologyProofSystem)

/-- Every Cook-Reckhow system p-simulates itself via the identity machine. -/
theorem pSimulates_refl (system : CookReckhowSystem) : system.PSimulates system :=
  ⟨PolyTimeProofTranslation.refl system.toTautologyProofSystem⟩

end CookReckhowSystem

end ComplexityTheory
