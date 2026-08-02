/-
Copyright (c) 2026 Windsor Nguyen and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Windsor Nguyen
-/

import ComplexityTheory.ProofComplexity.CookReckhow

/-!
# Jump operators for proof systems

A jump sends each Cook-Reckhow system to another system that it cannot
simulate. This module separates length simulation from p-simulation and does
not yet call either operator recursive; recursiveness requires a later encoding
of machines and proof systems.
-/

namespace ComplexityTheory

namespace CookReckhowSystem

/-- `target` length-simulates `source` through their semantic proof maps. -/
def Simulates (target source : CookReckhowSystem) : Prop :=
  target.toTautologyProofSystem.Simulates source.toTautologyProofSystem

/-- A system is optimal when it length-simulates every Cook-Reckhow system. -/
def IsOptimal (system : CookReckhowSystem) : Prop :=
  ∀ source, system.Simulates source

/-- A system is p-optimal when it p-simulates every Cook-Reckhow system. -/
def IsPOptimal (system : CookReckhowSystem) : Prop :=
  ∀ source, system.PSimulates source

end CookReckhowSystem

/--
A length-jump operator returns a Cook-Reckhow system not simulated by its
input. No effectiveness condition on constructing the output is included.
-/
structure LengthJumpOperator where
  /-- Produce the candidate stronger system. -/
  jump : CookReckhowSystem → CookReckhowSystem
  /-- The input system does not length-simulate its image. -/
  escapes : ∀ system : CookReckhowSystem, ¬system.Simulates (jump system)

/--
A p-jump operator returns a Cook-Reckhow system not p-simulated by its input.
No effectiveness condition on constructing the output is included.
-/
structure PJumpOperator where
  /-- Produce the candidate stronger system. -/
  jump : CookReckhowSystem → CookReckhowSystem
  /-- The input system does not p-simulate its image. -/
  escapes : ∀ system : CookReckhowSystem, ¬system.PSimulates (jump system)

namespace LengthJumpOperator

/-- The existence of a length jump rules out every optimal proof system. -/
theorem not_isOptimal (operator : LengthJumpOperator)
    (system : CookReckhowSystem) : ¬system.IsOptimal := by
  intro hOptimal
  exact operator.escapes system (hOptimal (operator.jump system))

/-- A length jump therefore implies that no optimal proof system exists. -/
theorem no_optimal (operator : LengthJumpOperator) :
    ¬∃ system : CookReckhowSystem, system.IsOptimal := by
  rintro ⟨system, hOptimal⟩
  exact operator.not_isOptimal system hOptimal

end LengthJumpOperator

namespace PJumpOperator

/-- The existence of a p-jump rules out every p-optimal proof system. -/
theorem not_isPOptimal (operator : PJumpOperator)
    (system : CookReckhowSystem) : ¬system.IsPOptimal := by
  intro hOptimal
  exact operator.escapes system (hOptimal (operator.jump system))

/-- A p-jump therefore implies that no p-optimal proof system exists. -/
theorem no_pOptimal (operator : PJumpOperator) :
    ¬∃ system : CookReckhowSystem, system.IsPOptimal := by
  rintro ⟨system, hOptimal⟩
  exact operator.not_isPOptimal system hOptimal

end PJumpOperator

end ComplexityTheory
