/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/ConfigCount.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.ConfigCount` to `Complexity.ClassicalProofs.SavitchProofs.ConfigCount`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchDefinitions.ConfigCount
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs.SavitchProofs

open Complexity.ClassicalProofs.SavitchDefinitions.BoundedConfigurations Complexity.Classical.SpaceMachines

def configurationEquiv (M : Machine) (n s : ℕ) :
    Config M n s ≃ M.Q × Fin (n + 2) × Fin s × (Fin s → M.Γ) where
  toFun c := (c.state, c.inputHead, c.workHead, c.tape)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
Count the four components of a bounded configuration.
-/
lemma configuration_count (M : Machine) (n s : ℕ) :
    Fintype.card (Config M n s) =
      Fintype.card M.Q * (n + 2) * s * Fintype.card M.Γ ^ s := by
  rw [Fintype.card_congr (configurationEquiv M n s)]
  simp [Nat.mul_assoc]

end Complexity.ClassicalProofs.SavitchProofs
