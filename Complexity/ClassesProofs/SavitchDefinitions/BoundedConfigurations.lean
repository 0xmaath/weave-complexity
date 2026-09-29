/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/BoundedConfigurations.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.BoundedConfigurations` to `Complexity.ClassesProofs.SavitchDefinitions.BoundedConfigurations`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.SpaceMachines
import Mathlib.Data.Fintype.Pi

set_option backward.isDefEq.respectTransparency false

/-!
A configuration using at most $s$ work cells consists of a control state,
an input-head position, a work-head position, and $s$ work symbols.
Cells beyond this prefix are blank.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.BoundedConfigurations

open Complexity.Classes.SpaceMachines

structure Config (M : Machine) (n s : ℕ) where
  state : M.Q
  inputHead : Fin (n + 2)
  workHead : Fin s
  tape : Fin s → M.Γ
  deriving Fintype

def expand {M : Machine} {n s : ℕ} (c : Config M n s) : M.Config :=
  ⟨c.state, c.inputHead.val, c.workHead.val,
    fun i => if h : i < s then c.tape ⟨i, h⟩ else M.blank⟩

end Complexity.ClassesProofs.SavitchDefinitions.BoundedConfigurations
