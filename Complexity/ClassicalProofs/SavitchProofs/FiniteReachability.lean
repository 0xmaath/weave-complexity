/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/FiniteReachability.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.FiniteReachability` to `Complexity.ClassicalProofs.SavitchProofs.FiniteReachability`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchProofs.Reachability
import Complexity.ClassicalProofs.SavitchProofs.ShortPaths
import Complexity.ClassicalProofs.SavitchProofs.Reachability

set_option backward.isDefEq.respectTransparency false
namespace Complexity.ClassicalProofs.SavitchProofs
open Complexity.ClassicalProofs.SavitchDefinitions Complexity.ClassicalProofs.SavitchDefinitions.Reachability
/--
The recursion covers every simple path because $N\leq 2^{\lceil\log_2 N\rceil}$.
-/
lemma finite_reachability {N : ℕ} (G : Graph N) (a b : Fin N) :
    search G (Nat.clog 2 N) a b = true ↔ Reachable G a b := by
  rw [Complexity.ClassicalProofs.SavitchProofs.recursive_reachability]
  constructor
  · rintro ⟨k, _, h⟩
    exact walk_reachable h
  · intro h
    obtain ⟨k, hk, hw⟩ := (Complexity.ClassicalProofs.SavitchProofs.short_paths G a b).mp h
    exact ⟨k, (Nat.le_of_lt hk).trans (Nat.le_pow_clog (by decide) N), hw⟩

end Complexity.ClassicalProofs.SavitchProofs
