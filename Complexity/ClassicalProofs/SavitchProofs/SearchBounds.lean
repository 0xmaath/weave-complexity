/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/SearchBounds.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.SearchBounds` to `Complexity.ClassicalProofs.SavitchProofs.SearchBounds`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchProofs.ConfigCount
import Complexity.ClassicalProofs.SavitchDefinitions.SearchBounds
import Complexity.ClassicalProofs.SavitchDefinitions.ConfigCount
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs.SavitchProofs

open Complexity.ClassicalProofs.SavitchDefinitions Complexity.ClassicalProofs.SavitchDefinitions.BoundedConfigurations Complexity.ClassicalProofs.SavitchDefinitions.SearchBounds
open Complexity.Classical.SpaceMachines Complexity.Classical.SpaceBounds

/--
Bound the configuration count by an exponential in $s$, then multiply depth by frame size.
-/
lemma quadratic_stack (M : Machine) :
    ∃ c : ℕ, 0 < c ∧ ∀ n s, logSpace n ≤ s → stackSpace M n s ≤ c * s ^ 2 := by
  let q := Fintype.card M.Q
  let g := Fintype.card M.Γ
  refine ⟨3 * (q + g + 4), by omega, ?_⟩
  intro n s hlog
  have hpos : 0 < s := (Nat.log_pos (by decide : 1 < (2 : ℕ)) (by omega : 2 ≤ n + 2)).trans_le hlog
  have hq : q ≤ 2 ^ q := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  have hn : n + 2 ≤ 2 ^ (logSpace n + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (n + 2)).le
  have hs : s ≤ 2 ^ s := (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  have hg : g ^ s ≤ 2 ^ (g * s) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le) s
  have hcard : Fintype.card (Config M n s) ≤ 2 ^ (q + (logSpace n + 1) + s + g * s) := by
    rw [Complexity.ClassicalProofs.SavitchProofs.configuration_count]
    calc
      q * (n + 2) * s * g ^ s ≤ 2 ^ q * 2 ^ (logSpace n + 1) * 2 ^ s * 2 ^ (g * s) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hq hn) hs) hg
      _ = _ := by simp only [pow_add]
  have hdepth := Nat.clog_le_of_le_pow hcard
  have hqs : q ≤ q * s := by nlinarith
  have hdepth' : Nat.clog 2 (Fintype.card (Config M n s)) + 1 ≤ (q + g + 4) * s := by
    nlinarith
  have hframe : s + logSpace n + 1 ≤ 3 * s := by omega
  have h := Nat.mul_le_mul hdepth' hframe
  simpa only [stackSpace, pow_two, Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using h

end Complexity.ClassicalProofs.SavitchProofs
