/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SpaceExponentialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SpaceExponentialTime` to `Complexity.ClassesProofs.SpaceExponentialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SpaceTimeDecider
import Complexity.ClassesProofs.GeneralTimeSimulation
import Complexity.Classes.PolynomialSpace
import Complexity.Classes.ExponentialTime

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassesProofs.SpaceExponentialTime

open Complexity.Classes.PolynomialTime Complexity.Classes.SpaceMachines
open Complexity.Classes.PolynomialSpace Complexity.Classes.ExponentialTime

lemma nat_le_exp (n : ℕ) : n ≤ 2 ^ n :=
  (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le

lemma add_exp_bound {a b e f : ℕ} (ha : a ≤ 2 ^ e) (hb : b ≤ 2 ^ f) :
    a + b ≤ 2 ^ (e + f + 1) := by
  have he : 0 < (2 : ℕ) ^ e := by positivity
  have hf : 0 < (2 : ℕ) ^ f := by positivity
  rw [pow_succ, pow_add]
  nlinarith

lemma mul_exp_bound {a b e f : ℕ} (ha : a ≤ 2 ^ e) (hb : b ≤ 2 ^ f) :
    a * b ≤ 2 ^ (e + f) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

set_option maxHeartbeats 2000000 in
lemma simulation_bound (C D n t q : ℕ) (ht : t ≤ 2 ^ q) :
    GeneralTimeSimulation.bound C D n t ≤ 2 ^ (2 * n + 2 * q + 2 * C + D + 13) := by
  have h₁ := mul_exp_bound ht (nat_le_exp C)
  have h₂ := add_exp_bound (nat_le_exp n) h₁
  have h₃ := add_exp_bound (mul_exp_bound (nat_le_exp 2) h₂) (nat_le_exp 2)
  have h₄ := add_exp_bound (nat_le_exp 1) (mul_exp_bound (nat_le_exp C) h₃)
  have h₅ := add_exp_bound (add_exp_bound (nat_le_exp n) (nat_le_exp 1))
    (mul_exp_bound ht h₄)
  have h₆ := add_exp_bound (mul_exp_bound h₅ (nat_le_exp D)) (nat_le_exp 1)
  convert! h₆ using 1 <;> congr 1 <;> ring

/-- Deterministic polynomial work space is simulated in exponential single-tape time. -/
lemma PSPACE_subset_EXPTIME : PSPACE ⊆ EXPTIME := by
  classical
  rintro A ⟨p, M, hd, hdec, hs⟩
  let e := ConfigurationTime.spaceTimeExponent M p
  have ht : ∀ w n c, M.Run w n c → n ≤ 2 ^ e.eval w.length := by
    intro w n c hr
    exact (ConfigurationTime.polynomial_space_branch_time M p (fun w => (hdec w).1) hs
      w n c hr).le
  let S := SpaceToStack.timeComputer M A hd hdec p.eval (fun n => 2 ^ e.eval n) hs ht
  have hfinite : ∀ k, Finite (S.tm.Γ k) := by
    intro k
    change Finite (SpaceToStack.Alphabet M k)
    infer_instance
  obtain ⟨C, D, N, hN⟩ := GeneralTimeSimulation.finite_stack_time A
    (fun w => decide (w ∈ A)) S (by simp) hfinite
  let q : Polynomial ℕ := e + Polynomial.X + p + 9
  have hq : ∀ n, S.time n ≤ 2 ^ q.eval n := by
    intro n
    have h := add_exp_bound (add_exp_bound (add_exp_bound (le_refl (2 ^ e.eval n))
      (nat_le_exp n)) (nat_le_exp (p.eval n))) (nat_le_exp 6)
    convert! h using 1
    simp [S, SpaceToStack.timeComputer]
    congr 1
    simp [q]
    omega
  let r : Polynomial ℕ := 2 * Polynomial.X + 2 * q + Polynomial.C (2 * C + D + 13)
  refine ⟨N, r, ?_⟩
  intro w
  obtain ⟨c, ⟨hc⟩, hhalt, hanswer⟩ := hN w
  have hb : GeneralTimeSimulation.bound C D w.length (S.time w.length) ≤
      2 ^ r.eval w.length := by
    simpa [r, Nat.add_assoc] using simulation_bound C D w.length (S.time w.length)
      (q.eval w.length) (hq w.length)
  exact ⟨c, ⟨{ hc with steps_le_m := hc.steps_le_m.trans hb }⟩, hhalt, hanswer⟩

end Complexity.ClassesProofs.SpaceExponentialTime
