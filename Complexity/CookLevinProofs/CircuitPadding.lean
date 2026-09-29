/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/CircuitPadding.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.CircuitPadding` to `Complexity.CookLevinProofs.CircuitPadding`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.CircuitExpressionLists

namespace Complexity.CookLevinProofs.CircuitBuilder

open Complexity.CookLevin.CNF

def pad : ℕ → Expr → Expr
  | 0, e => e
  | k + 1, e => .conj (pad k e) (.constant true)

lemma pad_eval (k : ℕ) (e : Expr) (ρ : Assignment) : (pad k e).eval ρ = e.eval ρ := by
  induction k <;> simp_all [pad, Expr.eval]

lemma pad_cost (k : ℕ) (e : Expr) : (pad k e).cost = e.cost + 2 * k := by
  induction k <;> simp_all [pad, Expr.cost] <;> omega

lemma pad_bounded (k : ℕ) (e : Expr) (n : ℕ) (h : e.Bounded n) : (pad k e).Bounded n := by
  induction k with
  | zero => exact h
  | succ k ih => exact ⟨ih, trivial⟩

end Complexity.CookLevinProofs.CircuitBuilder
