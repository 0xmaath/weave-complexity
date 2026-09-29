/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/OutputDivision.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.OutputDivision` to `Complexity.CookLevinProofs.OutputDivision`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.OutputTests

set_option backward.isDefEq.respectTransparency false

namespace Complexity.CookLevinProofs.Streaming

open Complexity.Classes.PolynomialTime

lemma selected_prefix (n bound : ℕ) :
    ((List.range n).flatMap fun i => if i < bound then [true] else []) =
      List.replicate (min n bound) true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases h : n < bound
    · have h1 : n ≤ bound := by omega
      have h2 : n + 1 ≤ bound := by omega
      simp [h, Nat.min_eq_left h1, Nat.min_eq_left h2, List.replicate_succ']
    · have h1 : bound ≤ n := by omega
      have h2 : bound ≤ n + 1 := by omega
      simp [h, Nat.min_eq_right h1, Nat.min_eq_right h2]

lemma quotient_tokens (n d : ℕ) :
    ((List.range n).flatMap fun i => if (i + 1) * d < n + 1 ∧ 0 < d then [true] else []) =
      List.replicate (n / d) true := by
  by_cases hd : d = 0
  · simp [hd]
  · have hd' : 0 < d := by omega
    have he : ∀ i, (i + 1) * d < n + 1 ∧ 0 < d ↔ i < n / d := by
      intro i
      rw [Nat.lt_succ_iff, and_iff_left hd', ← Nat.le_div_iff_mul_le hd']
      omega
    simp only [he]
    rw [selected_prefix, Nat.min_eq_right (Nat.div_le_self n d)]

variable {I : Type}

def Number.div (n d : Number I) : Number I where
  value a := n.value a / d.value a
  code := Code.loop n (Code.when
    ((Test.lt (((Number.length none).add (.constant 1)).mul (d.rename some))
      ((n.rename some).add (.constant 1))).and (Test.lt (.constant 0) (d.rename some)))
    (.literal [true]) (.literal []))
  correct a := by
    simp only [Code.eval_loop, Code.eval_when, Test.and, Test.lt, Number.add, Number.mul,
      Number.length, Number.constant, Number.rename, extend_some, extend, Option.elim_none,
      List.length_replicate, Code.eval, Bool.and_eq_true, decide_eq_true_eq]
    exact quotient_tokens (n.value a) (d.value a)

def Number.mod (n d : Number I) : Number I where
  value a := n.value a % d.value a
  code := (n.sub (d.mul (n.div d))).code
  correct a := by
    rw [Number.correct]
    simp only [Number.sub, Number.mul, Number.div, Nat.mod_eq_sub_mul_div]

end Complexity.CookLevinProofs.Streaming
