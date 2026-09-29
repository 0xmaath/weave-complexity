/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/ListTraversal.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.ListTraversal` to `Complexity.ArcKaylesProofs.ListTraversal`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Mathlib.Data.List.Range
import Mathlib.Tactic

namespace Complexity.ArcKaylesProofs.CNFTraversal

theorem range_heads {α β : Type} (f : List α → List β) (g : α → List β)
    (hnil : f [] = []) (hcons : ∀ x xs, f (x :: xs) = g x)
    (xs : List α) (n : ℕ) (hn : xs.length ≤ n) :
    (List.range n).flatMap (fun j => f (xs.drop j)) = xs.flatMap g := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := by simpa using hn
    simp [he]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    cases xs with
    | nil => simp [hnil]
    | cons x xs =>
      simp only [List.drop_zero, hcons, Function.comp_def, List.drop_succ_cons, List.flatMap_cons]
      rw [ih xs (by simpa using hn)]

theorem exists_heads {α : Type} (P : List α → Prop) (Q : α → Prop)
    (hnil : ¬ P []) (hcons : ∀ x xs, P (x :: xs) ↔ Q x)
    (xs : List α) (n : ℕ) (hn : xs.length ≤ n) :
    (∃ j < n, P (xs.drop j)) ↔ ∃ x ∈ xs, Q x := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := by simpa using hn
    simp [he]
  | succ n ih =>
    cases xs with
    | nil => simp [hnil]
    | cons x xs =>
      have hi := ih xs (show xs.length ≤ n by simpa using hn)
      constructor
      · rintro ⟨j, hj, hp⟩
        cases j with
        | zero => exact ⟨x, by simp, (hcons x xs).mp hp⟩
        | succ j =>
          obtain ⟨y, hy, hq⟩ := hi.mp ⟨j, by omega, by simpa using hp⟩
          exact ⟨y, by simp [hy], hq⟩
      · rintro ⟨y, hy, hq⟩
        rcases List.mem_cons.mp hy with he | hy
        · subst y; exact ⟨0, by omega, (hcons x xs).mpr hq⟩
        · obtain ⟨j, hj, hp⟩ := hi.mpr ⟨y, hy, hq⟩
          exact ⟨j + 1, by omega, by simpa using hp⟩

end Complexity.ArcKaylesProofs.CNFTraversal
