/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/UniformPrefix.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.UniformPrefix` to `Complexity.ArcKaylesProofs.UniformPrefix`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.UniformPatterns

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.CircuitStreaming

open Complexity.CookLevinProofs.CircuitBuilder Complexity.CookLevinProofs.Streaming
open Complexity.Classes.PolynomialTime
open Complexity.ClassesProofs.SavitchProofs.PatternAutomata

theorem matches_prefix_slice {α : Type} (ps : List (Set α)) (f : ℕ → α) (start n : ℕ) :
    Matches (ps.map Piece.one ++ [.star Set.univ]) (slice f start n) ↔
      ps.length ≤ n ∧ ∀ j (hj : j < ps.length), f (start + j) ∈ ps[j] := by
  induction ps generalizing start n with
  | nil => simp [slice]
  | cons S ps ih =>
    cases n with
    | zero => simp [slice_zero, Matches]
    | succ n =>
      rw [slice_cons]
      simp only [List.map_cons, List.cons_append, Matches, List.cons.injEq]
      have he : (∃ a ∈ S, ∃ tail, (f start = a ∧ slice f (start + 1) n = tail) ∧
          Matches (ps.map Piece.one ++ [.star Set.univ]) tail) ↔
          f start ∈ S ∧ Matches (ps.map Piece.one ++ [.star Set.univ]) (slice f (start + 1) n) := by
        simp
      rw [he, ih]
      constructor
      · rintro ⟨hf, hlen, hrest⟩
        refine ⟨by simp; omega, ?_⟩
        intro j hj
        cases j with
        | zero => simpa using hf
        | succ j => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest j (by simpa using hj)
      · rintro ⟨hlen, h⟩
        refine ⟨by simpa using h 0 (by simp), by simpa using hlen, ?_⟩
        intro j hj
        have hh := h (j + 1) (by simpa using hj)
        simp only [List.getElem_cons_succ] at hh
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def prefixCheck {I : Type} (count length : Number I) (term : Expression (Option I)) : Expression I :=
  (Expression.constant (Test.lt count length).not).conj (variableFold true length term)

theorem prefixCheck_correct {α I : Type} (count length : Number I) (term : Expression (Option I))
    (a : I → Word) (ρ : ℕ → Bool) (ps : List (Set α)) (f : ℕ → α)
    (hlen : length.value a = ps.length)
    (ht : ∀ j (hj : j < ps.length),
      (term.value (extend a (List.replicate j true))).eval ρ = true ↔ f j ∈ ps[j]) :
    ((prefixCheck count length term).value a).eval ρ = true ↔
      Matches (ps.map Piece.one ++ [.star Set.univ]) (slice f 0 (count.value a)) := by
  rw [matches_prefix_slice]
  simp only [prefixCheck, Expression.conj, Expression.binary, Bool.true_eq, ↓reduceIte,
    Expr.eval, Expression.constant, Test.not, Test.lt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt, variableFold_true_eval, hlen, Nat.zero_add]
  exact and_congr_right' (forall_congr' (fun j => forall_congr' (fun hj => ht j hj)))

end Complexity.ArcKaylesProofs.CircuitStreaming
