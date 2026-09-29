/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/UniformConfigurationSymbols.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.UniformConfigurationSymbols` to `Complexity.ArcKaylesProofs.UniformConfigurationSymbols`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.UniformPatterns
import Complexity.ArcKaylesProofs.ConfigurationExpressions

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.CircuitStreaming

open Complexity.CookLevinProofs.CircuitBuilder Complexity.CookLevinProofs.Streaming
open Complexity.Classical.PolynomialTime
open Complexity.ClassicalProofs.SavitchProofs

theorem decodeWord_slices (α : Type) [Fintype α] [Inhabited α] (n : ℕ) (xs : Word)
    (hx : xs.length = FiniteCoding.width α * n) :
    FiniteCoding.decodeWord α xs = slice
      (fun j => FiniteCoding.decodeBlock α ((xs.drop (j * FiniteCoding.width α)).take (FiniteCoding.width α))) 0 n := by
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := by simpa using hx
    simp [he, slice_zero]
  | succ n ih =>
    have hw := FiniteCoding.width_pos α
    have hne : xs ≠ [] := by
      intro he
      have hlen := congrArg List.length he
      simp only [List.length_nil] at hlen
      have hp : 0 < FiniteCoding.width α * (n + 1) := by positivity
      omega
    rw [FiniteCoding.decodeWord, if_neg hne, slice_cons]
    simp only [Nat.zero_mul, List.drop_zero, Nat.zero_add]
    congr 1
    rw [ih _ (by simp only [List.length_drop, hx, Nat.mul_succ, Nat.add_sub_cancel])]
    apply List.ext_getElem <;>
      simp [slice, List.drop_drop, Nat.add_mul, Nat.add_comm, Nat.add_left_comm]

theorem vectorWord_slice (ρ : ℕ → Bool) (base width : ℕ) :
    Quantified.vectorWord (fun i : Fin width => ρ (base + i.val)) = slice ρ base width := by
  apply List.ext_getElem <;> simp [Quantified.vectorWord, slice]

noncomputable def codedArray (α : Type) [Fintype α] [Inhabited α] {I : Type}
    (base : Number I) : UniformSymbol (FiniteCoding.Letter α) (Option I) :=
  uniformSymbol (fun v : Fin (FiniteCoding.width α) → Bool =>
    FiniteCoding.decodeBlock α (Quantified.vectorWord v))
    (fun b => ((base.rename some).add ((Number.length none).mul (.constant (FiniteCoding.width α)))).add
      (.constant b.val))

theorem codedArray_word (α : Type) [Fintype α] [Inhabited α] {I : Type}
    (base : Number I) (a : I → Word) (ρ : ℕ → Bool) (n : ℕ) :
    slice (fun j => (codedArray α base).value (extend a (List.replicate j true)) ρ) 0 n =
      FiniteCoding.decodeWord α (slice ρ (base.value a) (FiniteCoding.width α * n)) := by
  rw [decodeWord_slices α n _ (slice_length _ _ _)]
  apply List.ext_getElem
  · simp [slice]
  · intro j hj hk
    have hjn : j < n := by simpa [slice] using hj
    have hbound : FiniteCoding.width α ≤ FiniteCoding.width α * n - j * FiniteCoding.width α := by
      have hw := FiniteCoding.width_pos α
      have hmul := Nat.mul_le_mul_left (FiniteCoding.width α) (show j + 1 ≤ n by omega)
      apply Nat.le_sub_of_add_le
      nlinarith
    simp only [slice, List.getElem_map, List.getElem_range, Nat.zero_add]
    simp only [codedArray, uniformSymbol, Number.add, Number.mul, Number.constant,
      Number.rename, Number.length, extend_some, extend, Option.elim_none, List.length_replicate]
    change FiniteCoding.decodeBlock α (Quantified.vectorWord (fun i =>
      ρ (base.value a + j * FiniteCoding.width α + i.val))) = _
    rw [vectorWord_slice, ← slice]
    rw [slice_drop, slice_take _ _ _ _ hbound]

theorem pairedArray_word (α : Type) [Fintype α] [Inhabited α] {I : Type}
    (left right : Number I) (a : I → Word) (ρ : ℕ → Bool) (n : ℕ) :
    slice (fun j => ((codedArray α left).pair (codedArray α right)).value
      (extend a (List.replicate j true)) ρ) 0 n =
      List.zip (FiniteCoding.decodeWord α (slice ρ (left.value a) (FiniteCoding.width α * n)))
        (FiniteCoding.decodeWord α (slice ρ (right.value a) (FiniteCoding.width α * n))) := by
  rw [← codedArray_word α left a ρ n, ← codedArray_word α right a ρ n]
  apply List.ext_getElem <;> simp [slice, UniformSymbol.pair]

end Complexity.ArcKaylesProofs.CircuitStreaming
