/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/EncodedSymbols.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.EncodedSymbols` to `Complexity.ArcKaylesProofs.EncodedSymbols`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.PatternExpressions
import Complexity.ArcKaylesProofs.QuantifiedSizes
import Complexity.ClassicalProofs.SavitchProofs.FiniteCoding

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.Quantified

noncomputable def symbolTest {n : ℕ} {α β : Type} (decode : Vector n → α)
    (xs : Wires n β) (S : Set α) : Expr β := by
  classical
  exact Expr.any (Finset.univ.toList.map fun v : Vector n =>
    Expr.conj (.constant (decide (decode v ∈ S))) (vectorEq xs (fun i => .constant (v i))))

theorem symbolTest_correct {n : ℕ} {α β : Type} (decode : Vector n → α)
    (xs : Wires n β) (S : Set α) (a : β → Bool) :
    (symbolTest decode xs S).eval a = true ↔ decode (fun i => (xs i).eval a) ∈ S := by
  classical
  rw [symbolTest, Expr.eval_any]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
    simp only [Expr.eval, Bool.and_eq_true, decide_eq_true_eq, vectorEq_eval] at hv
    exact hv.2 ▸ hv.1
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨(fun i => (xs i).eval a), by simp, rfl⟩, ?_⟩
    simp only [Expr.eval, Bool.and_eq_true, decide_eq_true_eq, vectorEq_eval]
    exact ⟨h, trivial⟩

noncomputable def Symbol.fromWires {n : ℕ} {α β : Type} (decode : Vector n → α)
    (xs : Wires n β) : Symbol α β where
  value a := decode (fun i => (xs i).eval a)
  test := symbolTest decode xs
  correct := symbolTest_correct decode xs

theorem symbolTest_size {n : ℕ} {α β : Type} (decode : Vector n → α)
    (xs : Wires n β) (hx : ∀ i, (xs i).size = 1) (S : Set α) :
    (symbolTest decode xs S).size = 2 ^ n * (10 * n + 4) + 1 := by
  classical
  have hs (v : Vector n) :
      (Expr.conj (.constant (decide (decode v ∈ S)))
        (vectorEq xs (fun i => .constant (v i)))).size = 10 * n + 3 := by
    rw [Expr.size, Expr.size, vectorEq_size xs _ 1 1 hx (by intro i; rfl)]
    omega
  rw [symbolTest, Expr.any_size]
  simp only [List.map_map, Function.comp_def, hs, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, Finset.length_toList,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  ring

def vectorWord {n : ℕ} (v : Vector n) : List Bool := (List.finRange n).map v

theorem vectorWord_length {n : ℕ} (v : Vector n) : (vectorWord v).length = n := by simp [vectorWord]

theorem vectorWord_get {n : ℕ} (v : Vector n) (i : Fin n) : (vectorWord v)[i.val]'(by simp [vectorWord]) = v i := by
  simp [vectorWord]

theorem vectorWord_injective (n : ℕ) : Function.Injective (@vectorWord n) := by
  intro v w h
  funext i
  have hi := congrArg (fun xs : List Bool => xs[i.val]?) h
  simpa [vectorWord, List.getElem?_eq_getElem, i.isLt] using hi

open Complexity.ClassicalProofs.SavitchProofs

noncomputable def codedSymbol (α : Type) [Fintype α] [Inhabited α] {β : Type}
    (xs : Wires (FiniteCoding.width α) β) : Symbol (FiniteCoding.Letter α) β :=
  Symbol.fromWires (fun v => FiniteCoding.decodeBlock α (vectorWord v)) xs

def blockWires {β : Type} (xs : List (Expr β)) (start width : ℕ) : Wires width β :=
  fun i => (xs[start + i.val]?).getD (.constant false)

theorem blockWires_eval {β : Type} (xs : List (Expr β)) (start width : ℕ) (a : β → Bool)
    (h : start + width ≤ xs.length) :
    vectorWord (fun i => (blockWires xs start width i).eval a) =
      ((xs.map (Expr.eval a)).drop start).take width := by
  apply List.ext_getElem
  · simp [vectorWord, List.length_take, List.length_drop]; omega
  · intro j hj hk
    have hjw : j < width := by simpa [vectorWord] using hj
    have hjx : start + j < xs.length := by omega
    simp [vectorWord, blockWires, List.getElem?_eq_getElem, hjx, Nat.add_comm]

end Complexity.ArcKaylesProofs.Quantified
