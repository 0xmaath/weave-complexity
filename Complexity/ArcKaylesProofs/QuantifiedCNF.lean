/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/QuantifiedCNF.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.QuantifiedCNF` to `Complexity.ArcKaylesProofs.QuantifiedCNF`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.QuantifiedSizes
import Complexity.CookLevinProofs.CircuitExtension
import Complexity.CookLevinProofs.Tseitin
import Complexity.CookLevin.GateCorrect

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.Quantified

open Complexity.CookLevin

def assignBlock (start n : ℕ) (v : Vector n) (a : CNF.Assignment) : CNF.Assignment :=
  fun j => if h : start ≤ j ∧ j < start + n then v ⟨j - start, by omega⟩ else a j

theorem assignBlock_before (start n : ℕ) (v : Vector n) (a : CNF.Assignment)
    (j : ℕ) (hj : j < start) : assignBlock start n v a j = a j := by
  simp [assignBlock, Nat.not_le_of_gt hj]

theorem assignBlock_inside (start n : ℕ) (v : Vector n) (a : CNF.Assignment) (i : Fin n) :
    assignBlock start n v a (start + i.val) = v i := by
  have hi : start + i.val < start + n := by omega
  simp [assignBlock, hi]

theorem extendAll_after (start : ℕ) (gates : List Circuits.Gate) (a : CNF.Assignment)
    (j : ℕ) (hj : start + gates.length ≤ j) :
    Complexity.CookLevinProofs.CircuitBuilder.extendAll start gates a j = a j := by
  induction gates generalizing start a with
  | nil => rfl
  | cons g gs ih =>
    rw [Complexity.CookLevinProofs.CircuitBuilder.extendAll, ih (start + 1) _ (by simp_all; omega)]
    exact Function.update_of_ne (by simp only [List.length_cons] at hj; omega) _ _

def fragmentCNF (start : ℕ) (e : Complexity.CookLevinProofs.CircuitBuilder.Expr) : CNF.Formula :=
  let f := Complexity.CookLevinProofs.CircuitBuilder.compile start e
  [[Tseitin.positive f.output]] ++ (f.gates.zipIdx start).flatMap
    (fun gi => Tseitin.gateClauses gi.2 gi.1)

theorem fragmentCNF_eval (start : ℕ) (e : Complexity.CookLevinProofs.CircuitBuilder.Expr) (a : CNF.Assignment) :
    CNF.eval (fragmentCNF start e) a = true ↔
      a (Complexity.CookLevinProofs.CircuitBuilder.compile start e).output = true ∧
      Complexity.CookLevinProofs.CircuitBuilder.Satisfies start
        (Complexity.CookLevinProofs.CircuitBuilder.compile start e).gates a := by
  rw [fragmentCNF, Complexity.CookLevinProofs.eval_append, Complexity.CookLevinProofs.eval_flatMap]
  simp only [Bool.and_eq_true, List.all_eq_true, GateCorrect.correct]
  simp [CNF.eval, CNF.Literal.eval, Tseitin.positive,
    Complexity.CookLevinProofs.CircuitBuilder.Satisfies, Prod.forall]

theorem fragmentCNF_exists (start : ℕ) (e : Complexity.CookLevinProofs.CircuitBuilder.Expr)
    (he : e.Bounded start) (a : CNF.Assignment) :
    (∃ v : Vector (Complexity.CookLevinProofs.CircuitBuilder.compile start e).gates.length,
      CNF.eval (fragmentCNF start e)
        (assignBlock start (Complexity.CookLevinProofs.CircuitBuilder.compile start e).gates.length v a) = true) ↔
      e.eval a = true := by
  open Complexity.CookLevinProofs.CircuitBuilder in
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨ho, hs⟩ := (fragmentCNF_eval start e _).mp hv
    have hout := compile_sound start e _ hs
    have hagree := expr_agrees e start _ a he (assignBlock_before start _ v a)
    exact hagree ▸ hout ▸ ho
  · intro hv
    let gs := (compile start e).gates
    let s := extendAll start gs a
    let v : Vector gs.length := fun i => s (start + i.val)
    have hbefore := extendAll_before start gs a
    have hafter := extendAll_after start gs a
    have heq : assignBlock start gs.length v a = s := by
      funext j
      by_cases hi : start ≤ j ∧ j < start + gs.length
      · simp only [assignBlock, dif_pos hi, v]
        congr 1; omega
      · rw [assignBlock, dif_neg hi]
        by_cases hj : j < start
        · exact (hbefore j hj).symm
        · exact (hafter j (by omega)).symm
    refine ⟨v, ?_⟩
    change CNF.eval (fragmentCNF start e) (assignBlock start gs.length v a) = true
    rw [heq, fragmentCNF_eval]
    have hs := extendAll_satisfies start gs a (compile_ordered start e he)
    refine ⟨?_, hs⟩
    rw [compile_sound start e s hs, expr_agrees e start s a he hbefore]
    exact hv

def Expr.toCircuit {α : Type} (index : α → ℕ) : Expr α → Complexity.CookLevinProofs.CircuitBuilder.Expr
  | .var i => .wire (index i)
  | .constant b => .constant b
  | .neg p => .neg (p.toCircuit index)
  | .conj p q => .conj (p.toCircuit index) (q.toCircuit index)
  | .disj p q => .disj (p.toCircuit index) (q.toCircuit index)

theorem Expr.toCircuit_eval {α : Type} (index : α → ℕ) (p : Expr α) (a : CNF.Assignment) :
    (p.toCircuit index).eval a = p.eval (a ∘ index) := by
  induction p <;> simp_all [Expr.toCircuit, Expr.eval, Complexity.CookLevinProofs.CircuitBuilder.Expr.eval]

theorem Expr.toCircuit_bounded {α : Type} (index : α → ℕ) (p : Expr α) (n : ℕ)
    (h : ∀ i, index i < n) : (p.toCircuit index).Bounded n := by
  induction p <;> simp_all [Expr.toCircuit, Complexity.CookLevinProofs.CircuitBuilder.Expr.Bounded]

abbrev Prefix := List (Bool × ℕ)

def Prefix.Holds (cs : CNF.Formula) : Prefix → ℕ → CNF.Assignment → Prop
  | [], _, a => CNF.eval cs a = true
  | (all, k) :: qs, n, a =>
      if all then ∀ v, Prefix.Holds cs qs (n + k) (assignBlock n k v a)
      else ∃ v, Prefix.Holds cs qs (n + k) (assignBlock n k v a)

def bindIndex {α : Type} (start : ℕ) (index : α → ℕ) {k : ℕ} : Fin k ⊕ α → ℕ :=
  Sum.elim (fun i => start + i.val) index

theorem bindIndex_bounded {α : Type} (start : ℕ) (index : α → ℕ) (k : ℕ)
    (h : ∀ i, index i < start) : ∀ i : Fin k ⊕ α, bindIndex start index i < start + k := by
  intro i; cases i with
  | inl i => change start + i.val < start + k; omega
  | inr i => exact (h i).trans_le (Nat.le_add_right _ _)

theorem assignBlock_bindIndex {α : Type} (start : ℕ) (index : α → ℕ) (k : ℕ)
    (h : ∀ i, index i < start) (v : Vector k) (a : CNF.Assignment) :
    assignBlock start k v a ∘ bindIndex start index = Sum.elim v (a ∘ index) := by
  funext i
  cases i with
  | inl i => exact assignBlock_inside start k v a i
  | inr i => exact assignBlock_before start k v a _ (h i)

def Formula.toCNF {α : Type} : Formula α → (α → ℕ) → ℕ → Prefix × CNF.Formula
  | .matrix p, index, start =>
      let e := p.toCircuit index
      ([(false, (Complexity.CookLevinProofs.CircuitBuilder.compile start e).gates.length)], fragmentCNF start e)
  | .ex k p, index, start =>
      let next := p.toCNF (bindIndex start index) (start + k)
      ((false, k) :: next.1, next.2)
  | .all k p, index, start =>
      let next := p.toCNF (bindIndex start index) (start + k)
      ((true, k) :: next.1, next.2)

theorem Formula.toCNF_correct {α : Type} (p : Formula α) (index : α → ℕ)
    (start : ℕ) (h : ∀ i, index i < start) (a : CNF.Assignment) :
    (p.toCNF index start).1.Holds (p.toCNF index start).2 start a ↔ p.Holds (a ∘ index) := by
  induction p generalizing start a with
  | matrix p =>
    simp only [Formula.toCNF, Prefix.Holds, Bool.false_eq_true, ↓reduceIte]
    rw [fragmentCNF_exists start _ (Expr.toCircuit_bounded index p start h), Expr.toCircuit_eval]
    rfl
  | ex k p ih =>
    simp only [Formula.toCNF, Prefix.Holds, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
    apply exists_congr
    intro v
    rw [ih _ _ (bindIndex_bounded start index k h), assignBlock_bindIndex start index k h]
  | all k p ih =>
    simp only [Formula.toCNF, Prefix.Holds, Bool.true_eq, ↓reduceIte, Formula.Holds]
    apply forall_congr'
    intro v
    rw [ih _ _ (bindIndex_bounded start index k h), assignBlock_bindIndex start index k h]

end Complexity.ArcKaylesProofs.Quantified
