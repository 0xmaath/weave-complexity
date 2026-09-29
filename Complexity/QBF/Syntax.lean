/-
Milestone 2: quantified Boolean formulas.

A QBF in prenex form is a quantifier prefix `Q_0 x_0 ⋯ Q_{n-1} x_{n-1}` over an unquantified
Boolean formula (the matrix) built from variables, negation, conjunction and disjunction
(Arora–Barak, Definition 4.9; Sipser, §8.3). The prefix is a list of Booleans, `true` for a
universal quantifier and `false` for an existential one; variable `i` is bound by the `i`-th
quantifier. A formula is closed when every variable of the matrix is bound.
-/
import Complexity.Classes.PolynomialTime
import Mathlib.Tactic

namespace Complexity.QBF

open Complexity.Classes.PolynomialTime

/-- Unquantified Boolean formulas over variables indexed by natural numbers. -/
inductive Expr
  | var (i : ℕ)
  | not (p : Expr)
  | and (p q : Expr)
  | or (p q : Expr)
  deriving DecidableEq

namespace Expr

def eval (ρ : ℕ → Bool) : Expr → Bool
  | var i => ρ i
  | not p => !p.eval ρ
  | and p q => p.eval ρ && q.eval ρ
  | or p q => p.eval ρ || q.eval ρ

/-- Every variable is below `n`. -/
def Bounded (n : ℕ) : Expr → Prop
  | var i => i < n
  | not p => p.Bounded n
  | and p q => p.Bounded n ∧ q.Bounded n
  | or p q => p.Bounded n ∧ q.Bounded n

/-- Number of nodes. -/
def size : Expr → ℕ
  | var _ => 1
  | not p => p.size + 1
  | and p q => p.size + q.size + 1
  | or p q => p.size + q.size + 1

theorem size_pos (p : Expr) : 0 < p.size := by
  cases p <;> simp [size]

/-- Evaluation only depends on the bounded variables. -/
theorem eval_congr {n : ℕ} {p : Expr} (hp : p.Bounded n) {ρ σ : ℕ → Bool}
    (h : ∀ i, i < n → ρ i = σ i) : p.eval ρ = p.eval σ := by
  induction p with
  | var i => exact h i hp
  | not p ih => simp [eval, ih hp]
  | and p q ihp ihq => simp [eval, ihp hp.1, ihq hp.2]
  | or p q ihp ihq => simp [eval, ihp hp.1, ihq hp.2]

end Expr

/-- A prenex quantified Boolean formula: `quantifiers[i] = true` means `∀ x_i`, `false`
means `∃ x_i`. -/
structure Formula where
  quantifiers : List Bool
  matrix : Expr
  deriving DecidableEq

/-- `Holds M qs k ρ`: the formula `Q_k x_k ⋯ Q_{k+|qs|-1} x_{k+|qs|-1}. M` is true under the
assignment `ρ` of the variables below `k`. -/
def Holds (M : Expr) : List Bool → ℕ → (ℕ → Bool) → Prop
  | [], _, ρ => M.eval ρ = true
  | q :: qs, k, ρ =>
      if q then ∀ b : Bool, Holds M qs (k + 1) (Function.update ρ k b)
      else ∃ b : Bool, Holds M qs (k + 1) (Function.update ρ k b)

namespace Formula

def Closed (φ : Formula) : Prop := φ.matrix.Bounded φ.quantifiers.length

/-- Truth of a (closed) QBF. The initial assignment is irrelevant for closed formulas. -/
def IsTrue (φ : Formula) : Prop := Holds φ.matrix φ.quantifiers 0 (fun _ => false)

end Formula

/-- `Holds` only depends on the variables below `k` that the matrix mentions. -/
theorem Holds_congr (M : Expr) (qs : List Bool) (k : ℕ) (hM : M.Bounded (k + qs.length))
    {ρ σ : ℕ → Bool} (h : ∀ i, i < k → ρ i = σ i) : Holds M qs k ρ ↔ Holds M qs k σ := by
  induction qs generalizing k ρ σ with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at hM
    simp [Holds, Expr.eval_congr hM h]
  | cons q qs ih =>
    have hM' : M.Bounded (k + 1 + qs.length) := by
      rw [show k + 1 + qs.length = k + (qs.length + 1) by omega]; exact hM
    have hupd : ∀ b, ∀ i, i < k + 1 → Function.update ρ k b i = Function.update σ k b i := by
      intro b i hi
      by_cases hik : i = k
      · subst hik; simp
      · rw [Function.update_of_ne hik, Function.update_of_ne hik]
        exact h i (by omega)
    simp only [Holds]
    split
    · exact forall_congr' fun b => ih (k + 1) hM' (hupd b)
    · exact exists_congr fun b => ih (k + 1) hM' (hupd b)

end Complexity.QBF
