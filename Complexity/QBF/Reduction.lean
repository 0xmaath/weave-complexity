/-
Milestone 2: translating the ported signed-CNF language into TQBF (formula level).

The ported Arc Kayles proof shows PSPACE-hardness of `Byskov.signedLanguage`: instances are
signed CNF formulas over `r` rounds, true when `∀ b₀ ∃ c₀ ∀ b₁ ∃ c₁ ⋯` the CNF is satisfied,
where the literal `(i, existential, positive)` reads `c_i` or `b_i` and compares it with its
sign. This is a prenex QBF with the alternating prefix `∀ x₀ ∃ x₁ ∀ x₂ ∃ x₃ ⋯` (variable
`2i` is `b_i`, variable `2i+1` is `c_i`) and a CNF matrix. `translate` builds that QBF with a
uniform matrix shape: every clause is a left-deep disjunction of one 14-node gadget per
variable, and the gadget of variable `u` in clause `K` evaluates to `x_u` when the positive
literal is present, `¬x_u` when the negative literal is present, their disjunction when both
are, and `false` when neither is. `translate_true` is the semantic equivalence.
-/
import Complexity.QBF.Encoding
import Complexity.ArcKaylesProofs.ByskovEncoding

namespace Complexity.QBF.Reduction

open Complexity.ArcKaylesProofs.Byskov
open Complexity.Classes.PolynomialTime

/-! ### Gadgets -/

/-- Presence of the positive literal of variable `u` in a clause. -/
def posIn {r : ℕ} (K : Finset (SignedLiteral r)) (u : ℕ) : Bool :=
  decide (∃ l ∈ K, l.index.val = 2 * u + 1)

/-- Presence of the negative literal of variable `u` in a clause. -/
def negIn {r : ℕ} (K : Finset (SignedLiteral r)) (u : ℕ) : Bool :=
  decide (∃ l ∈ K, l.index.val = 2 * u)

/-- `x ∧ ¬x`: always false. -/
def falseA (u : ℕ) : Expr := .and (.var u) (.not (.var u))

/-- `false ∨ x` or `false ∧ x`. -/
def branchB (p : Bool) (u : ℕ) : Expr :=
  if p then .or (falseA u) (.var u) else .and (falseA u) (.var u)

/-- `false ∨ ¬x` or `false ∧ ¬x`. -/
def branchC (q : Bool) (u : ℕ) : Expr :=
  if q then .or (falseA u) (.not (.var u)) else .and (falseA u) (.not (.var u))

/-- The literal gadget of variable `u`. -/
def slot (p q : Bool) (u : ℕ) : Expr := .or (branchB p u) (branchC q u)

def clauseExpr (r : ℕ) {r' : ℕ} (K : Finset (SignedLiteral r')) : Expr :=
  (List.range (2 * r)).foldl (fun acc u => .or acc (slot (posIn K u) (negIn K u) u)) (slot false false 0)

def matrixExpr (r : ℕ) (F : SignedCNF r) : Expr :=
  F.foldl (fun acc K => .and acc (clauseExpr r K)) (slot true true 0)

def prefixOf (r : ℕ) : List Bool := (List.range (2 * r)).map fun u => decide (u % 2 = 0)

def translate (r : ℕ) (F : SignedCNF r) : Formula := ⟨prefixOf r, matrixExpr r F⟩

/-! ### Evaluation -/

theorem falseA_eval (u : ℕ) (ρ : ℕ → Bool) : (falseA u).eval ρ = false := by
  simp [falseA, Expr.eval]

theorem slot_eval (p q : Bool) (u : ℕ) (ρ : ℕ → Bool) :
    (slot p q u).eval ρ = ((p && ρ u) || (q && !ρ u)) := by
  cases p <;> cases q <;> simp [slot, branchB, branchC, Expr.eval, falseA_eval]

theorem foldl_or_eval (f : ℕ → Expr) (l : List ℕ) (init : Expr) (ρ : ℕ → Bool) :
    (l.foldl (fun acc u => Expr.or acc (f u)) init).eval ρ = true ↔
      init.eval ρ = true ∨ ∃ u ∈ l, (f u).eval ρ = true := by
  induction l generalizing init with
  | nil => simp
  | cons u l ih =>
    rw [List.foldl_cons, ih]
    simp only [Expr.eval, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

theorem foldl_and_eval {α : Type} (f : α → Expr) (l : List α) (init : Expr) (ρ : ℕ → Bool) :
    (l.foldl (fun acc K => Expr.and acc (f K)) init).eval ρ = true ↔
      init.eval ρ = true ∧ ∀ K ∈ l, (f K).eval ρ = true := by
  induction l generalizing init with
  | nil => simp
  | cons K l ih =>
    rw [List.foldl_cons, ih]
    simp only [Expr.eval, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

theorem clauseExpr_eval (r : ℕ) {r' : ℕ} (K : Finset (SignedLiteral r')) (ρ : ℕ → Bool) :
    (clauseExpr r K).eval ρ = true ↔
      ∃ u, u < 2 * r ∧ ((posIn K u && ρ u) || (negIn K u && !ρ u)) = true := by
  unfold clauseExpr
  rw [foldl_or_eval]
  simp [slot_eval, List.mem_range]

theorem matrixExpr_eval (r : ℕ) (F : SignedCNF r) (ρ : ℕ → Bool) :
    (matrixExpr r F).eval ρ = true ↔ ∀ K ∈ F, (clauseExpr r K).eval ρ = true := by
  unfold matrixExpr
  rw [foldl_and_eval]
  simp [slot_eval]

/-! ### Closedness -/

theorem slot_bounded (p q : Bool) (u n : ℕ) (h : u < n) : (slot p q u).Bounded n := by
  cases p <;> cases q <;> simp [slot, branchB, branchC, falseA, Expr.Bounded, h]

theorem foldl_or_bounded (f : ℕ → Expr) (l : List ℕ) (init : Expr) (n : ℕ) (hi : init.Bounded n)
    (hf : ∀ u ∈ l, (f u).Bounded n) :
    (l.foldl (fun acc u => Expr.or acc (f u)) init).Bounded n := by
  induction l generalizing init with
  | nil => exact hi
  | cons u l ih =>
    rw [List.foldl_cons]
    exact ih _ ⟨hi, hf u List.mem_cons_self⟩ (fun v hv => hf v (List.mem_cons_of_mem _ hv))

theorem foldl_and_bounded {α : Type} (f : α → Expr) (l : List α) (init : Expr) (n : ℕ)
    (hi : init.Bounded n) (hf : ∀ K ∈ l, (f K).Bounded n) :
    (l.foldl (fun acc K => Expr.and acc (f K)) init).Bounded n := by
  induction l generalizing init with
  | nil => exact hi
  | cons K l ih =>
    rw [List.foldl_cons]
    exact ih _ ⟨hi, hf K List.mem_cons_self⟩ (fun v hv => hf v (List.mem_cons_of_mem _ hv))

theorem prefixOf_length (r : ℕ) : (prefixOf r).length = 2 * r := by simp [prefixOf]

theorem translate_closed (r : ℕ) (hr : 1 ≤ r) (F : SignedCNF r) : (translate r F).Closed := by
  show (matrixExpr r F).Bounded (prefixOf r).length
  rw [prefixOf_length]
  apply foldl_and_bounded _ _ _ _ (slot_bounded _ _ _ _ (by omega))
  intro K _
  apply foldl_or_bounded _ _ _ _ (slot_bounded _ _ _ _ (by omega))
  intro u hu
  exact slot_bounded _ _ _ _ (List.mem_range.mp hu)

/-! ### Assignments -/

/-- The QBF assignment corresponding to a round assignment. -/
def ρOf {r : ℕ} (a : Assignment r) : ℕ → Bool := fun i =>
  if h : i / 2 < r then (if i % 2 = 0 then (a ⟨i / 2, h⟩).1 else (a ⟨i / 2, h⟩).2) else false

theorem ρOf_apply {r : ℕ} (a : Assignment r) (i : Fin r) (e : Bool) :
    ρOf a (2 * i.val + if e then 1 else 0) = (if e then (a i).2 else (a i).1) := by
  have hi := i.isLt
  cases e <;> simp [ρOf, Nat.mul_add_div, Nat.mul_add_mod, hi]

theorem literal_value {r : ℕ} (l : SignedLiteral r) (a : Assignment r) :
    l.value a = true ↔ ρOf a (2 * l.round.val + if l.existential then 1 else 0) = l.positive := by
  rw [ρOf_apply]
  simp only [SignedLiteral.value, decide_eq_true_eq]

theorem index_val {r : ℕ} (l : SignedLiteral r) :
    l.index.val = 2 * (2 * l.round.val + if l.existential then 1 else 0) + if l.positive then 1 else 0 := by
  simp only [SignedLiteral.index]
  split <;> split <;> omega

theorem satisfied_iff {r : ℕ} (F : SignedCNF r) (a : Assignment r) :
    F.Satisfied a ↔ (matrixExpr r F).eval (ρOf a) = true := by
  rw [matrixExpr_eval]
  unfold SignedCNF.Satisfied
  apply forall_congr'; intro K
  apply forall_congr'; intro _
  rw [clauseExpr_eval]
  constructor
  · rintro ⟨l, hl, hv⟩
    refine ⟨2 * l.round.val + if l.existential then 1 else 0, ?_, ?_⟩
    · have := l.round.isLt; split <;> omega
    · rw [literal_value] at hv
      cases hp : l.positive
      · rw [hp] at hv
        have hn : negIn K (2 * l.round.val + if l.existential then 1 else 0) = true := by
          simp only [negIn, decide_eq_true_eq]
          exact ⟨l, hl, by rw [index_val, hp]; simp⟩
        simp [hn, hv]
      · rw [hp] at hv
        have hn : posIn K (2 * l.round.val + if l.existential then 1 else 0) = true := by
          simp only [posIn, decide_eq_true_eq]
          exact ⟨l, hl, by rw [index_val, hp]; simp⟩
        simp [hn, hv]
  · rintro ⟨u, hu, hv⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hv
    rcases hv with ⟨hp, hρ⟩ | ⟨hn, hρ⟩
    · simp only [posIn, decide_eq_true_eq] at hp
      obtain ⟨l, hl, hi⟩ := hp
      rw [index_val] at hi
      have hpos : l.positive = true := by
        by_contra hc
        simp only [Bool.not_eq_true] at hc
        rw [hc] at hi; simp at hi; omega
      have hu' : u = 2 * l.round.val + if l.existential then 1 else 0 := by
        rw [hpos] at hi; simp at hi; omega
      refine ⟨l, hl, ?_⟩
      rw [literal_value, ← hu', hρ, hpos]
    · simp only [negIn, decide_eq_true_eq] at hn
      obtain ⟨l, hl, hi⟩ := hn
      rw [index_val] at hi
      have hneg : l.positive = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        rw [hc] at hi; simp at hi; omega
      have hu' : u = 2 * l.round.val + if l.existential then 1 else 0 := by
        rw [hneg] at hi; simp at hi; omega
      refine ⟨l, hl, ?_⟩
      rw [literal_value, ← hu', hρ, hneg]

theorem ρOf_update {r : ℕ} (a : Assignment r) (k : Fin r) (b c : Bool) :
    ρOf (Function.update a k (b, c)) =
      Function.update (Function.update (ρOf a) (2 * k.val) b) (2 * k.val + 1) c := by
  funext i
  have hk := k.isLt
  by_cases h1 : i = 2 * k.val + 1
  · subst h1
    simp [ρOf, Nat.mul_add_div, Nat.mul_add_mod, hk]
  · rw [Function.update_of_ne h1]
    by_cases h0 : i = 2 * k.val
    · subst h0
      simp [ρOf, Nat.mul_div_cancel_left, hk, Nat.mul_mod_right]
    · rw [Function.update_of_ne h0]
      simp only [ρOf]
      by_cases hi : i / 2 < r
      · have hne : (⟨i / 2, hi⟩ : Fin r) ≠ k := by
          intro hc
          have := congrArg Fin.val hc
          simp at this
          omega
        simp [hi, Function.update_of_ne hne]
      · simp [hi]

theorem prefixOf_getElem (r k : ℕ) (h : k < (prefixOf r).length) :
    (prefixOf r)[k] = decide (k % 2 = 0) := by
  simp [prefixOf]

theorem truth_iff (r : ℕ) (F : SignedCNF r) :
    ∀ (d : ℕ) (a : Assignment r), d ≤ r →
      (F.TruthFrom ((List.finRange r).drop (r - d)) a ↔
        Holds (matrixExpr r F) ((prefixOf r).drop (2 * (r - d))) (2 * (r - d)) (ρOf a)) := by
  intro d
  induction d with
  | zero =>
    intro a _
    simp only [Nat.sub_zero, List.drop_length, List.length_finRange, prefixOf_length,
      SignedCNF.TruthFrom, Holds]
    rw [show (prefixOf r).drop (2 * r) = [] from List.drop_of_length_le (by rw [prefixOf_length]),
      show (List.finRange r).drop r = [] from List.drop_of_length_le (by simp)]
    simp only [Holds, SignedCNF.TruthFrom]
    exact satisfied_iff F a
  | succ d ih =>
    intro a hd
    have hk : r - (d + 1) < r := by omega
    have hkd : r - (d + 1) + 1 = r - d := by omega
    have hfin : (List.finRange r).drop (r - (d + 1)) =
        ⟨r - (d + 1), hk⟩ :: (List.finRange r).drop (r - d) := by
      rw [List.drop_eq_getElem_cons (by simpa using hk), List.getElem_finRange, hkd]
      rfl
    have hpre : (prefixOf r).drop (2 * (r - (d + 1))) =
        true :: false :: (prefixOf r).drop (2 * (r - d)) := by
      rw [List.drop_eq_getElem_cons (by rw [prefixOf_length]; omega), prefixOf_getElem,
        List.drop_eq_getElem_cons (by rw [prefixOf_length]; omega), prefixOf_getElem]
      simp only [Nat.mul_mod_right, decide_true, Nat.mul_add_mod, Nat.one_mod]
      rw [show 2 * (r - (d + 1)) + 1 + 1 = 2 * (r - d) by omega]
      simp
    rw [hfin, hpre]
    simp only [SignedCNF.TruthFrom, Holds, Bool.false_eq_true, ↓reduceIte]
    apply forall_congr'; intro b
    apply exists_congr; intro c
    rw [ih _ (by omega), ρOf_update]
    simp only [Fin.val_mk]
    rw [show 2 * (r - (d + 1)) + 1 + 1 = 2 * (r - d) by omega]

theorem ρOf_const {r : ℕ} : ρOf (fun _ : Fin r => (false, false)) = fun _ => false := by
  funext i; simp [ρOf]

/-- The translation preserves truth. -/
theorem translate_true (r : ℕ) (F : SignedCNF r) : F.True ↔ (translate r F).IsTrue := by
  have h := truth_iff r F r (fun _ => (false, false)) (le_refl r)
  simp only [Nat.sub_self, List.drop_zero, Nat.mul_zero, ρOf_const] at h
  exact h

end Complexity.QBF.Reduction
