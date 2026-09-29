/-
Milestone 2: TQBF is the winner-determination language of the formula game, hence in PSPACE.

`game` packages the moves of `Complexity.QBF.Game` with their programs into the generic
`Complexity.Games.Game` template. The main theorem `winning_iff_val` shows by induction on
the rank that, at any well-formed position, the player to move wins exactly when the value
of the residual formula is on their side; at the initial position this is truth of the
formula, so `game.language = TQBF`, and the template's membership theorem gives
`TQBF ∈ PSPACE`.
-/
import Complexity.QBF.GameCode
import Complexity.Games.Membership

namespace Complexity.QBF.TQBFGame

open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace
open Complexity.Games Complexity.QBF.Game Polynomial

/-! ### The game -/

noncomputable def game : Game where
  arity := C 2
  succ := succ
  start := start
  size := C 3 * X + C 4
  rank := rank
  length := C 8 * X + C 13
  succCode := GameCode.succCode
  startCode := GameCode.startCode
  succ_eval := GameCode.succCode_eval
  start_eval := GameCode.startCode_eval
  start_size := by
    intro w p h
    simpa using start_size w p h
  succ_size := by
    intro w p k q _ _ h
    simpa using succ_size w p k q h
  rank_lt := by
    intro w p k q _ _ h
    exact rank_lt w p k q h
  rank_le := by
    intro w p hp
    have h := rank_le w p
    simp only [Game.Bounded, eval_add, eval_mul, eval_C, eval_X] at hp ⊢
    omega

theorem game_arity (w : Word) : game.arity.eval w.length = 2 := by simp [game]

theorem game_move_iff (w p q : Word) : game.Move w p q ↔ ∃ κ, κ < 2 ∧ succ w p κ = some q := by
  simp only [Game.Move, game_arity]
  rfl

theorem bounded_mkPos (w : Word) (t s : Bool) (ρ : Word) (j : ℕ) (hk : ρ.length ≤ vars w)
    (hj : j < nodes w) : game.Bounded w (mkPos t s ρ j) := by
  have hn := vars_le w
  have hN := nodes_le w
  simp only [Game.Bounded, game, eval_add, eval_mul, eval_C, eval_X, mkPos_length]
  omega

theorem bounded_nil (w : Word) : game.Bounded w [] := by
  simp [Game.Bounded, game]

theorem not_winning_nil (w : Word) : ¬ game.Winning w [] := by
  rw [game.winning_iff (bounded_nil w)]
  rintro ⟨q, hm, _⟩
  obtain ⟨κ, _, h⟩ := (game_move_iff w [] q).mp hm
  simp [succ, succCore] at h

/-! ### Moves at well-formed positions -/

section moves
variable (w : Word) (t s : Bool) (ρ : Word) (j : ℕ)

theorem mkPos_length_ne (κ : ℕ) : ¬ ((mkPos t s ρ j).length = 0) := by
  rw [mkPos_length]; omega

theorem succ_assign (hk : ρ.length < vars w) (hj : j < nodes w) (ht : t = bit (body w) ρ.length) (κ : ℕ) :
    succ w (mkPos t s ρ j) κ = if κ < 2 then some (mkPos (!t) s (ρ ++ [decide (κ = 1)]) j) else none := by
  unfold succ succCore
  simp [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_mkPos, mkPos_length, hk, hj, ht,
    Nat.le_of_lt hk]

theorem succ_qpass (hk : ρ.length < vars w) (hj : j < nodes w) (ht : ¬ t = bit (body w) ρ.length) (κ : ℕ) :
    succ w (mkPos t s ρ j) κ = if κ = 0 then some (mkPos (!t) s ρ j) else none := by
  unfold succ succCore
  simp [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_mkPos, mkPos_length, hk, hj, ht,
    Nat.le_of_lt hk]

theorem succ_leaf (hk : ρ.length = vars w) (hj : j < nodes w)
    (hvar : isVar (records w) (width w) j = true) (κ : ℕ) :
    succ w (mkPos t s ρ j) κ =
      if κ = 0 ∧ ¬ (t = (bit ρ (field (records w) (width w) j) != s)) then some [] else none := by
  unfold succ succCore
  simp [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_mkPos, mkPos_length, hk, hj, hvar]

theorem succ_neg (hk : ρ.length = vars w) (hj : j < nodes w)
    (hvar : isVar (records w) (width w) j = false) (hnot : isNot (records w) (width w) j = true)
    (h1 : 1 ≤ j) (κ : ℕ) :
    succ w (mkPos t s ρ j) κ = if κ = 0 then some (mkPos (!t) (!s) ρ (j - 1)) else none := by
  unfold succ succCore
  simp [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_mkPos, mkPos_length, hk, hj, hvar, hnot, h1]

theorem succ_bin_owner (hk : ρ.length = vars w) (hj : j < nodes w)
    (hvar : isVar (records w) (width w) j = false) (hnot : isNot (records w) (width w) j = false)
    (h1 : 1 ≤ j) (hsz : sizeAt (records w) (width w) (j - 1) < j)
    (ht : t = (isAnd (records w) (width w) j != s)) (κ : ℕ) :
    succ w (mkPos t s ρ j) κ =
      if κ = 0 then some (mkPos (!t) s ρ (leftChild (records w) (width w) j))
      else if κ = 1 then some (mkPos (!t) s ρ (rightChild j)) else none := by
  unfold succ succCore
  simp [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_mkPos, mkPos_length, hk, hj, hvar, hnot,
    h1, hsz, ht]

theorem succ_bin_pass (hk : ρ.length = vars w) (hj : j < nodes w)
    (hvar : isVar (records w) (width w) j = false) (hnot : isNot (records w) (width w) j = false)
    (h1 : 1 ≤ j) (hsz : sizeAt (records w) (width w) (j - 1) < j)
    (ht : ¬ t = (isAnd (records w) (width w) j != s)) (κ : ℕ) :
    succ w (mkPos t s ρ j) κ = if κ = 0 then some (mkPos (!t) s ρ j) else none := by
  unfold succ succCore
  simp [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_mkPos, mkPos_length, hk, hj, hvar, hnot,
    h1, hsz, ht]

end moves

/-- Winning via a single forced move to `q`. -/
theorem winning_single (w p q : Word) (hp : game.Bounded w p)
    (h : ∀ κ, succ w p κ = if κ = 0 then some q else none) :
    game.Winning w p ↔ ¬ game.Winning w q := by
  rw [game.winning_iff hp]
  constructor
  · rintro ⟨q', hm, hq'⟩
    obtain ⟨κ, hκ, hs⟩ := (game_move_iff w p q').mp hm
    rw [h] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact hq'
    · exact absurd hs (by simp)
  · intro hq
    exact ⟨q, (game_move_iff w p q).mpr ⟨0, by omega, by rw [h]; simp⟩, hq⟩

/-- Winning via two moves to `q₀` and `q₁`. -/
theorem winning_pair (w p q₀ q₁ : Word) (hp : game.Bounded w p)
    (h : ∀ κ, succ w p κ = if κ = 0 then some q₀ else if κ = 1 then some q₁ else none) :
    game.Winning w p ↔ ¬ game.Winning w q₀ ∨ ¬ game.Winning w q₁ := by
  rw [game.winning_iff hp]
  constructor
  · rintro ⟨q', hm, hq'⟩
    obtain ⟨κ, hκ, hs⟩ := (game_move_iff w p q').mp hm
    rw [h] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact Or.inl hq'
    · split at hs
      · simp only [Option.some.injEq] at hs; subst hs; exact Or.inr hq'
      · exact absurd hs (by simp)
  · rintro (hq | hq)
    · exact ⟨q₀, (game_move_iff w p q₀).mpr ⟨0, by omega, by rw [h]; simp⟩, hq⟩
    · exact ⟨q₁, (game_move_iff w p q₁).mpr ⟨1, by omega, by rw [h]; simp⟩, hq⟩

/-- Winning via the two assignment moves. -/
theorem winning_assign (w p : Word) (f : Bool → Word) (hp : game.Bounded w p)
    (h : ∀ κ, succ w p κ = if κ < 2 then some (f (decide (κ = 1))) else none) :
    game.Winning w p ↔ ¬ game.Winning w (f false) ∨ ¬ game.Winning w (f true) := by
  apply winning_pair w p (f false) (f true) hp
  intro κ
  rw [h]
  by_cases h0 : κ = 0
  · subst h0; simp
  · by_cases h1 : κ = 1
    · subst h1; simp
    · simp [h0, h1]; omega

/-- Winning via a conditional move to the sink. -/
theorem winning_leaf (w p : Word) (P : Prop) [Decidable P] (hp : game.Bounded w p)
    (h : ∀ κ, succ w p κ = if κ = 0 ∧ P then some [] else none) :
    game.Winning w p ↔ P := by
  rw [game.winning_iff hp]
  constructor
  · rintro ⟨q', hm, _⟩
    obtain ⟨κ, hκ, hs⟩ := (game_move_iff w p q').mp hm
    rw [h] at hs
    split at hs
    · rename_i hc; exact hc.2
    · exact absurd hs (by simp)
  · intro hP
    exact ⟨[], (game_move_iff w p []).mpr ⟨0, by omega, by rw [h]; simp [hP]⟩, not_winning_nil w⟩

/-! ### Semantics of positions -/

/-- The assignment read off a word. -/
def asgn (ρ : Word) : ℕ → Bool := fun i => bit ρ i

theorem asgn_append (ρ : Word) (b : Bool) : asgn (ρ ++ [b]) = Function.update (asgn ρ) ρ.length b := by
  funext i
  unfold asgn bit
  by_cases hi : i = ρ.length
  · subst hi; simp
  · rw [Function.update_of_ne hi]
    rcases Nat.lt_or_gt_of_ne hi with h | h
    · rw [List.getElem?_append_left h]
    · have h1 : (ρ ++ [b])[i]? = none := List.getElem?_eq_none (by simp; omega)
      have h2 : ρ[i]? = none := List.getElem?_eq_none (by omega)
      rw [h1, h2]

/-- The matrix of the input. -/
def matrix (w : Word) : Expr := decodeNode (records w) (width w) (nodes w - 1)

/-- Truth of the residual quantified formula after assigning `ρ`. -/
def HoldsAt (w : Word) (ρ : Word) : Prop :=
  Holds (matrix w) ((prefixWord w).drop ρ.length) ρ.length (asgn ρ)

/-- The value of a position (from E's point of view). -/
def Val (w : Word) (s : Bool) (ρ : Word) (j : ℕ) : Prop :=
  if ρ.length < vars w then HoldsAt w ρ
  else ((decodeNode (records w) (width w) j).eval (asgn ρ) != s) = true

/-- Invariant of reachable positions. -/
def Inv (w : Word) (s : Bool) (ρ : Word) (j : ℕ) : Prop :=
  ρ.length ≤ vars w ∧ j < nodes w ∧ (ρ.length < vars w → s = false ∧ j = nodes w - 1)

/-- Facts extracted from validity. -/
theorem valid_facts (w : Word) (hw : valid w = true) :
    1 ≤ nodes w ∧ (prefixWord w).length = vars w ∧ vars w ≤ (body w).length ∧
    ∀ j, j < nodes w → nodeValid (records w) (vars w) (width w) j = true := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hw
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hlen⟩, hpos⟩, _⟩, hval⟩ := hw
  refine ⟨hpos, ?_, ?_, hval⟩
  · simp only [prefixWord, List.length_take]
    rw [hlen]
    exact Nat.min_eq_left (Nat.le_add_right _ _)
  · rw [hlen]; exact Nat.le_add_right _ _

theorem holdsAt_step (w : Word) (hw : valid w = true) (ρ : Word) (hk : ρ.length < vars w) :
    HoldsAt w ρ ↔ if bit (body w) ρ.length then ∀ b, HoldsAt w (ρ ++ [b]) else ∃ b, HoldsAt w (ρ ++ [b]) := by
  obtain ⟨_, hpl, hbl, _⟩ := valid_facts w hw
  have hkp : ρ.length < (prefixWord w).length := by omega
  have hget : (prefixWord w)[ρ.length] = bit (body w) ρ.length := by
    simp only [prefixWord, List.getElem_take, bit]
    rw [List.getElem?_eq_getElem (by omega)]
    rfl
  unfold HoldsAt
  rw [List.drop_eq_getElem_cons hkp, hget]
  simp only [Holds, List.length_append, List.length_singleton, asgn_append]

theorem val_root (w : Word) (hw : valid w = true) (ρ : Word) (hk : ρ.length ≤ vars w) :
    Val w false ρ (nodes w - 1) ↔ HoldsAt w ρ := by
  obtain ⟨_, hpl, _, _⟩ := valid_facts w hw
  unfold Val
  split
  · exact Iff.rfl
  · have he : ρ.length = vars w := by omega
    unfold HoldsAt
    rw [he, ← hpl, List.drop_length]
    simp [Holds, matrix]

/-! ### Boolean helpers -/

theorem not_iff_flip (t : Bool) (V : Prop) : ¬ ((!t) = false ↔ V) ↔ (t = false ↔ V) := by
  cases t <;> simp

theorem leaf_iff (t v : Bool) : ¬ (t = v) ↔ (t = false ↔ v = true) := by
  cases t <;> cases v <;> simp

theorem bin_val (a b s isAnd : Bool) :
    (((if isAnd then a && b else a || b) != s) = true) ↔
      (if (isAnd != s) = true then ((a != s) = true ∧ (b != s) = true)
        else ((a != s) = true ∨ (b != s) = true)) := by
  cases a <;> cases b <;> cases s <;> cases isAnd <;> simp

/-! ### The main invariant -/

theorem node_facts (w : Word) (hw : valid w = true) (j : ℕ) (hj : j < nodes w) :
    (isNot (records w) (width w) j = true → 1 ≤ j) ∧
    (isVar (records w) (width w) j = false → isNot (records w) (width w) j = false →
      1 ≤ j ∧ sizeAt (records w) (width w) (j - 1) < j) := by
  obtain ⟨_, _, _, hval⟩ := valid_facts w hw
  have hv := hval j hj
  simp only [nodeValid, Bool.and_eq_true] at hv
  constructor
  · intro hnot
    have hvar : isVar (records w) (width w) j = false := by
      simp only [isVar, isNot, Bool.and_eq_true, Bool.not_eq_true'] at hnot ⊢
      simp [hnot.1]
    simp only [hvar, hnot, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.2.1
  · intro hvar hnot
    simp only [hvar, hnot, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ⟨hv.2.1.1, hv.2.1.2⟩

theorem decode_leaf (rs : Word) (W j : ℕ) (h : isVar rs W j = true) :
    decodeNode rs W j = .var (field rs W j) := by
  rw [decodeNode_eq, if_pos h]

theorem decode_neg (rs : Word) (W j : ℕ) (hv : isVar rs W j = false) (h : isNot rs W j = true)
    (h1 : 1 ≤ j) : decodeNode rs W j = .not (decodeNode rs W (j - 1)) := by
  rw [decodeNode_eq, if_neg (by simp [hv]), if_pos h1, if_pos h]

theorem decode_bin (rs : Word) (W j : ℕ) (hv : isVar rs W j = false) (hn : isNot rs W j = false)
    (h1 : 1 ≤ j) (hsz : sizeAt rs W (j - 1) < j) :
    decodeNode rs W j = if isAnd rs W j then
      .and (decodeNode rs W (leftChild rs W j)) (decodeNode rs W (rightChild j))
      else .or (decodeNode rs W (leftChild rs W j)) (decodeNode rs W (rightChild j)) := by
  rw [decodeNode_eq, if_neg (by simp [hv]), if_pos h1, if_neg (by simp [hn]), if_pos hsz]
  rfl

theorem winning_iff_val (w : Word) (hw : valid w = true) :
    ∀ (r : ℕ) (t s : Bool) (ρ : Word) (j : ℕ), Inv w s ρ j → rank w (mkPos t s ρ j) = r →
      (game.Winning w (mkPos t s ρ j) ↔ (t = false ↔ Val w s ρ j)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro t s ρ j hinv hr
    obtain ⟨hk, hj, hq⟩ := hinv
    have hb := bounded_mkPos w t s ρ j hk hj
    -- the induction hypothesis, applied through a move
    have ih' : ∀ (κ : ℕ) (t' s' : Bool) (ρ' : Word) (j' : ℕ),
        succ w (mkPos t s ρ j) κ = some (mkPos t' s' ρ' j') → Inv w s' ρ' j' →
        (game.Winning w (mkPos t' s' ρ' j') ↔ (t' = false ↔ Val w s' ρ' j')) := by
      intro κ t' s' ρ' j' hs hinv'
      exact ih _ (hr ▸ rank_lt w _ κ _ hs) t' s' ρ' j' hinv' rfl
    by_cases hkn : ρ.length < vars w
    · -- quantifier phase
      obtain ⟨rfl, rfl⟩ := hq hkn
      rw [val_root w hw ρ hk, holdsAt_step w hw ρ hkn]
      have hinvb : ∀ b : Bool, Inv w false (ρ ++ [b]) (nodes w - 1) :=
        fun b => ⟨by simp; omega, hj, fun _ => ⟨rfl, rfl⟩⟩
      by_cases ht : t = bit (body w) ρ.length
      · rw [winning_assign w _ (fun b => mkPos (!t) false (ρ ++ [b]) (nodes w - 1)) hb
          (succ_assign w t false ρ _ hkn hj ht)]
        have hc : ∀ b : Bool, game.Winning w (mkPos (!t) false (ρ ++ [b]) (nodes w - 1)) ↔
            ((!t) = false ↔ HoldsAt w (ρ ++ [b])) := by
          intro b
          rw [← val_root w hw (ρ ++ [b]) (by simp; omega)]
          exact ih' (if b then 1 else 0) (!t) false (ρ ++ [b]) (nodes w - 1)
            (by rw [succ_assign w t false ρ _ hkn hj ht]; cases b <;> simp) (hinvb b)
        rw [hc false, hc true, ← ht]
        cases t <;> simp [Bool.forall_bool, Bool.exists_bool] <;> tauto
      · rw [winning_single w _ (mkPos (!t) false ρ (nodes w - 1)) hb (succ_qpass w t false ρ _ hkn hj ht)]
        rw [ih' 0 (!t) false ρ (nodes w - 1) (by rw [succ_qpass w t false ρ _ hkn hj ht]; simp)
          ⟨hk, hj, fun _ => ⟨rfl, rfl⟩⟩, val_root w hw ρ hk, holdsAt_step w hw ρ hkn]
        exact not_iff_flip t _
    · -- matrix phase
      have hkn' : ρ.length = vars w := by omega
      have hV : Val w s ρ j = (((decodeNode (records w) (width w) j).eval (asgn ρ) != s) = true) := by
        simp [Val, hkn]
      rw [hV]
      obtain ⟨hnot1, hbin⟩ := node_facts w hw j hj
      by_cases hvar : isVar (records w) (width w) j = true
      · rw [winning_leaf w _ _ hb (succ_leaf w t s ρ j hkn' hj hvar), decode_leaf _ _ _ hvar]
        simp only [Expr.eval, asgn]
        exact leaf_iff t _
      · have hvar' : isVar (records w) (width w) j = false := by simpa using hvar
        by_cases hnot : isNot (records w) (width w) j = true
        · have h1 := hnot1 hnot
          rw [winning_single w _ (mkPos (!t) (!s) ρ (j - 1)) hb (succ_neg w t s ρ j hkn' hj hvar' hnot h1)]
          have hinv1 : Inv w (!s) ρ (j - 1) := ⟨hk, by omega, fun h => absurd h hkn⟩
          rw [ih' 0 (!t) (!s) ρ (j - 1) (by rw [succ_neg w t s ρ j hkn' hj hvar' hnot h1]; simp) hinv1]
          have hVc : Val w (!s) ρ (j - 1) =
              (((decodeNode (records w) (width w) (j - 1)).eval (asgn ρ) != !s) = true) := by
            simp [Val, hkn]
          rw [hVc, decode_neg _ _ _ hvar' hnot h1]
          simp only [Expr.eval]
          have hbool : ∀ a : Bool, ((!a) != s) = (a != !s) := by intro a; cases a <;> cases s <;> rfl
          rw [hbool]
          exact not_iff_flip t _
        · have hnot' : isNot (records w) (width w) j = false := by simpa using hnot
          obtain ⟨h1, hsz⟩ := hbin hvar' hnot'
          have hl : leftChild (records w) (width w) j < nodes w := by unfold leftChild; omega
          have hr' : rightChild j < nodes w := by unfold rightChild; omega
          have hVl : Val w s ρ (leftChild (records w) (width w) j) =
              (((decodeNode (records w) (width w) (leftChild (records w) (width w) j)).eval (asgn ρ) != s) = true) := by
            simp [Val, hkn]
          have hVr : Val w s ρ (rightChild j) =
              (((decodeNode (records w) (width w) (rightChild j)).eval (asgn ρ) != s) = true) := by
            simp [Val, hkn]
          rw [decode_bin _ _ _ hvar' hnot' h1 hsz]
          have heval : (if isAnd (records w) (width w) j then
              Expr.and (decodeNode (records w) (width w) (leftChild (records w) (width w) j))
                (decodeNode (records w) (width w) (rightChild j))
              else Expr.or (decodeNode (records w) (width w) (leftChild (records w) (width w) j))
                (decodeNode (records w) (width w) (rightChild j))).eval (asgn ρ) =
              if isAnd (records w) (width w) j then
                ((decodeNode (records w) (width w) (leftChild (records w) (width w) j)).eval (asgn ρ) &&
                  (decodeNode (records w) (width w) (rightChild j)).eval (asgn ρ))
              else ((decodeNode (records w) (width w) (leftChild (records w) (width w) j)).eval (asgn ρ) ||
                  (decodeNode (records w) (width w) (rightChild j)).eval (asgn ρ)) := by
            split <;> simp only [Expr.eval]
          rw [heval, bin_val]
          by_cases ht : t = (isAnd (records w) (width w) j != s)
          · rw [winning_pair w _ _ _ hb (succ_bin_owner w t s ρ j hkn' hj hvar' hnot' h1 hsz ht)]
            rw [ih' 0 (!t) s ρ _ (by rw [succ_bin_owner w t s ρ j hkn' hj hvar' hnot' h1 hsz ht]; simp)
              ⟨hk, hl, fun h => absurd h hkn⟩,
              ih' 1 (!t) s ρ _ (by rw [succ_bin_owner w t s ρ j hkn' hj hvar' hnot' h1 hsz ht]; simp)
              ⟨hk, hr', fun h => absurd h hkn⟩, hVl, hVr, ← ht]
            generalize Expr.eval (asgn ρ) (decodeNode (records w) (width w) (leftChild (records w) (width w) j)) = bl
            generalize Expr.eval (asgn ρ) (decodeNode (records w) (width w) (rightChild j)) = br
            cases t <;> cases bl <;> cases br <;> cases s <;> simp
          · rw [winning_single w _ (mkPos (!t) s ρ j) hb (succ_bin_pass w t s ρ j hkn' hj hvar' hnot' h1 hsz ht)]
            rw [ih' 0 (!t) s ρ j (by rw [succ_bin_pass w t s ρ j hkn' hj hvar' hnot' h1 hsz ht]; simp)
              ⟨hk, hj, fun h => absurd h hkn⟩, hV, decode_bin _ _ _ hvar' hnot' h1 hsz, heval, bin_val]
            exact not_iff_flip t _

/-! ### TQBF is the language of the game -/

theorem asgn_nil : asgn [] = fun _ => false := by
  funext i; simp [asgn, bit]

theorem language_eq : game.language = TQBF := by
  ext w
  rw [Game.mem_language_iff, mem_TQBF_iff]
  by_cases hw : valid w = true
  · obtain ⟨hN, hpl, _, _⟩ := valid_facts w hw
    have hstart : game.start w = some (mkPos false false [] (nodes w - 1)) := by
      show start w = _
      simp [start, hw]
    have hinv : Inv w false [] (nodes w - 1) := ⟨by simp, by omega, fun _ => ⟨rfl, rfl⟩⟩
    have hwin := winning_iff_val w hw _ false false [] (nodes w - 1) hinv rfl
    rw [val_root w hw [] (by simp)] at hwin
    simp only [hstart, Option.some.injEq, exists_eq_left', hwin, true_iff]
    have hdec : decode w = some ⟨prefixWord w, matrix w⟩ := by simp [decode, hw, matrix]
    simp only [hdec, Option.some.injEq, exists_eq_left', Formula.IsTrue, HoldsAt, List.length_nil,
      List.drop_zero, asgn_nil]
  · have hstart : game.start w = none := by
      show start w = _
      simp [start, hw]
    have hdec : decode w = none := by simp [decode, hw]
    simp [hstart, hdec]

/-- **TQBF ∈ PSPACE**, as an instance of the game template. -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := by
  rw [← language_eq]
  exact game.language_mem_PSPACE

end Complexity.QBF.TQBFGame
