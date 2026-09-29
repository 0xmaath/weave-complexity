/-
Milestone 2: TQBF as a normal-play game (Sipser's formula game, §8.3).

A position is a word `t s 1^k 0 ρ 1^j 0`: `t` says whose turn it is (`false` = the
existential player E, `true` = the universal player A), `s` is the negation parity of the
current matrix node, `ρ` is the assignment of the first `k` variables, and `j` is the current
matrix node. While `k < n` the owner of quantifier `k` (E for `∃`, A for `∀`) picks the value
of `x_k`; when it is not the owner's turn the only move is a pass. Once all variables are
assigned the players walk down the matrix: A chooses a conjunct, E a disjunct (with the roles
swapped under an odd number of negations), a negation node flips the parity, and at a leaf
the player who is right about the literal moves to the empty sink position, which has no
moves. Alternation is strict, so the player who cannot move loses; `Winning` of this game is
truth of the formula (proved in `Complexity.QBF.TQBFGame`).

`succ` and `start` are written in the exact shape of the `Code` programs of
`Complexity.QBF.GameCode`; positions of malformed instances or malformed positions have no
moves, which is what makes the template's universal laws hold.
-/
import Complexity.QBF.Encoding
import Complexity.Games.Alternating

namespace Complexity.QBF.Game

open Complexity.Classes.PolynomialTime

/-! ### Positions -/

def posT (p : Word) : Bool := bit p 0
def posS (p : Word) : Bool := bit p 1
def posK (p : Word) : ℕ := readUnary (p.drop 2)
def posRest (p : Word) : Word := p.drop (posK p + 3)
def posRho (p : Word) : Word := (List.range (posK p)).map fun i => ((posRest p)[i]?).getD false
def posJ (p : Word) : ℕ := readUnary ((posRest p).drop (posK p))

def mkPos (t s : Bool) (ρ : Word) (j : ℕ) : Word :=
  t :: s :: (List.replicate ρ.length true ++ false :: (ρ ++ (List.replicate j true ++ [false])))

theorem range_map_prefix (pos rest : Word) :
    ((List.range pos.length).map fun i => ((pos ++ rest)[i]?).getD false) = pos := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at hi ⊢
    rw [List.getElem?_append_left hi]
    simp [List.getElem?_eq_getElem hi]

@[simp] theorem posT_mkPos (t s : Bool) (ρ : Word) (j : ℕ) : posT (mkPos t s ρ j) = t := rfl
@[simp] theorem posS_mkPos (t s : Bool) (ρ : Word) (j : ℕ) : posS (mkPos t s ρ j) = s := rfl
@[simp] theorem posK_mkPos (t s : Bool) (ρ : Word) (j : ℕ) : posK (mkPos t s ρ j) = ρ.length := by
  simp [posK, mkPos, readUnary_replicate]
@[simp] theorem posRest_mkPos (t s : Bool) (ρ : Word) (j : ℕ) :
    posRest (mkPos t s ρ j) = ρ ++ (List.replicate j true ++ [false]) := by
  unfold posRest
  rw [posK_mkPos]
  simp only [mkPos]
  rw [show ρ.length + 3 = (ρ.length + 1) + 1 + 1 by omega, List.drop_succ_cons, List.drop_succ_cons,
    drop_replicate]
@[simp] theorem posRho_mkPos (t s : Bool) (ρ : Word) (j : ℕ) : posRho (mkPos t s ρ j) = ρ := by
  simp only [posRho, posK_mkPos, posRest_mkPos]
  exact range_map_prefix ρ _
@[simp] theorem posJ_mkPos (t s : Bool) (ρ : Word) (j : ℕ) : posJ (mkPos t s ρ j) = j := by
  simp only [posJ, posRest_mkPos, posK_mkPos, List.drop_left]
  exact readUnary_replicate j []
theorem mkPos_length (t s : Bool) (ρ : Word) (j : ℕ) :
    (mkPos t s ρ j).length = 2 * ρ.length + j + 4 := by
  simp [mkPos]; omega
theorem mkPos_ne_nil (t s : Bool) (ρ : Word) (j : ℕ) : mkPos t s ρ j ≠ [] := by simp [mkPos]

theorem posRho_length (p : Word) : (posRho p).length = posK p := by simp [posRho]

theorem readUnary_le (w : Word) : readUnary w ≤ w.length := (List.takeWhile_prefix _).length_le

theorem length_drop_le (l : Word) (n : ℕ) : (l.drop n).length ≤ l.length := by
  rw [List.length_drop]; omega

theorem posJ_le (p : Word) : posJ p ≤ p.length := by
  unfold posJ posRest
  exact (readUnary_le _).trans ((length_drop_le _ _).trans (length_drop_le _ _))

theorem posK_le (p : Word) : posK p ≤ p.length := by
  unfold posK
  exact (readUnary_le _).trans (length_drop_le _ _)

theorem vars_le (w : Word) : vars w ≤ w.length := readUnary_le w
theorem nodes_le (w : Word) : nodes w ≤ w.length :=
  (readUnary_le _).trans (length_drop_le _ _)

/-! ### Moves -/

/-- The successor function on parsed positions: `n N W` are the header numbers, `bodyw` and
`rs` the prefix-and-records block and the record table, `plen` the length of the position
word, `t s k ρ j` its components, and `κ` the candidate move index. -/
def succCore (n N W : ℕ) (bodyw rs : Word) (plen : ℕ) (t s : Bool) (k : ℕ) (ρ : Word) (j κ : ℕ) :
    Option Word :=
  if decide (plen = 0) then none
  else if !(decide (k ≤ n) && decide (j < N)) then none
  else if decide (k < n) then
    if decide (t = bit bodyw k) then
      if decide (κ < 2) then some (mkPos (!t) s (ρ ++ [decide (κ = 1)]) j) else none
    else if decide (κ = 0) then some (mkPos (!t) s ρ j) else none
  else if isVar rs W j then
    if decide (κ = 0) && !decide (t = (bit ρ (field rs W j) != s)) then some [] else none
  else if !decide (1 ≤ j) then none
  else if isNot rs W j then
    if decide (κ = 0) then some (mkPos (!t) (!s) ρ (j - 1)) else none
  else if !decide (sizeAt rs W (j - 1) < j) then none
  else if decide (t = (isAnd rs W j != s)) then
    if decide (κ = 0) then some (mkPos (!t) s ρ (leftChild rs W j))
    else if decide (κ = 1) then some (mkPos (!t) s ρ (rightChild j)) else none
  else if decide (κ = 0) then some (mkPos (!t) s ρ j) else none

/-- The successor function; `κ` is the candidate move index. -/
def succ (w p : Word) (κ : ℕ) : Option Word :=
  succCore (vars w) (nodes w) (width w) (body w) (records w) p.length (posT p) (posS p) (posK p)
    (posRho p) (posJ p) κ

/-- The initial position: E to move, no negation, nothing assigned, at the root. -/
def start (w : Word) : Option Word :=
  if valid w then some (mkPos false false [] (nodes w - 1)) else none

/-- A rank decreasing along every move. -/
def rank (w p : Word) : ℕ :=
  let n := vars w
  let W := width w
  let rs := records w
  let t := posT p
  let s := posS p
  let k := posK p
  let j := posJ p
  if p.length = 0 then 0
  else if k < n then 2 * (n - k) + (if t = bit (body w) k then 0 else 1) + 2 * j + 4
  else 2 * j + 2 + (if isVar rs W j || isNot rs W j then 0
    else if t = (isAnd rs W j != s) then 0 else 1)

/-! ### Bounds -/

theorem start_size (w p : Word) (h : start w = some p) : p.length ≤ 3 * w.length + 4 := by
  unfold start at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [mkPos_length]
    have := nodes_le w
    simp; omega
  · exact absurd h (by simp)

theorem succ_size (w p : Word) (κ : ℕ) (q : Word) (h : succ w p κ = some q) :
    q.length ≤ 3 * w.length + 4 := by
  have hn := vars_le w
  have hN := nodes_le w
  unfold succ succCore at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i hwf
  have hwf' : posK p ≤ vars w ∧ posJ p < nodes w := by simpa using hwf
  split at h
  · rename_i hk0
    have hk : posK p < vars w := by simpa using hk0
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        rw [mkPos_length, List.length_append, posRho_length]; simp; omega
      · exact absurd h (by simp)
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        rw [mkPos_length, posRho_length]; omega
      · exact absurd h (by simp)
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; simp
    · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      rw [mkPos_length, posRho_length]; omega
    · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      rw [mkPos_length, posRho_length]
      unfold leftChild; omega
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        rw [mkPos_length, posRho_length]
        unfold rightChild; omega
      · exact absurd h (by simp)
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      rw [mkPos_length, posRho_length]; omega
    · exact absurd h (by simp)

theorem rank_le (w p : Word) : rank w p ≤ 2 * w.length + 2 * p.length + 5 := by
  have hn := vars_le w
  have hj := posJ_le p
  unfold rank
  simp only
  split
  · omega
  split
  · split <;> omega
  · split
    · omega
    · split <;> omega

theorem rank_lt (w p : Word) (κ : ℕ) (q : Word) (h : succ w p κ = some q) :
    rank w q < rank w p := by
  unfold succ succCore at h
  split at h
  · exact absurd h (by simp)
  rename_i hne0
  have hne : ¬ p.length = 0 := by simpa using hne0
  split at h
  · exact absurd h (by simp)
  rename_i hwf0
  have hwf' : posK p ≤ vars w ∧ posJ p < nodes w := by simpa using hwf0
  split at h
  · -- quantifier phase
    rename_i hk0
    have hk : posK p < vars w := by simpa using hk0
    split at h
    · rename_i howner0
      have howner : posT p = bit (body w) (posK p) := by simpa using howner0
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold rank
        simp only [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, List.length_append,
          posRho_length, List.length_singleton, mkPos_length]
        rw [if_neg (by omega), if_neg hne, if_pos hk, if_pos howner]
        split_ifs <;> omega
      · exact absurd h (by simp)
    · rename_i howner0
      have howner : ¬ posT p = bit (body w) (posK p) := by simpa using howner0
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold rank
        simp only [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_length, mkPos_length]
        rw [if_neg (by omega), if_neg hne, if_pos hk, if_pos hk, if_neg howner]
        have this : (!posT p) = bit (body w) (posK p) := by
          cases hb : posT p <;> cases hb' : bit (body w) (posK p) <;> simp_all
        rw [if_pos this]
        omega
      · exact absurd h (by simp)
  rename_i hk0
  have hk : ¬ posK p < vars w := by simpa using hk0
  split at h
  · -- leaf
    rename_i hvar
    split at h
    · simp only [Option.some.injEq] at h; subst h
      unfold rank
      simp only [List.length_nil, ↓reduceIte]
      rw [if_neg hne]
      split_ifs <;> omega
    · exact absurd h (by simp)
  rename_i hvar
  split at h
  · exact absurd h (by simp)
  rename_i hj10
  have hj1' : 1 ≤ posJ p := by
    have h' : ¬ posJ p = 0 := by simpa using hj10
    omega
  split at h
  · -- negation
    rename_i hnot
    split at h
    · simp only [Option.some.injEq] at h; subst h
      unfold rank
      simp only [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_length, mkPos_length]
      rw [if_neg (by omega), if_neg hne, if_neg hk, if_neg hk]
      split_ifs <;> omega
    · exact absurd h (by simp)
  rename_i hnot
  split at h
  · exact absurd h (by simp)
  rename_i hsz0
  have hsz' : sizeAt (records w) (width w) (posJ p - 1) < posJ p := by simpa using hsz0
  have hvar' : isVar (records w) (width w) (posJ p) = false := by simpa using hvar
  have hnot' : isNot (records w) (width w) (posJ p) = false := by simpa using hnot
  split at h
  · rename_i howner0
    have howner : posT p = (isAnd (records w) (width w) (posJ p) != posS p) := by simpa using howner0
    split at h
    · simp only [Option.some.injEq] at h; subst h
      unfold rank
      simp only [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_length, mkPos_length]
      rw [if_neg (by omega), if_neg hne, if_neg hk, if_neg hk, hvar', hnot']
      simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, if_pos howner]
      unfold leftChild
      split_ifs <;> omega
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold rank
        simp only [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_length, mkPos_length]
        rw [if_neg (by omega), if_neg hne, if_neg hk, if_neg hk, hvar', hnot']
        simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, if_pos howner]
        unfold rightChild
        split_ifs <;> omega
      · exact absurd h (by simp)
  · rename_i howner0
    have howner : ¬ posT p = (isAnd (records w) (width w) (posJ p) != posS p) := by simpa using howner0
    split at h
    · simp only [Option.some.injEq] at h; subst h
      unfold rank
      simp only [posT_mkPos, posS_mkPos, posK_mkPos, posJ_mkPos, posRho_length, mkPos_length]
      rw [if_neg (by omega), if_neg hne, if_neg hk, if_neg hk, hvar', hnot']
      simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, if_neg howner]
      have this : (!posT p) = (isAnd (records w) (width w) (posJ p) != posS p) := by
        cases hb : posT p <;> cases hb' : (isAnd (records w) (width w) (posJ p) != posS p) <;> simp_all
      rw [if_pos this]
      omega
    · exact absurd h (by simp)

end Complexity.QBF.Game
