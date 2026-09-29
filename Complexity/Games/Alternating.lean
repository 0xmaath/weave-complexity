/-
Milestone 2: an abstract two-player game template.

A `Game` is a normal-play game on binary words: an instance word `w` determines an initial
position (or no position at all, when `w` is not a valid instance), and every position `p`
has a finite list of candidate moves indexed by `k < arity(|w|)`, each either absent
(`none`) or leading to a successor position. The player who cannot move loses, and the two
players alternate: after any move it is the other player's turn. Games in which the same
player moves twice are modelled with explicit pass moves in `succ`.

The template carries the data needed to decide the winner in polynomial space:
positions of size at most `size(|w|)`, a rank that decreases along every move and is at
most `length(|w|)` (so every play has polynomial length), and `Code` programs (the tree's
word-program language, every program of which runs in polynomial time and space) computing
the initial position and the successor function. `Complexity.Games.Membership` proves that
the winner-determination language of every such game is in PSPACE.
-/
import Complexity.ClassesProofs.InclusionAux.TimeHelpers.OutputPolynomials
import Complexity.ArcKaylesProofs.CodeComputer

namespace Complexity.Games

open Complexity.Classes.PolynomialTime
open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming

/-- The inputs of a successor program: the instance, the current position, the move index
(in unary). -/
inductive MoveInput
  | instance
  | position
  | index
  deriving DecidableEq

/-- The environment read by a successor program: instance, position, and the move index
(as a word; the game's law only constrains unary index words). -/
def moveEnv (w p idx : Word) : MoveInput → Word
  | .instance => w
  | .position => p
  | .index => idx

/-- Words encoding an optional position: the empty word for `none`, else a leading `true`. -/
def optionWord : Option Word → Word
  | none => []
  | some q => true :: q

theorem optionWord_injective : Function.Injective optionWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [optionWord]

/-- A polynomially bounded normal-play game with computable moves. -/
structure Game where
  /-- Candidate move indices at any position are `k < arity.eval |w|`. -/
  arity : Polynomial ℕ
  /-- `succ w p k` is the position reached by candidate move `k` from `p`, if legal. -/
  succ : Word → Word → ℕ → Option Word
  /-- The initial position of instance `w`, or `none` when `w` is not an instance. -/
  start : Word → Option Word
  /-- Every reachable position has length at most `size.eval |w|`. -/
  size : Polynomial ℕ
  /-- A rank that strictly decreases along every move. -/
  rank : Word → Word → ℕ
  /-- Ranks of bounded positions are at most `length.eval |w|`. -/
  length : Polynomial ℕ
  /-- The word program computing `succ`. -/
  succCode : Code MoveInput
  /-- The word program computing `start`. -/
  startCode : Code Unit
  succ_eval : ∀ w p k, succCode.eval (moveEnv w p (List.replicate k true)) = optionWord (succ w p k)
  start_eval : ∀ w, startCode.eval (fun _ => w) = optionWord (start w)
  start_size : ∀ w p, start w = some p → p.length ≤ size.eval w.length
  succ_size : ∀ w p k q, p.length ≤ size.eval w.length → k < arity.eval w.length →
    succ w p k = some q → q.length ≤ size.eval w.length
  rank_lt : ∀ w p k q, p.length ≤ size.eval w.length → k < arity.eval w.length →
    succ w p k = some q → rank w q < rank w p
  rank_le : ∀ w p, p.length ≤ size.eval w.length → rank w p ≤ length.eval w.length

namespace Game

variable (G : Game)

/-- Renaming the successor program into any context evaluates it on the renamed environment. -/
theorem succCode_rename_eval {J : Type} (f : MoveInput → J) (a : J → Word) :
    (G.succCode.rename f).eval a =
      G.succCode.eval (moveEnv (a (f .instance)) (a (f .position)) (a (f .index))) := by
  rw [Code.eval_rename]
  congr 1
  funext i
  cases i <;> rfl

theorem startCode_rename_eval {J : Type} (f : Unit → J) (a : J → Word) :
    (G.startCode.rename f).eval a = optionWord (G.start (a (f ()))) := by
  rw [Code.eval_rename]
  have h : a ∘ f = fun _ => a (f ()) := by funext u; cases u; rfl
  rw [h]
  exact G.start_eval _

/-- A legal move from `p` to `q` on instance `w`. -/
def Move (w p q : Word) : Prop := ∃ k, k < G.arity.eval w.length ∧ G.succ w p k = some q

/-- Bounded positions. -/
def Bounded (w p : Word) : Prop := p.length ≤ G.size.eval w.length

/-- Normal-play evaluation with a fuel bound on the number of moves. -/
def winEval (w : Word) : ℕ → Word → Bool
  | 0, _ => false
  | fuel + 1, p => (List.range (G.arity.eval w.length)).any fun k =>
      (G.succ w p k).elim false fun q => !winEval w fuel q

theorem winEval_succ_iff (w p : Word) (fuel : ℕ) :
    G.winEval w (fuel + 1) p = true ↔ ∃ q, G.Move w p q ∧ G.winEval w fuel q = false := by
  simp only [winEval, List.any_eq_true, List.mem_range, Move]
  constructor
  · rintro ⟨k, hk, hq⟩
    cases hs : G.succ w p k with
    | none => rw [hs] at hq; simp [Option.elim] at hq
    | some q =>
      rw [hs] at hq
      exact ⟨q, ⟨k, hk, hs⟩, by simpa [Option.elim] using hq⟩
  · rintro ⟨q, ⟨k, hk, hs⟩, hq⟩
    exact ⟨k, hk, by simp [hs, hq, Option.elim]⟩

theorem move_bounded {w p q : Word} (hp : G.Bounded w p) (h : G.Move w p q) : G.Bounded w q := by
  obtain ⟨k, hk, hs⟩ := h
  exact G.succ_size w p k q hp hk hs

theorem move_rank {w p q : Word} (hp : G.Bounded w p) (h : G.Move w p q) :
    G.rank w q < G.rank w p := by
  obtain ⟨k, hk, hs⟩ := h
  exact G.rank_lt w p k q hp hk hs

/-- Beyond the rank, the fuel bound does not matter. -/
theorem winEval_stable (w : Word) : ∀ (r : ℕ) (p : Word), G.Bounded w p → G.rank w p = r →
    ∀ f g, r < f → r < g → G.winEval w f p = G.winEval w g p := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro p hp hr f g hf hg
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f ≠ 0)
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
    apply Bool.eq_iff_iff.mpr
    rw [winEval_succ_iff, winEval_succ_iff]
    apply exists_congr
    intro q
    apply and_congr_right
    intro hm
    have hq := G.move_bounded hp hm
    have hlt := G.move_rank hp hm
    rw [ih (G.rank w q) (by omega) q hq rfl f g (by omega) (by omega)]

/-- The winning positions: the player to move can force a win. -/
def Winning (w p : Word) : Prop := G.winEval w (G.length.eval w.length + 1) p = true

/-- The normal-play recursion, for bounded positions. -/
theorem winning_iff {w p : Word} (hp : G.Bounded w p) :
    G.Winning w p ↔ ∃ q, G.Move w p q ∧ ¬ G.Winning w q := by
  unfold Winning
  rw [winEval_succ_iff]
  apply exists_congr
  intro q
  apply and_congr_right
  intro hm
  have hq := G.move_bounded hp hm
  have hr := G.rank_le w p hp
  have hlt := G.move_rank hp hm
  rw [Bool.not_eq_true, G.winEval_stable w _ q hq rfl (G.length.eval w.length)
    (G.length.eval w.length + 1) (by omega) (by omega)]

/-- The winner-determination language: instances whose initial position is winning. -/
def language : Language := {w | ∃ p, G.start w = some p ∧ G.Winning w p}

theorem mem_language_iff (w : Word) :
    w ∈ G.language ↔ ∃ p, G.start w = some p ∧ G.Winning w p := Iff.rfl

end Game

end Complexity.Games
