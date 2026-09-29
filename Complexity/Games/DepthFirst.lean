/-
Milestone 2: a generic depth-first evaluation of the game tree of a `Game`.

This is the game-independent version of the depth-first search used for Arc Kayles
(`Complexity.ArcKaylesProofs.DepthFirst`). A stack of frames records, for each position on
the current path, how many candidate moves remain to be tried and how much fuel is left.
`evaluate_frame` shows that the search from a frame ends by returning the frame's value,
along a trace whose stack depth stays bounded by the fuel.
-/
import Complexity.Games.Alternating

namespace Complexity.Games.DepthFirst

open Complexity.Classes.PolynomialTime

/-- A search frame: a position, the number of candidate moves still to try (the next one
has index `arity - count`), and the remaining fuel. -/
structure Frame where
  pos : Word
  count : ℕ
  fuel : ℕ

inductive State
  | search (frames : List Frame)
  | returning (result : Bool) (frames : List Frame)

def State.frames : State → List Frame
  | .search fs => fs
  | .returning _ fs => fs

def State.depth (s : State) : ℕ := s.frames.length

variable (G : Game) (w : Word)

/-- The value of the remaining candidates `arity - count, …, arity - 1` at fuel `fuel`. -/
def winFrom (fuel : ℕ) (p : Word) (count : ℕ) : Bool :=
  (List.range count).any fun i =>
    (G.succ w p (G.arity.eval w.length - (i + 1))).elim false fun q => !G.winEval w fuel q

def frameValue (f : Frame) : Bool :=
  match f.fuel with
  | 0 => false
  | fuel + 1 => winFrom G w fuel f.pos f.count

theorem winFrom_zero (fuel : ℕ) (p : Word) : winFrom G w fuel p 0 = false := by
  simp [winFrom]

theorem winFrom_succ (fuel : ℕ) (p : Word) (count : ℕ) :
    winFrom G w fuel p (count + 1) =
      (((G.succ w p (G.arity.eval w.length - (count + 1))).elim false fun q =>
        !G.winEval w fuel q) || winFrom G w fuel p count) := by
  unfold winFrom
  rw [List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_comm]

theorem winEval_eq_winFrom (fuel : ℕ) (p : Word) :
    G.winEval w (fuel + 1) p = winFrom G w fuel p (G.arity.eval w.length) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Game.winEval, winFrom, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, hq⟩
    refine ⟨G.arity.eval w.length - (k + 1), by omega, ?_⟩
    have he : G.arity.eval w.length - (G.arity.eval w.length - (k + 1) + 1) = k := by omega
    rwa [he]
  · rintro ⟨i, hi, hq⟩
    exact ⟨_, by omega, hq⟩

inductive Step : State → State → Prop
  | zero (p count rest) : Step (.search (⟨p, count, 0⟩ :: rest)) (.returning false rest)
  | exhausted (p fuel rest) : Step (.search (⟨p, 0, fuel + 1⟩ :: rest)) (.returning false rest)
  | skip (p count fuel rest) (h : G.succ w p (G.arity.eval w.length - (count + 1)) = none) :
      Step (.search (⟨p, count + 1, fuel + 1⟩ :: rest)) (.search (⟨p, count, fuel + 1⟩ :: rest))
  | descend (p count fuel rest q) (h : G.succ w p (G.arity.eval w.length - (count + 1)) = some q) :
      Step (.search (⟨p, count + 1, fuel + 1⟩ :: rest))
        (.search (⟨q, G.arity.eval w.length, fuel⟩ :: ⟨p, count, fuel + 1⟩ :: rest))
  | childWins (parent rest) : Step (.returning true (parent :: rest)) (.search (parent :: rest))
  | childLoses (parent rest) : Step (.returning false (parent :: rest)) (.returning true rest)

def BoundedStep (bound : ℕ) (s t : State) : Prop :=
  Step G w s t ∧ s.depth ≤ bound ∧ t.depth ≤ bound

abbrev Trace (bound : ℕ) := Relation.ReflTransGen (BoundedStep G w bound)

theorem one_step {b : ℕ} {s t : State} (h : Step G w s t) (hs : s.depth ≤ b) (ht : t.depth ≤ b) :
    Trace G w b s t :=
  Relation.ReflTransGen.single ⟨h, hs, ht⟩

theorem evaluate_frame (fuel : ℕ) (p : Word) (count : ℕ) (rest : List Frame) :
    Trace G w (rest.length + fuel + 1) (.search (⟨p, count, fuel⟩ :: rest))
      (.returning (frameValue G w ⟨p, count, fuel⟩) rest) := by
  induction fuel generalizing p count rest with
  | zero =>
    exact one_step G w (Step.zero p count rest) (by simp [State.depth, State.frames])
      (by simp [State.depth, State.frames])
  | succ fuel ih =>
    induction count with
    | zero =>
      have h : Trace G w (rest.length + (fuel + 1) + 1) (.search (⟨p, 0, fuel + 1⟩ :: rest))
          (.returning false rest) :=
        one_step G w (Step.exhausted p fuel rest)
          (by simp [State.depth, State.frames] <;> omega) (by simp [State.depth, State.frames] <;> omega)
      have hv : frameValue G w ⟨p, 0, fuel + 1⟩ = false := by
        change winFrom G w fuel p 0 = false
        exact winFrom_zero G w fuel p
      rw [hv]
      exact h
    | succ count ihc =>
      cases hs : G.succ w p (G.arity.eval w.length - (count + 1)) with
      | none =>
        have hfirst : Trace G w (rest.length + (fuel + 1) + 1)
            (.search (⟨p, count + 1, fuel + 1⟩ :: rest)) (.search (⟨p, count, fuel + 1⟩ :: rest)) :=
          one_step G w (Step.skip p count fuel rest hs)
            (by simp [State.depth, State.frames] <;> omega) (by simp [State.depth, State.frames] <;> omega)
        have hv : frameValue G w ⟨p, count + 1, fuel + 1⟩ = frameValue G w ⟨p, count, fuel + 1⟩ := by
          change winFrom G w fuel p (count + 1) = winFrom G w fuel p count
          rw [winFrom_succ, hs]
          rfl
        rw [hv]
        exact hfirst.trans ihc
      | some q =>
        have hfirst : Trace G w (rest.length + (fuel + 1) + 1)
            (.search (⟨p, count + 1, fuel + 1⟩ :: rest))
            (.search (⟨q, G.arity.eval w.length, fuel⟩ :: ⟨p, count, fuel + 1⟩ :: rest)) :=
          one_step G w (Step.descend p count fuel rest q hs)
            (by simp [State.depth, State.frames] <;> omega) (by simp [State.depth, State.frames] <;> omega)
        have hchild := ih q (G.arity.eval w.length) (⟨p, count, fuel + 1⟩ :: rest)
        have hval : frameValue G w ⟨q, G.arity.eval w.length, fuel⟩ = G.winEval w fuel q := by
          cases fuel with
          | zero => rfl
          | succ fuel => exact (winEval_eq_winFrom G w fuel q).symm
        rw [hval] at hchild
        have hbound : (⟨p, count, fuel + 1⟩ :: rest).length + fuel + 1 = rest.length + (fuel + 1) + 1 := by
          simp; omega
        rw [hbound] at hchild
        have hv : frameValue G w ⟨p, count + 1, fuel + 1⟩ =
            (!G.winEval w fuel q || frameValue G w ⟨p, count, fuel + 1⟩) := by
          change winFrom G w fuel p (count + 1) = (!G.winEval w fuel q || winFrom G w fuel p count)
          rw [winFrom_succ, hs]
          rfl
        rw [hv]
        cases hc : G.winEval w fuel q with
        | false =>
          rw [hc] at hchild
          have hlast : Trace G w (rest.length + (fuel + 1) + 1)
              (.returning false (⟨p, count, fuel + 1⟩ :: rest)) (.returning true rest) :=
            one_step G w (Step.childLoses _ _)
              (by simp [State.depth, State.frames] <;> omega) (by simp [State.depth, State.frames] <;> omega)
          simpa using (hfirst.trans hchild).trans hlast
        | true =>
          rw [hc] at hchild
          have hresume : Trace G w (rest.length + (fuel + 1) + 1)
              (.returning true (⟨p, count, fuel + 1⟩ :: rest)) (.search (⟨p, count, fuel + 1⟩ :: rest)) :=
            one_step G w (Step.childWins _ _)
              (by simp [State.depth, State.frames] <;> omega) (by simp [State.depth, State.frames] <;> omega)
          simpa using ((hfirst.trans hchild).trans hresume).trans ihc

/-- The search from the initial frame of a bounded position returns its winning value. -/
theorem evaluate_initial (p : Word) :
    Trace G w (G.length.eval w.length + 2)
      (.search [⟨p, G.arity.eval w.length, G.length.eval w.length + 1⟩])
      (.returning (G.winEval w (G.length.eval w.length + 1) p) []) := by
  have h := evaluate_frame G w (G.length.eval w.length + 1) p (G.arity.eval w.length) []
  have hv : frameValue G w ⟨p, G.arity.eval w.length, G.length.eval w.length + 1⟩ =
      G.winEval w (G.length.eval w.length + 1) p := (winEval_eq_winFrom G w _ p).symm
  simpa only [List.length_nil, Nat.zero_add, hv] using h

/-! ### Invariants of reachable search states -/

def Frame.Good (f : Frame) : Prop :=
  G.Bounded w f.pos ∧ f.count ≤ G.arity.eval w.length ∧ f.fuel ≤ G.length.eval w.length + 1

def State.Good (s : State) : Prop := ∀ f ∈ s.frames, Frame.Good G w f

theorem step_good {s t : State} (h : Step G w s t) (hs : State.Good G w s) : State.Good G w t := by
  cases h with
  | zero p count rest => exact fun f hf => hs f (List.mem_cons_of_mem _ hf)
  | exhausted p fuel rest => exact fun f hf => hs f (List.mem_cons_of_mem _ hf)
  | skip p count fuel rest hn =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · have hp := hs _ List.mem_cons_self
      have hc : count + 1 ≤ G.arity.eval w.length := hp.2.1
      exact ⟨hp.1, by show count ≤ _; omega, hp.2.2⟩
    · exact hs f (List.mem_cons_of_mem _ hf)
  | descend p count fuel rest q hq =>
    have hp := hs _ List.mem_cons_self
    have hc : count + 1 ≤ G.arity.eval w.length := hp.2.1
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨G.succ_size w p _ q hp.1 (by omega) hq, le_refl _, ?_⟩
      have hf : fuel + 1 ≤ G.length.eval w.length + 1 := hp.2.2
      show fuel ≤ _
      omega
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨hp.1, by show count ≤ _; omega, hp.2.2⟩
      · exact hs f (List.mem_cons_of_mem _ hf)
  | childWins parent rest => exact hs
  | childLoses parent rest => exact fun f hf => hs f (List.mem_cons_of_mem _ hf)

theorem trace_good {b : ℕ} {s t : State} (h : Trace G w b s t) (hs : State.Good G w s) :
    State.Good G w t := by
  induction h with
  | refl => exact hs
  | tail _ hlast ih => exact step_good G w hlast.1 ih

theorem initial_good (p : Word) (hp : G.Bounded w p) :
    State.Good G w (.search [⟨p, G.arity.eval w.length, G.length.eval w.length + 1⟩]) := by
  intro f hf
  simp only [State.frames, List.mem_singleton] at hf
  subst f
  exact ⟨hp, le_refl _, le_refl _⟩

end Complexity.Games.DepthFirst
