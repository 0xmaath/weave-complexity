/-
Milestone 2: binary encoding of depth-first search states, and the word-level transition.

A frame `⟨pos, count, fuel⟩` is written as `1^fuel 0 1^count 0 1^|pos| 0 pos`; a state is a
two-bit mode prefix followed by the frames. `nextWord` is the transition function on these
words, written so that it can be transcribed into the tree's `Code` language; it only reads
the top frame and the game's successor function once.
-/
import Complexity.Games.DepthFirst

namespace Complexity.Games.DepthFirst

open Complexity.Classes.PolynomialTime

def bit (w : Word) (i : ℕ) : Bool := (w[i]?).getD false

def frameWord (f : Frame) : Word :=
  List.replicate f.fuel true ++ false :: (List.replicate f.count true ++ false ::
    (List.replicate f.pos.length true ++ false :: f.pos))

def rawFrame (fuel count : ℕ) (pos : Word) : Word :=
  List.replicate fuel true ++ false :: (List.replicate count true ++ false ::
    (List.replicate pos.length true ++ false :: pos))

theorem frameWord_eq (f : Frame) : frameWord f = rawFrame f.fuel f.count f.pos := rfl

def stateWord : State → Word
  | .search fs => [false, false] ++ fs.flatMap frameWord
  | .returning b fs => [true, b] ++ fs.flatMap frameWord

theorem frameWord_length (f : Frame) : (frameWord f).length = f.fuel + f.count + 2 * f.pos.length + 3 := by
  simp only [frameWord, List.length_append, List.length_cons, List.length_replicate]
  omega

theorem stateWord_ne_nil (s : State) : stateWord s ≠ [] := by
  cases s <;> simp [stateWord]

/-- The word-level transition body, given the parsed top frame and the encoded child. -/
def nextBody (A fuel count : ℕ) (state frames pos rest child : Word) : Word :=
  if bit state 0 then
    if bit state 1 then [false, false] ++ frames else [true, true] ++ rest
  else if fuel = 0 ∨ count = 0 then [true, false] ++ rest
  else if child.length = 0 then [false, false] ++ rawFrame fuel (count - 1) pos ++ rest
  else [false, false] ++ rawFrame (fuel - 1) A (child.drop 1) ++ rawFrame fuel (count - 1) pos ++ rest

variable (G : Game)

/-- The transition on state words: parse the top frame, ask the game for the next candidate
move, and rebuild the stack. -/
def nextWord (w s : Word) : Word :=
  let A := G.arity.eval w.length
  let frames := s.drop 2
  let fuel := (frames.takeWhile id).length
  let r1 := frames.drop (fuel + 1)
  let count := (r1.takeWhile id).length
  let r2 := r1.drop (count + 1)
  let len := (r2.takeWhile id).length
  let r3 := r2.drop (len + 1)
  let pos := (List.range len).map fun i => (r3[i]?).getD false
  let rest := r3.drop len
  nextBody A fuel count s frames pos rest (optionWord (G.succ w pos (A - count)))

theorem takeWhile_unary (n : ℕ) (rest : Word) :
    ((List.replicate n true ++ false :: rest).takeWhile id).length = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.takeWhile_cons, ih]

theorem drop_unary (n : ℕ) (rest : Word) :
    (List.replicate n true ++ false :: rest).drop (n + 1) = rest := by
  simp [List.drop_append]

theorem range_map_prefix (pos rest : Word) :
    ((List.range pos.length).map fun i => ((pos ++ rest)[i]?).getD false) = pos := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at hi ⊢
    rw [List.getElem?_append_left hi]
    simp [List.getElem?_eq_getElem hi]

theorem nextWord_frame (w : Word) (f : Frame) (fs : List Frame) (mode result : Bool) :
    nextWord G w ([mode, result] ++ (f :: fs).flatMap frameWord) =
      nextBody (G.arity.eval w.length) f.fuel f.count ([mode, result] ++ (f :: fs).flatMap frameWord)
        ((f :: fs).flatMap frameWord) f.pos (fs.flatMap frameWord)
        (optionWord (G.succ w f.pos (G.arity.eval w.length - f.count))) := by
  simp only [nextWord, List.flatMap_cons, frameWord, List.append_assoc, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero, takeWhile_unary, drop_unary,
    range_map_prefix, List.drop_left]

theorem nextWord_step (w : Word) {s t : State} (h : Step G w s t) :
    nextWord G w (stateWord s) = stateWord t := by
  cases h with
  | zero p count rest =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord]
  | exhausted p fuel rest =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord]
  | skip p count fuel rest hs =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord, hs, optionWord, frameWord_eq]
  | descend p count fuel rest q hs =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord, hs, optionWord, frameWord_eq]
  | childWins parent rest =>
    change nextWord G w ([true, true] ++ (parent :: rest).flatMap frameWord) = _
    rw [nextWord_frame]
    simp [nextBody, bit, stateWord]
  | childLoses parent rest =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord]

/-! ### Length bounds -/

theorem frameWord_length_bound (w : Word) (f : Frame) (hf : Frame.Good G w f) :
    (frameWord f).length ≤ G.length.eval w.length + G.arity.eval w.length + 2 * G.size.eval w.length + 4 := by
  rw [frameWord_length]
  have h1 := hf.1
  have h2 := hf.2.1
  have h3 := hf.2.2
  unfold Game.Bounded at h1
  omega

theorem stateWord_length_bound (w : Word) (s : State) (hs : State.Good G w s)
    (hd : s.depth ≤ G.length.eval w.length + 2) :
    (stateWord s).length ≤ (G.length.eval w.length + 2) *
      (G.length.eval w.length + G.arity.eval w.length + 2 * G.size.eval w.length + 4) + 2 := by
  have hframes (fs : List Frame) (hfs : ∀ f ∈ fs, Frame.Good G w f) :
      (fs.flatMap frameWord).length ≤ fs.length *
        (G.length.eval w.length + G.arity.eval w.length + 2 * G.size.eval w.length + 4) := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
      have hf := frameWord_length_bound G w f (hfs f List.mem_cons_self)
      have hi := ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith
  have hf := hframes s.frames hs
  have hm := Nat.mul_le_mul_right
    (G.length.eval w.length + G.arity.eval w.length + 2 * G.size.eval w.length + 4) hd
  cases s <;> simp only [stateWord, State.depth, State.frames, List.length_append,
    List.length_cons, List.length_nil] at * <;> omega

theorem step_running {w : Word} {s t : State} (h : Step G w s t) : stateWord s ≠ [] ∧ (stateWord s).length ≠ 2 := by
  refine ⟨stateWord_ne_nil s, ?_⟩
  cases h <;> simp only [stateWord, List.length_append, List.length_cons, List.length_nil,
    List.flatMap_cons, frameWord_length] <;> omega

end Complexity.Games.DepthFirst
