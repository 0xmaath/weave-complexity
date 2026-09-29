/-
Milestone 2: the winner-determination language of every `Game` is in PSPACE.

The proof follows the Arc Kayles membership proof of the ported tree step for step, with the
game-specific pieces replaced by the generic depth-first search: the driver `Code` is
iterated by the ported `CodeStepper` loop, the input is captured onto the work stack by the
ported `InputCapture`, and the ported stack-to-tape compiler (`dspace_of_execution`) turns the
resulting stack command into a deterministic read-only-input work-tape machine with a
polynomial space bound.
-/
import Complexity.Games.StepCode
import Complexity.ArcKaylesProofs.InputCapture
import Complexity.ArcKaylesProofs.CodeStepper

set_option backward.isDefEq.respectTransparency false

namespace Complexity.Games.Membership

open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
open Complexity.ClassesProofs.SavitchProofs
open StackLanguage
open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace
open Complexity.ArcKaylesProofs.CodeStepper
open Complexity.Games.DepthFirst Complexity.Games.StepCode Polynomial
open Complexity.ArcKaylesProofs
open scoped Classical

noncomputable section

variable (G : Game)

/-- A polynomial bounding every state word of the search on inputs of length `n`. -/
def stateBound : Polynomial ℕ :=
  (G.length + C 2) * (G.length + G.arity + C 2 * G.size + C 4) + C 2 * X + C 4

theorem stateBound_eval (n : ℕ) : (stateBound G).eval n =
    (G.length.eval n + 2) * (G.length.eval n + G.arity.eval n + 2 * G.size.eval n + 4) + 2 * n + 4 := by
  simp [stateBound]

theorem stateBound_input (n : ℕ) : 2 * n + 2 ≤ (stateBound G).eval n := by
  rw [stateBound_eval]; omega

theorem stateBound_stack (n : ℕ) :
    (G.length.eval n + 2) * (G.length.eval n + G.arity.eval n + 2 * G.size.eval n + 4) + 2 ≤
      (stateBound G).eval n := by
  rw [stateBound_eval]; omega

theorem step_running' {w : Word} {s t : State} (h : Step G w s t) : running (stateWord s) = true := by
  simp [running, (step_running G h).2]

theorem driver_trace (w : Word) {s t : State} (h : Trace G w (G.length.eval w.length + 2) s t)
    (hs : State.Good G w s) :
    Relation.ReflTransGen (Transition (driverCode G) w ((stateBound G).eval w.length))
      (stateWord s) (stateWord t) := by
  have hb := stateBound_stack G w.length
  induction h with
  | refl => exact .refl
  | @tail t u ht htu ih =>
    have hgood := trace_good G w ht hs
    apply ih.tail
    refine ⟨step_running' G htu.1, ?_, ?_, ?_⟩
    · rw [show args w (stateWord t) = (fun b => if b then stateWord t else w) from rfl,
        driverCode_next _ _ _ (stateWord_ne_nil t)]
      exact nextWord_step G w htu.1
    · exact (stateWord_length_bound G w t hgood htu.2.1).trans hb
    · exact (stateWord_length_bound G w u (step_good G w htu.1 hgood) htu.2.2).trans hb

theorem driver_decides (w : Word) : ∃ b : Bool,
    Relation.ReflTransGen (Transition (driverCode G) w ((stateBound G).eval w.length)) [] [true, b] ∧
    (b = true ↔ w ∈ G.language) := by
  have hbound := stateBound_input G w.length
  cases hp : G.start w with
  | none =>
    refine ⟨false, Relation.ReflTransGen.single ?_, ?_⟩
    · refine ⟨by decide, ?_, by simp, by simp; omega⟩
      change (driverCode G).eval (fun b => if b then [] else w) = _
      rw [driverCode_initial]
      simp [initialWord, hp]
    · simp [Game.language, hp]
  | some p =>
    have hpb : G.Bounded w p := G.start_size w p hp
    let start : State := .search [⟨p, G.arity.eval w.length, G.length.eval w.length + 1⟩]
    have hlen : (stateWord start).length ≤ (stateBound G).eval w.length :=
      (stateWord_length_bound G w start (initial_good G w p hpb)
        (by simp [start, State.depth, State.frames])).trans (stateBound_stack G w.length)
    have hinit : Transition (driverCode G) w ((stateBound G).eval w.length) [] (stateWord start) := by
      refine ⟨by decide, ?_, by simp, hlen⟩
      change (driverCode G).eval (fun b => if b then [] else w) = _
      rw [driverCode_initial]
      simp [initialWord, hp, start, stateWord, frameWord_eq]
    have hdfs := driver_trace G w (evaluate_initial G w p) (initial_good G w p hpb)
    refine ⟨G.winEval w (G.length.eval w.length + 1) p,
      (Relation.ReflTransGen.single hinit).trans hdfs, ?_⟩
    simp [Game.language, hp, Game.Winning]

def workPolynomial : Polynomial ℕ :=
  C 4 * (flagCode (driverCode G)).emitter.bound.comp (stateBound G) + C 3 * stateBound G + C 6

theorem workPolynomial_eval (n : ℕ) :
    (workPolynomial G).eval n = spaceBound (driverCode G) ((stateBound G).eval n) := by
  simp [workPolynomial, spaceBound, eval_comp]

def setInitial (q : Register) : Register := ((q.1.1, some true), none)
def saveBit (q : Register) (v : Option Bool) : Register := ((q.1.1, v), none)

def readAnswer : Command (Keys (driverCode G)) Bool Register :=
  .seq (.pop (fun _ => .input true) saveBit) (.pop (fun _ => .input true) saveBit)

def decider : Command (Keys (driverCode G)) Bool Register :=
  .seq (capture (driverCode G))
    (.seq (.assign setInitial) (.seq (machineLoop (driverCode G)) (readAnswer G)))

theorem decider_execution (w : Word) :
    ∃ e, Exec w ((workPolynomial G).eval w.length) (decider G) ⟨(((), none), none), 0, fun _ => []⟩ e ∧
      (e.state.1.2.getD false = true ↔ w ∈ G.language) := by
  rw [workPolynomial_eval]
  let B := (stateBound G).eval w.length
  have hB : 2 * w.length + 2 ≤ B := stateBound_input G w.length
  have hcap := capture_input (driverCode G) w
    (spaceBound (driverCode G) B) (by unfold spaceBound; omega)
  let d := ProgramSpace.encode (configuration (driverCode G) w [] none) (w.length + 1)
  have hi := Exec.assign d setInitial hcap.good.2
  have hiend : assigned d (setInitial d.state) =
      ProgramSpace.encode (configuration (driverCode G) w [] (some (running []))) (w.length + 1) := rfl
  rw [hiend] at hi
  obtain ⟨b, htrace, hb⟩ := driver_decides G w
  have hl := loop_space (driverCode G) w B (w.length + 1) (by omega) (Nat.le_refl _) htrace
    (by simp [running]) (by simp; omega)
  let last := ProgramSpace.encode (configuration (driverCode G) w [true, b] (some false)) (w.length + 1)
  have hfirst := Exec.pop last (fun _ : Register => Key.input true) saveBit hl.good.2
  let first := popped last (.input true) saveBit
  have hsecond := Exec.pop first (fun _ : Register => Key.input true) saveBit hfirst.good.2
  refine ⟨_, .seq hcap (.seq hi (.seq hl (.seq hfirst hsecond))), ?_⟩
  simpa [first, last, popped, saveBit, ProgramSpace.encode, configuration, store, args] using hb

/-- **The game template.** The winner-determination language of every polynomially bounded
normal-play game with computable moves is decidable in polynomial space. -/
theorem language_mem_PSPACE : G.language ∈ PSPACE := by
  refine ⟨workPolynomial G, ?_⟩
  exact dspace_of_execution (decider G) (((), none), none) (fun q => q.1.2.getD false)
    (workPolynomial G).eval (fun n => by rw [workPolynomial_eval]; unfold spaceBound; omega)
    G.language (decider_execution G)

end

end Complexity.Games.Membership

namespace Complexity.Games

/-- Any concrete game instantiates the template by supplying its moves. -/
theorem Game.language_mem_PSPACE (G : Game) :
    G.language ∈ Complexity.Classes.PolynomialSpace.PSPACE :=
  Membership.language_mem_PSPACE G

end Complexity.Games
