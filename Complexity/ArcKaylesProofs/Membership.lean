/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/Membership.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.Membership` to `Complexity.ArcKaylesProofs.Membership`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.DriverTrace
import Complexity.ArcKaylesProofs.InputCapture
import Complexity.ArcKayles.Completeness
import Batteries.Tactic.Alias

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.ArcKaylesMachine

open Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
open Complexity.ClassesProofs.SavitchProofs
open StackLanguage
open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace
open Complexity.ArcKayles Encoding MachineCode CodeStepper DepthFirst Polynomial
open scoped Classical

noncomputable section

def workPolynomial : Polynomial ℕ :=
  C 4 * (flagCode driverCode).emitter.bound.comp stateBound + C 3 * stateBound + C 6

theorem workPolynomial_eval (n : ℕ) :
    workPolynomial.eval n = spaceBound driverCode (stateBound.eval n) := by
  simp [workPolynomial, spaceBound, eval_comp]

def setInitial (q : Register) : Register := ((q.1.1, some true), none)
def saveBit (q : Register) (v : Option Bool) : Register := ((q.1.1, v), none)

def readAnswer : Command (Keys driverCode) Bool Register :=
  .seq (.pop (fun _ => .input true) saveBit) (.pop (fun _ => .input true) saveBit)

def decider : Command (Keys driverCode) Bool Register :=
  .seq (capture driverCode)
    (.seq (.assign setInitial) (.seq (machineLoop driverCode) readAnswer))

theorem decider_execution (w : Word) :
    ∃ e, Exec w (workPolynomial.eval w.length) decider ⟨(((), none), none), 0, fun _ => []⟩ e ∧
      (e.state.1.2.getD false = true ↔ w ∈ arcKayles) := by
  rw [workPolynomial_eval]
  let B := stateBound.eval w.length
  have hB : 2 * w.length + 2 ≤ B := stateBound_input w.length
  have hcap := capture_input driverCode w (spaceBound driverCode B) (by unfold spaceBound; omega)
  let d := ProgramSpace.encode (configuration driverCode w [] none) (w.length + 1)
  have hi := Exec.assign d setInitial hcap.good.2
  have hiend : assigned d (setInitial d.state) =
      ProgramSpace.encode (configuration driverCode w [] (some (running []))) (w.length + 1) := rfl
  rw [hiend] at hi
  obtain ⟨b, htrace, hb⟩ := driver_decides w
  have hl := loop_space driverCode w B (w.length + 1) (by omega) (Nat.le_refl _) htrace
    (by simp [running]) (by simp; omega)
  let last := ProgramSpace.encode (configuration driverCode w [true, b] (some false)) (w.length + 1)
  have hfirst := Exec.pop last (fun _ : Register => Key.input true) saveBit hl.good.2
  let first := popped last (.input true) saveBit
  have hsecond := Exec.pop first (fun _ : Register => Key.input true) saveBit hfirst.good.2
  refine ⟨_, .seq hcap (.seq hi (.seq hl (.seq hfirst hsecond))), ?_⟩
  simpa [first, last, popped, saveBit, ProgramSpace.encode, configuration, store, args] using hb

theorem membership : arcKayles ∈ PSPACE := by
  refine ⟨workPolynomial, ?_⟩
  exact dspace_of_execution decider (((), none), none) (fun q => q.1.2.getD false)
    workPolynomial.eval (fun n => by rw [workPolynomial_eval]; unfold spaceBound; omega)
    arcKayles decider_execution

end

end Complexity.ArcKaylesProofs.ArcKaylesMachine

namespace Complexity.ArcKaylesProofs

/--
---
conclusion: Complexity.ArcKayles.Completeness.membership
---
Validate the graph word and evaluate the game tree by a depth-first stack.
The encoded stack is cubically bounded, and each transition is compiled
from a polynomially bounded word program. Reusing its cleared workspace
gives a single polynomial space bound for the entire terminating search.
The archived stack-to-tape compiler provides the required deterministic
read-only-input work-tape machine.
-/
theorem arcKayles_membership : Complexity.ArcKayles.Encoding.arcKayles ∈ Complexity.Classes.PolynomialSpace.PSPACE :=
  ArcKaylesMachine.membership

alias _root_.Complexity.ArcKayles.Completeness.membership := arcKayles_membership

end Complexity.ArcKaylesProofs
