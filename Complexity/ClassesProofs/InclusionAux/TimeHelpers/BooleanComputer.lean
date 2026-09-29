/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/InclusionAux/TimeHelpers/BooleanComputer.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.InclusionAux.TimeHelpers.BooleanComputer` to `Complexity.ClassesProofs.InclusionAux.TimeHelpers.BooleanComputer`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.InclusionAux.TimeHelpers.BoundedCode

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming

open Complexity.Classes.PolynomialTime Turing
open Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackProgram Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackTransfer
open Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackClear (clear clear_store)
open Polynomial

lemma Code.boolean_computer (p : Code Unit) (f : Word → Bool)
    (hp : ∀ w, p.eval (fun _ => w) = [f w]) :
    Nonempty (TM2ComputableInPolyTime id Computability.encodeBool f) := by
  classical
  let E := p.emitter
  let program := Program.seq E.program (clear (.input ()))
  apply program_polytime program (.input ()) .output ((), none) id Computability.encodeBool f
    (E.bound + C 2 * X + C 2)
  intro w
  obtain ⟨t, ht, he⟩ := E.executes (fun _ => w) [] none w.length (by intro i; rfl)
  have hout : p.eval (fun _ => w) = [f w] := hp w
  simp only [E, hout, List.reverse_singleton, List.append_nil] at he
  have hi : store (W := E.Workspace) (fun _ : Unit => w) [] none = ioStore (.input ()) ((), none) w := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with u | _ | v
    · cases u; simp [store, ioStore]
    · simp [store, ioStore]
    · simp [store, ioStore]
  have hc := clear_store (Key.input ()) (store (W := E.Workspace) (fun _ : Unit => w) [f w] none)
  have hf : (⟨((), none), Function.update
      (store (W := E.Workspace) (fun _ : Unit => w) [f w] none).stk (.input ()) []⟩ :
      BitStore (Key Unit E.Workspace) Unit) = ioStore .output ((), none) [f w] := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with u | _ | v
    · cases u; simp [store, ioStore]
    · simp [store, ioStore]
    · simp [store, ioStore]
  change Executes (clear (Key.input () : Key Unit E.Workspace)) _ _ (2 * w.length + 2) at hc
  rw [hf] at hc
  refine ⟨t + (2 * w.length + 2), ?_, ?_⟩
  · simp only [id_eq, eval_add, eval_mul, eval_C, eval_X]
    omega
  change Executes program (ioStore (.input ()) ((), none) w) (ioStore .output ((), none) [f w]) _
  rw [← hi]
  exact .seq he hc

end Complexity.ClassesProofs.InclusionAux.TimeHelpers.Streaming
