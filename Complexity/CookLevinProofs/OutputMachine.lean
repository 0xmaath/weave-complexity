/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/OutputMachine.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.OutputMachine` to `Complexity.CookLevinProofs.OutputMachine`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.OutputCode

namespace Complexity.CookLevinProofs.Streaming

open Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackProgram Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackTransfer Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackRename
open Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackClear (clear clear_store)
open CNFOutput Complexity.Classical.PolynomialTime Polynomial Turing

lemma Code.polynomial_time (c : Code Unit) :
    Nonempty (TM2ComputableInPolyTime id id (fun x => c.eval (fun _ => x))) := by
  let p := c.emitter
  let K := Key Unit (Option p.Workspace)
  let input : K := .input ()
  let output : K := .work none
  let program : BitProgram K Unit := .seq (Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackRename.rename (workMap some) p.program)
    (.seq (clear input) (transfer .output output))
  apply program_polytime program input output ((), none) id id
    (fun x => c.eval (fun _ => x)) (C 4 * p.bound + C 2 * X + C 4)
  intro x
  let a : Unit → Word := fun _ => x
  let s : BitStore K Unit := ioStore input ((), none) x
  obtain ⟨t, ht, he⟩ := p.run_in (workMap some) (workMap_injective _ (Option.some_injective _))
    s a x.length (by intro i; cases i; simp [s, input, workMap, ioStore, a])
    (by intro w; simp [s, input, workMap, ioStore]) (by intro i; rfl)
  simp only [workMap] at he
  let mid := emitted Key.output (c.eval a) s
  have hclear := clear_store input mid
  let cleaned : BitStore K Unit := ⟨((), none), Function.update mid.stk input []⟩
  change Executes (clear input) mid cleaned (2 * (mid.stk input).length + 2) at hclear
  have htransfer := transfer_store (Key.output : K) output (by simp [output]) cleaned
  have hinput : mid.stk input = x := by simp [mid, emitted, s, ioStore, input]
  have hbuffer : cleaned.stk Key.output = (c.eval a).reverse := by
    simp [cleaned, mid, emitted, s, ioStore, input]
  rw [hinput] at hclear
  rw [hbuffer, List.length_reverse] at htransfer
  have hend : (⟨(cleaned.state.1, none),
      Function.update (Function.update cleaned.stk Key.output []) output
        (((c.eval a).reverse).reverse ++ cleaned.stk output)⟩ : BitStore K Unit) =
      ioStore output ((), none) (c.eval a) := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with u | _ | w
    · cases u; simp [cleaned, mid, emitted, s, ioStore, input, output]
    · simp [cleaned, mid, emitted, s, ioStore, input, output]
    · cases w <;> simp [cleaned, mid, emitted, s, ioStore, input, output, Function.update_apply]
  rw [hend] at htransfer
  have hlen := p.length_bound a x.length (by intro i; rfl)
  refine ⟨t + ((2 * x.length + 2) + (3 * (c.eval a).length + 2)), ?_,
    .seq he (.seq hclear htransfer)⟩
  simp only [eval_add, eval_mul, eval_C, eval_X, id_eq]
  change (c.eval a).length ≤ p.bound.eval x.length at hlen
  omega

end Complexity.CookLevinProofs.Streaming
