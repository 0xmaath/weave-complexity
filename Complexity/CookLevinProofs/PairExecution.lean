/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/PairExecution.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.PairExecution` to `Complexity.CookLevinProofs.PairExecution`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.PairLoop

set_option backward.isDefEq.respectTransparency false

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classes.PolynomialTime Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackProgram Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackTransfer

def ready (x y : Word) (good : Bool) : Data :=
  ⟨(⟨good, false, true, false⟩, none), fun r =>
    if r = .input then y else if r = .formula then x else []⟩

lemma initial_read (w : Word) :
    Executes (read .input) (ioStore .input initial w)
      (decodingData (fun _ => []) w [] true false) 1 := by
  have he := Executes.atom (.pop Register.input (fun s : Control => fun b => (s.1, b)))
    (ioStore Register.input initial w : Data)
  convert! he using 1
  apply Store.ext
  · simp [ioStore, initial, Op.apply, decodingData]
  · funext r
    cases r <;> simp [ioStore, Op.apply, decodingData]

lemma decodePair_executes (w : Word) :
    ∃ t, t ≤ 10 * w.length + 8 ∧
      Executes decodePair (ioStore .input initial w)
        (ready (splitInput w).formula (splitInput w).certificate (splitInput w).valid) t := by
  have hread := initial_read w
  have hloop := decodingLoop_executes (fun _ => []) w [] true false
  let d := decodingDone (fun _ => []) (splitInput w) [] true false
  have htrans := transfer_store .reverse .formula (by decide) d
  have heq :
      (⟨(d.state.1, none), Function.update (Function.update d.stk .reverse []) .formula
        ((d.stk .reverse).reverse ++ d.stk .formula)⟩ : Data) =
      ready (splitInput w).formula (splitInput w).certificate (splitInput w).valid := by
    apply Store.ext
    · rfl
    · funext r
      cases r <;> simp [d, decodingDone, ready]
  rw [heq] at htrans
  refine ⟨_, ?_, .seq hread (.seq hloop htrans)⟩
  have ht := decodeCost_bound w
  have hl := splitInput_length w
  simp [d, decodingDone] at *
  omega

end Complexity.CookLevinProofs.VerifierProgram
