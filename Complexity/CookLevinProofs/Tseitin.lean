/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/Tseitin.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.Tseitin` to `Complexity.CookLevinProofs.Tseitin`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.GateCorrect
import Complexity.CookLevin.TseitinCorrect
import Mathlib.Tactic

namespace Complexity.CookLevinProofs

open Complexity.CookLevin Complexity.CookLevin.CNF Complexity.CookLevin.Circuits Complexity.CookLevin.Tseitin

/--
---
conclusion: Complexity.CookLevin.GateCorrect.correct
assumptions:
---
Check the finite truth tables of the five gate forms.
-/
lemma gate_correct (i : ℕ) (g : Gate) (ρ : Assignment) :
    eval (gateClauses i g) ρ = g.check ρ i := by
  cases g with
  | input => rfl
  | constant b =>
    cases b <;> cases hi : ρ i <;>
      simp [gateClauses, eval, Literal.eval, Gate.check, hi]
  | neg a =>
    cases hi : ρ i <;> cases ha : ρ a <;>
      simp [gateClauses, eval, Literal.eval, positive, negative, Gate.check, hi, ha]
  | conj a b =>
    cases hi : ρ i <;> cases ha : ρ a <;> cases hb : ρ b <;>
      simp [gateClauses, eval, Literal.eval, positive, negative, Gate.check, hi, ha, hb]
  | disj a b =>
    cases hi : ρ i <;> cases ha : ρ a <;> cases hb : ρ b <;>
      simp [gateClauses, eval, Literal.eval, positive, negative, Gate.check, hi, ha, hb]

alias _root_.Complexity.CookLevin.GateCorrect.correct := gate_correct

lemma eval_append (F H : Formula) (ρ : Assignment) :
    eval (F ++ H) ρ = (eval F ρ && eval H ρ) := by simp [eval]

lemma eval_flatMap {α : Type} (as : List α) (f : α → Formula) (ρ : Assignment) :
    eval (as.flatMap f) ρ = as.all (fun a => eval (f a) ρ) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.flatMap_cons, eval_append, List.all_cons, ih]

/--
---
conclusion: Complexity.CookLevin.TseitinCorrect.correct
assumptions:
  - Complexity.CookLevin.GateCorrect.correct
---
Conjoin the gate equivalences with the unit output clause.
-/
lemma tseitin_correct (C : Circuit) : CNF.Satisfiable (Tseitin.encode C) ↔ Circuits.Satisfiable C := by
  have h (ρ : Assignment) : eval (Tseitin.encode C) ρ = check C ρ := by
    unfold Tseitin.encode
    rw [eval_append, eval_flatMap]
    simp_rw [GateCorrect.correct]
    simp [eval, Literal.eval, positive, check]
  simp only [CNF.Satisfiable, Circuits.Satisfiable, h]

alias _root_.Complexity.CookLevin.TseitinCorrect.correct := tseitin_correct

end Complexity.CookLevinProofs
