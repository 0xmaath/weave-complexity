/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/MachineCircuitRuns.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.MachineCircuitRuns` to `Complexity.CookLevinProofs.MachineCircuitRuns`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.MachineCircuitSize

namespace Complexity.CookLevinProofs.MachineCircuit

open Turing Complexity.Classes.MachineModels
open WindowMachine CircuitBuilder Complexity.CookLevin.CNF

lemma evaluate_rounds (M : SingleTape) (radius t : ℕ) (c : Cfg M radius) :
    (evaluateLayer (stepExpressions M radius))^[t] (encode M radius c) =
      encode M radius ((next M radius)^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, stepExpressions_eval, Function.iterate_succ_apply']

lemma simulation_sound (M : SingleTape) (radius start t : ℕ) (v : Fin (bitCount M radius) → ℕ)
    (c : Cfg M radius) (ρ : Assignment)
    (hi : (fun i => ρ (v i)) = encode M radius c)
    (hs : Satisfies start (compileRounds start (stepExpressions M radius) t v).gates ρ) :
    (fun i => ρ ((compileRounds start (stepExpressions M radius) t v).outputs i)) =
      encode M radius ((next M radius)^[t] c) := by
  have h := compileRounds_sound start (stepExpressions M radius) t v
    (fun i => stepExpr_bounded M radius _) ρ hs
  rw [hi, evaluate_rounds] at h
  exact h

lemma simulation_complete (M : SingleTape) (radius start t : ℕ) (v : Fin (bitCount M radius) → ℕ)
    (hv : ∀ i, v i < start) (c : Cfg M radius) (ρ : Assignment)
    (hi : (fun i => ρ (v i)) = encode M radius c) :
    ∃ σ, (∀ j < start, σ j = ρ j) ∧
      Satisfies start (compileRounds start (stepExpressions M radius) t v).gates σ ∧
      (fun i => σ ((compileRounds start (stepExpressions M radius) t v).outputs i)) =
        encode M radius ((next M radius)^[t] c) := by
  obtain ⟨σ, hσ, hs, ho⟩ := compileRounds_complete start (stepExpressions M radius) t v
    (fun i => stepExpr_bounded M radius _) hv ρ
  rw [hi, evaluate_rounds] at ho
  exact ⟨σ, hσ, hs, ho⟩

end Complexity.CookLevinProofs.MachineCircuit
