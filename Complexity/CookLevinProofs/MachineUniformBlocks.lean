/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/MachineUniformBlocks.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.MachineUniformBlocks` to `Complexity.CookLevinProofs.MachineUniformBlocks`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.MachineCircuitRuns

namespace Complexity.CookLevinProofs.MachineCircuit

open Complexity.Classical.MachineModels CircuitBuilder

lemma stepExpr_cost_exact (M : SingleTape) (radius : ℕ) (b : Bit M radius) :
    (stepExpr M radius b).cost = 5 * (casesList M radius).length + 1 := by
  simp [stepExpr, anyExpr_cost, List.map_map, Function.comp_def, Expr.cost,
    guard_cost, caseResult_cost, Nat.mul_comm] <;> omega

def blockSize (M : SingleTape) (radius : ℕ) : ℕ :=
  5 * Fintype.card M.Q * (2 * radius + 1) * Fintype.card M.Γ + 1

lemma blockSize_eq (M : SingleTape) (radius : ℕ) :
    blockSize M radius = 5 * (casesList M radius).length + 1 := by
  simp [blockSize, casesList_length, Nat.mul_assoc]

lemma machine_layer_cost_exact (M : SingleTape) (radius : ℕ) :
    layerCost (stepExpressions M radius) = bitCount M radius * blockSize M radius := by
  simp [layerCost, stepExpressions, stepExpr_cost_exact, blockSize_eq]

lemma machine_rounds_size_exact (M : SingleTape) (radius start t : ℕ)
    (v : Fin (bitCount M radius) → ℕ) :
    (compileRounds start (stepExpressions M radius) t v).gates.length =
      t * bitCount M radius * blockSize M radius := by
  rw [compileRounds_length, machine_layer_cost_exact, Nat.mul_assoc]

end Complexity.CookLevinProofs.MachineCircuit
