/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/VariableFoldLayout.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.VariableFoldLayout` to `Complexity.ArcKaylesProofs.VariableFoldLayout`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.ExpressionFold

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.CircuitStreaming

open Complexity.CookLevinProofs Complexity.CookLevinProofs.CircuitBuilder Complexity.CookLevinProofs.Streaming
open Complexity.CookLevin.Circuits Complexity.CookLevin.Tseitin

def prefixCost (f : ℕ → Expr) (n : ℕ) : ℕ := ((List.range n).map (fun i => (f i).cost)).sum

theorem prefixCost_zero (f : ℕ → Expr) : prefixCost f 0 = 0 := rfl

theorem prefixCost_succ (f : ℕ → Expr) (n : ℕ) : prefixCost f (n + 1) = prefixCost f n + (f n).cost := by
  simp [prefixCost, List.range_succ]

theorem compileMany_variable_range' (start offset n : ℕ) (f : ℕ → Expr) :
    gatesWord (start + prefixCost f offset)
      (compileMany (start + prefixCost f offset) ((List.range' offset n).map f)).gates =
      (List.range' offset n).flatMap (fun i => gatesWord (start + prefixCost f i)
        (compile (start + prefixCost f i) (f i)).gates) := by
  induction n generalizing offset with
  | zero => simp [compileMany, gatesWord_nil]
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, List.flatMap_cons, compileMany, gatesWord_append,
      compile_length]
    have he : start + prefixCost f offset + (f offset).cost = start + prefixCost f (offset + 1) := by
      rw [prefixCost_succ]; omega
    rw [he, ih]

theorem compileMany_variable_range (start n : ℕ) (f : ℕ → Expr) :
    gatesWord start (compileMany start ((List.range n).map f)).gates =
      (List.range n).flatMap (fun i => gatesWord (start + prefixCost f i)
        (compile (start + prefixCost f i) (f i)).gates) := by
  simpa [← List.range_eq_range', prefixCost_zero] using compileMany_variable_range' start 0 n f

theorem compileMany_variable_outputs' (start offset n : ℕ) (f : ℕ → Expr) :
    (compileMany (start + prefixCost f offset) ((List.range' offset n).map f)).outputs =
      (List.range' offset n).map (fun i => (compile (start + prefixCost f i) (f i)).output) := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, compileMany, compile_length]
    have he : start + prefixCost f offset + (f offset).cost = start + prefixCost f (offset + 1) := by
      rw [prefixCost_succ]; omega
    rw [he, ih]

theorem compileMany_variable_outputs (start n : ℕ) (f : ℕ → Expr) :
    (compileMany start ((List.range n).map f)).outputs =
      (List.range n).map (fun i => (compile (start + prefixCost f i) (f i)).output) := by
  simpa [← List.range_eq_range', prefixCost_zero] using compileMany_variable_outputs' start 0 n f

theorem reverse_range_map {α : Type} (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).reverse = (List.range n).map (fun i => f (n - 1 - i)) := by
  rw [← List.map_reverse]
  have hr : (List.range n).reverse = (List.range n).map (n - 1 - ·) := by
    simpa [← List.range_eq_range'] using (List.reverse_range' (s := 0) (n := n))
  rw [hr, List.map_map]
  rfl

theorem compile_fold_variable_word (conjunction : Bool) (start n : ℕ) (f : ℕ → Expr) :
    gatesWord start (compile start (foldExpr conjunction ((List.range n).map f))).gates =
      (List.range n).flatMap (fun i => gatesWord (start + prefixCost f i)
        (compile (start + prefixCost f i) (f i)).gates) ++
      (CNFOutput.segment (gateClauses (start + prefixCost f n) (.constant conjunction)) ++
        (List.range n).flatMap (fun i => CNFOutput.segment
          (gateClauses (start + prefixCost f n + i + 1)
            (foldGate conjunction
              (compile (start + prefixCost f (n - 1 - i)) (f (n - 1 - i))).output
              (start + prefixCost f n + i))))) := by
  rw [compile_fold_gates, gatesWord_append, gatesWord_cons, compileMany_variable_range,
    compileMany_length, compileMany_variable_outputs, reverse_range_map]
  simp only [List.map_map, Function.comp_def]
  change _ = _
  rw [combineGates_range_word]
  rfl

end Complexity.ArcKaylesProofs.CircuitStreaming
