/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/VariableFoldCode.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.VariableFoldCode` to `Complexity.ArcKaylesProofs.VariableFoldCode`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.VariableFoldLayout

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.CircuitStreaming

open Complexity.CookLevinProofs.CircuitBuilder Complexity.CookLevinProofs.Streaming
open Complexity.Classes.PolynomialTime

theorem flatMap_replicate_sum {α : Type} (xs : List α) (f : α → ℕ) :
    (xs.flatMap (fun x => List.replicate (f x) true)) = List.replicate ((xs.map f).sum) true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, ih, List.replicate_add]

def sumNumber {I : Type} (count : Number I) (term : Number (Option I)) : Number I where
  value a := ((List.range (count.value a)).map (fun i => term.value (extend a (List.replicate i true)))).sum
  code := Code.loop count term.code
  correct a := by
    rw [Code.eval_loop]
    simp only [Number.correct, flatMap_replicate_sum]

def termCost {I : Type} (count : Number I) (term : Expression (Option I)) : Number I :=
  sumNumber count term.cost

theorem termCost_value {I : Type} (count : Number I) (term : Expression (Option I)) (a : I → Word) :
    (termCost count term).value a =
      prefixCost (fun i => term.value (extend a (List.replicate i true))) (count.value a) := by
  simp only [termCost, sumNumber, Expression.cost_correct, prefixCost]

def indexedOutput {I : Type} (i start : Number I) (term : Expression (Option I)) : Number I :=
  i.bind (term.outputAt (start.rename some))

theorem indexedOutput_value {I : Type} (i start : Number I) (term : Expression (Option I)) (a : I → Word) :
    (indexedOutput i start term).value a =
      (compile (start.value a) (term.value (extend a (List.replicate (i.value a) true)))).output := by
  simp only [indexedOutput, Number.bind, Expression.outputAt_value, Number.rename, extend_some]

def variableFoldCode {I : Type} (conjunction : Bool) (start count : Number I)
    (term : Expression (Option I)) : Code I :=
  let i : Number (Option I) := .length none
  let s := start.rename some
  let c := count.rename some
  let lifted := term.rename (Option.map some)
  let terms := Code.loop count (term.run (s.add (termCost i lifted)))
  let total := termCost count term
  let initial := (GateCode.constant (.constant conjunction)).code (start.add total)
  let rev := (c.sub (.constant 1)).sub i
  let left := indexedOutput rev (s.add (termCost rev lifted)) lifted
  let current := ((start.add total).rename some).add i
  let gate := if conjunction then GateCode.conj left current else GateCode.disj left current
  .append terms (.append initial (Code.loop count (gate.code (current.add (.constant 1)))))

theorem variableFoldCode_correct {I : Type} (conjunction : Bool) (start count : Number I)
    (term : Expression (Option I)) (a : I → Word) :
    (variableFoldCode conjunction start count term).eval a =
      gatesWord (start.value a) (compile (start.value a)
        (foldExpr conjunction ((List.range (count.value a)).map
          (fun i => term.value (extend a (List.replicate i true)))))).gates := by
  rw [compile_fold_variable_word]
  cases conjunction <;>
    simp only [variableFoldCode, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
      code_append_eval, Code.eval_loop, Expression.eval_run, GateCode.correct, GateCode.value,
      termCost_value, indexedOutput_value, Expression.rename, Number.add, Number.sub,
      Number.constant, Number.length, Number.rename, Test.constant, extend_some, extend_skip,
      extend, Option.elim_none, List.length_replicate, foldGate]

def variableFold {I : Type} (conjunction : Bool) (count : Number I) (term : Expression (Option I)) :
    Expression I where
  value a := foldExpr conjunction ((List.range (count.value a)).map
    (fun i => term.value (extend a (List.replicate i true))))
  cost := ((termCost count term).add count).add (.constant 1)
  output := ((Number.length none).add ((termCost count term).rename some)).add (count.rename some)
  code := variableFoldCode conjunction (.length none) (count.rename some) (term.rename (Option.map some))
  cost_correct a := by
    simp only [Number.add, Number.constant, termCost_value, foldExpr_cost, List.length_map,
      List.length_range, List.map_map, Function.comp_def, prefixCost]
  output_correct a start := by
    rw [compile_fold_output]
    simp only [Number.add, Number.length, Number.rename, termCost_value, extend_some,
      extend, Option.elim_none, Option.elim_some, List.length_replicate, List.map_map, Function.comp_def,
      List.length_map, List.length_range, prefixCost]
  correct a start := by
    rw [variableFoldCode_correct]
    simp only [Number.length, Number.rename, Expression.rename, extend_some, extend_skip,
      extend, Option.elim_none, List.length_replicate]

end Complexity.ArcKaylesProofs.CircuitStreaming
