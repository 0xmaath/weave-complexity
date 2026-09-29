/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/CNFTraversalCode.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.CNFTraversalCode` to `Complexity.ArcKaylesProofs.CNFTraversalCode`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.CNFTraversal

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ArcKaylesProofs.CNFTraversal

open Complexity.Classical.PolynomialTime
open Complexity.ClassicalProofs.InclusionAux.TimeHelpers.Streaming

def dropCode {I : Type} (word : I) (n : Number I) : Code I :=
  .bind n.code (.drop (some word) none)

theorem dropCode_eval {I : Type} (word : I) (n : Number I) (a : I → Word) :
    (dropCode word n).eval a = (a word).drop (n.value a) := by
  simp [dropCode, Code.eval, Number.correct, extend]

def literalStepCode {I : Type} (word : I) : Code I :=
  .branch word (.bind (dropCode word (.constant 1))
    (dropCode (some word) ((MachineCode.leadingOnes none).add (.constant 3)))) (.source word)

theorem literalStepCode_eval {I : Type} (word : I) (a : I → Word) :
    (literalStepCode word).eval a = literalStep (a word) := by
  simp only [literalStepCode, Code.eval, dropCode_eval, Number.add, Number.constant,
    MachineCode.leadingOnes_value, extend, Option.elim_some, Option.elim_none, literalStep]

theorem iterate_clip {f : Word → Word} (hf : ∀ w, (f w).length ≤ w.length)
    (cap : ℕ) (w : Word) (hw : w.length ≤ cap) (j : ℕ) :
    (fun x => (f x).take cap)^[j] w = f^[j] w := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      List.take_of_length_le ((hf w).trans hw)]
    exact ih _ ((hf w).trans hw)

def clauseStepCode {I : Type} (word : I) : Code I :=
  .bind (Code.iterateValues (.length word) (.length word) (.source word) (literalStepCode none))
    (dropCode none (.constant 1))

theorem clauseStepCode_eval {I : Type} (word : I) (a : I → Word) :
    (clauseStepCode word).eval a = clauseStep (a word) := by
  simp only [clauseStepCode, Code.eval, dropCode_eval, Number.constant, extend, Option.elim_none,
    Code.eval_iterateValues, literalStepCode_eval, List.length_replicate]
  rw [iterate_clip literalStep_length _ _ (le_refl _)]
  rfl

def formulaStepCode {I : Type} (word : I) : Code I :=
  .branch word (.bind (dropCode word (.constant 1)) (clauseStepCode none)) (.source word)

theorem formulaStepCode_eval {I : Type} (word : I) (a : I → Word) :
    (formulaStepCode word).eval a = formulaStep (a word) := by
  simp only [formulaStepCode, Code.eval, dropCode_eval, Number.constant, clauseStepCode_eval,
    extend, Option.elim_none, formulaStep]

def literalSuffixCode {I : Type} (word : I) (j : Number I) : Code I :=
  Code.iterateValues j.code (.length word) (.source word) (literalStepCode none)

theorem literalSuffixCode_eval {I : Type} (word : I) (j : Number I) (a : I → Word) :
    (literalSuffixCode word j).eval a = literalStep^[j.value a] (a word) := by
  simp only [literalSuffixCode, Code.eval_iterateValues, Number.correct, Code.eval,
    literalStepCode_eval, extend, Option.elim_none, List.length_replicate]
  exact iterate_clip literalStep_length _ _ (le_refl _) _

def formulaSuffixCode {I : Type} (word : I) (j : Number I) : Code I :=
  Code.iterateValues j.code (.length word) (.source word) (formulaStepCode none)

theorem formulaSuffixCode_eval {I : Type} (word : I) (j : Number I) (a : I → Word) :
    (formulaSuffixCode word j).eval a = formulaStep^[j.value a] (a word) := by
  simp only [formulaSuffixCode, Code.eval_iterateValues, Number.correct, Code.eval,
    formulaStepCode_eval, extend, Option.elim_none, List.length_replicate]
  exact iterate_clip formulaStep_length _ _ (le_refl _) _

end Complexity.ArcKaylesProofs.CNFTraversal
