/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/FormulaExecution.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.FormulaExecution` to `Complexity.CookLevinProofs.FormulaExecution`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.FormulaLoop

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classical.PolynomialTime Complexity.ClassicalProofs.InclusionAux.TimeCompiler.StackProgram

def endCheck : Code := .atom (.load (fun s => ({s.1 with valid := s.1.valid && s.2.isNone}, s.2)))

lemma parsing_end (xs ys : Word) (flags : Flags) (scratch : Option Bool) :
    Executes endCheck (parsing xs ys [] flags scratch)
      (parsing xs ys [] {flags with valid := flags.valid && scratch.isNone} scratch) 1 := .atom _ _

def checkedFormulaFlags (xs ys : Word) (flags : Flags) : Flags :=
  {formulaFlags xs ys flags with
    valid := (scanFormula xs).valid && (scanFormula xs).rest.head?.isNone}

lemma formula_executes (xs ys : Word) (flags : Flags) (scratch : Option Bool)
    (hv : flags.valid = true) :
    ∃ t, t ≤ 28 * (xs.length + 1) ^ 3 * (ys.length + 1) ∧
      Executes formula (parsing xs ys [] flags scratch)
        (parsing (scanFormula xs).rest.tail ys [] (checkedFormulaFlags xs ys flags)
          (scanFormula xs).rest.head?) t := by
  have hr := parsing_read xs ys [] flags scratch
  obtain ⟨t, ht, he⟩ := formulaTail_executes xs ys flags hv
  have hz := parsing_read (scanFormula xs).rest ys [] (formulaFlags xs ys flags)
    (if (scanFormula xs).valid then some false else none)
  have heof := parsing_end (scanFormula xs).rest.tail ys (formulaFlags xs ys flags)
    (scanFormula xs).rest.head?
  cases he with
  | seq hl hq =>
    have h := Executes.seq hr (.seq hl (.seq hq (.seq hz heof)))
    refine ⟨_, ?_, h⟩
    have hp : 0 < (xs.length + 1) ^ 3 * (ys.length + 1) := by positivity
    nlinarith

lemma formula_invalid_executes (xs ys : Word) (flags : Flags) (scratch : Option Bool)
    (hv : flags.valid = false) :
    Executes formula (parsing xs ys [] flags scratch)
      (parsing xs.tail.tail ys [] flags xs.tail.head?) 5 := by
  have hf : {flags with valid := false} = flags := by cases flags; simp_all
  have hr := parsing_read xs ys [] flags scratch
  have hl := Executes.loop_false (p := formulaBody) (b := continuing)
    (s := parsing xs.tail ys [] flags xs.head?) (by simp [continuing, parsing, hv])
  have hq := parsing_require xs.tail ys [] flags xs.head?
  have hq' : Executes requireTerminator (parsing xs.tail ys [] flags xs.head?)
      (parsing xs.tail ys [] flags xs.head?) 1 := by simpa [hv, hf] using hq
  have hz := parsing_read xs.tail ys [] flags xs.head?
  have heof := parsing_end xs.tail.tail ys flags xs.tail.head?
  have heof' : Executes endCheck (parsing xs.tail.tail ys [] flags xs.tail.head?)
      (parsing xs.tail.tail ys [] flags xs.tail.head?) 1 := by simpa [hv, hf] using heof
  exact .seq hr (.seq hl (.seq hq' (.seq hz heof')))

end Complexity.CookLevinProofs.VerifierProgram
