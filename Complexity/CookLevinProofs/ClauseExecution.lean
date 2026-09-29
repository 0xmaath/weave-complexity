/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/ClauseExecution.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.ClauseExecution` to `Complexity.CookLevinProofs.ClauseExecution`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.ClauseLoop

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classes.PolynomialTime Complexity.ClassesProofs.InclusionAux.TimeCompiler.StackProgram

def checkedClauseFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanClause xs).valid
    conjunction := flags.conjunction && clauseValue (scanClause xs).value ys
    clause := clauseValue (scanClause xs).value ys}

lemma clause_executes (xs ys : Word) (flags : Flags) (scratch : Option Bool)
    (hv : flags.valid = true) :
    ∃ t, t ≤ 20 * (xs.length + 1) ^ 2 * (ys.length + 1) ∧
      Executes clause (parsing xs ys [] flags scratch)
        (parsing (scanClause xs).rest ys [] (checkedClauseFlags xs ys flags)
          (if (scanClause xs).valid then some false else none)) t := by
  let f : Flags := {flags with clause := false}
  have ha := parsing_assign (fun s => {s with clause := false}) xs ys [] flags scratch
  have hr := parsing_read xs ys [] f scratch
  obtain ⟨t, ht, he⟩ := clauseTail_executes xs ys f hv
  have hz := parsing_assign (fun s => {s with conjunction := s.conjunction && s.clause})
    (scanClause xs).rest ys [] (clauseFlags xs ys f)
    (if (scanClause xs).valid then some false else none)
  cases he with
  | seq hl hq =>
    have h := Executes.seq ha (.seq hr (.seq hl (.seq hq hz)))
    refine ⟨_, ?_, by simpa [clause, f, clauseFlags, checkedClauseFlags] using h⟩
    have hp : 0 < (xs.length + 1) ^ 2 * (ys.length + 1) := by positivity
    nlinarith

end Complexity.CookLevinProofs.VerifierProgram
