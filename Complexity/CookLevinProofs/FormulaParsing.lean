/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/FormulaParsing.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.FormulaParsing` to `Complexity.CookLevinProofs.FormulaParsing`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.ClauseParsing

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classes.PolynomialTime Complexity.CookLevin.Encoding Complexity.CookLevin.CNF Complexity.CookLevin.Satisfiability

def scanFormula : Word → Parsed Formula := scanMany scanClause scanClause_length

lemma scanFormula_length (xs : Word) : (scanFormula xs).rest.length ≤ xs.length :=
  scanMany_length _ _ xs

lemma scanFormula_sound (xs : Word) (hv : (scanFormula xs).valid = true) :
    xs = encodeCNF (scanFormula xs).value ++ (scanFormula xs).rest :=
  scanMany_sound _ _ _ scanClause_sound xs hv

lemma scanFormula_encoded (F : Formula) (xs : Word) :
    scanFormula (encodeCNF F ++ xs) = ⟨F, xs, true⟩ :=
  scanMany_encoded _ _ _ scanClause_encoded F xs

lemma scanFormula_invalid_rest (xs : Word) (hv : (scanFormula xs).valid = false) :
    (scanFormula xs).rest = [] :=
  scanMany_invalid_rest _ _ scanClause_invalid_rest xs hv

def lastClause (ys : Word) : Formula → Bool → Bool
  | [], previous => previous
  | C :: Cs, _ => lastClause ys Cs (clauseValue C ys)

def formulaFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanFormula xs).valid
    conjunction := flags.conjunction && eval (scanFormula xs).value (assignment ys)
    clause := lastClause ys (scanFormula xs).value flags.clause}

end Complexity.CookLevinProofs.VerifierProgram
