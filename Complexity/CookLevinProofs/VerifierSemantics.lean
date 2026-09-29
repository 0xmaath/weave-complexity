/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/VerifierSemantics.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.VerifierSemantics` to `Complexity.CookLevinProofs.VerifierSemantics`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.FormulaParsing
import Complexity.CookLevinProofs.PairDecoding

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classes.PolynomialTime Complexity.Classes.Certificates
open Complexity.CookLevin.Encoding Complexity.CookLevin.CNF Complexity.CookLevin.Satisfiability

def checkFormula (xs ys : Word) : Bool :=
  (scanFormula xs).valid && (scanFormula xs).rest.head?.isNone &&
    eval (scanFormula xs).value (assignment ys)

def decideVerifier (w : Word) : Bool :=
  let s := splitInput w
  s.valid && checkFormula s.formula s.certificate

lemma checkFormula_sound (xs ys : Word) (h : checkFormula xs ys = true) :
    ∃ F, encodeCNF F = xs ∧ eval F (assignment ys) = true := by
  have hv : ((scanFormula xs).valid = true ∧ (scanFormula xs).rest.head?.isNone = true) ∧
      eval (scanFormula xs).value (assignment ys) = true := by
    simpa only [checkFormula, Bool.and_eq_true] using h
  have he : (scanFormula xs).rest = [] := by
    cases hr : (scanFormula xs).rest <;> simp_all
  refine ⟨(scanFormula xs).value, ?_, hv.2⟩
  simpa [he] using (scanFormula_sound xs hv.1.1).symm

lemma checkFormula_encoded (F : Formula) (ys : Word) :
    checkFormula (encodeCNF F) ys = eval F (assignment ys) := by
  have h := scanFormula_encoded F []
  simp only [List.append_nil] at h
  simp [checkFormula, h]

lemma decideVerifier_correct (w : Word) : decideVerifier w = true ↔ w ∈ Verifier := by
  constructor
  · intro h
    have hv : (splitInput w).valid = true ∧
        checkFormula (splitInput w).formula (splitInput w).certificate = true := by
      simpa only [decideVerifier, Bool.and_eq_true] using h
    obtain ⟨F, hF, he⟩ := checkFormula_sound _ _ hv.2
    refine ⟨F, (splitInput w).certificate, ?_, he⟩
    rw [hF]
    exact splitInput_sound w hv.1
  · rintro ⟨F, ys, rfl, he⟩
    simpa [decideVerifier, splitInput_pair, checkFormula_encoded] using he

end Complexity.CookLevinProofs.VerifierProgram
