/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/PairDecoding.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.PairDecoding` to `Complexity.CookLevinProofs.PairDecoding`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.VerifierProgram
import Complexity.Classical.Certificates

set_option backward.isDefEq.respectTransparency false

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classical.PolynomialTime Complexity.Classical.Certificates

structure SplitInput where
  formula : Word
  certificate : Word
  valid : Bool
  deriving DecidableEq

def splitInput : Word → SplitInput
  | [] => ⟨[], [], false⟩
  | true :: y => ⟨[], y, true⟩
  | [false] => ⟨[], [], false⟩
  | false :: b :: rest =>
      let r := splitInput rest
      ⟨b :: r.formula, r.certificate, r.valid⟩

lemma splitInput_pair (x y : Word) : splitInput (pair x y) = ⟨x, y, true⟩ := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [pair, splitInput, ih]

lemma splitInput_unpair (w : Word) :
    unpair w = if (splitInput w).valid then some ((splitInput w).formula, (splitInput w).certificate) else none := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton b => cases b <;> rfl
  | cons_cons b c w ih _ =>
    cases b with
    | true => rfl
    | false =>
      simp only [unpair, splitInput, ih]
      cases (splitInput w).valid <;> rfl

lemma splitInput_sound (w : Word) (h : (splitInput w).valid = true) :
    w = pair (splitInput w).formula (splitInput w).certificate := by
  induction w using List.twoStepInduction with
  | nil => simp [splitInput] at h
  | singleton b => cases b <;> simp [splitInput, pair] at *
  | cons_cons b c w ih _ =>
    cases b with
    | true => rfl
    | false =>
      change false :: c :: w = false :: c :: pair (splitInput w).formula (splitInput w).certificate
      exact congrArg (fun xs => false :: c :: xs) (ih h)

lemma splitInput_length (w : Word) :
    (splitInput w).formula.length + (splitInput w).certificate.length ≤ w.length := by
  induction w using List.twoStepInduction with
  | nil => decide
  | singleton b => cases b <;> decide
  | cons_cons b c w ih _ => cases b <;> simp [splitInput] at * <;> omega

def decodeCost : Word → ℕ
  | [] => 4
  | true :: _ => 5
  | [false] => 7
  | false :: _ :: rest => 7 + decodeCost rest

lemma decodeCost_bound (w : Word) : decodeCost w ≤ 7 * w.length + 5 := by
  induction w using List.twoStepInduction with
  | nil => decide
  | singleton b => cases b <;> decide
  | cons_cons b c w ih _ => cases b <;> simp [decodeCost] at * <;> omega

end Complexity.CookLevinProofs.VerifierProgram
