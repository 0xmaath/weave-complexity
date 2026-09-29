/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/UnaryParsing.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.UnaryParsing` to `Complexity.CookLevinProofs.UnaryParsing`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.PairExecution

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classical.PolynomialTime Complexity.CookLevin.Encoding

structure UnaryResult where
  index : ℕ
  rest : Word
  valid : Bool
  deriving DecidableEq

def unary : Word → UnaryResult
  | [] => ⟨0, [], false⟩
  | false :: xs => ⟨0, xs, true⟩
  | true :: xs => let r := unary xs; ⟨r.index + 1, r.rest, r.valid⟩

lemma unary_length (xs : Word) :
    (unary xs).index + (unary xs).rest.length ≤ xs.length := by
  induction xs with
  | nil => simp [unary]
  | cons b xs ih => cases b <;> simp_all [unary] <;> omega

lemma unary_sound (xs : Word) (h : (unary xs).valid = true) :
    xs = encodeNat (unary xs).index ++ (unary xs).rest := by
  induction xs with
  | nil => simp [unary] at h
  | cons b xs ih =>
    cases b with
    | false => simp [unary, encodeNat]
    | true =>
      have hr := congrArg (List.cons true) (ih h)
      simpa [unary, encodeNat, List.replicate_succ] using hr

lemma unary_encoded (n : ℕ) (xs : Word) :
    unary (encodeNat n ++ xs) = ⟨n, xs, true⟩ := by
  induction n with
  | zero => simp [encodeNat, unary]
  | succ n ih =>
    change (let r := unary (encodeNat n ++ xs); UnaryResult.mk (r.index + 1) r.rest r.valid) = _
    rw [ih]

end Complexity.CookLevinProofs.VerifierProgram
