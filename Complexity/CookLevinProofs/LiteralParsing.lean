/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/LiteralParsing.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.LiteralParsing` to `Complexity.CookLevinProofs.LiteralParsing`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.UnaryExecution
import Complexity.CookLevin.Satisfiability

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classical.PolynomialTime Complexity.CookLevin.Encoding Complexity.CookLevin.CNF Complexity.CookLevin.Satisfiability

structure Parsed (α : Type) where
  value : α
  rest : Word
  valid : Bool

def scanLiteral (xs : Word) : Parsed Literal :=
  let u := unary xs
  ⟨⟨u.index, u.rest.head?.getD false⟩, u.rest.tail, u.valid && u.rest.head?.isSome⟩

lemma scanLiteral_length (xs : Word) : (scanLiteral xs).rest.length ≤ xs.length := by
  have h := unary_length xs
  simp only [scanLiteral, List.length_tail]
  omega

lemma scanLiteral_sound (xs : Word) (h : (scanLiteral xs).valid = true) :
    xs = encodeLiteral (scanLiteral xs).value ++ (scanLiteral xs).rest := by
  have hv : (unary xs).valid = true ∧ (unary xs).rest.head?.isSome = true := by
    simpa only [scanLiteral, Bool.and_eq_true] using h
  have hu := unary_sound xs hv.1
  cases hr : (unary xs).rest with
  | nil => simp [hr] at hv
  | cons b rest =>
    simpa [scanLiteral, encodeLiteral, hr, List.append_assoc] using hu

lemma scanLiteral_encoded (l : Literal) (xs : Word) :
    scanLiteral (encodeLiteral l ++ xs) = ⟨l, xs, true⟩ := by
  have h : encodeLiteral l ++ xs = encodeNat l.index ++ (l.positive :: xs) := by
    simp [encodeLiteral, List.append_assoc]
  rw [h]
  simp [scanLiteral, unary_encoded]

def literalFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanLiteral xs).valid
    clause := flags.clause || (scanLiteral xs).value.eval (assignment ys)}

def literalCost (xs ys : Word) : ℕ :=
  7 * ys.length + 3 * (unary xs).index +
    2 * (ys.drop (unary xs).index).tail.length + 11

lemma literalCost_bound (xs ys : Word) : literalCost xs ys ≤ 12 * (xs.length + ys.length + 1) := by
  have hu := unary_length xs
  simp only [literalCost, List.length_tail, List.length_drop]
  omega

end Complexity.CookLevinProofs.VerifierProgram
