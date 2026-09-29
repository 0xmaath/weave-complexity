/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/ClauseParsing.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.ClauseParsing` to `Complexity.CookLevinProofs.ClauseParsing`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.ListParsing

namespace Complexity.CookLevinProofs.VerifierProgram

open Complexity.Classical.PolynomialTime Complexity.CookLevin.Encoding Complexity.CookLevin.CNF Complexity.CookLevin.Satisfiability

def scanClause : Word → Parsed Clause := scanMany scanLiteral scanLiteral_length

lemma scanClause_length (xs : Word) : (scanClause xs).rest.length ≤ xs.length :=
  scanMany_length _ _ xs

lemma scanClause_sound (xs : Word) (hv : (scanClause xs).valid = true) :
    xs = encodeClause (scanClause xs).value ++ (scanClause xs).rest :=
  scanMany_sound _ _ _ scanLiteral_sound xs hv

lemma scanClause_encoded (C : Clause) (xs : Word) :
    scanClause (encodeClause C ++ xs) = ⟨C, xs, true⟩ :=
  scanMany_encoded _ _ _ scanLiteral_encoded C xs

lemma scanClause_invalid_rest (xs : Word) (hv : (scanClause xs).valid = false) :
    (scanClause xs).rest = [] :=
  scanMany_invalid_rest _ _ scanLiteral_invalid_rest xs hv

def clauseValue (C : Clause) (ys : Word) : Bool := C.any (fun l => l.eval (assignment ys))

def clauseFlags (xs ys : Word) (flags : Flags) : Flags :=
  {flags with
    valid := (scanClause xs).valid
    clause := flags.clause || clauseValue (scanClause xs).value ys}

lemma clauseFlags_cons (xs ys : Word) (flags : Flags) :
    clauseFlags (scanLiteral xs).rest ys (literalFlags xs ys flags) =
      clauseFlags (true :: xs) ys flags := by
  cases hv : (scanLiteral xs).valid with
  | true => simp [clauseFlags, literalFlags, scanClause, scanMany, clauseValue, hv, Bool.or_assoc]
  | false => simp [clauseFlags, literalFlags, scanClause, scanMany, clauseValue,
      scanLiteral_invalid_rest xs hv, hv, Bool.or_assoc]

end Complexity.CookLevinProofs.VerifierProgram
