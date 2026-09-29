/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/Certificates.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.Certificates` to `Complexity.CookLevinProofs.Certificates`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.Encoding
import Complexity.CookLevin.FiniteWitness
import Complexity.CookLevin.VerifierCorrect
import Complexity.CookLevin.VerifierTime
import Complexity.CookLevin.SATinNP
import Complexity.CookLevin.SATEncoding
import Batteries.Tactic.Alias
import Complexity.CookLevinProofs.VerifierTime
import Complexity.ClassesProofs.Certificates

namespace Complexity.CookLevinProofs

open Complexity.CookLevin Complexity.CookLevin.CNF Complexity.CookLevin.Encoding Complexity.CookLevin.Satisfiability
open Complexity.Classes.PolynomialTime Complexity.Classes.Certificates
open Complexity.Classes.NondeterministicPolynomialTime

/--
---
conclusion: Complexity.CookLevin.FiniteWitness.bounded
assumptions:
---
Restrict a satisfying assignment to the input-length prefix containing every variable.
-/
lemma finite_witness (F : Formula) :
    Satisfiable F ↔ ∃ y : Word, y.length ≤ (encodeCNF F).length ∧
      eval F (assignment y) = true := by
  constructor
  · rintro ⟨ρ, hρ⟩
    let y : Word := List.ofFn (fun i : Fin (encodeCNF F).length => ρ i)
    refine ⟨y, by simp [y], ?_⟩
    have hagree (C : Clause) (hC : C ∈ F) (l : Literal) (hl : l ∈ C) :
        l.eval (assignment y) = l.eval ρ := by
      have hi := literal_index_lt F C l hC hl
      have hv : assignment y l.index = ρ l.index := by
        simp [assignment, y, hi]
      simp only [Literal.eval, hv]
    simp only [eval, List.all_eq_true, List.any_eq_true] at hρ ⊢
    intro C hC
    obtain ⟨l, hl, he⟩ := hρ C hC
    exact ⟨l, hl, (hagree C hC l hl).trans he⟩
  · rintro ⟨y, _, hy⟩
    exact ⟨assignment y, hy⟩

alias _root_.Complexity.CookLevin.FiniteWitness.bounded := finite_witness

/--
---
conclusion: Complexity.CookLevin.VerifierCorrect.correct
assumptions:
  - Complexity.CookLevin.FiniteWitness.bounded
  - Complexity.Classes.Certificates.pair_injective
---
Use the bounded assignment and the injective encoding of input-certificate pairs.
-/
lemma verifier_correct (w : Word) :
    w ∈ SAT ↔ ∃ y : Word, y.length ≤ w.length ∧ pair w y ∈ Verifier := by
  constructor
  · rintro ⟨F, rfl, hF⟩
    obtain ⟨y, hy, he⟩ := (FiniteWitness.bounded F).mp hF
    exact ⟨y, hy, F, y, rfl, he⟩
  · rintro ⟨y, _, F, z, hz, he⟩
    have hp : (w, y) = (encodeCNF F, z) := pair_injective hz
    have hw := congrArg Prod.fst hp
    exact ⟨F, hw.symm, assignment z, he⟩

alias _root_.Complexity.CookLevin.VerifierCorrect.correct := verifier_correct

/--
---
conclusion: Complexity.CookLevin.SATEncoding.correct
assumptions:
  - Complexity.CookLevin.EncodingCorrect.roundtrip
---
The decoder's left-inverse property makes the binary encoding injective.
-/
lemma sat_encoding (F : Formula) : encodeCNF F ∈ SAT ↔ Satisfiable F := by
  constructor
  · rintro ⟨G, hG, hsat⟩
    have h := congrArg decodeCNF hG
    rw [EncodingCorrect.roundtrip, EncodingCorrect.roundtrip] at h
    cases Option.some.inj h
    exact hsat
  · intro h
    exact ⟨F, rfl, h⟩

alias _root_.Complexity.CookLevin.SATEncoding.correct := sat_encoding

/--
---
conclusion: Complexity.CookLevin.SATinNP.membership
assumptions:
  - Complexity.CookLevin.VerifierCorrect.correct
  - Complexity.CookLevin.VerifierTime.polynomial
---
Use the identity polynomial as the certificate-length bound.
-/
lemma sat_in_np : SAT ∈ NP := by
  refine ⟨Verifier, VerifierTime.polynomial, Polynomial.X, ?_⟩
  intro w
  simpa using VerifierCorrect.correct w

alias _root_.Complexity.CookLevin.SATinNP.membership := sat_in_np

end Complexity.CookLevinProofs
