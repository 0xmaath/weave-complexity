/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/CertificateRepresentation.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.CertificateRepresentation` to `Complexity.CookLevinProofs.CertificateRepresentation`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.CertificateAssignments

namespace Complexity.CookLevinProofs.CertificateCircuit

open Complexity.Classical.PolynomialTime Complexity.CookLevin.CNF Complexity.CookLevin.Satisfiability

def Represents (bound : ℕ) (ρ : Assignment) (y : Word) : Prop :=
  y.length ≤ bound ∧ (∀ i, live bound ρ i = true ↔ i < y.length) ∧
    (∀ i, i < y.length → y[i]? = some (ρ (dataPort i)))

lemma assignment_represents (bound : ℕ) (y : Word) (hy : y.length ≤ bound) :
    Represents bound (certificateAssignment bound y) y := by
  refine ⟨hy, ?_, ?_⟩
  · intro i
    rw [certificateAssignment_live bound y hy]
    simp
  · intro i hi
    rw [certificateAssignment_data bound y i (by omega)]
    simp [assignment, hi]

lemma represents_agrees (bound : ℕ) (ρ σ : Assignment) (y : Word) (h : Represents bound ρ y)
    (ha : ∀ i < inputCount bound, σ i = ρ i) : Represents bound σ y := by
  refine ⟨h.1, ?_, ?_⟩
  · intro i
    have he : live bound σ i = live bound ρ i := by
      by_cases hi : i < bound
      · simp only [live, hi, if_true]
        exact ha _ (by simp only [livePort, inputCount]; omega)
      · simp [live, hi]
    rw [he]
    exact h.2.1 i
  · intro i hi
    rw [ha _ (by have hb := h.1; simp only [dataPort, inputCount]; omega)]
    exact h.2.2 i hi

end Complexity.CookLevinProofs.CertificateCircuit
