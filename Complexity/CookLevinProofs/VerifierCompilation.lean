/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/VerifierCompilation.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.VerifierCompilation` to `Complexity.CookLevinProofs.VerifierCompilation`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.VerifierCircuitCorrectness
import Complexity.CookLevinProofs.CircuitSizeBounds

namespace Complexity.CookLevinProofs.VerifierCircuit

open Complexity.Classes.PolynomialTime Complexity.Classes.Certificates Complexity.CookLevin
open Complexity.Classes.MachineModels

lemma verifier_circuits (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
    ∃ (M : SingleTape) (R : Polynomial ℕ), ∀ x : Word,
      (Circuits.Satisfiable (circuit M x (p.eval x.length) (R.eval x.length)) ↔
        ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V) ∧
      (circuit M x (p.eval x.length) (R.eval x.length)).gates.length ≤
        (sizePolynomial M p R).eval x.length := by
  obtain ⟨M, R, hM⟩ := WindowMachine.bounded_verifier V hV p
  refine ⟨M, R, ?_⟩
  intro x
  refine ⟨?_, circuit_polynomial_size M p R x⟩
  rw [circuit_correct]
  constructor
  · rintro ⟨y, hy, ha⟩
    exact ⟨y, hy, ((hM x y hy).2).mp ha⟩
  · rintro ⟨y, hy, ha⟩
    exact ⟨y, hy, ((hM x y hy).2).mpr ha⟩

end Complexity.CookLevinProofs.VerifierCircuit
