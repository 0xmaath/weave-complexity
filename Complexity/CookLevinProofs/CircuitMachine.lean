/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/CircuitMachine.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.CircuitMachine` to `Complexity.CookLevinProofs.CircuitMachine`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.VerifierOutputCode
import Complexity.CookLevinProofs.OutputMachine
import Complexity.CookLevinProofs.OutputPolynomials
import Complexity.CookLevinProofs.VerifierCompilation
import Complexity.CookLevin.CircuitMachine
import Batteries.Tactic.Alias

set_option backward.isDefEq.respectTransparency false

namespace Complexity.CookLevinProofs.Streaming

open Complexity.Classes.PolynomialTime Complexity.Classes.Certificates Complexity.Classes.MachineModels
open Complexity.CookLevin.Encoding Turing

lemma verifier_polynomial_time (M : SingleTape) (p R : Polynomial ℕ) :
    Nonempty (TM2ComputableInPolyTime id id (fun x =>
      encodeCNF (Complexity.CookLevin.Tseitin.encode
        (VerifierCircuit.circuit M x (p.eval x.length) (R.eval x.length))))) := by
  let c := verifierCode M () (Number.polynomial p (.length ())) (Number.polynomial R (.length ()))
  have he : (fun x => c.eval (fun _ => x)) = (fun x =>
      encodeCNF (Complexity.CookLevin.Tseitin.encode
        (VerifierCircuit.circuit M x (p.eval x.length) (R.eval x.length)))) := by
    funext x
    simpa only [Number.polynomial_value, Number.length] using!
      verifierCode_correct M () (Number.polynomial p (.length ()))
        (Number.polynomial R (.length ())) (fun _ => x)
  have h := c.polynomial_time
  rw [he] at h
  exact h

/--
---
conclusion: Complexity.CookLevin.CircuitMachine.compile
assumptions:
  - Complexity.Classes.Certificates.pair_length
  - Complexity.Classes.ModelEquivalence.singleTapeP_eq_P
---
Unroll the bounded verifier and emit its gate clauses with polynomially bounded loops.
-/
lemma circuit_machine (V : Language) (hV : V ∈ P) (p : Polynomial ℕ) :
    ∃ circuits : Word → Complexity.CookLevin.Circuits.Circuit,
      Nonempty (TM2ComputableInPolyTime id id
        (fun x => encodeCNF (Complexity.CookLevin.Tseitin.encode (circuits x)))) ∧
      ∀ x, Complexity.CookLevin.Circuits.Satisfiable (circuits x) ↔
        ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V := by
  obtain ⟨M, R, hM⟩ := VerifierCircuit.verifier_circuits V hV p
  exact ⟨fun x => VerifierCircuit.circuit M x (p.eval x.length) (R.eval x.length),
    verifier_polynomial_time M p R, fun x => (hM x).1⟩

alias _root_.Complexity.CookLevin.CircuitMachine.compile := circuit_machine

end Complexity.CookLevinProofs.Streaming
