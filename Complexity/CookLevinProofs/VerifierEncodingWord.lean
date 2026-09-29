/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/VerifierEncodingWord.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.VerifierEncodingWord` to `Complexity.CookLevinProofs.VerifierEncodingWord`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.VerifierOutputLayout

namespace Complexity.CookLevinProofs.Streaming

open Complexity.Classical.PolynomialTime Complexity.Classical.MachineModels
open Complexity.CookLevin.CNF Complexity.CookLevin.Circuits Complexity.CookLevin.Encoding Complexity.CookLevin.Tseitin
open CircuitBuilder CertificateCircuit

lemma circuit_encoding_word (C : Circuit) :
    encodeCNF (Complexity.CookLevin.Tseitin.encode C) =
      CNFOutput.segment [[positive C.output]] ++ gatesWord 0 C.gates ++ [false] := by
  rw [← CNFOutput.segment_encode]
  simp [Complexity.CookLevin.Tseitin.encode, CNFOutput.segment, gatesWord, List.flatMap_assoc]

lemma gatesWord_inputs (start count : ℕ) : gatesWord start (List.replicate count Gate.input) = [] := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    change gatesWord start ([Gate.input] ++ List.replicate count Gate.input) = []
    rw [gatesWord_append, gatesWord_singleton]
    simpa [gateClauses, CNFOutput.segment] using ih (start + 1)

lemma verifier_encoding_word (M : SingleTape) (x : Word) (bound radius : ℕ) :
    encodeCNF (Complexity.CookLevin.Tseitin.encode (VerifierCircuit.circuit M x bound radius)) =
      CNFOutput.segment [[positive (VerifierCircuit.conclusion M x bound radius).output]] ++
      (gatesWord (inputCount bound) (VerifierCircuit.preparation M x bound radius).gates ++
      (gatesWord (VerifierCircuit.simulationStart M x bound radius) (VerifierCircuit.simulation M x bound radius).gates ++
      (gatesWord (VerifierCircuit.conclusionStart M x bound radius) (VerifierCircuit.conclusion M x bound radius).gates ++
      [false]))) := by
  rw [circuit_encoding_word]
  simp only [VerifierCircuit.circuit, assemble, gatesWord_append, gatesWord_inputs,
    List.length_replicate, Nat.zero_add, List.nil_append, VerifierCircuit.body,
    gatesWord_append, List.append_assoc, VerifierCircuit.simulationStart, VerifierCircuit.conclusionStart]

end Complexity.CookLevinProofs.Streaming
