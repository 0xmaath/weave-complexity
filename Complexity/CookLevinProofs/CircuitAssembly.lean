/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/CircuitAssembly.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.CircuitAssembly` to `Complexity.CookLevinProofs.CircuitAssembly`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevinProofs.CircuitAcceptance

namespace Complexity.CookLevinProofs.CircuitBuilder

open Complexity.CookLevin.Circuits Complexity.CookLevin.CNF

lemma ordered_inputs (start count : ℕ) : Ordered start (List.replicate count Gate.input) := by
  induction count generalizing start with
  | zero => simp [Ordered]
  | succ count ih =>
    exact ordered_append start [Gate.input] _
      (ordered_singleton start _ (by simp [Gate.inputs])) (ih (start + 1))

lemma satisfies_inputs (start count : ℕ) (ρ : Assignment) :
    Satisfies start (List.replicate count Gate.input) ρ := by
  induction count generalizing start with
  | zero => simp [Satisfies]
  | succ count ih =>
    apply (satisfies_append start [Gate.input] _ ρ).mpr
    exact ⟨(satisfies_singleton start _ ρ).mpr rfl, ih (start + 1)⟩

lemma satisfies_iff_all (start : ℕ) (gates : List Gate) (ρ : Assignment) :
    Satisfies start gates ρ ↔ (gates.zipIdx start).all (fun p => p.1.check ρ p.2) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h p hp
    exact h p.1 p.2 hp
  · intro h g i hg
    exact h (g, i) hg

def assemble (inputs : ℕ) (gates : List Gate) (out : ℕ)
    (horder : Ordered inputs gates) (hout : out < inputs + gates.length) : Circuit where
  gates := List.replicate inputs Gate.input ++ gates
  output := ⟨out, by simpa using hout⟩
  ordered := by
    simpa using! ordered_append 0 (List.replicate inputs Gate.input) gates
      (ordered_inputs 0 inputs) (by simpa using horder)

lemma assemble_check (inputs : ℕ) (gates : List Gate) (out : ℕ)
    (horder : Ordered inputs gates) (hout : out < inputs + gates.length) (ρ : Assignment) :
    check (assemble inputs gates out horder hout) ρ = true ↔
      ρ out = true ∧ Satisfies inputs gates ρ := by
  change (ρ out && ((List.replicate inputs Gate.input ++ gates).zipIdx).all
    (fun p => p.1.check ρ p.2)) = true ↔ _
  rw [Bool.and_eq_true, ← satisfies_iff_all, satisfies_append]
  simp [satisfies_inputs]

end Complexity.CookLevinProofs.CircuitBuilder
