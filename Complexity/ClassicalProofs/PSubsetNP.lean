/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/PSubsetNP.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.PSubsetNP` to `Complexity.ClassicalProofs.PSubsetNP`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.BasicProperties
import Complexity.ClassicalProofs.CertificateProjection

namespace Complexity.ClassicalProofs

open Complexity.Classical.PolynomialTime Complexity.Classical.NondeterministicPolynomialTime
open Complexity.Classical.Certificates CertificateProjection

/--
---
conclusion: Complexity.Classical.BasicProperties.P_subset_NP
assumptions:
---
Extract the input from the existing pair encoding in linear time, then run the
polynomial-time decider. The empty certificate suffices for every input.
-/
theorem P_subset_NP : P ⊆ NP := by
  rintro A ⟨f, hf, ⟨M⟩⟩
  obtain ⟨N⟩ := PolynomialComposition.comp computable M
  let V : Language := {w | f (first w) = true}
  refine ⟨V, ⟨f ∘ first, fun _ => Iff.rfl, ⟨N⟩⟩, 0, ?_⟩
  intro x
  constructor
  · intro hx
    refine ⟨[], by simp, ?_⟩
    change f (first (pair x [])) = true
    rw [first_pair]
    exact (hf x).mpr hx
  · rintro ⟨y, _, hy⟩
    change f (first (pair x y)) = true at hy
    rw [first_pair] at hy
    exact (hf x).mp hy

alias _root_.Complexity.Classical.BasicProperties.P_subset_NP := P_subset_NP

end Complexity.ClassicalProofs
