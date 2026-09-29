/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/ReductionComposition.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.ReductionComposition` to `Complexity.ArcKaylesProofs.ReductionComposition`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.PolynomialComposition
import Complexity.ArcKayles.PSPACE

namespace Complexity.ArcKaylesProofs

open Complexity.Classical.PolynomialTime Complexity.Classical.PolynomialSpace Complexity.CookLevin.Reductions

theorem manyOne_trans {A B C : Language} (hab : ManyOne A B) (hbc : ManyOne B C) :
    ManyOne A C := by
  obtain ⟨f, ⟨hf⟩, hfc⟩ := hab
  obtain ⟨g, ⟨hg⟩, hgc⟩ := hbc
  refine ⟨g ∘ f, Complexity.ClassicalProofs.PolynomialComposition.comp hf hg, ?_⟩
  intro w
  exact (hfc w).trans (hgc (f w))

theorem pspace_hard_of_reduction {A B : Language} (hA : Complexity.ArcKayles.PSPACE.Hard A)
    (hAB : ManyOne A B) : Complexity.ArcKayles.PSPACE.Hard B := by
  intro C hC
  exact manyOne_trans (hA C hC) hAB

theorem pspace_complete_of_reduction {A B : Language} (hA : Complexity.ArcKayles.PSPACE.Hard A)
    (hAB : ManyOne A B) (hB : B ∈ PSPACE) : Complexity.ArcKayles.PSPACE.Complete B :=
  ⟨hB, pspace_hard_of_reduction hA hAB⟩

end Complexity.ArcKaylesProofs
