/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/Completeness.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.Completeness` to `Complexity.ArcKaylesProofs.Completeness`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.PositiveCNFHardness
import Complexity.ArcKaylesProofs.ReductionTime
import Complexity.ArcKaylesProofs.Membership
import Batteries.Tactic.Alias

namespace Complexity.ArcKaylesProofs

/--
---
conclusion: Complexity.ArcKayles.Completeness.pspace_complete
---
The compiled depth-first evaluator gives PSPACE membership. Compose
positive-CNF PSPACE-hardness with the checked polynomial-time graph
reduction to obtain PSPACE-hardness of Arc Kayles.
-/
theorem arcKayles_pspace_complete : Complexity.ArcKayles.PSPACE.Complete Complexity.ArcKayles.Encoding.arcKayles :=
  pspace_complete_of_reduction Complexity.ArcKayles.PositiveCNFHardness.hard
    Complexity.ArcKayles.Reduction.polynomial_reduction Complexity.ArcKayles.Completeness.membership

alias _root_.Complexity.ArcKayles.Completeness.pspace_complete := arcKayles_pspace_complete

end Complexity.ArcKaylesProofs
