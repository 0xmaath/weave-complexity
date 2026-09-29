/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/NPSpaceExponentialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.NPSpaceExponentialTime` to `Complexity.ClassicalProofs.NPSpaceExponentialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.BasicProperties
import Complexity.ClassicalProofs.SpaceExponentialTime
import Complexity.ClassicalProofs.PolynomialSpaceEquality

namespace Complexity.ClassicalProofs

open Complexity.Classical.PolynomialSpace Complexity.Classical.NondeterministicPolynomialSpace
open Complexity.Classical.ExponentialTime

/--
---
conclusion: Complexity.Classical.BasicProperties.NPSPACE_subset_EXPTIME
assumptions:
  - Complexity.Classical.PolynomialSpaceEquality.PSPACE_eq_NPSPACE
---
Apply the proved Savitch simulation, bound the deterministic machine's run
length by its configuration count, and use the time-bounded stack and tape simulations.
-/
theorem NPSPACE_subset_EXPTIME : NPSPACE ⊆ EXPTIME := by
  intro A h
  apply SpaceExponentialTime.PSPACE_subset_EXPTIME
  rw [Complexity.Classical.PolynomialSpaceEquality.PSPACE_eq_NPSPACE]
  exact h

alias _root_.Complexity.Classical.BasicProperties.NPSPACE_subset_EXPTIME := NPSPACE_subset_EXPTIME

end Complexity.ClassicalProofs
