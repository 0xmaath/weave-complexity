/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/PositiveCNFHardness.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.PositiveCNFHardness` to `Complexity.ArcKayles.PositiveCNFHardness`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Encoding
import Complexity.ArcKayles.PSPACE

/-!
---
title: PSPACE-hardness of the positive CNF game
type: theorem
---
Schaefer's theorem: determining whether True wins the positive CNF game
is PSPACE-hard under polynomial-time many-one reductions.

# References
Thomas J. Schaefer, *On the complexity of some two-person
perfect-information games*, JCSS 16(2), 185–225 (1978).
-/

namespace Complexity.ArcKayles.PositiveCNFHardness

/- The archived concept stated `hard` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.positiveCNF_hard` in `Complexity.ArcKaylesProofs.PositiveCNFHardness`, which
re-exports it under the name `Complexity.ArcKayles.PositiveCNFHardness.hard` via `alias`. -/

end Complexity.ArcKayles.PositiveCNFHardness
