/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614` to `Complexity.ArcKayles`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.ArcKayles
import Complexity.ArcKayles.Grundy
import Complexity.ArcKayles.GrundyProperties
import Complexity.ArcKayles.Biclique
import Complexity.ArcKayles.PositiveCNF
import Complexity.ArcKayles.Encoding
import Complexity.ArcKayles.PSPACE
import Complexity.ArcKayles.PositiveCNFHardness
import Complexity.ArcKayles.Construction
import Complexity.ArcKayles.Reduction
import Complexity.ArcKayles.Completeness
import Complexity.ArcKayles.RegularPlay
import Complexity.ArcKayles.Passes
import Complexity.ArcKayles.Sizes
