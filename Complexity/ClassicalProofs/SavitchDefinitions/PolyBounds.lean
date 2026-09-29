/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/PolyBounds.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.PolyBounds` to `Complexity.ClassicalProofs.SavitchDefinitions.PolyBounds`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchDefinitions.SpaceConstructibility

set_option backward.isDefEq.respectTransparency false

/-!
For every polynomial $p$ with natural coefficients, the positive bound
$p(n)+n+2$ is fully space-constructible.
Nested input counters append the polynomial terms to a unary output track.
A final scan halts at the required work position.
-/

namespace Complexity.ClassicalProofs.SavitchDefinitions.PolyBounds

open SpaceConstructibility


end Complexity.ClassicalProofs.SavitchDefinitions.PolyBounds
