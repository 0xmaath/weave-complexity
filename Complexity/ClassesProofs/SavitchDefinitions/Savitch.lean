/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/Savitch.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.Savitch` to `Complexity.ClassesProofs.SavitchDefinitions.Savitch`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.SpaceConstructibility

set_option backward.isDefEq.respectTransparency false

/-!
If $s$ is fully space-constructible and at least logarithmic, every
nondeterministic $s(n)$-space decider has a deterministic decider using
$O(s(n)^2)$ space.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.Savitch

open Complexity.Classes.PolynomialTime Complexity.Classes.SpaceBounds SpaceConstructibility


end Complexity.ClassesProofs.SavitchDefinitions.Savitch
