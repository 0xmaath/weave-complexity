/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/ShortPaths.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.ShortPaths` to `Complexity.ClassesProofs.SavitchDefinitions.ShortPaths`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.Reachability

set_option backward.isDefEq.respectTransparency false

/-!
If one vertex reaches another in a graph with $N$ vertices, a walk of
length less than $N$ suffices.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.ShortPaths

open Reachability


end Complexity.ClassesProofs.SavitchDefinitions.ShortPaths
