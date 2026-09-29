/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/Recursion.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.Recursion` to `Complexity.ClassesProofs.SavitchDefinitions.Recursion`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.SplitWalk

set_option backward.isDefEq.respectTransparency false

/-!
At recursion depth $k$, the search accepts exactly the vertex pairs
joined by a walk of length at most $2^k$.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.Recursion

open Reachability


end Complexity.ClassesProofs.SavitchDefinitions.Recursion
