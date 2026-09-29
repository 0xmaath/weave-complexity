/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/SplitWalk.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.SplitWalk` to `Complexity.ClassicalProofs.SavitchDefinitions.SplitWalk`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchDefinitions.Reachability

set_option backward.isDefEq.respectTransparency false

/-!
A walk of length at most $r+s$ can be split at a vertex into walks of
length at most $r$ and at most $s$.
-/

namespace Complexity.ClassicalProofs.SavitchDefinitions.SplitWalk

open Reachability


end Complexity.ClassicalProofs.SavitchDefinitions.SplitWalk
