/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/ConfigCount.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.ConfigCount` to `Complexity.ClassesProofs.SavitchDefinitions.ConfigCount`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.BoundedConfigurations

set_option backward.isDefEq.respectTransparency false

/-!
For input length $n$ and work bound $s$, a machine with state set $Q$
and work alphabet $\Gamma$ has $|Q|(n+2)s|\Gamma|^s$ bounded configurations.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.ConfigCount

open Complexity.Classes.SpaceMachines BoundedConfigurations


end Complexity.ClassesProofs.SavitchDefinitions.ConfigCount
