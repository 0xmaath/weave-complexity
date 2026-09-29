/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/Runs.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.Runs` to `Complexity.ClassicalProofs.SavitchDefinitions.Runs`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchDefinitions.ConfigurationGraph

set_option backward.isDefEq.respectTransparency false

/-!
For a machine whose runs stay within the space bound, bounded configuration
reachability agrees with machine acceptance.
-/

namespace Complexity.ClassicalProofs.SavitchDefinitions.Runs

open Complexity.Classical.PolynomialTime Complexity.Classical.SpaceMachines ConfigurationGraph


end Complexity.ClassicalProofs.SavitchDefinitions.Runs
