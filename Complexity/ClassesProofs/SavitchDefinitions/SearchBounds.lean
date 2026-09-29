/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/SearchBounds.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.SearchBounds` to `Complexity.ClassesProofs.SavitchDefinitions.SearchBounds`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.ConfigurationGraph
import Complexity.Classes.SpaceBounds

set_option backward.isDefEq.respectTransparency false

/-!
The number of recursion frames is logarithmic in the configuration count.
Multiplying this depth by the space for configurations and counters gives
$O(s^2)$ when $s$ bounds the input logarithm.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.SearchBounds

open Complexity.Classes.SpaceMachines Complexity.Classes.SpaceBounds BoundedConfigurations

def stackSpace (M : Machine) (n s : ℕ) : ℕ :=
  (Nat.clog 2 (Fintype.card (Config M n s)) + 1) * (s + logSpace n + 1)


end Complexity.ClassesProofs.SavitchDefinitions.SearchBounds
