/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/Acceptance.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.Acceptance` to `Complexity.ClassesProofs.SavitchDefinitions.Acceptance`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.ConfigurationGraph

set_option backward.isDefEq.respectTransparency false

/-!
On space-bounded computations, the recursive configuration search accepts
exactly when the original machine does.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.Acceptance

open Complexity.Classes.PolynomialTime Complexity.Classes.SpaceMachines ConfigurationGraph


end Complexity.ClassesProofs.SavitchDefinitions.Acceptance
