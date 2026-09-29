/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/SearchMachine.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.SearchMachine` to `Complexity.ClassesProofs.SavitchDefinitions.SearchMachine`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.ConfigurationGraph
import Complexity.ClassesProofs.SavitchDefinitions.SpaceConstructibility

set_option backward.isDefEq.respectTransparency false

/-!
The deterministic machine constructs the space bound, encodes configurations,
and evaluates recursive reachability using parallel stacks. Its work space
is quadratic in the original machine's space bound.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.SearchMachine

open Complexity.Classes.PolynomialTime Complexity.Classes.SpaceMachines Complexity.Classes.SpaceBounds
open ConfigurationGraph SpaceConstructibility


end Complexity.ClassesProofs.SavitchDefinitions.SearchMachine
