/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/FiniteSearch.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.FiniteSearch` to `Complexity.ClassesProofs.SavitchDefinitions.FiniteSearch`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.Recursion
import Complexity.ClassesProofs.SavitchDefinitions.ShortPaths
import Mathlib.Data.Nat.Log

set_option backward.isDefEq.respectTransparency false

/-!
Recursion depth $\lceil\log_2 N\rceil$ suffices to decide reachability
in a graph with $N$ vertices.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.FiniteSearch

open Reachability


end Complexity.ClassesProofs.SavitchDefinitions.FiniteSearch
