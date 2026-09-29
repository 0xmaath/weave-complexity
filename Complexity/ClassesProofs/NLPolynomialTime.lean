/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/NLPolynomialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.NLPolynomialTime` to `Complexity.ClassesProofs.NLPolynomialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.BasicProperties
import Complexity.ClassesProofs.InclusionAux.ConfigurationSearch
import Batteries.Tactic.Alias

namespace Complexity.ClassesProofs

open Complexity.Classes.NondeterministicLogarithmicSpace Complexity.Classes.PolynomialTime

/--
---
conclusion: Complexity.Classes.BasicProperties.NL_subset_P
---
A finite deterministic stack machine computes reachability in a polynomial-size
encoding of the original logarithmic-space machine's configurations.
The checked compiler gives polynomial running time and the original acceptance
definition gives the characteristic function.
-/
theorem NL_subset_P : NL ⊆ P := InclusionAux.NL_subset_P

alias _root_.Complexity.Classes.BasicProperties.NL_subset_P := NL_subset_P

end Complexity.ClassesProofs
