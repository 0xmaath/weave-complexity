/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/NLPolynomialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.NLPolynomialTime` to `Complexity.ClassicalProofs.NLPolynomialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.BasicProperties
import Complexity.ClassicalProofs.InclusionAux.ConfigurationSearch
import Batteries.Tactic.Alias

namespace Complexity.ClassicalProofs

open Complexity.Classical.NondeterministicLogarithmicSpace Complexity.Classical.PolynomialTime

/--
---
conclusion: Complexity.Classical.BasicProperties.NL_subset_P
---
A finite deterministic stack machine computes reachability in a polynomial-size
encoding of the original logarithmic-space machine's configurations.
The checked compiler gives polynomial running time and the original acceptance
definition gives the characteristic function.
-/
theorem NL_subset_P : NL ⊆ P := InclusionAux.NL_subset_P

alias _root_.Complexity.Classical.BasicProperties.NL_subset_P := NL_subset_P

end Complexity.ClassicalProofs
