/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/BasicProperties.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.BasicProperties` to `Complexity.Classical.BasicProperties`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.LogarithmicSpace
import Complexity.Classical.NondeterministicLogarithmicSpace
import Complexity.Classical.PolynomialSpace
import Complexity.Classical.NondeterministicPolynomialSpace
import Complexity.Classical.ComplementClasses
import Complexity.Classical.ExponentialTime
import Complexity.Classical.PolynomialSpaceEquality

/-!
---
title: The inclusion chain of complexity classes
type: theorem
---
The classical classes satisfy
$\mathrm{L}\subseteq\mathrm{NL}\subseteq\mathrm{P}\subseteq\mathrm{NP}
\subseteq\mathrm{PSPACE}=\mathrm{NPSPACE}\subseteq\mathrm{EXPTIME}$.
-/

namespace Complexity.Classical.BasicProperties

open PolynomialTime LogarithmicSpace NondeterministicLogarithmicSpace
open NondeterministicPolynomialTime PolynomialSpace NondeterministicPolynomialSpace
open ExponentialTime

/- The archived concept stated `L_subset_NL` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassicalProofs.BasicProperties.L_subset_NL` in `Complexity.ClassicalProofs.BasicProperties`, which
re-exports it under the name `Complexity.Classical.BasicProperties.L_subset_NL` via `alias`. -/

/- The archived concept stated `NL_subset_P` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassicalProofs.NL_subset_P` in `Complexity.ClassicalProofs.NLPolynomialTime`, which
re-exports it under the name `Complexity.Classical.BasicProperties.NL_subset_P` via `alias`. -/

/- The archived concept stated `P_subset_NP` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassicalProofs.P_subset_NP` in `Complexity.ClassicalProofs.PSubsetNP`, which
re-exports it under the name `Complexity.Classical.BasicProperties.P_subset_NP` via `alias`. -/

/- The archived concept stated `NP_subset_PSPACE` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassicalProofs.NP_subset_PSPACE` in `Complexity.ClassicalProofs.NPPolynomialSpace`, which
re-exports it under the name `Complexity.Classical.BasicProperties.NP_subset_PSPACE` via `alias`. -/

/- The archived concept stated `NPSPACE_subset_EXPTIME` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassicalProofs.NPSPACE_subset_EXPTIME` in `Complexity.ClassicalProofs.NPSpaceExponentialTime`, which
re-exports it under the name `Complexity.Classical.BasicProperties.NPSPACE_subset_EXPTIME` via `alias`. -/

end Complexity.Classical.BasicProperties
