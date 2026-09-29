/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/PolynomialSpaceEquality.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.PolynomialSpaceEquality` to `Complexity.Classes.PolynomialSpaceEquality`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.PolynomialSpace
import Complexity.Classes.NondeterministicPolynomialSpace

/-!
---
title: Savitch's theorem
type: theorem
---
The polynomial-space form of Savitch's theorem is
$\mathrm{PSPACE}=\mathrm{NPSPACE}$.
-/

namespace Complexity.Classes.PolynomialSpaceEquality

open PolynomialSpace NondeterministicPolynomialSpace

/- The archived concept stated `PSPACE_eq_NPSPACE` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.PSPACE_eq_NPSPACE` in `Complexity.ClassesProofs.PolynomialSpaceEquality`, which
re-exports it under the name `Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE` via `alias`. -/

end Complexity.Classes.PolynomialSpaceEquality
