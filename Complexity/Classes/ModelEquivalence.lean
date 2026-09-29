/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/ModelEquivalence.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.ModelEquivalence` to `Complexity.Classes.ModelEquivalence`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.MachineModels

/-!
---
title: Single-tape characterization of P
type: lemma
---
The elementary single-tape and stack-machine definitions of $\mathrm{P}$
coincide. Both simulations include polynomial bounds for input conversion,
execution, and final output conversion.
-/

namespace Complexity.Classes.ModelEquivalence

open PolynomialTime MachineModels

/- The archived concept stated `singleTapeP_eq_P` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.ModelEquivalence.singleTapeP_eq_P` in `Complexity.ClassesProofs.ModelEquivalence`, which
re-exports it under the name `Complexity.Classes.ModelEquivalence.singleTapeP_eq_P` via `alias`. -/

end Complexity.Classes.ModelEquivalence
