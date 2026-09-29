/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/FiniteStackEquivalence.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.FiniteStackEquivalence` to `Complexity.Classes.FiniteStackEquivalence`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.MachineModels

/-!
---
title: Finite stack alphabets suffice
type: lemma
---
Requiring every work-stack alphabet to be finite leaves $\mathrm{P}$ unchanged.
-/

namespace Complexity.Classes.FiniteStackEquivalence

open PolynomialTime MachineModels

/- The archived concept stated `finiteStackP_eq_P` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.ModelEquivalence.finiteStackP_eq_P` in `Complexity.ClassesProofs.ModelEquivalence`, which
re-exports it under the name `Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P` via `alias`. -/

end Complexity.Classes.FiniteStackEquivalence
