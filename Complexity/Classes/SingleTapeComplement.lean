/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/SingleTapeComplement.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.SingleTapeComplement` to `Complexity.Classes.SingleTapeComplement`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.MachineModels

/-!
---
title: Single-tape P is closed under complement
type: lemma
---
The elementary single-tape class $\mathrm{P}$ is closed under complement.
-/

namespace Complexity.Classes.SingleTapeComplement

open PolynomialTime MachineModels

/- The archived concept stated `closed_under_complement` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.ModelEquivalence.singleTape_closed_under_complement` in `Complexity.ClassesProofs.ModelEquivalence`, which
re-exports it under the name `Complexity.Classes.SingleTapeComplement.closed_under_complement` via `alias`. -/

end Complexity.Classes.SingleTapeComplement
