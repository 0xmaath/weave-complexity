/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/GateCorrect.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.GateCorrect` to `Complexity.CookLevin.GateCorrect`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Tseitin

/-!
---
title: Correctness of gate clauses
type: lemma
---
The clauses for one gate hold exactly when its output agrees with its
Boolean operation.
-/

namespace Complexity.CookLevin.GateCorrect

open CNF Circuits Tseitin

/- The archived concept stated `correct` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.gate_correct` in `Complexity.CookLevinProofs.Tseitin`, which
re-exports it under the name `Complexity.CookLevin.GateCorrect.correct` via `alias`. -/

end Complexity.CookLevin.GateCorrect
