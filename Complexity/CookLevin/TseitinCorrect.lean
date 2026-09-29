/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/TseitinCorrect.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.TseitinCorrect` to `Complexity.CookLevin.TseitinCorrect`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Tseitin

/-!
---
title: Correctness of the circuit encoding
type: lemma
---
The gate clauses and output clause are satisfiable exactly when the circuit is satisfiable.
-/

namespace Complexity.CookLevin.TseitinCorrect

open Circuits

/- The archived concept stated `correct` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.tseitin_correct` in `Complexity.CookLevinProofs.Tseitin`, which
re-exports it under the name `Complexity.CookLevin.TseitinCorrect.correct` via `alias`. -/

end Complexity.CookLevin.TseitinCorrect
