/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/CookLevin.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.CookLevin` to `Complexity.CookLevin.CookLevin`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability
import Complexity.CookLevin.Reductions

/-!
---
title: The Cook–Levin theorem
type: theorem
---
Satisfiability of CNF formulas is NP-complete under polynomial many-one reductions.
-/

namespace Complexity.CookLevin.CookLevin

open Satisfiability Reductions

/- The archived concept stated `np_complete` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.cook_levin` in `Complexity.CookLevinProofs.CookLevin`, which
re-exports it under the name `Complexity.CookLevin.CookLevin.np_complete` via `alias`. -/

end Complexity.CookLevin.CookLevin
