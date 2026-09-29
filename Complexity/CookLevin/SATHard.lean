/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/SATHard.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.SATHard` to `Complexity.CookLevin.SATHard`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability
import Complexity.CookLevin.Reductions

/-!
---
title: NP-hardness of SAT
type: lemma
---
Every language in NP has a polynomial many-one reduction to the binary
language of satisfiable CNF formulas.
-/

namespace Complexity.CookLevin.SATHard

open Satisfiability Reductions Complexity.Classes.PolynomialTime Complexity.Classes.NondeterministicPolynomialTime

/- The archived concept stated `hardness` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.sat_hard` in `Complexity.CookLevinProofs.CookLevin`, which
re-exports it under the name `Complexity.CookLevin.SATHard.hardness` via `alias`. -/

end Complexity.CookLevin.SATHard
