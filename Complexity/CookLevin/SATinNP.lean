/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/SATinNP.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.SATinNP` to `Complexity.CookLevin.SATinNP`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability
import Complexity.Classical.NondeterministicPolynomialTime

/-!
---
title: SAT belongs to NP
type: lemma
---
A polynomial time verifier checks a satisfying assignment of polynomial length.
-/

namespace Complexity.CookLevin.SATinNP

open Satisfiability Complexity.Classical.NondeterministicPolynomialTime

/- The archived concept stated `membership` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.sat_in_np` in `Complexity.CookLevinProofs.Certificates`, which
re-exports it under the name `Complexity.CookLevin.SATinNP.membership` via `alias`. -/

end Complexity.CookLevin.SATinNP
