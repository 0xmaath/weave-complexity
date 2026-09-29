/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/SATEncoding.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.SATEncoding` to `Complexity.CookLevin.SATEncoding`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability

/-!
---
title: Satisfiability and binary encodings
type: lemma
---
An encoded formula belongs to the SAT language exactly when the formula is satisfiable.
-/

namespace Complexity.CookLevin.SATEncoding

open CNF Encoding Satisfiability

/- The archived concept stated `correct` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.sat_encoding` in `Complexity.CookLevinProofs.Certificates`, which
re-exports it under the name `Complexity.CookLevin.SATEncoding.correct` via `alias`. -/

end Complexity.CookLevin.SATEncoding
