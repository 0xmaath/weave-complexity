/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/FiniteWitness.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.FiniteWitness` to `Complexity.CookLevin.FiniteWitness`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability

/-!
---
title: A bounded satisfying assignment
type: lemma
---
A satisfiable formula has a certificate whose length is at most the length
of its binary encoding. Only variables occurring in the formula matter.
-/

namespace Complexity.CookLevin.FiniteWitness

open CNF Encoding Satisfiability Complexity.Classes.PolynomialTime

/- The archived concept stated `bounded` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.finite_witness` in `Complexity.CookLevinProofs.Certificates`, which
re-exports it under the name `Complexity.CookLevin.FiniteWitness.bounded` via `alias`. -/

end Complexity.CookLevin.FiniteWitness
