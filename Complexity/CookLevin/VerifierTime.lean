/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/VerifierTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.VerifierTime` to `Complexity.CookLevin.VerifierTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability

/-!
---
title: Polynomial time for CNF verification
type: lemma
---
A finite stack machine decodes the paired input and checks the supplied
assignment. Its running time is polynomial in the input length, including
on malformed encodings, using the machine model of
[lax-434930](https://laxarchive.org/lax-434930/).
-/

namespace Complexity.CookLevin.VerifierTime

open Satisfiability Complexity.Classes.PolynomialTime

/- The archived concept stated `polynomial` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.verifier_polynomial` in `Complexity.CookLevinProofs.VerifierTime`, which
re-exports it under the name `Complexity.CookLevin.VerifierTime.polynomial` via `alias`. -/

end Complexity.CookLevin.VerifierTime
