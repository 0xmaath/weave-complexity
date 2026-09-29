/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/VerifierCorrect.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.VerifierCorrect` to `Complexity.CookLevin.VerifierCorrect`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Satisfiability

/-!
---
title: Correctness of the SAT verifier
type: lemma
---
Membership in SAT is equivalent to the existence of an accepted certificate
of length at most the input length.
-/

namespace Complexity.CookLevin.VerifierCorrect

open Satisfiability Complexity.Classes.PolynomialTime Complexity.Classes.Certificates

/- The archived concept stated `correct` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.verifier_correct` in `Complexity.CookLevinProofs.Certificates`, which
re-exports it under the name `Complexity.CookLevin.VerifierCorrect.correct` via `alias`. -/

end Complexity.CookLevin.VerifierCorrect
