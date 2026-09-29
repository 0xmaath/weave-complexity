/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/PolynomialSpaceEquality.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.PolynomialSpaceEquality` to `Complexity.ClassesProofs.PolynomialSpaceEquality`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.PolynomialSpaceEquality
import Complexity.ClassesProofs.SavitchProofs.Savitch
import Batteries.Tactic.Alias

namespace Complexity.ClassesProofs

open Complexity.Classes.PolynomialSpace Complexity.Classes.NondeterministicPolynomialSpace

/--
---
conclusion: Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE
assumptions:
---
Deterministic machines are special cases of nondeterministic machines.
Conversely, apply the proved Savitch simulation to the constructible bound
$p(n)+n+2$. Its squared space bound is still polynomial.
-/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE :=
  SavitchProofs.polynomial_space

alias _root_.Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE := PSPACE_eq_NPSPACE

end Complexity.ClassesProofs
