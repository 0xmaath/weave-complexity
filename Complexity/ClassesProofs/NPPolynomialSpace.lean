/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/NPPolynomialSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.NPPolynomialSpace` to `Complexity.ClassesProofs.NPPolynomialSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.BasicProperties
import Complexity.ClassesProofs.InclusionAux.NPPolynomialSpace
import Batteries.Tactic.Alias
import Complexity.ClassesProofs.PolynomialSpaceEquality

namespace Complexity.ClassesProofs

open Complexity.Classes.NondeterministicPolynomialTime Complexity.Classes.PolynomialSpace

/--
---
conclusion: Complexity.Classes.BasicProperties.NP_subset_PSPACE
assumptions:
  - Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE
---
A finite nondeterministic machine guesses a bounded certificate and runs
the original polynomial-time verifier within polynomial work space.
Savitch's theorem, proved separately, then gives deterministic polynomial
space and the inclusion.
-/
theorem NP_subset_PSPACE : NP ⊆ PSPACE := by
  rw [Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE]
  exact InclusionAux.NP_subset_NPSPACE

alias _root_.Complexity.Classes.BasicProperties.NP_subset_PSPACE := NP_subset_PSPACE

end Complexity.ClassesProofs
