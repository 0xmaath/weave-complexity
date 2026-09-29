/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/PolynomialSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.PolynomialSpace` to `Complexity.Classes.PolynomialSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.SpaceBounds

/-!
---
title: The complexity class PSPACE
type: definition
---
A binary language belongs to $\mathrm{PSPACE}$ if one deterministic Turing
machine decides membership using at most $p(n)$ work cells on inputs of
length $n$, for some polynomial $p\in\mathbb{N}[X]$. The input tape is
read-only and excluded from work space, and the machine always halts.
-/

namespace Complexity.Classes.PolynomialSpace

open PolynomialTime SpaceBounds

/-- Deterministic polynomial work space. -/
def PSPACE : Set Language :=
  {A | ∃ p : Polynomial ℕ, A ∈ DSPACE p.eval}

end Complexity.Classes.PolynomialSpace
