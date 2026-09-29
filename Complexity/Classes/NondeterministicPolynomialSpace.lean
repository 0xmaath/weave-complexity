/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/NondeterministicPolynomialSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.NondeterministicPolynomialSpace` to `Complexity.Classes.NondeterministicPolynomialSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.SpaceBounds

/-!
---
title: The complexity class NPSPACE
type: definition
---
A binary language belongs to $\mathrm{NPSPACE}$ if one nondeterministic
Turing machine decides membership using at most $p(n)$ work cells on
every branch on inputs of length $n$, for some polynomial
$p\in\mathbb{N}[X]$. All branches halt; at least one accepts precisely
when the input belongs to the language. The input tape is read-only and
excluded from work space.
-/

namespace Complexity.Classes.NondeterministicPolynomialSpace

open PolynomialTime SpaceBounds

/-- Nondeterministic polynomial work space. -/
def NPSPACE : Set Language :=
  {A | ∃ p : Polynomial ℕ, A ∈ NSPACE p.eval}

end Complexity.Classes.NondeterministicPolynomialSpace
