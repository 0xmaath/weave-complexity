/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/NondeterministicLogarithmicSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.NondeterministicLogarithmicSpace` to `Complexity.Classical.NondeterministicLogarithmicSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.SpaceBounds

/-!
---
title: The complexity class NL
type: definition
---
A binary language belongs to $\mathrm{NL}$ if a nondeterministic Turing
machine decides membership using $O(\log n)$ work space and a separate
read-only input tape. Every branch halts and respects the space bound;
membership means that at least one branch accepts. The bound is
$c\lfloor\log_2(n+2)\rfloor$ for one positive constant $c$.
-/

namespace Complexity.Classical.NondeterministicLogarithmicSpace

open PolynomialTime SpaceBounds

/-- Nondeterministic logarithmic work space. -/
def NL : Set Language :=
  {A | ∃ c : ℕ, 0 < c ∧ A ∈ NSPACE (fun n => c * logSpace n)}

end Complexity.Classical.NondeterministicLogarithmicSpace
