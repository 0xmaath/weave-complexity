/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/LogarithmicSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.LogarithmicSpace` to `Complexity.Classical.LogarithmicSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.SpaceBounds

/-!
---
title: The complexity class L
type: definition
---
A binary language belongs to $\mathrm{L}$ if a deterministic Turing machine
decides membership using $O(\log n)$ work space and a separate read-only
input tape. Precisely, some positive constant $c$ bounds work space by
$c\lfloor\log_2(n+2)\rfloor$ on every input of length $n$.
-/

namespace Complexity.Classical.LogarithmicSpace

open PolynomialTime SpaceBounds

/-- Deterministic logarithmic work space. -/
def L : Set Language :=
  {A | ∃ c : ℕ, 0 < c ∧ A ∈ DSPACE (fun n => c * logSpace n)}

end Complexity.Classical.LogarithmicSpace
