/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/ComplementClosure.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.ComplementClosure` to `Complexity.Classes.ComplementClosure`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.PolynomialTime

/-!
---
title: P is closed under complement
type: lemma
---
If a language of binary strings belongs to $\mathrm{P}$, then its complement
also belongs to $\mathrm{P}$. The complement is taken in the set of all finite
binary strings.
-/

namespace Complexity.Classes.ComplementClosure

open Complexity.Classes.PolynomialTime

/- The archived concept stated `closed_under_complement` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ClassesProofs.closed_under_complement` in `Complexity.ClassesProofs.ComplementClosure`, which
re-exports it under the name `Complexity.Classes.ComplementClosure.closed_under_complement` via `alias`. -/

end Complexity.Classes.ComplementClosure
