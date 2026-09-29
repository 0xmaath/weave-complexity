/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/Completeness.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.Completeness` to `Complexity.ArcKayles.Completeness`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Reduction
import Complexity.ArcKayles.PositiveCNFHardness

/-!
---
title: Arc Kayles is PSPACE-complete
type: theorem
---
Theorem 1. Determining the winner of Arc Kayles on a finite simple
undirected graph is PSPACE-complete under polynomial-time many-one
reductions. Membership follows by depth-first evaluation of the game tree:
at most $n/2$ moves are played and each position uses $O(n^2)$ bits.
Hardness follows from the positive CNF game and the reduction graph.
-/

namespace Complexity.ArcKayles.Completeness

/- The archived concept stated `membership` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.arcKayles_membership` in `Complexity.ArcKaylesProofs.Membership`, which
re-exports it under the name `Complexity.ArcKayles.Completeness.membership` via `alias`. -/

/- The archived concept stated `pspace_complete` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.arcKayles_pspace_complete` in `Complexity.ArcKaylesProofs.Completeness`, which
re-exports it under the name `Complexity.ArcKayles.Completeness.pspace_complete` via `alias`. -/

end Complexity.ArcKayles.Completeness
