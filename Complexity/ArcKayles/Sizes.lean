/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/Sizes.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.Sizes` to `Complexity.ArcKayles.Sizes`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Construction

/-!
---
title: Sizes of encodings and the reduction graph
type: theorem
---
The graph encoding has $n^2+n+1$ bits. The formula encoding has
$mn+n+m+2$ bits, where $n$ and $m$ are its variable and clause counts.
The reduction graph has exactly $13n+4m+18$ vertices.
These bounds account explicitly for the unary size prefixes and incidence
matrices; they are separate from the running-time proof of the reduction.
-/

namespace Complexity.ArcKayles.Sizes

/- The archived concept stated `graph_length` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.graph_length` in `Complexity.ArcKaylesProofs.Sizes`, which
re-exports it under the name `Complexity.ArcKayles.Sizes.graph_length` via `alias`. -/

/- The archived concept stated `formula_length` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.formula_length` in `Complexity.ArcKaylesProofs.Sizes`, which
re-exports it under the name `Complexity.ArcKayles.Sizes.formula_length` via `alias`. -/

/- The archived concept stated `construction_size` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.construction_size` in `Complexity.ArcKaylesProofs.Sizes`, which
re-exports it under the name `Complexity.ArcKayles.Sizes.construction_size` via `alias`. -/

end Complexity.ArcKayles.Sizes
