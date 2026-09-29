/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/Reduction.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.Reduction` to `Complexity.ArcKayles.Reduction`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Construction
import Complexity.ArcKayles.PSPACE

/-!
---
title: Correctness and complexity of the reduction
type: theorem
---
Claims 9 and 10: for a formula with an odd number of clauses, the first
player wins Arc Kayles on the constructed graph if and only if True wins
the positive CNF game. The second player's winning implication is stated
separately to expose the two strategy arguments.

There is a polynomial-time many-one reduction on all binary strings.
Before applying the construction, duplicate a clause if the nonempty clause
list has even length. Handle the empty conjunction and malformed encodings
separately by fixed yes and no instances.
-/

namespace Complexity.ArcKayles.Reduction

open PositiveCNF Construction ArcKayles

/- The archived concept stated `false_strategy` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.false_strategy` in `Complexity.ArcKaylesProofs.FalseSimulation`, which
re-exports it under the name `Complexity.ArcKayles.Reduction.false_strategy` via `alias`. -/

/- The archived concept stated `true_strategy` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.true_strategy` in `Complexity.ArcKaylesProofs.TrueSimulation`, which
re-exports it under the name `Complexity.ArcKayles.Reduction.true_strategy` via `alias`. -/

/- The archived concept stated `polynomial_reduction` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.polynomial_reduction` in `Complexity.ArcKaylesProofs.ReductionTime`, which
re-exports it under the name `Complexity.ArcKayles.Reduction.polynomial_reduction` via `alias`. -/

end Complexity.ArcKayles.Reduction
