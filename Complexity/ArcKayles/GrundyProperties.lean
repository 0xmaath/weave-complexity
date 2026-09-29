/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/GrundyProperties.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.GrundyProperties` to `Complexity.ArcKayles.GrundyProperties`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Grundy
import Mathlib.Data.Nat.Bitwise

/-!
---
title: Basic properties of Sprague–Grundy values
type: theorem
---
Observation 2 and Lemma 3: every smaller value is reachable, the current
value is not reachable, and a position is losing exactly when its value is
zero. Lemma 4: on a disjoint union, the value is the bitwise exclusive-or
of the component values. The binary formula gives the finite-family formula
by iteration.
-/

namespace Complexity.ArcKayles.GrundyProperties

open ArcKayles Grundy

/- The archived concept stated `smaller_reachable` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.smaller_reachable` in `Complexity.ArcKaylesProofs.Grundy`, which
re-exports it under the name `Complexity.ArcKayles.GrundyProperties.smaller_reachable` via `alias`. -/

/- The archived concept stated `value_not_reachable` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.value_not_reachable` in `Complexity.ArcKaylesProofs.Grundy`, which
re-exports it under the name `Complexity.ArcKayles.GrundyProperties.value_not_reachable` via `alias`. -/

/- The archived concept stated `losing_iff_zero` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.losing_iff_zero` in `Complexity.ArcKaylesProofs.Grundy`, which
re-exports it under the name `Complexity.ArcKayles.GrundyProperties.losing_iff_zero` via `alias`. -/

/- The archived concept stated `disjoint_union` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.disjoint_union` in `Complexity.ArcKaylesProofs.DisjointUnion`, which
re-exports it under the name `Complexity.ArcKayles.GrundyProperties.disjoint_union` via `alias`. -/

end Complexity.ArcKayles.GrundyProperties
