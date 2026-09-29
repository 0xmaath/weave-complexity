/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/Grundy.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.Grundy` to `Complexity.ArcKayles.Grundy`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.ArcKayles
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
---
title: Sprague–Grundy values
type: definition
---
The minimum excluded value of a finite set of natural numbers is the least
natural number outside the set. The Sprague–Grundy value of a position is
the minimum excluded value of the values reachable in one move.
In particular, a terminal position has value zero.
-/

namespace Complexity.ArcKayles.Grundy

open ArcKayles

noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

noncomputable def value {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  mex ((moves G S).attach.image fun e => value G (remove S e.val.1 e.val.2))
termination_by S.card
decreasing_by
  have h := e.property
  simp only [moves, Finset.mem_filter, Finset.mem_product] at h
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem h.1.1)

end Complexity.ArcKayles.Grundy
