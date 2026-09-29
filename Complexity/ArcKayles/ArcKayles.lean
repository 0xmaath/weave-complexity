/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/ArcKayles.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.ArcKayles` to `Complexity.ArcKayles.ArcKayles`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
---
title: Arc Kayles
type: definition
---
A position consists of a finite set of surviving vertices of a simple graph.
A move removes the two endpoints of a surviving edge. Under normal play,
the player with no legal move loses. A position is winning for the player
to move if some legal move leaves a position losing for the opponent.
Isolated vertices may be retained: they permit no moves.
-/

namespace Complexity.ArcKayles.ArcKayles

variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S ×ˢ S).filter fun e => G.Adj e.1 e.2

/-- Winning for the next player, by backward induction on surviving vertices. -/
def Winning (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ e : {e // e ∈ moves G S}, ¬ Winning G (remove S e.val.1 e.val.2)
termination_by S.card
decreasing_by
  have h := e.property
  simp only [moves, Finset.mem_filter, Finset.mem_product] at h
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem h.1.1)

end Complexity.ArcKayles.ArcKayles
