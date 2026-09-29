/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/RegularPlay.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.RegularPlay` to `Complexity.ArcKayles.RegularPlay`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Construction
import Complexity.ArcKayles.Grundy

/-!
---
title: Assignment moves, pass moves, and deviations
type: theorem
---
An assignment move is $v_it_i$ or $v_if_i$ with $i<n$. A pass move is
$v_it_i$ with $n\leq i<R$, or $y_iz_i$. A regular position is reachable
from the initial graph by such moves. Write $r$ and $k$ for the numbers
of surviving $v_i$ and $y_i$, respectively.

Claim 7: when $m$ is odd, $r\geq m$, and $k\geq1$, any other move
loses unless it is $sa_j$ and all literal vertices of clause $j$ are gone.
Claim 8: at a regular position with $r\geq m$, such an exceptional move
wins exactly when $r+k$ is even.
-/

namespace Complexity.ArcKayles.RegularPlay

open PositiveCNF Construction ArcKayles

def SameEdge (u w x z : ℕ) : Prop := (u = x ∧ w = z) ∨ (u = z ∧ w = x)

def RegularMove (φ : Formula) (u w : ℕ) : Prop :=
  (∃ i < R φ, SameEdge u w (v φ i) (vt φ i)) ∨
  (∃ i < φ.nvars, SameEdge u w (v φ i) (f φ i)) ∨
  (∃ i < K φ, SameEdge u w (y φ i) (z φ i))

inductive Reachable (φ : Formula) : Finset ℕ → Prop
  | initial : Reachable φ (board φ)
  | step {S : Finset ℕ} {u w : ℕ} : Reachable φ S →
      u ∈ S → w ∈ S → (graph φ).Adj u w → RegularMove φ u w →
      Reachable φ (remove S u w)

def remainingV (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (R φ)).filter fun i => v φ i ∈ S).card

def remainingY (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (K φ)).filter fun i => y φ i ∈ S).card

def Exhausted (φ : Formula) (S : Finset ℕ) (j : Fin φ.clauses.length) : Prop :=
  ∀ i ∈ φ.clauses[j], f φ i ∉ S

def Exceptional (φ : Formula) (S : Finset ℕ) (u w : ℕ) : Prop :=
  ∃ j : Fin φ.clauses.length, SameEdge u w s (a φ j) ∧ Exhausted φ S j

/- The archived concept stated `deviation_loses` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.deviation_loses` in `Complexity.ArcKaylesProofs.Deviations`, which
re-exports it under the name `Complexity.ArcKayles.RegularPlay.deviation_loses` via `alias`. -/

/- The archived concept stated `exceptional_parity` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.exceptional_parity` in `Complexity.ArcKaylesProofs.ExceptionalMove`, which
re-exports it under the name `Complexity.ArcKayles.RegularPlay.exceptional_parity` via `alias`. -/

end Complexity.ArcKayles.RegularPlay
