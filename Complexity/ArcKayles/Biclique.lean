/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/Biclique.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.Biclique` to `Complexity.ArcKayles.Biclique`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Grundy

/-!
---
title: Bicliques with pendant neighbors
type: theorem
---
Lemma 6. Partition the surviving vertices into sets $L,R,I$. The sets
$L$ and $R$ induce a complete bipartite graph, $I$ is independent, and
each vertex of $L\cup R$ has a neighbor in $I$ whose only surviving
neighbor is that vertex. Other edges between $L\cup R$ and $I$ are
unrestricted. The value is
$g(|L|,|R|)=(|L|+|R|)\bmod 2+2(\min(|L|,|R|)\bmod 2)$.
Either side of the biclique may be empty.
-/

namespace Complexity.ArcKayles.Biclique

def g (a b : ℕ) : ℕ := (a + b) % 2 + 2 * (min a b % 2)

structure Partition {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) : Prop where
  cover : S = L ∪ R ∪ I
  left_right : Disjoint L R
  left_independent : Disjoint L I
  right_independent : Disjoint R I
  left_stable : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v
  right_stable : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v
  independent_stable : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v
  complete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v
  pendant : ∀ u ∈ L ∪ R, ∃ v ∈ I, G.Adj u v ∧
    ∀ w ∈ S, G.Adj v w → w = u

/- The archived concept stated `value_eq` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.ArcKaylesProofs.biclique_value` in `Complexity.ArcKaylesProofs.Biclique`, which
re-exports it under the name `Complexity.ArcKayles.Biclique.value_eq` via `alias`. -/

end Complexity.ArcKayles.Biclique
