/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/Reachability.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.Reachability` to `Complexity.ClassicalProofs.SavitchDefinitions.Reachability`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

set_option backward.isDefEq.respectTransparency false

/-!
A directed graph on $N$ vertices is given by its Boolean adjacency matrix.
A walk may repeat vertices. The recursive reachability test divides the
length bound in two and enumerates possible middle vertices.
-/

namespace Complexity.ClassicalProofs.SavitchDefinitions.Reachability

abbrev Graph (N : ℕ) := Fin N → Fin N → Bool

inductive Walk {α : Type} (R : α → α → Prop) : ℕ → α → α → Prop
  | nil (a : α) : Walk R 0 a a
  | tail {n : ℕ} {a b c : α} : Walk R n a b → R b c → Walk R (n + 1) a c

def Within {α : Type} (R : α → α → Prop) (n : ℕ) (a b : α) : Prop :=
  ∃ k ≤ n, Walk R k a b

def Reachable {N : ℕ} (G : Graph N) (a b : Fin N) : Prop :=
  Relation.ReflTransGen (fun u v => G u v = true) a b

def search {N : ℕ} (G : Graph N) : ℕ → Fin N → Fin N → Bool
  | 0, a, b => decide (a = b) || G a b
  | k + 1, a, b => (List.finRange N).any fun m => search G k a m && search G k m b

end Complexity.ClassicalProofs.SavitchDefinitions.Reachability
