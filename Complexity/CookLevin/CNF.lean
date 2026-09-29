/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/CNF.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.CNF` to `Complexity.CookLevin.CNF`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.PolynomialTime

/-!
---
title: Conjunctive normal form
type: definition
---
A literal names a natural-number variable and its sign. A CNF formula is a
list of clauses, each a list of literals. Empty clauses are false and the
empty conjunction is true. Satisfiability quantifies over Boolean assignments.
-/

namespace Complexity.CookLevin.CNF

structure Literal where
  index : ℕ
  positive : Bool
  deriving DecidableEq

abbrev Clause := List Literal
abbrev Formula := List Clause
abbrev Assignment := ℕ → Bool

def Literal.eval (l : Literal) (ρ : Assignment) : Bool :=
  if l.positive then ρ l.index else !(ρ l.index)

def eval (F : Formula) (ρ : Assignment) : Bool :=
  F.all fun C => C.any fun l => l.eval ρ

def Satisfiable (F : Formula) : Prop := ∃ ρ, eval F ρ = true

end Complexity.CookLevin.CNF
