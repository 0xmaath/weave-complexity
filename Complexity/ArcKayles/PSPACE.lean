/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/PSPACE.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.PSPACE` to `Complexity.ArcKayles.PSPACE`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.PolynomialSpace
import Complexity.CookLevin.Reductions

/-!
---
title: PSPACE-completeness
type: definition
---
A binary language is PSPACE-hard if every language decidable in polynomial
space has a polynomial-time many-one reduction to it. It is PSPACE-complete
if it is also decidable in polynomial space. Polynomial space and reductions
are those of the classical complexity and Cook–Levin submissions.
-/

namespace Complexity.ArcKayles.PSPACE

open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace Complexity.CookLevin.Reductions

def Hard (B : Language) : Prop := ∀ A : Language, A ∈ PSPACE → ManyOne A B

def Complete (B : Language) : Prop := B ∈ PSPACE ∧ Hard B

end Complexity.ArcKayles.PSPACE
