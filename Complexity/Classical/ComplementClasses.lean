/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/ComplementClasses.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.ComplementClasses` to `Complexity.Classical.ComplementClasses`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.NondeterministicLogarithmicSpace
import Complexity.Classical.NondeterministicPolynomialTime

/-!
---
title: The complexity classes coNL and coNP
type: definition
---
For a class $\mathcal C$ of binary languages, $\mathrm{co}\mathcal C$
consists of languages whose complements belong to $\mathcal C$.
Complements are taken among all finite binary strings. In particular,
$A\in\mathrm{coNL}$ means $\overline A\in\mathrm{NL}$, and
$A\in\mathrm{coNP}$ means $\overline A\in\mathrm{NP}$.
This operation complements each language; it does not take the set-theoretic
complement of the class of languages.
-/

namespace Complexity.Classical.ComplementClasses

open PolynomialTime NondeterministicLogarithmicSpace NondeterministicPolynomialTime

/-- The class of languages whose complements belong to the given class. -/
def co (C : Set Language) : Set Language := {A | Aᶜ ∈ C}

/-- Complements of languages in NL. -/
def coNL : Set Language := co NL

/-- Complements of languages in NP. -/
def coNP : Set Language := co NP

end Complexity.Classical.ComplementClasses
