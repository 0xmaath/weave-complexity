/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/Reductions.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.Reductions` to `Complexity.CookLevin.Reductions`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.NondeterministicPolynomialTime

/-!
---
title: Polynomial many-one reductions and NP-completeness
type: definition
---
A polynomial many-one reduction is one polynomial time computable function
on binary words that preserves membership. A language is NP-complete if it
belongs to NP and every language in NP reduces to it.
-/

namespace Complexity.CookLevin.Reductions

open Complexity.Classes.PolynomialTime Complexity.Classes.NondeterministicPolynomialTime

def ManyOne (A B : Language) : Prop :=
  ∃ f : Word → Word, Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ x, x ∈ A ↔ f x ∈ B

def NPComplete (B : Language) : Prop := B ∈ NP ∧ ∀ A : Language, A ∈ NP → ManyOne A B

end Complexity.CookLevin.Reductions
