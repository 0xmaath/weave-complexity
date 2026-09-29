/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/NondeterministicPolynomialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.NondeterministicPolynomialTime` to `Complexity.Classical.NondeterministicPolynomialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.Certificates

/-!
---
title: The complexity class NP
type: definition
---
A binary language $A$ belongs to $\mathrm{NP}$ if there are a verifier
language $V\in\mathrm{P}$ and a polynomial $p\in\mathbb{N}[X]$ such that
$x\in A$ precisely when some binary certificate $y$ with $|y|\le p(|x|)$
satisfies $\langle x,y\rangle\in V$.
The verifier is a single deterministic polynomial-time decider on the
explicit pair encoding, and its running time is polynomial in the combined
input and certificate lengths. The certificate bound depends only on the
original input length. This is the standard certificate definition of NP.
-/

namespace Complexity.Classical.NondeterministicPolynomialTime

open PolynomialTime Certificates

/-- Languages with polynomially bounded, polynomial-time verifiable certificates. -/
def NP : Set Language :=
  {A | ∃ V : Language, V ∈ P ∧ ∃ p : Polynomial ℕ, ∀ x : Word,
    x ∈ A ↔ ∃ y : Word, y.length ≤ p.eval x.length ∧ pair x y ∈ V}

end Complexity.Classical.NondeterministicPolynomialTime
