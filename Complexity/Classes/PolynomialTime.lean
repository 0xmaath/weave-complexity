/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/PolynomialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.PolynomialTime` to `Complexity.Classes.PolynomialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: The complexity class P
type: definition
---
A language of finite binary strings belongs to $\mathrm{P}$ if a deterministic
Turing machine decides membership in that language in polynomial time.
Precisely, there are a single machine and a polynomial $p \in \mathbb{N}[X]$
such that, on every input $w$, the machine halts within $p(|w|)$ steps and
returns the bit $1$ if $w$ belongs to the language and $0$ otherwise.

The definition uses mathlib's deterministic stack machines, the identity
encoding of binary strings, and a singleton Boolean output. Time counts
transitions of fixed finite instruction blocks. We also prove equivalence
with elementary single-tape machines.
-/

namespace Complexity.Classes.PolynomialTime

/-- A finite binary string. -/
abbrev Word := List Bool

/-- A language of finite binary strings. -/
abbrev Language := Set Word

/-- Languages whose Boolean characteristic functions are computable in polynomial time. -/
def P : Set Language :=
  {L | ∃ f : Word → Bool,
    (∀ w, f w = true ↔ w ∈ L) ∧
    Nonempty (Turing.TM2ComputableInPolyTime id Computability.encodeBool f)}

end Complexity.Classes.PolynomialTime
