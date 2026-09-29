/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930/ExponentialTime.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930.ExponentialTime` to `Complexity.Classical.ExponentialTime`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.PolynomialTime
import Complexity.Classical.MachineModels

/-!
---
title: The complexity class EXPTIME
type: definition
---
A binary language belongs to $\mathrm{EXPTIME}$ if a deterministic Turing
machine decides membership within $2^{p(n)}$ transitions on every input
of length $n$, for some polynomial $p\in\mathbb{N}[X]$.
The machine is the finite elementary single-tape machine defined here:
input bits are distinct from blank, input appears in its original order,
and each transition performs one move or one write. A terminal state's
Boolean label gives the answer. The polynomial in the exponent may have
any fixed degree; this is the usual EXPTIME, also called EXP.
-/

namespace Complexity.Classical.ExponentialTime

open PolynomialTime Complexity.Classical.MachineModels Turing

/-- Deterministic time bounded by two to a polynomial in the input length. -/
def EXPTIME : Set Language :=
  {A | ∃ (M : SingleTape) (p : Polynomial ℕ), ∀ w : Word,
    ∃ c : TM0.Cfg M.Γ M.Q,
      Nonempty (StateTransition.EvalsToInTime (TM0.step M.transition)
        (TM0.init (w.map M.input)) (some c) (2 ^ p.eval w.length)) ∧
      TM0.step M.transition c = none ∧ (M.accept c.q = true ↔ w ∈ A)}

end Complexity.Classical.ExponentialTime
