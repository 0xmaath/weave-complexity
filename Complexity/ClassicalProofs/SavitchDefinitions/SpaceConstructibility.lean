/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/SpaceConstructibility.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.SpaceConstructibility` to `Complexity.ClassicalProofs.SavitchDefinitions.SpaceConstructibility`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.SpaceBounds

set_option backward.isDefEq.respectTransparency false

/-!
A positive bound $s$ is fully space-constructible if a deterministic
machine, on each input of length $n$, halts at work position $s(n)-1$
without leaving the first $s(n)$ work cells. The input tape is read-only.
-/

namespace Complexity.ClassicalProofs.SavitchDefinitions.SpaceConstructibility

open Complexity.Classical.PolynomialTime Complexity.Classical.SpaceMachines

def Constructible (s : ℕ → ℕ) : Prop :=
  ∃ M : Machine, M.Deterministic ∧ ∀ w : Word,
    M.HaltsOn w ∧ M.UsesSpace w (s w.length) ∧
    ∃ (t : ℕ) (c : M.Config), M.Run w t c ∧ M.Terminal w c ∧
      c.workHead + 1 = s w.length

end Complexity.ClassicalProofs.SavitchDefinitions.SpaceConstructibility
