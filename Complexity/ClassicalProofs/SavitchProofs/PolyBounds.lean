/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/PolyBounds.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.PolyBounds` to `Complexity.ClassicalProofs.SavitchProofs.PolyBounds`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchProofs.PolynomialConstructor
import Complexity.ClassicalProofs.SavitchDefinitions.PolyBounds

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassicalProofs.SavitchProofs

open Complexity.ClassicalProofs.SavitchDefinitions.SpaceConstructibility

/--
Count the input, append each polynomial term using nested counters, and scan
the output track to halt at position $p(n)+n+1$.
-/
lemma polynomial_constructible (p : Polynomial ℕ) :
    Constructible (fun n => p.eval n + n + 2) := by
  refine ⟨UnaryPolynomial.constructor p, ?_, UnaryPolynomial.constructor_execution p⟩
  exact ParkMachine.deterministic _ _ (StackMachine.deterministic _)

end Complexity.ClassicalProofs.SavitchProofs
