/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/PolynomialSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.PolynomialSpace` to `Complexity.ClassicalProofs.SavitchDefinitions.PolynomialSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassicalProofs.SavitchDefinitions.Savitch
import Complexity.ClassicalProofs.SavitchDefinitions.PolyBounds
import Complexity.Classical.PolynomialSpace
import Complexity.Classical.NondeterministicPolynomialSpace

set_option backward.isDefEq.respectTransparency false

/-!
Deterministic and nondeterministic polynomial space define the same class
of binary languages.
-/

namespace Complexity.ClassicalProofs.SavitchDefinitions.PolynomialSpace

open Complexity.Classical.PolynomialSpace Complexity.Classical.NondeterministicPolynomialSpace


end Complexity.ClassicalProofs.SavitchDefinitions.PolynomialSpace
