/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchDefinitions/PolynomialSpace.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchDefinitions.PolynomialSpace` to `Complexity.ClassesProofs.SavitchDefinitions.PolynomialSpace`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchDefinitions.Savitch
import Complexity.ClassesProofs.SavitchDefinitions.PolyBounds
import Complexity.Classes.PolynomialSpace
import Complexity.Classes.NondeterministicPolynomialSpace

set_option backward.isDefEq.respectTransparency false

/-!
Deterministic and nondeterministic polynomial space define the same class
of binary languages.
-/

namespace Complexity.ClassesProofs.SavitchDefinitions.PolynomialSpace

open Complexity.Classes.PolynomialSpace Complexity.Classes.NondeterministicPolynomialSpace


end Complexity.ClassesProofs.SavitchDefinitions.PolynomialSpace
