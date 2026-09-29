/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930` to `Complexity.Classes`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.BasicProperties
import Complexity.Classes.Certificates
import Complexity.Classes.ComplementClasses
import Complexity.Classes.ComplementClosure
import Complexity.Classes.ExponentialTime
import Complexity.Classes.FiniteStackEquivalence
import Complexity.Classes.LogarithmicSpace
import Complexity.Classes.MachineModels
import Complexity.Classes.ModelEquivalence
import Complexity.Classes.NondeterministicLogarithmicSpace
import Complexity.Classes.NondeterministicPolynomialSpace
import Complexity.Classes.NondeterministicPolynomialTime
import Complexity.Classes.PolynomialSpace
import Complexity.Classes.PolynomialTime
import Complexity.Classes.SingleTapeComplement
import Complexity.Classes.SpaceBounds
import Complexity.Classes.SpaceMachines
import Complexity.Classes.PolynomialSpaceEquality
