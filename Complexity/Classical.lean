/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `concepts/Lax434930.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930` to `Complexity.Classical`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classical.BasicProperties
import Complexity.Classical.Certificates
import Complexity.Classical.ComplementClasses
import Complexity.Classical.ComplementClosure
import Complexity.Classical.ExponentialTime
import Complexity.Classical.FiniteStackEquivalence
import Complexity.Classical.LogarithmicSpace
import Complexity.Classical.MachineModels
import Complexity.Classical.ModelEquivalence
import Complexity.Classical.NondeterministicLogarithmicSpace
import Complexity.Classical.NondeterministicPolynomialSpace
import Complexity.Classical.NondeterministicPolynomialTime
import Complexity.Classical.PolynomialSpace
import Complexity.Classical.PolynomialTime
import Complexity.Classical.SingleTapeComplement
import Complexity.Classical.SpaceBounds
import Complexity.Classical.SpaceMachines
import Complexity.Classical.PolynomialSpaceEquality
