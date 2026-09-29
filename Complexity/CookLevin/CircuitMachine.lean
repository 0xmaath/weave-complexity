/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075/CircuitMachine.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075.CircuitMachine` to `Complexity.CookLevin.CircuitMachine`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.Tseitin
import Complexity.CookLevin.Encoding
import Complexity.Classical.NondeterministicPolynomialTime

/-!
---
title: Polynomial circuit simulation of a verifier
type: lemma
---
For a fixed polynomial time verifier and polynomial certificate bound,
construct a circuit whose free inputs represent the certificate. The circuit
is satisfiable exactly when some bounded certificate is accepted. Its encoded
gate clauses are produced in polynomial time. The machine simulation and
time bound follow from a finite stack program that emits the initial layer,
the transition layers, and the final acceptance constraint.
-/

namespace Complexity.CookLevin.CircuitMachine

open Complexity.Classical.PolynomialTime Complexity.Classical.Certificates Circuits Encoding

/- The archived concept stated `compile` here as an `axiom`. In this port it is a
theorem: it is proved as `Complexity.CookLevinProofs.Streaming.circuit_machine` in `Complexity.CookLevinProofs.CircuitMachine`, which
re-exports it under the name `Complexity.CookLevin.CircuitMachine.compile` via `alias`. -/

end Complexity.CookLevin.CircuitMachine
