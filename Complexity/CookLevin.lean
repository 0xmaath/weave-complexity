/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `concepts/Lax429075.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075` to `Complexity.CookLevin`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.CNF
import Complexity.CookLevin.CircuitMachine
import Complexity.CookLevin.Circuits
import Complexity.CookLevin.CookLevin
import Complexity.CookLevin.Encoding
import Complexity.CookLevin.EncodingCorrect
import Complexity.CookLevin.FiniteWitness
import Complexity.CookLevin.GateCorrect
import Complexity.CookLevin.Reductions
import Complexity.CookLevin.Satisfiability
import Complexity.CookLevin.SATEncoding
import Complexity.CookLevin.SATHard
import Complexity.CookLevin.SATinNP
import Complexity.CookLevin.Tseitin
import Complexity.CookLevin.TseitinCorrect
import Complexity.CookLevin.VerifierCorrect
import Complexity.CookLevin.VerifierTime
