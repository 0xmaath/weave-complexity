/-
Ported from https://github.com/EdouardBonnet/cook-levin (Lax submission lax-429075, commit 905f2da2698d),
file `proofs/Lax429075Proofs/CookLevin.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/cook-levin.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax429075Proofs.CookLevin` to `Complexity.CookLevinProofs.CookLevin`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.CookLevin.CircuitMachine
import Complexity.CookLevin.TseitinCorrect
import Complexity.CookLevin.SATEncoding
import Complexity.CookLevin.SATinNP
import Complexity.CookLevin.SATHard
import Complexity.CookLevin.CookLevin
import Batteries.Tactic.Alias
import Complexity.CookLevinProofs.Certificates
import Complexity.CookLevinProofs.CircuitMachine
import Complexity.CookLevinProofs.Tseitin

namespace Complexity.CookLevinProofs

open Complexity.CookLevin Complexity.CookLevin.Satisfiability Complexity.CookLevin.Encoding Complexity.CookLevin.Reductions
open Complexity.Classical.PolynomialTime Complexity.Classical.NondeterministicPolynomialTime

/--
---
conclusion: Complexity.CookLevin.SATHard.hardness
assumptions:
  - Complexity.CookLevin.CircuitMachine.compile
  - Complexity.CookLevin.SATEncoding.correct
  - Complexity.CookLevin.TseitinCorrect.correct
---
Compile the verifier, impose the gate clauses, and encode the resulting formula.
-/
lemma sat_hard (A : Language) : A ∈ NP → ManyOne A SAT := by
  rintro ⟨V, hV, p, hA⟩
  obtain ⟨circuits, htime, hcircuits⟩ := CircuitMachine.compile V hV p
  refine ⟨fun x => encodeCNF (Tseitin.encode (circuits x)), htime, ?_⟩
  intro x
  rw [SATEncoding.correct, TseitinCorrect.correct, hcircuits, hA]

alias _root_.Complexity.CookLevin.SATHard.hardness := sat_hard

/--
---
conclusion: Complexity.CookLevin.CookLevin.np_complete
assumptions:
  - Complexity.CookLevin.SATHard.hardness
  - Complexity.CookLevin.SATinNP.membership
---
Combine membership in NP with polynomial many-one hardness.
-/
theorem cook_levin : NPComplete SAT :=
  ⟨SATinNP.membership, SATHard.hardness⟩

alias _root_.Complexity.CookLevin.CookLevin.np_complete := cook_levin

end Complexity.CookLevinProofs
