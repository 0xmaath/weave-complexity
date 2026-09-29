/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/PositiveCNFHardness.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.PositiveCNFHardness` to `Complexity.ArcKaylesProofs.PositiveCNFHardness`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.SpaceReductionCode
import Complexity.ArcKaylesProofs.ReductionComposition
import Complexity.ArcKayles.PositiveCNFHardness
import Batteries.Tactic.Alias

namespace Complexity.ArcKaylesProofs

open Complexity.Classical.PolynomialTime Complexity.Classical.PolynomialSpace Complexity.CookLevin.Reductions

theorem signedCNF_hard : Complexity.ArcKayles.PSPACE.Hard Byskov.signedLanguage := by
  intro A hA
  obtain ⟨p, M, _hd, hdec, hspace⟩ := hA
  refine ⟨fun w => (CircuitStreaming.sourceCode M p).eval (fun _ => w),
    MachineCode.code_polynomial_time (CircuitStreaming.sourceCode M p), ?_⟩
  intro w
  exact (hdec w).2.symm.trans (CircuitStreaming.sourceCode_correct M p w (hspace w)).symm

/--
---
conclusion: Complexity.ArcKayles.PositiveCNFHardness.hard
---
Compile polynomial-space machine reachability into a quantified circuit,
then use the verified Cook–Levin gate clauses and quantifier normalization.
The checked Byskov game gadgets transfer the resulting alternating-CNF
game to positive CNF. Both word transformations have compiled polynomial-
time Turing-machine witnesses; their composition uses the archived
polynomial-time composition proof.
-/
theorem positiveCNF_hard : Complexity.ArcKayles.PSPACE.Hard Complexity.ArcKayles.Encoding.positiveCNF :=
  pspace_hard_of_reduction signedCNF_hard Byskov.signedReduction_polynomial

alias _root_.Complexity.ArcKayles.PositiveCNFHardness.hard := positiveCNF_hard

end Complexity.ArcKaylesProofs
