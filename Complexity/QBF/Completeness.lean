/-
Milestone 2: TQBF is PSPACE-complete.

Membership is `Complexity.QBF.TQBFGame.TQBF_mem_PSPACE` (the formula game through the generic
template); hardness composes the ported PSPACE-hardness of the signed-CNF language (proved
in the Arc Kayles port from the definition of PSPACE) with the Karp reduction of
`Complexity.QBF.ReductionCode`. `PSPACE.Hard` and `PSPACE.Complete` are the tree's
definitions: hardness under polynomial-time many-one reductions computed by Mathlib stack
machines, as in the Arc Kayles port.
-/
import Complexity.QBF.TQBFGame
import Complexity.QBF.ReductionCode
import Complexity.ArcKaylesProofs.PositiveCNFHardness

namespace Complexity.QBF

open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace

/-- **TQBF ∈ PSPACE.** -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := TQBFGame.TQBF_mem_PSPACE

/-- **TQBF is PSPACE-hard** under polynomial-time many-one reductions. -/
theorem TQBF_hard : Complexity.ArcKayles.PSPACE.Hard TQBF :=
  Complexity.ArcKaylesProofs.pspace_hard_of_reduction Complexity.ArcKaylesProofs.signedCNF_hard
    ReductionCode.reduction_polynomial

/-- **TQBF is PSPACE-complete.** -/
theorem TQBF_complete : Complexity.ArcKayles.PSPACE.Complete TQBF :=
  ⟨TQBF_mem_PSPACE, TQBF_hard⟩

end Complexity.QBF
