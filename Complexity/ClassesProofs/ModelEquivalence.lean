/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/ModelEquivalence.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.ModelEquivalence` to `Complexity.ClassesProofs.ModelEquivalence`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.Classes.ModelEquivalence
import Complexity.Classes.FiniteStackEquivalence
import Complexity.Classes.SingleTapeComplement
import Complexity.Classes.ComplementClosure
import Complexity.ClassesProofs.StackToTape
import Complexity.ClassesProofs.TapeToStack
import Complexity.ClassesProofs.ComplementClosure
import Batteries.Tactic.Alias

namespace Complexity.ClassesProofs.ModelEquivalence

open Complexity.Classes.PolynomialTime Complexity.Classes.MachineModels

/--
---
conclusion: Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P
---
Retain the input/output symbols and the finite ranges of push instructions.
Restricting each stack alphabet to these symbols preserves every transition
and the original time polynomial.
-/
theorem finiteStackP_eq_P : FiniteStackP = P := FiniteAlphabet.finiteStackP_eq_P

/-- Requiring all work alphabets to be finite does not change P. -/
alias _root_.Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P := finiteStackP_eq_P

/-- Direct class equality, without any concept-statement assumptions. -/
theorem singleTapeP_eq_P_closed : SingleTapeP = P :=
  Set.Subset.antisymm TapeToStack.singleTapeP_subset_P StackToTape.P_subset_singleTapeP

/--
---
conclusion: Complexity.Classes.ModelEquivalence.singleTapeP_eq_P
assumptions:
  - Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P
---
After restricting stack alphabets, compile stacks to tape tracks with polynomial
overhead. Conversely, simulate a tape by two stacks with linear overhead.
Both bounds include input conversion and final output conversion.
-/
theorem singleTapeP_eq_P : SingleTapeP = P :=
  Set.Subset.antisymm TapeToStack.singleTapeP_subset_P (by
    rw [← Complexity.Classes.FiniteStackEquivalence.finiteStackP_eq_P]
    exact StackToTape.finiteStackP_subset_singleTapeP)

/-- The elementary single-tape and stack definitions give the same class P. -/
alias _root_.Complexity.Classes.ModelEquivalence.singleTapeP_eq_P := singleTapeP_eq_P

/--
---
conclusion: Complexity.Classes.SingleTapeComplement.closed_under_complement
assumptions:
  - Complexity.Classes.ModelEquivalence.singleTapeP_eq_P
  - Complexity.Classes.ComplementClosure.closed_under_complement
---
Transport the established complement theorem across the proved class equality.
-/
theorem singleTape_closed_under_complement (L : Language) :
    L ∈ SingleTapeP → Lᶜ ∈ SingleTapeP := by
  rw [Complexity.Classes.ModelEquivalence.singleTapeP_eq_P]
  exact Complexity.Classes.ComplementClosure.closed_under_complement L

/-- Complement closure for the elementary single-tape definition. -/
alias _root_.Complexity.Classes.SingleTapeComplement.closed_under_complement := singleTape_closed_under_complement

end Complexity.ClassesProofs.ModelEquivalence
