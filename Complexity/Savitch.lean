/-
Milestone 2: Savitch's theorem as an inclusion.

The ported classical-complexity package already proves the polynomial-space form of
Savitch's theorem as an equality of classes
(`Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE`), with a full simulation
proof in `Complexity.ClassesProofs.SavitchProofs`. This module exposes the nontrivial
direction, `NPSPACE ⊆ PSPACE`, as a theorem in its own right, next to the trivial
direction `PSPACE ⊆ NPSPACE` that the port also proves.
-/
import Complexity.ClassesProofs.PolynomialSpaceEquality
import Complexity.ClassesProofs.BasicProperties

namespace Complexity.Savitch

open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace
open Complexity.Classes.NondeterministicPolynomialSpace

/-- The trivial direction: a deterministic polynomial-space decider is a nondeterministic one. -/
theorem PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE :=
  Complexity.ClassesProofs.BasicProperties.PSPACE_subset_NPSPACE

/-- Savitch's theorem, inclusion form: every language decided by a nondeterministic
polynomial-space machine is decided by a deterministic one. -/
theorem NPSPACE_subset_PSPACE : NPSPACE ⊆ PSPACE := by
  rw [Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE]

/-- Savitch's theorem as an equality, restated from the port. -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE :=
  Complexity.Classes.PolynomialSpaceEquality.PSPACE_eq_NPSPACE

end Complexity.Savitch
