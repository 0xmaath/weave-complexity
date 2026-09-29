/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/Savitch.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.Savitch` to `Complexity.ClassesProofs.SavitchProofs.Savitch`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchProofs.Configurations
import Complexity.ClassesProofs.SavitchProofs.PolyBounds
import Complexity.ClassesProofs.SavitchProofs.SearchMachine
import Complexity.ClassesProofs.SavitchDefinitions.Savitch
import Complexity.ClassesProofs.SavitchDefinitions.Acceptance
import Complexity.ClassesProofs.SavitchDefinitions.SearchMachine
import Complexity.ClassesProofs.SavitchDefinitions.PolynomialSpace
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassesProofs.SavitchProofs

open Complexity.ClassesProofs.SavitchDefinitions Complexity.ClassesProofs.SavitchDefinitions.SpaceConstructibility
open Complexity.Classes.PolynomialTime Complexity.Classes.SpaceMachines Complexity.Classes.SpaceBounds
open Complexity.Classes.PolynomialSpace Complexity.Classes.NondeterministicPolynomialSpace

/--
Apply the deterministic search machine to a space-bounded nondeterministic decider.
-/
theorem savitch (s : ℕ → ℕ) (hs : Constructible s)
    (hlog : ∀ n, logSpace n ≤ s n) (A : Language) :
    A ∈ NSPACE s → ∃ c : ℕ, 0 < c ∧ A ∈ DSPACE (fun n => c * (s n) ^ 2) := by
  rintro ⟨M, hd, hb⟩
  obtain ⟨c, D, hc, hdet, hD, hspace⟩ := Complexity.ClassesProofs.SavitchProofs.search_machine M s hs hlog hb
  refine ⟨c, hc, D, hdet, ?_, hspace⟩
  · intro w
    exact ⟨(hD w).1, (hD w).2.trans ((Complexity.ClassesProofs.SavitchProofs.search_acceptance M w _ (hb w)).trans (hd w).2)⟩

/--
Enlarge the original polynomial bound to $p(n)+n+2$ and square it.
-/
theorem polynomial_space : PSPACE = NPSPACE := by
  ext A
  constructor
  · rintro ⟨p, M, _, hd, hb⟩
    exact ⟨p, M, hd, hb⟩
  · rintro ⟨p, M, hd, hb⟩
    let s := fun n => p.eval n + n + 2
    have hs : Constructible s := Complexity.ClassesProofs.SavitchProofs.polynomial_constructible p
    have hlog : ∀ n, logSpace n ≤ s n := by
      intro n
      have := Nat.log_le_self 2 (n + 2)
      dsimp [logSpace, s]
      omega
    have hA : A ∈ NSPACE s := by
      refine ⟨M, hd, ?_⟩
      intro w t c hr
      have := hb w t c hr
      change c.workHead < p.eval w.length at this
      dsimp [s]
      omega
    obtain ⟨c, _, D, hdet, hD, hbound⟩ := Complexity.ClassesProofs.SavitchProofs.savitch s hs hlog A hA
    refine ⟨Polynomial.C c * (p + Polynomial.X + Polynomial.C 2) ^ 2, D, hdet, hD, ?_⟩
    intro w
    simpa [s] using hbound w

end Complexity.ClassesProofs.SavitchProofs
