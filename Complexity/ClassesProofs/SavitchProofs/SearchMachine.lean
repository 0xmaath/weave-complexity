/-
Ported from https://github.com/EdouardBonnet/classical-complexity (Lax submission lax-434930, commit 0c0840319318),
file `proofs/Lax434930Proofs/SavitchProofs/SearchMachine.lean`.
Original authors: Édouard Bonnet, Codex 5.6 and 6. Licensed under the Apache License, Version 2.0;
see `LICENSES/classical-complexity.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax434930Proofs.SavitchProofs.SearchMachine` to `Complexity.ClassesProofs.SavitchProofs.SearchMachine`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ClassesProofs.SavitchProofs.Configurations
import Complexity.ClassesProofs.SavitchProofs.ConstructedSearch
import Complexity.ClassesProofs.SavitchDefinitions.SearchMachine
import Complexity.ClassesProofs.SavitchDefinitions.Acceptance

set_option backward.isDefEq.respectTransparency false

namespace Complexity.ClassesProofs.SavitchProofs

open Complexity.ClassesProofs.SavitchDefinitions Complexity.ClassesProofs.SavitchDefinitions.SpaceConstructibility
open Complexity.Classes.PolynomialTime Complexity.Classes.SpaceMachines Complexity.Classes.SpaceBounds

/--
Compose the space constructor, configuration query, and stack search.
The stack compiler supplies a deterministic machine in the original tape model.
-/
lemma search_machine (M : Machine) (s : ℕ → ℕ) (hs : Constructible s)
    (hlog : ∀ n, logSpace n ≤ s n)
    (hM : ∀ w, M.UsesSpace w (s w.length)) :
    ∃ (c : ℕ) (D : Machine), 0 < c ∧ D.Deterministic ∧
      (∀ w, D.HaltsOn w ∧ (D.Accepts w ↔ ConfigurationGraph.SearchAccepts M w (s w.length))) ∧
      ∀ w, D.UsesSpace w (c * (s w.length) ^ 2) := by
  obtain ⟨B, hdet, hB⟩ := hs
  refine ⟨ConstructedSearch.spaceConstant M, ConstructedSearch.machine M B,
    ConstructedSearch.spaceConstant_pos M, ConstructedSearch.deterministic M B, ?_, ?_⟩
  · intro w
    have he := ConstructedSearch.execution M B w (s w.length) hdet
      (hB w).2.1 (hB w).2.2 (hlog _) (hM w)
    exact ⟨he.1, he.2.2.trans (Complexity.ClassesProofs.SavitchProofs.search_acceptance M w _ (hM w)).symm⟩
  · intro w t c hc
    have he := ConstructedSearch.execution M B w (s w.length) hdet
      (hB w).2.1 (hB w).2.2 (hlog _) (hM w)
    have hpos : 0 < s w.length := hM w 0 M.initial .zero
    exact (he.2.1 t c hc).trans_le (ConstructedSearch.quadratic M _ hpos)

end Complexity.ClassesProofs.SavitchProofs
