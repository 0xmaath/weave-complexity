/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/CNFRestriction.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.CNFRestriction` to `Complexity.ArcKaylesProofs.CNFRestriction`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.CNFStrategyComparison

namespace Complexity.ArcKaylesProofs

open Complexity.ArcKayles PositiveCNF

/-- Only terminal assignments drawn from the available board matter. -/
theorem cnf_payoff_congr_on (n : ℕ) (cs ds : List (Finset (Fin n)))
    (U T T' : Finset (Fin n)) (turn : Bool)
    (h : ∀ S ⊆ U, Satisfied ⟨n, cs⟩ (T ∪ S) ↔ Satisfied ⟨n, ds⟩ (T' ∪ S)) :
    TrueWins ⟨n, cs⟩ U T turn ↔ TrueWins ⟨n, ds⟩ U T' turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T T' turn with
  | h m ih =>
    by_cases he : U = ∅
    · subst U
      rw [cnf_empty, cnf_empty]
      simpa using h ∅ (Finset.empty_subset _)
    · cases turn
      · rw [cnf_false _ _ _ he, cnf_false _ _ _ he]
        apply forall_congr'; intro x
        apply forall_congr'; intro hx
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ true
          (fun S hS => h S (hS.trans (Finset.erase_subset _ _))) rfl
      · rw [cnf_true _ _ _ he, cnf_true _ _ _ he]
        apply exists_congr; intro x
        apply and_congr_right; intro hx
        apply ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ false ?_ rfl
        intro S hS
        have hi : insert x S ⊆ U := Finset.insert_subset hx (hS.trans (Finset.erase_subset _ _))
        simpa only [Finset.insert_union, Finset.union_insert] using h (insert x S) hi

end Complexity.ArcKaylesProofs
