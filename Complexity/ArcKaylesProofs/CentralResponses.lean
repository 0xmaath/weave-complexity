/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/CentralResponses.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.CentralResponses` to `Complexity.ArcKaylesProofs.CentralResponses`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.ProtectedPositions
import Complexity.ArcKaylesProofs.Grundy

namespace Complexity.ArcKaylesProofs

open Complexity.ArcKayles PositiveCNF ArcKayles Grundy Biclique

theorem winning_of_value_ne_zero {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (h : value G S ≠ 0) : Winning G S := by
  by_contra hn
  exact h ((GrundyProperties.losing_iff_zero G S).mp hn)

theorem winning_of_zero_reply {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (he : G.Adj u v)
    (hz : value G (remove S u v) = 0) : Winning G S :=
  (winning_iff_move G S).mpr ⟨u, hu, v, hv, he, (GrundyProperties.losing_iff_zero G _).mpr hz⟩

theorem high_xor_nonzero (a k : ℕ) (ha : a = 2 ∨ a = 3) : Nat.xor a (k % 2) ≠ 0 := by
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hk with hk | hk <;> rw [hk] <;> decide

theorem central_t_winning {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (hmin : min (liveB S).card (liveV S).card % 2 = 1) :
    Winning (vertexGraph φ) (remove S .s .t) := by
  apply winning_of_value_ne_zero
  rw [central_t_value S h]
  apply high_xor_nonzero
  unfold g
  omega

theorem central_y_winning {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (i : Fin (Construction.K φ))
    (hmin : min (liveB S).card (liveV S).card % 2 = 1) :
    Winning (vertexGraph φ) (remove S .s (.y i)) := by
  apply winning_of_value_ne_zero
  rw [central_y_value S h i]
  apply high_xor_nonzero
  unfold g
  omega

theorem central_reply_wins {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (hs : Vertex.s ∈ S) (ht : Vertex.t ∈ S) (hk : 0 < (liveY S).card)
    (hmin : min (liveB S).card (liveV S).card % 2 = 0) :
    Winning (vertexGraph φ) S := by
  have hg : g (liveB S).card (liveV S).card =
      ((liveB S).card + (liveV S).card) % 2 := by simp [g, hmin]
  by_cases hz : ((liveB S).card + (liveV S).card + (liveY S).card) % 2 = 0
  · apply winning_of_zero_reply (vertexGraph φ) S .s .t hs ht
      ((adj_s (.t : Vertex φ)).mpr (Or.inl rfl))
    rw [central_t_value S h, hg, parity_xor]
    exact hz
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp hk
    have hiS : Vertex.y i ∈ S := (Finset.mem_filter.mp hi).2
    apply winning_of_zero_reply (vertexGraph φ) S .s (.y i) hs hiS
      ((adj_s (.y i)).mpr (Or.inr (Or.inr ⟨i, rfl⟩)))
    rw [central_y_value S h i, Finset.card_erase_of_mem hi, hg, parity_xor]
    omega

end Complexity.ArcKaylesProofs
