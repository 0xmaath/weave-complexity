/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/GraphEncoding.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.GraphEncoding` to `Complexity.ArcKaylesProofs.GraphEncoding`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKaylesProofs.FormulaParser

namespace Complexity.ArcKaylesProofs

open Complexity.ArcKayles Encoding
open scoped Classical

noncomputable def graphRows (G : Graph) : List (Finset (Fin G.vertices)) :=
  (List.finRange G.vertices).map fun u => Finset.univ.filter fun v => G.graph.Adj u v

theorem graphRows_length (G : Graph) : (graphRows G).length = G.vertices := by simp [graphRows]

theorem graphWord_rows (G : Graph) : graphWord G =
    List.replicate G.vertices true ++ false :: (graphRows G).flatMap clauseBits := by
  simp [graphWord, graphRows, clauseBits, List.append_assoc, List.flatMap_map,
    List.map_map, Function.comp_def]

theorem graphWord_injective : Function.Injective graphWord := by
  intro G H he
  rw [graphWord_rows, graphWord_rows] at he
  have hu := congrArg readUnary he
  rw [readUnary_prefix, readUnary_prefix] at hu
  have hp := Option.some.inj hu
  have hn := congrArg Prod.fst hp
  have hw := congrArg Prod.snd hp
  cases G with
  | mk n g =>
    cases H with
    | mk m h =>
      dsimp only at hn hw
      subst m
      have hr := congrArg (readClauses n n) hw
      have readRows (G : Graph) : readClauses G.vertices G.vertices
          ((graphRows G).flatMap clauseBits) = some (graphRows G, []) := by
        have hp := readClauses_prefix (graphRows G) []
        simpa only [graphRows_length, List.append_nil] using hp
      rw [readRows ⟨n, g⟩, readRows ⟨n, h⟩] at hr
      have hrows := congrArg Prod.fst (Option.some.inj hr)
      have hgraph : g = h := by
        ext u v
        change (List.finRange n).map (fun u => Finset.univ.filter (g.Adj u)) =
          (List.finRange n).map (fun u => Finset.univ.filter (h.Adj u)) at hrows
        have hu := List.map_inj_left.mp hrows u (by simp)
        have hv := congrArg (fun C : Finset (Fin n) => v ∈ C) hu
        simpa using Iff.of_eq hv
      subst h
      rfl

theorem graphWord_mem (G : Graph) : graphWord G ∈ arcKayles ↔
    ArcKayles.Winning G.graph Finset.univ := by
  constructor
  · rintro ⟨H, he, hw⟩
    exact graphWord_injective he ▸ hw
  · intro hw; exact ⟨G, rfl, hw⟩

end Complexity.ArcKaylesProofs
