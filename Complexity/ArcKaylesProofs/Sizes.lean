/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `proofs/Lax689614Proofs/Sizes.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614Proofs.Sizes` to `Complexity.ArcKaylesProofs.Sizes`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.Sizes
import Mathlib.Tactic
import Batteries.Tactic.Alias

namespace Complexity.ArcKaylesProofs

open Complexity.ArcKayles

/--
---
conclusion: Complexity.ArcKayles.Sizes.graph_length
---
-/
theorem graph_length (G : Encoding.Graph) :
    (Encoding.graphWord G).length = G.vertices ^ 2 + G.vertices + 1 := by
  classical
  simp [Encoding.graphWord, List.length_flatMap, pow_two]
  omega

alias _root_.Complexity.ArcKayles.Sizes.graph_length := graph_length

/--
---
conclusion: Complexity.ArcKayles.Sizes.formula_length
---
-/
theorem formula_length (φ : PositiveCNF.Formula) :
    (Encoding.formulaWord φ).length =
      φ.clauses.length * φ.nvars + φ.nvars + φ.clauses.length + 2 := by
  simp [Encoding.formulaWord, List.length_flatMap]
  omega

alias _root_.Complexity.ArcKayles.Sizes.formula_length := formula_length

/--
---
conclusion: Complexity.ArcKayles.Sizes.construction_size
---
-/
theorem construction_size (φ : PositiveCNF.Formula) :
    Construction.size φ = 13 * φ.nvars + 4 * φ.clauses.length + 18 := by
  simp only [Construction.size, Construction.K, Construction.R]
  omega

alias _root_.Complexity.ArcKayles.Sizes.construction_size := construction_size

end Complexity.ArcKaylesProofs
