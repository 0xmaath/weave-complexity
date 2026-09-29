/-
Ported from https://github.com/EdouardBonnet/arc-kayles (Lax submission lax-689614, commit dd8b6e67317f),
file `concepts/Lax689614/Encoding.lean`.
Original authors: Édouard Bonnet, gpt-6-astra. Licensed under the Apache License, Version 2.0;
see `LICENSES/arc-kayles.LICENSE`. Modifications for this port: module and namespace
renamed from `Lax689614.Encoding` to `Complexity.ArcKayles.Encoding`; concept-package `axiom` statements
replaced by `alias`es of their proofs; imports adjusted accordingly.
-/
import Complexity.ArcKayles.ArcKayles
import Complexity.ArcKayles.PositiveCNF
import Complexity.Classes.PolynomialTime

/-!
---
title: Binary encodings of graphs and positive CNF formulas
type: definition
---
A graph on $n$ labeled vertices is encoded by $1^n0$ followed by its
$n\times n$ adjacency matrix in row order. A formula on $n$ variables
with $m$ clauses is encoded by $1^n0\,1^m0$ followed by the $m\times n$
clause-variable incidence matrix in row order. These encodings retain
isolated vertices, unused variables, empty clauses, and repeated clauses.
Malformed strings are excluded from the associated languages.
-/

namespace Complexity.ArcKayles.Encoding

open Complexity.Classes.PolynomialTime

structure Graph where
  vertices : ℕ
  graph : SimpleGraph (Fin vertices)

noncomputable def graphWord (G : Graph) : Word := by
  classical
  exact List.replicate G.vertices true ++ [false] ++
    (List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => decide (G.graph.Adj u v)

def formulaWord (φ : PositiveCNF.Formula) : Word :=
  List.replicate φ.nvars true ++ [false] ++
    List.replicate φ.clauses.length true ++ [false] ++
    φ.clauses.flatMap fun C =>
      (List.finRange φ.nvars).map fun x => decide (x ∈ C)

def arcKayles : Language :=
  {w | ∃ G : Graph, graphWord G = w ∧ ArcKayles.Winning G.graph Finset.univ}

def positiveCNF : Language :=
  {w | ∃ φ : PositiveCNF.Formula, formulaWord φ = w ∧ PositiveCNF.FirstWins φ}

end Complexity.ArcKayles.Encoding
