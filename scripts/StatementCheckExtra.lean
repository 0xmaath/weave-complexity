
/-! ## Milestone 2 statements

Textbook restatements of the new theorems, checked against the declarations that carry them. -/

section Milestone2
open Complexity.Classes.PolynomialTime Complexity.Classes.PolynomialSpace
open Complexity.Classes.NondeterministicPolynomialSpace

/-- Savitch's theorem, inclusion form. -/
example : NPSPACE ⊆ PSPACE := Complexity.Savitch.NPSPACE_subset_PSPACE
example : PSPACE = NPSPACE := Complexity.Savitch.PSPACE_eq_NPSPACE

/-- The game template: every polynomially bounded normal-play game with computable moves has
its winner-determination language in PSPACE. -/
example : ∀ G : Complexity.Games.Game, G.language ∈ PSPACE :=
  Complexity.Games.Game.language_mem_PSPACE

/-- Normal-play recursion of the template's winning positions. -/
example : ∀ (G : Complexity.Games.Game) (w p : Word), G.Bounded w p →
    (G.Winning w p ↔ ∃ q, G.Move w p q ∧ ¬ G.Winning w q) :=
  fun G w p hp => G.winning_iff hp

/-- Every closed QBF has a word, and every valid word is the word of a closed QBF. -/
example : ∀ φ : Complexity.QBF.Formula, φ.Closed → Complexity.QBF.decode (Complexity.QBF.encode φ) = some φ :=
  Complexity.QBF.decode_encode
example : ∀ (w : Word) (φ : Complexity.QBF.Formula), Complexity.QBF.decode w = some φ → φ.Closed :=
  fun _ _ h => Complexity.QBF.decode_closed h

/-- TQBF is the set of words decoding to a true QBF, and it is the language of the formula game. -/
example : Complexity.QBF.TQBF = {w | ∃ φ : Complexity.QBF.Formula, Complexity.QBF.decode w = some φ ∧ φ.IsTrue} :=
  rfl
example : Complexity.QBF.TQBFGame.game.language = Complexity.QBF.TQBF :=
  Complexity.QBF.TQBFGame.language_eq

/-- TQBF is in PSPACE, PSPACE-hard under polynomial-time many-one reductions, hence complete. -/
example : Complexity.QBF.TQBF ∈ PSPACE := Complexity.QBF.TQBF_mem_PSPACE
example : ∀ A : Language, A ∈ PSPACE → Complexity.CookLevin.Reductions.ManyOne A Complexity.QBF.TQBF :=
  Complexity.QBF.TQBF_hard
example : Complexity.QBF.TQBF ∈ PSPACE ∧
    ∀ A : Language, A ∈ PSPACE → Complexity.CookLevin.Reductions.ManyOne A Complexity.QBF.TQBF :=
  Complexity.QBF.TQBF_complete

end Milestone2
