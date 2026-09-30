
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

/-! ## Milestone 3 statements

The modular `j`-function and its `q`-expansion, restated in textbook form. -/

section Milestone3
open UpperHalfPlane ModularForm MatrixGroups Complexity.Modular

/-- `j = E₄³ / Δ` with Mathlib's `Δ = η²⁴ = q ∏ (1 − qⁿ)²⁴`; the defining equation. -/
example : ∀ z : ℍ, j z * ModularForm.discriminant z = E₄ z ^ 3 := j_mul_discriminant

/-- The defining equation with the discriminant normalised as `E₄³ − E₆² (= 1728 Δ)`. -/
example : ∀ z : ℍ, j z * (E₄ z ^ 3 - E₆ z ^ 2) = 1728 * E₄ z ^ 3 := j_mul_E₄_cube_sub_E₆_sq
example : ∀ z : ℍ, j z = 1728 * E₄ z ^ 3 / (E₄ z ^ 3 - E₆ z ^ 2) := j_eq_E₄_cube_sub_E₆_sq

/-- Invariance under the full modular group. -/
example : ∀ (γ : SL(2, ℤ)) (z : ℍ), j (γ • z) = j z := j_SL_smul
example : ∀ γ : SL(2, ℤ), j ∣[(0 : ℤ)] γ = j := j_slash_invariant

/-- Stage (a): `q · j` extends holomorphically to the open unit disc with value `1` at `q = 0`. -/
example : cuspFunction 1 qj 0 = 1 := cuspFunction_qj_zero
example : DifferentiableOn ℂ (cuspFunction 1 qj) (Metric.ball 0 1) := differentiableOn_cuspFunction_qj
example : (qExpansion 1 qj).coeff 0 = 1 := qExpansion_qj_coeff_zero

/-- The Laurent expansion `j τ = q⁻¹ Σ Q_m qᵐ` converges for every `τ ∈ ℍ`. -/
example : ∀ τ : ℍ,
    HasSum (fun m ↦ (qExpansion 1 qj).coeff m * Function.Periodic.qParam 1 τ ^ m) (Function.Periodic.qParam 1 τ * j τ) :=
  hasSum_qExpansion_qj

/-- Stage (b): the constant term of `j` is `744`. -/
example : (qExpansion 1 qj).coeff 1 = 744 := qExpansion_qj_coeff_one

/-- Stage (c): the coefficient of `q` in `j` is `196884`. -/
example : (qExpansion 1 qj).coeff 2 = 196884 := qExpansion_qj_coeff_two

end Milestone3
