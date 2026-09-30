/-
Milestone 3: the first few `q`-expansion coefficients of `E₄`, `E₆` and `Δ`.

`E₄ = 1 + 240 Σ σ₃(n) qⁿ`, `E₆ = 1 − 504 Σ σ₅(n) qⁿ` (Serre ch. VII §4.2, Apostol
Theorem 1.18) come from Mathlib's `EisensteinSeries.E_qExpansion_coeff`; the
coefficients `τ(1) = 1, τ(2) = −24, τ(3) = 252` of `Δ = Σ τ(n) qⁿ` (Serre ch. VII
§4.5, Apostol §1.14) are derived from `1728 Δ = E₄³ − E₆²`
(`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`) by multiplying the two
Eisenstein expansions, independently of the product formula
`Δ = q ∏ (1 − qⁿ)²⁴` that Mathlib uses to define `Δ`.
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

noncomputable section

namespace Complexity.Modular

/-! ### Divisor sums and Bernoulli numbers -/

theorem sigma_three_two : σ 3 2 = 9 := by decide
theorem sigma_three_three : σ 3 3 = 28 := by decide
theorem sigma_five_two : σ 5 2 = 33 := by decide
theorem sigma_five_three : σ 5 3 = 244 := by decide
theorem bernoulli_four : bernoulli 4 = -1 / 30 := by decide +kernel
theorem bernoulli_six : bernoulli 6 = 1 / 42 := by decide +kernel

/-! ### `E₄ = 1 + 240 q + 2160 q² + 6720 q³ + …` -/

/-- `E₄ = 1 + 240 Σ σ₃(m) qᵐ`. -/
theorem E₄_coeff (m : ℕ) :
    (qExpansion 1 E₄).coeff m = if m = 0 then 1 else 240 * (σ 3 m : ℂ) := by
  rw [E_qExpansion_coeff (by norm_num) ⟨2, rfl⟩ m]
  norm_num [bernoulli_four]

theorem E₄_coeff_zero : (qExpansion 1 E₄).coeff 0 = 1 := by simp [E₄_coeff]
theorem E₄_coeff_one : (qExpansion 1 E₄).coeff 1 = 240 := by simp [E₄_coeff]
theorem E₄_coeff_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  norm_num [E₄_coeff, sigma_three_two]
theorem E₄_coeff_three : (qExpansion 1 E₄).coeff 3 = 6720 := by
  norm_num [E₄_coeff, sigma_three_three]

/-! ### `E₆ = 1 − 504 q − 16632 q² − 122976 q³ − …` -/

/-- `E₆ = 1 − 504 Σ σ₅(m) qᵐ`. -/
theorem E₆_coeff (m : ℕ) :
    (qExpansion 1 E₆).coeff m = if m = 0 then 1 else -504 * (σ 5 m : ℂ) := by
  rw [E_qExpansion_coeff (by norm_num) ⟨3, rfl⟩ m]
  norm_num [bernoulli_six]

theorem E₆_coeff_zero : (qExpansion 1 E₆).coeff 0 = 1 := by simp [E₆_coeff]
theorem E₆_coeff_one : (qExpansion 1 E₆).coeff 1 = -504 := by simp [E₆_coeff]
theorem E₆_coeff_two : (qExpansion 1 E₆).coeff 2 = -16632 := by
  norm_num [E₆_coeff, sigma_five_two]
theorem E₆_coeff_three : (qExpansion 1 E₆).coeff 3 = -122976 := by
  norm_num [E₆_coeff, sigma_five_three]

/-! ### `E₄³ = 1 + 720 q + 179280 q² + 16954560 q³ + …` and `E₆² = 1 − 1008 q + 220752 q² + 16519104 q³ + …` -/

theorem E₄_cube_coeff_zero : (qExpansion 1 E₄ ^ 3).coeff 0 = 1 := by
  rw [show qExpansion 1 E₄ ^ 3 = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ by ring]
  norm_num [PowerSeries.coeff_mul, E₄_coeff_zero]

theorem E₄_cube_coeff_one : (qExpansion 1 E₄ ^ 3).coeff 1 = 720 := by
  rw [show qExpansion 1 E₄ ^ 3 = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ by ring]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_coeff_zero, E₄_coeff_one]

theorem E₄_cube_coeff_two : (qExpansion 1 E₄ ^ 3).coeff 2 = 179280 := by
  rw [show qExpansion 1 E₄ ^ 3 = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ by ring]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_coeff_zero, E₄_coeff_one,
    E₄_coeff_two]

theorem E₄_cube_coeff_three : (qExpansion 1 E₄ ^ 3).coeff 3 = 16954560 := by
  rw [show qExpansion 1 E₄ ^ 3 = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ by ring]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_coeff_zero, E₄_coeff_one,
    E₄_coeff_two, E₄_coeff_three]

theorem E₆_sq_coeff_two : (qExpansion 1 E₆ ^ 2).coeff 2 = 220752 := by
  rw [show qExpansion 1 E₆ ^ 2 = qExpansion 1 E₆ * qExpansion 1 E₆ by ring]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₆_coeff_zero, E₆_coeff_one,
    E₆_coeff_two]

theorem E₆_sq_coeff_three : (qExpansion 1 E₆ ^ 2).coeff 3 = 16519104 := by
  rw [show qExpansion 1 E₆ ^ 2 = qExpansion 1 E₆ * qExpansion 1 E₆ by ring]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₆_coeff_zero, E₆_coeff_one,
    E₆_coeff_two, E₆_coeff_three]

/-! ### `Δ = q − 24 q² + 252 q³ + …` -/

/-- `1728 · (q-expansion of Δ) = (q-expansion of E₄)³ − (q-expansion of E₆)²`. -/
theorem discriminant_qExpansion_smul :
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  have hΔ : AnalyticAt ℂ (cuspFunction 1 ModularForm.discriminant) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
  have hE4 : AnalyticAt ℂ (cuspFunction 1 (E₄.pow 3)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL
  have hE6 : AnalyticAt ℂ (cuspFunction 1 (E₆.pow 2)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL
  have hfun : (1728 : ℂ) • (ModularForm.discriminant : ℍ → ℂ) = ⇑(E₄.pow 3) - ⇑(E₆.pow 2) := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, coe_pow, Pi.pow_apply, smul_eq_mul,
      discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← qExpansion_smul hΔ, hfun, qExpansion_sub hE4 hE6,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem discriminant_coeff_zero : (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL

theorem discriminant_coeff_one : (qExpansion 1 ModularForm.discriminant).coeff 1 = 1 :=
  discriminant_qExpansion_coeff_one

/-- `τ(2) = −24`. -/
theorem discriminant_coeff_two : (qExpansion 1 ModularForm.discriminant).coeff 2 = -24 := by
  have h := congr_arg (PowerSeries.coeff 2) discriminant_qExpansion_smul
  rw [PowerSeries.coeff_smul, map_sub, E₄_cube_coeff_two, E₆_sq_coeff_two, smul_eq_mul] at h
  linear_combination h / 1728

/-- `τ(3) = 252`. -/
theorem discriminant_coeff_three : (qExpansion 1 ModularForm.discriminant).coeff 3 = 252 := by
  have h := congr_arg (PowerSeries.coeff 3) discriminant_qExpansion_smul
  rw [PowerSeries.coeff_smul, map_sub, E₄_cube_coeff_three, E₆_sq_coeff_three, smul_eq_mul] at h
  linear_combination h / 1728

end Complexity.Modular
