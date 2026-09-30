/-
Milestone 3: the classical modular `j`-function.

`j = E₄³ / Δ`, where `E₄` is Mathlib's normalised weight-4 Eisenstein series
(`ModularForm.E₄`, constant term `1`) and `Δ = η²⁴` is Mathlib's modular
discriminant (`ModularForm.discriminant`, leading coefficient `1`).

Normalisation. Serre (A Course in Arithmetic, ch. VII, §3.3 and §4.4) writes
`j = 1728 g₂³ / Δ` with `g₂ = 60 G₂` and `Δ = g₂³ − 27 g₃²`; there
`g₂ = (2π)⁴/12 · E₄` and `Δ = (2π)¹² · q ∏ (1 − qⁿ)²⁴`, so the two
`(2π)¹²` factors cancel and `1728 g₂³ / Δ = E₄³ / (q ∏ (1 − qⁿ)²⁴)`.  With
Mathlib's `discriminant` (already divided by `(2π)¹²`) the classical function
is therefore `E₄ ^ 3 / discriminant`; the literal expression
`1728 * E₄ ^ 3 / discriminant` would be `1728 · j`, contradicting the
expansion `q⁻¹ + 744 + 196884 q + …` that this milestone establishes.  The
factor `1728` reappears in the equivalent form
`j = 1728 E₄³ / (E₄³ − E₆²)` (`j_eq_E₄_cube_sub_E₆_sq`), since
`1728 Δ = E₄³ − E₆²` (`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`).
-/
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

open UpperHalfPlane ModularForm MatrixGroups

noncomputable section

namespace Complexity.Modular

/-- The modular `j`-function, `j = E₄³ / Δ` (Serre ch. VII §3.3, Apostol ch. 1 §1.12). -/
def j (z : ℍ) : ℂ := E₄ z ^ 3 / ModularForm.discriminant z

/-- Well-definedness: the denominator of `j` never vanishes on `ℍ`. -/
theorem discriminant_ne_zero (z : ℍ) : ModularForm.discriminant z ≠ 0 :=
  ModularForm.discriminant_ne_zero z

/-- The defining equation `j · Δ = E₄³`. -/
theorem j_mul_discriminant (z : ℍ) : j z * ModularForm.discriminant z = E₄ z ^ 3 := by
  unfold j
  field_simp [ModularForm.discriminant_ne_zero z]

/-- The defining equation in Serre's normalisation of the discriminant,
`1728 Δ = E₄³ − E₆²`: `j · (E₄³ − E₆²) = 1728 E₄³`. -/
theorem j_mul_E₄_cube_sub_E₆_sq (z : ℍ) :
    j z * (E₄ z ^ 3 - E₆ z ^ 2) = 1728 * E₄ z ^ 3 := by
  have h := discriminant_eq_E₄_cube_sub_E₆_sq z
  have h2 := j_mul_discriminant z
  rw [h] at h2
  linear_combination 1728 * h2

/-- `E₄ z ^ 3 - E₆ z ^ 2 ≠ 0` on `ℍ`. -/
theorem E₄_cube_sub_E₆_sq_ne_zero (z : ℍ) : E₄ z ^ 3 - E₆ z ^ 2 ≠ 0 := by
  intro h
  have h1 := discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [h, zero_div] at h1
  exact ModularForm.discriminant_ne_zero z h1

/-- `j = 1728 E₄³ / (E₄³ − E₆²)`. -/
theorem j_eq_E₄_cube_sub_E₆_sq (z : ℍ) :
    j z = 1728 * E₄ z ^ 3 / (E₄ z ^ 3 - E₆ z ^ 2) := by
  rw [eq_div_iff (E₄_cube_sub_E₆_sq_ne_zero z)]
  exact j_mul_E₄_cube_sub_E₆_sq z

/-- The `j`-function is uniquely determined by the defining equation. -/
theorem eq_j_of_mul_discriminant {f : ℍ → ℂ}
    (hf : ∀ z, f z * ModularForm.discriminant z = E₄ z ^ 3) : f = j := by
  funext z
  have := hf z
  rw [← j_mul_discriminant z] at this
  exact mul_right_cancel₀ (ModularForm.discriminant_ne_zero z) this

section invariance

/-- Transformation law of `E₄` under `SL(2, ℤ)`. -/
theorem E₄_SL_smul (γ : SL(2, ℤ)) (z : ℍ) :
    E₄ (γ • z) = denom γ z ^ (4 : ℤ) * E₄ z := by
  have h : (⇑E₄ ∣[(4 : ℤ)] γ) z = E₄ z :=
    congr_fun (SlashInvariantForm.slash_action_eqn E₄
      (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩) z
  rw [SL_slash_apply, zpow_neg] at h
  rw [← h]
  field_simp [zpow_ne_zero (4 : ℤ) (denom_ne_zero γ z)]

/-- Transformation law of `Δ` under `SL(2, ℤ)`. -/
theorem discriminant_SL_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ModularForm.discriminant (γ • z) = denom γ z ^ (12 : ℤ) * ModularForm.discriminant z := by
  have h : (⇑CuspForm.discriminant ∣[(12 : ℤ)] γ) z = CuspForm.discriminant z :=
    congr_fun (SlashInvariantForm.slash_action_eqn CuspForm.discriminant
      (Matrix.SpecialLinearGroup.mapGL ℝ γ) ⟨γ, rfl⟩) z
  rw [SL_slash_apply, zpow_neg, CuspForm.coe_discriminant] at h
  rw [← h]
  field_simp [zpow_ne_zero (12 : ℤ) (denom_ne_zero γ z)]

/-- Invariance of `j` under the full modular group: the weight `12 = 3 · 4` cancels. -/
theorem j_SL_smul (γ : SL(2, ℤ)) (z : ℍ) : j (γ • z) = j z := by
  unfold j
  rw [E₄_SL_smul, discriminant_SL_smul, mul_pow, ← zpow_natCast, ← zpow_mul]
  have hd : denom γ z ^ ((4 : ℤ) * (3 : ℕ)) ≠ 0 := zpow_ne_zero _ (denom_ne_zero γ z)
  have h12 : ((4 : ℤ) * (3 : ℕ) : ℤ) = 12 := by norm_num
  rw [h12] at hd ⊢
  field_simp [hd, ModularForm.discriminant_ne_zero z]

/-- `j` is a weight-`0` slash-invariant function. -/
theorem j_slash_invariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  ext z
  rw [SL_slash_apply, j_SL_smul, neg_zero, zpow_zero, mul_one]

/-- Translation invariance `j (z + 1) = j z`. -/
theorem j_vadd_one (z : ℍ) : j ((1 : ℝ) +ᵥ z) = j z := by
  rw [← modular_T_smul, j_SL_smul]

/-- Inversion invariance `j (-1 / z) = j z`. -/
theorem j_neg_inv (z : ℍ) : j (ModularGroup.S • z) = j z := j_SL_smul _ z

end invariance

end Complexity.Modular
