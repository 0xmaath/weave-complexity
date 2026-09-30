/-
Milestone 3: the `q`-expansion of the modular `j`-function,

  `j = q⁻¹ + 744 + 196884 q + …`   (`q = e^{2πiτ}`),

Serre, A Course in Arithmetic, ch. VII §4.5 (`j = q⁻¹ + 744 + Σ c(n) qⁿ`, `c(1) = 196884`);
Apostol, Modular Functions and Dirichlet Series, §1.15 (Theorem 1.20).

Since `j` has a pole at the cusp, Mathlib's `cuspFunction`/`qExpansion` machinery is
applied to the holomorphic, `1`-periodic, bounded function `qj τ = 𝕢 τ · j τ`; its
cusp function is the regular function `q ↦ E₄c(q)³ / ∏ (1 − qⁿ)²⁴` on the open unit
disc (`cuspFunction_qj_eqOn`), which is the precise sense in which "`q · j` extends
holomorphically to `q = 0` with value `1`" (stage (a)).  Its power series `Q` satisfies
`Q · P = X · A³` where `P`, `A` are the expansions of `Δ`, `E₄` (`qExpansion_qj_mul`),
and comparing coefficients with `P = q − 24 q² + 252 q³ + …`, `A³ = 1 + 720 q + 179280 q² + …`
gives `Q = 1 + 744 q + 196884 q² + …` (stages (b) and (c)).  The Laurent expansion
`j τ = q⁻¹ Σ Q_m qᵐ` is `hasSum_qExpansion_qj` / `j_eq_tsum`.
-/
import Complexity.Modular.J
import Complexity.Modular.Coefficients

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups Complex Filter Function Metric Set
open scoped Topology Manifold

local notation "𝕢" => Periodic.qParam

noncomputable section

namespace Complexity.Modular

/-! ### The regular part of `j` at the cusp -/

/-- `q · j`: the function on `ℍ` whose cusp function is the regular part of `j` at `∞`. -/
def qj (τ : ℍ) : ℂ := 𝕢 1 τ * j τ

/-- The Euler-product factor `u(q) = ∏ (1 − q^{n+1})²⁴`, so that `cuspFunction 1 Δ = q · u`. -/
def deltaProd (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

/-- The regular part of `j` as a function of `q`: `E₄c(q)³ / u(q)`. -/
def jReg (q : ℂ) : ℂ := cuspFunction 1 E₄ q ^ 3 / deltaProd q

theorem deltaProd_zero : deltaProd 0 = 1 := by
  simp [deltaProd]

theorem cuspFunction_discriminant_eq {q : ℂ} (hq : ‖q‖ < 1) :
    cuspFunction 1 ModularForm.discriminant q = q * deltaProd q :=
  discriminant_cuspFunction_eqOn (mem_ball_zero_iff.mpr hq)

theorem deltaProd_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : deltaProd q ≠ 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [deltaProd_zero]
  · intro h
    have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0
    have h1 : cuspFunction 1 ModularForm.discriminant q = ModularForm.discriminant ⟨_, him⟩ := by
      simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0, ofComplex_apply_of_im_pos him]
    rw [cuspFunction_discriminant_eq hq, h, mul_zero] at h1
    exact ModularForm.discriminant_ne_zero _ h1.symm

theorem differentiableOn_deltaProd : DifferentiableOn ℂ deltaProd (ball 0 1) :=
  differentiableOn_tprod_one_sub_pow_pow 24

theorem differentiableOn_cuspFunction_E₄ : DifferentiableOn ℂ (cuspFunction 1 E₄) (ball 0 1) :=
  fun _ hq ↦ (ModularFormClass.differentiableAt_cuspFunction E₄ one_pos one_mem_strictPeriods_SL
    (mem_ball_zero_iff.mp hq)).differentiableWithinAt

theorem differentiableOn_jReg : DifferentiableOn ℂ jReg (ball 0 1) :=
  (differentiableOn_cuspFunction_E₄.pow 3).div differentiableOn_deltaProd
    fun _ hq ↦ deltaProd_ne_zero (mem_ball_zero_iff.mp hq)

theorem continuousAt_jReg_zero : ContinuousAt jReg 0 :=
  (differentiableOn_jReg.differentiableAt (ball_mem_nhds 0 one_pos)).continuousAt

theorem cuspFunction_E₄_zero : cuspFunction 1 E₄ 0 = 1 := by
  have h := E₄_coeff_zero
  simpa [qExpansion_coeff] using h

theorem jReg_zero : jReg 0 = 1 := by
  simp [jReg, cuspFunction_E₄_zero, deltaProd_zero]

/-- `q · j(τ) = jReg (𝕢 τ)`: the regular part evaluated at `q = e^{2πiτ}`. -/
theorem qj_eq_jReg (τ : ℍ) : qj τ = jReg (𝕢 1 τ) := by
  have hq : ‖𝕢 1 τ‖ < 1 := Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hE : cuspFunction 1 E₄ (𝕢 1 τ) = E₄ τ :=
    SlashInvariantFormClass.eq_cuspFunction E₄ τ one_mem_strictPeriods_SL one_ne_zero
  have hΔ : cuspFunction 1 ModularForm.discriminant (𝕢 1 τ) = ModularForm.discriminant τ :=
    SlashInvariantFormClass.eq_cuspFunction CuspForm.discriminant τ one_mem_strictPeriods_SL
      one_ne_zero
  rw [cuspFunction_discriminant_eq hq] at hΔ
  have hu := deltaProd_ne_zero hq
  have hq0 : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero (τ : ℂ)
  unfold qj jReg j
  rw [hE, ← hΔ]
  field_simp

/-! ### Transfer to the cusp function -/

/-- If `f τ = H (𝕢 τ)` on `ℍ` and `H` is continuous at `0`, then the cusp function of `f`
is `H` on the open unit disc (including the non-canonical value at `0`). -/
theorem cuspFunction_eqOn_of_comp {f : ℍ → ℂ} {H : ℂ → ℂ} (hf : ∀ τ, f τ = H (𝕢 1 τ))
    (hH : ContinuousAt H 0) : EqOn (cuspFunction 1 f) H (ball 0 1) := by
  have hne : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → cuspFunction 1 f q = H q := by
    intro q hq hq0
    have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq hq0
    rw [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ hq0, comp_apply,
      ofComplex_apply_of_im_pos him, hf]
    congr 1
    exact Periodic.qParam_right_inv one_ne_zero hq0
  intro q hq
  rw [mem_ball_zero_iff] at hq
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [cuspFunction, Periodic.cuspFunction, update_self]
    refine Tendsto.limUnder_eq ((tendsto_nhdsWithin_of_tendsto_nhds hH.tendsto).congr' ?_)
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds (0 : ℂ) one_pos)] with x hx0 hx
    have hx0' : x ≠ 0 := hx0
    rw [← hne x (mem_ball_zero_iff.mp hx) hx0']
    exact Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ ofComplex) hx0'
  · exact hne q hq hq0

/-- **Stage (a).** The cusp function of `q · j` is the regular function `jReg` on the
open unit disc. -/
theorem cuspFunction_qj_eqOn : EqOn (cuspFunction 1 qj) jReg (ball 0 1) :=
  cuspFunction_eqOn_of_comp qj_eq_jReg continuousAt_jReg_zero

/-- **Stage (a).** `q · j` extends to `q = 0` with value `1`. -/
theorem cuspFunction_qj_zero : cuspFunction 1 qj 0 = 1 := by
  rw [cuspFunction_qj_eqOn (mem_ball_self one_pos), jReg_zero]

/-- **Stage (a).** The extension is holomorphic on the open unit disc. -/
theorem differentiableOn_cuspFunction_qj :
    DifferentiableOn ℂ (cuspFunction 1 qj) (ball 0 1) :=
  differentiableOn_jReg.congr cuspFunction_qj_eqOn

theorem analyticAt_cuspFunction_qj : AnalyticAt ℂ (cuspFunction 1 qj) 0 :=
  differentiableOn_cuspFunction_qj.analyticAt (ball_mem_nhds 0 one_pos)

/-- **Stage (a)**, coefficient form: the constant term of the expansion of `q · j` is `1`,
i.e. `j` has a simple pole with residue `1` at the cusp. -/
theorem qExpansion_qj_coeff_zero : (qExpansion 1 qj).coeff 0 = 1 := by
  simpa [qExpansion_coeff] using cuspFunction_qj_zero

/-! ### `q · j` is periodic, holomorphic and bounded at `∞` -/

theorem qParam_add_one (w : ℂ) : 𝕢 1 (w + 1) = 𝕢 1 w := by
  simp only [Periodic.qParam, ofReal_one, div_one, mul_add, mul_one]
  exact Complex.exp_periodic _

theorem qj_periodic : Periodic (qj ∘ ofComplex) 1 := by
  intro w
  show (qj ∘ ofComplex) (w + 1) = (qj ∘ ofComplex) w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw, qj_eq_jReg]
    exact congrArg jReg (qParam_add_one w)
  · rw [not_lt] at hw
    simp only [comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hw) hw]

theorem qj_mdiff : MDiff qj := by
  rw [mdifferentiable_iff]
  have hE : DifferentiableOn ℂ (⇑E₄ ∘ ofComplex) {z | 0 < z.im} :=
    mdifferentiable_iff.mp (ModularFormClass.holo E₄)
  have hΔ : DifferentiableOn ℂ (ModularForm.discriminant ∘ ofComplex) {z | 0 < z.im} :=
    mdifferentiable_iff.mp (ModularFormClass.holo CuspForm.discriminant)
  have hq : DifferentiableOn ℂ (𝕢 1) {z | 0 < z.im} :=
    Periodic.differentiable_qParam.differentiableOn
  refine ((hq.mul (hE.pow 3)).div hΔ ?_).congr ?_
  · intro z hz
    simp only [comp_apply, ofComplex_apply_of_im_pos hz]
    exact ModularForm.discriminant_ne_zero _
  · intro z hz
    simp only [comp_apply, Pi.div_apply, Pi.mul_apply, Pi.pow_apply, ofComplex_apply_of_im_pos hz,
      qj, j]
    ring

/-- `q · j → 1` at the cusp. -/
theorem qj_tendsto : Tendsto qj atImInfty (𝓝 1) := by
  have h1 : Tendsto (fun τ : ℍ ↦ 𝕢 1 τ) atImInfty (𝓝 0) := qParam_tendsto_atImInfty one_pos
  have h2 := continuousAt_jReg_zero.tendsto.comp h1
  rw [jReg_zero] at h2
  exact h2.congr fun τ ↦ (qj_eq_jReg τ).symm

theorem qj_isBoundedAtImInfty : IsBoundedAtImInfty qj :=
  qj_tendsto.isBigO_one ℝ

/-- The Laurent expansion of `j`: `q · j(τ) = Σ Q_m qᵐ` with `Q = qExpansion 1 qj`. -/
theorem hasSum_qExpansion_qj (τ : ℍ) :
    HasSum (fun m ↦ (qExpansion 1 qj).coeff m * 𝕢 1 τ ^ m) (𝕢 1 τ * j τ) := by
  have h := hasSum_qExpansion one_pos qj_periodic qj_mdiff qj_isBoundedAtImInfty τ
  simpa [qj, smul_eq_mul] using h

/-- `j τ = q⁻¹ · Σ Q_m qᵐ`. -/
theorem j_eq_tsum (τ : ℍ) :
    j τ = (𝕢 1 τ)⁻¹ * ∑' m, (qExpansion 1 qj).coeff m * 𝕢 1 τ ^ m := by
  rw [(hasSum_qExpansion_qj τ).tsum_eq]
  have hq0 : 𝕢 1 τ ≠ 0 := Periodic.qParam_ne_zero (τ : ℂ)
  field_simp

/-! ### The power-series identity `Q · P = X · A³` -/

/-- Uniqueness of `q`-expansion coefficients for an unbundled function (Mathlib's
`UpperHalfPlane.qExpansion_coeff_unique` is stated for `FunLike` types). -/
theorem qExpansion_coeff_unique' {f : ℍ → ℂ} {c : ℕ → ℂ}
    (hfanalytic : AnalyticAt ℂ (cuspFunction 1 f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • 𝕢 1 τ ^ m) (f τ)) (m : ℕ) :
    c m = (qExpansion 1 f).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 f)
      (.ofScalars ℂ fun m ↦ (qExpansion 1 f).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hfanalytic.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

theorem cuspFunction_qParam_eqOn : EqOn (cuspFunction 1 fun τ : ℍ ↦ 𝕢 1 τ) id (ball 0 1) :=
  cuspFunction_eqOn_of_comp (fun _ ↦ rfl) continuousAt_id

theorem analyticAt_cuspFunction_qParam : AnalyticAt ℂ (cuspFunction 1 fun τ : ℍ ↦ 𝕢 1 τ) 0 :=
  analyticAt_id.congr (cuspFunction_qParam_eqOn.eventuallyEq_of_mem (ball_mem_nhds 0 one_pos)).symm

/-- The `q`-expansion of `τ ↦ 𝕢 τ` is `X`. -/
theorem qExpansion_qParam : qExpansion 1 (fun τ : ℍ ↦ 𝕢 1 τ) = PowerSeries.X := by
  ext m
  rw [← qExpansion_coeff_unique' (c := fun m ↦ if m = 1 then 1 else 0)
    analyticAt_cuspFunction_qParam ?_ m]
  · simp [PowerSeries.coeff_X]
  · intro τ
    convert hasSum_ite_eq 1 (𝕢 1 τ) using 1
    funext m
    split_ifs with h <;> simp [h]

/-- `Q · P = X · A³`, where `Q`, `P`, `A` are the expansions of `q · j`, `Δ`, `E₄`. -/
theorem qExpansion_qj_mul :
    qExpansion 1 qj * qExpansion 1 ModularForm.discriminant =
      PowerSeries.X * qExpansion 1 E₄ ^ 3 := by
  have hΔ : AnalyticAt ℂ (cuspFunction 1 ModularForm.discriminant) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
      one_mem_strictPeriods_SL
  have hE : AnalyticAt ℂ (cuspFunction 1 (E₄.pow 3)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero _ one_pos one_mem_strictPeriods_SL
  have hfun : qj * ModularForm.discriminant = (fun τ : ℍ ↦ 𝕢 1 τ) * ⇑(E₄.pow 3) := by
    funext τ
    simp only [Pi.mul_apply, coe_pow, Pi.pow_apply, qj, mul_assoc, j_mul_discriminant]
  rw [← qExpansion_mul analyticAt_cuspFunction_qj hΔ, hfun,
    qExpansion_mul analyticAt_cuspFunction_qParam hE, qExpansion_qParam,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

/-! ### Stages (b) and (c) -/

/-- **Stage (b).** The constant term of `j` is `744`. -/
theorem qExpansion_qj_coeff_one : (qExpansion 1 qj).coeff 1 = 744 := by
  have h := congr_arg (PowerSeries.coeff 2) qExpansion_qj_mul
  rw [PowerSeries.coeff_succ_X_mul, E₄_cube_coeff_one] at h
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, discriminant_coeff_zero,
    discriminant_coeff_one, discriminant_coeff_two, qExpansion_qj_coeff_zero] at h
  linear_combination h

/-- **Stage (c).** The coefficient of `q` in `j` is `196884`. -/
theorem qExpansion_qj_coeff_two : (qExpansion 1 qj).coeff 2 = 196884 := by
  have h := congr_arg (PowerSeries.coeff 3) qExpansion_qj_mul
  rw [PowerSeries.coeff_succ_X_mul, E₄_cube_coeff_two] at h
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, discriminant_coeff_zero,
    discriminant_coeff_one, discriminant_coeff_two, discriminant_coeff_three,
    qExpansion_qj_coeff_zero, qExpansion_qj_coeff_one] at h
  linear_combination h

/-- The three leading terms together: `j = q⁻¹ + 744 + 196884 q + O(q²)`, as a statement
about the Laurent coefficients `c(-1), c(0), c(1)` of `j`. -/
theorem j_expansion (τ : ℍ) :
    HasSum (fun m ↦ (qExpansion 1 qj).coeff m * 𝕢 1 τ ^ m) (𝕢 1 τ * j τ) ∧
      (qExpansion 1 qj).coeff 0 = 1 ∧ (qExpansion 1 qj).coeff 1 = 744 ∧
      (qExpansion 1 qj).coeff 2 = 196884 :=
  ⟨hasSum_qExpansion_qj τ, qExpansion_qj_coeff_zero, qExpansion_qj_coeff_one,
    qExpansion_qj_coeff_two⟩

end Complexity.Modular
