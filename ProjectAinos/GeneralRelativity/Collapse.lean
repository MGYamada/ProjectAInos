/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildOrbit
public import ProjectAinos.GeneralRelativity.EddingtonFinkelstein
public import ProjectAinos.GeneralRelativity.FLRW
public import ProjectAinos.GeneralRelativity.ProperTime
public import ProjectAinos.SmoothGeometry.Lorentzian.OrthogonalSlicing
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Gravitational collapse of a spherical body

Landau–Lifshitz, §§102–103, with `G = c = 1`, `r_g = 2M`, the signature `(−+++)` and the
exterior Schwarzschild co-ordinates `(t, r, θ, φ)` of `SchwarzschildExterior`.

* **Kepler's function** `η ↦ η + sin η` is a homeomorphism of the line (`cycloidHomeomorph`); its
  inverse `cycloidParam` is smooth where `|s| < π` (`contDiffAt_cycloidParam`).
* **The fall from rest at `r₀ > 2M`.** The cycloid `r = (r₀/2)(1 + cos η)`,
  `τ = √(r₀³/8M)(η + sin η)` (`fallRadius`, `fallAngle`, `fallScale_mul_cycloidTime`) satisfies
  `(dr/dτ)² = 2M/r − 2M/r₀` and `d²r/dτ² = −M/r²` from `r₀` to the centre (`fallVelocity_sq`,
  `hasDerivAt_fallVelocity`). With the Schwarzschild time `t(τ) = ∫₀^τ E/(1 − 2M/r)`,
  `E = √(1 − 2M/r₀)` (`fallTime`), the curve `fall` is a geodesic of the exterior for `|τ| < τ_h`
  (`isGeodesicOn_fall`), parametrized by its proper time (`form_curveVelocity_fall`,
  `properTime_fall`) and at rest at `r₀` for `τ = 0` (`fall_rest`).
* `radialInfall_properTime`: the proper time `τ_h = √(r₀³/8M)(η_h + sin η_h)`,
  `cos η_h = 4M/r₀ − 1`, to the sphere `r = 2M` is finite, and the centre is reached by the
  cycloid at `π √(r₀³/8M)`. In the Eddington–Finkelstein chart the same body
  (`toEddington_fall`), with the advanced time `v(τ) = v(0) + ∫ dτ/(E − dr/dτ)`
  (`advancedFall`), is a geodesic through `r = 2M` up to the centre (`isGeodesicOn_advancedFall`),
  which it reaches at the proper time `π √(r₀³/8M)` (`advancedFall_properTime`);
  `lemaitreObserver_properTime`: the Lemaître observers, which fall from rest at infinity, are
  geodesics that cross `r = 2M` and reach `r = 0` in finite proper time.
* `tendsto_coordinateTime`: the Schwarzschild time diverges, `t → ∞` as `τ → τ_h`.
* `tendsto_observedFrequency`: **the red shift of the collapsing surface**. Along the outgoing
  radial light rays (`outgoingRay`, `isGeodesicOn_outgoingRay`, `form_outgoingRay_velocity`), the
  ratio of the frequency received by a static observer (`observedFrequency`, §88) to the frequency
  emitted by the falling surface (`emittedFrequency`, `ω = −g(u, k)`) tends to `0` as `τ → τ_h`.
* `ComovingData`: the centrally symmetric metrics `−dτ² + e^λ dR² + r² dΩ²` of a comoving frame
  (Landau–Lifshitz, (103.1)), synchronous and orthogonally sliced by the shells `R = const`, with
  the induced metric `−dτ² + r² dΩ²` and the second fundamental form
  `ε (∂_R r/e^{λ/2}) r dΩ²` of a shell (`ComovingData.inducedMetric_eq`,
  `ComovingData.secondFundamental_eq`); two shells match when their areal radii and their rates
  `∂_R r/e^{λ/2}` agree (`ComovingData.junction`, `ComovingData.inducedMetric_eq_iff`,
  `ComovingData.secondFundamental_eq_iff`).
* **The Lemaître chart** `lemaitre` (Landau–Lifshitz, (102.2)), `r = ((9/2) M (R − τ)²)^{1/3}`:
  it is the pullback of the Eddington–Finkelstein metric (`form_lemaitreToEddington`,
  `hasFDerivAt_lemaitreToEddington`), its shells have the rate `1` (`shellEnergy_lemaitre`), the
  sphere `r = 2M` is `R − τ = 4M/3` (`lemaitreRadius_lt_iff`), and inside it every causal vector
  future directed for `τ` has `dr < 0` (`radius_deriv_neg_of_causal`).
* **The interior**: the collapsing flat dust ball `dustInterior`, `a = ((τ_c − τ)/τ_c)^{2/3}`,
  the pullback by spherical co-ordinates (`form_toCartesian`, `hasFDerivAt_toCartesian`) of the
  isotropic model `dustData`, which solves the Einstein equations with dust of density
  `ρ = 4/(3κ(τ_c − τ)²)` (`isEinstein_dustData`).
* `junction_oppenheimerSnyder`: the boundary of the ball matches a Lemaître shell `R = R_b`,
  with equal induced metrics and second fundamental forms, exactly when `R_b = τ_c` and
  `2M = (κ/3) ρ r_b³`. The closed model `k = +1` (`closedInterior`, whose shells have the rate
  `cos χ`) cannot be matched to a Lemaître shell
  (`secondFundamental_closedInterior_ne_lemaitre`).

Not stated: that the glued metric solves the Einstein equations across the boundary without a
surface layer (with a jump of the density the glued metric is only `C^{1,1}`, while a
`CoordinateMetric` is smooth and the library's Einstein equations are pointwise), the junction of
the closed model with a comoving chart of bound shells (Novikov's co-ordinates, whose areal
radius `fallRadius M R τ` is given by the inverse of Kepler's function), and the event horizon as
the boundary of the causal past of future null infinity.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.Collapse

open SmoothGeometry

/-! ### Kepler's function `η + sin η` and its inverse -/

/-- Kepler's function `η ↦ η + sin η`, the proper time of the cycloid in units of its scale. -/
def cycloidTime (η : ℝ) : ℝ := η + Real.sin η

/-- For `h > 0`, `|sin h| < h`. -/
theorem abs_sin_lt {h : ℝ} (hh : 0 < h) : |Real.sin h| < h := by
  rcases lt_or_ge h π with hπ | hπ
  · rw [abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hh hπ)]
    exact Real.sin_lt hh
  · exact (Real.abs_sin_le_one h).trans_lt (by linarith [Real.two_le_pi])

/-- Kepler's function is strictly increasing. -/
theorem strictMono_cycloidTime : StrictMono cycloidTime := by
  intro x y hxy
  have hh : 0 < (y - x) / 2 := by linarith
  have hs := Real.sin_sub_sin y x
  have h1 := abs_sin_lt hh
  have h2 : |Real.sin ((y - x) / 2) * Real.cos ((y + x) / 2)| ≤ |Real.sin ((y - x) / 2)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h3 := neg_abs_le (Real.sin ((y - x) / 2) * Real.cos ((y + x) / 2))
  unfold cycloidTime
  linarith

/-- Kepler's function is continuous. -/
theorem continuous_cycloidTime : Continuous cycloidTime :=
  continuous_id.add Real.continuous_sin

/-- Kepler's function is smooth. -/
theorem contDiff_cycloidTime : ContDiff ℝ ∞ cycloidTime :=
  contDiff_id.add Real.contDiff_sin

/-- The derivative of Kepler's function is `1 + cos η`. -/
theorem hasDerivAt_cycloidTime (η : ℝ) : HasDerivAt cycloidTime (1 + Real.cos η) η :=
  (hasDerivAt_id η).add (Real.hasDerivAt_sin η)

/-- Kepler's function is onto. -/
theorem surjective_cycloidTime : Function.Surjective cycloidTime := by
  refine continuous_cycloidTime.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun η => ?_) (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    simp only [cycloidTime, id]
    linarith [Real.neg_one_le_sin η]
  · refine tendsto_atBot_mono (fun η => ?_) (tendsto_atBot_add_const_right _ 1 tendsto_id)
    simp only [cycloidTime, id]
    linarith [Real.sin_le_one η]

/-- Kepler's function is odd. -/
theorem cycloidTime_neg (η : ℝ) : cycloidTime (-η) = -cycloidTime η := by
  simp only [cycloidTime, Real.sin_neg]
  ring

/-- `π + sin π = π`. -/
theorem cycloidTime_pi : cycloidTime π = π := by simp [cycloidTime]

/-- Kepler's function as a homeomorphism of the line. -/
def cycloidHomeomorph : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective cycloidTime strictMono_cycloidTime
    surjective_cycloidTime).toHomeomorph

/-- The solution `η` of Kepler's equation `η + sin η = s`. -/
def cycloidParam (s : ℝ) : ℝ := cycloidHomeomorph.symm s

theorem cycloidHomeomorph_apply (η : ℝ) : cycloidHomeomorph η = cycloidTime η := rfl

theorem cycloidTime_cycloidParam (s : ℝ) : cycloidTime (cycloidParam s) = s :=
  cycloidHomeomorph.apply_symm_apply s

theorem cycloidParam_cycloidTime (η : ℝ) : cycloidParam (cycloidTime η) = η :=
  cycloidHomeomorph.symm_apply_apply η

/-- The solution of Kepler's equation is strictly increasing. -/
theorem strictMono_cycloidParam : StrictMono cycloidParam := by
  intro s s' h
  rw [← strictMono_cycloidTime.lt_iff_lt, cycloidTime_cycloidParam, cycloidTime_cycloidParam]
  exact h

/-- The solution of Kepler's equation is continuous. -/
theorem continuous_cycloidParam : Continuous cycloidParam :=
  cycloidHomeomorph.symm.continuous

/-- For `|s| < π` the solution satisfies `|η| < π`. -/
theorem cycloidParam_mem_Ioo {s : ℝ} (hs : s ∈ Ioo (-π) π) : cycloidParam s ∈ Ioo (-π) π := by
  constructor
  · rw [← strictMono_cycloidTime.lt_iff_lt, cycloidTime_cycloidParam, cycloidTime_neg,
      cycloidTime_pi]
    exact hs.1
  · rw [← strictMono_cycloidTime.lt_iff_lt, cycloidTime_cycloidParam, cycloidTime_pi]
    exact hs.2

/-- For `|η| < π`, `1 + cos η > 0`. -/
theorem one_add_cos_pos {η : ℝ} (hη : η ∈ Ioo (-π) π) : 0 < 1 + Real.cos η := by
  have hc : 0 < Real.cos (η / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hη.1], by linarith [hη.2]⟩
  have h := Real.cos_sq (η / 2)
  rw [show 2 * (η / 2) = η by ring] at h
  nlinarith

/-- Where `|s| < π`, the solution of Kepler's equation has the derivative `1/(1 + cos η)`. -/
theorem hasDerivAt_cycloidParam {s : ℝ} (hs : s ∈ Ioo (-π) π) :
    HasDerivAt cycloidParam (1 + Real.cos (cycloidParam s))⁻¹ s :=
  cycloidHomeomorph.toOpenPartialHomeomorph.hasDerivAt_symm (mem_univ s)
    (one_add_cos_pos (cycloidParam_mem_Ioo hs)).ne' (hasDerivAt_cycloidTime _)

/-- Where `|s| < π`, the solution of Kepler's equation is smooth. -/
theorem contDiffAt_cycloidParam {s : ℝ} (hs : s ∈ Ioo (-π) π) :
    ContDiffAt ℝ ∞ cycloidParam s :=
  cycloidHomeomorph.toOpenPartialHomeomorph.contDiffAt_symm_deriv
    (one_add_cos_pos (cycloidParam_mem_Ioo hs)).ne' (mem_univ s) (hasDerivAt_cycloidTime _)
    contDiff_cycloidTime.contDiffAt

/-! ### The cycloid of the radial fall from rest -/

variable {M r₀ : ℝ}

/-- The scale `√(r₀³/8M)` of the proper time of a fall from rest at `r₀`. -/
def fallScale (M r₀ : ℝ) : ℝ := Real.sqrt (r₀ ^ 3 / (8 * M))

/-- The proper time `π √(r₀³/8M)` of the fall from rest at `r₀` to the centre. -/
def crunchTime (M r₀ : ℝ) : ℝ := π * fallScale M r₀

/-- The cycloid parameter `η(τ)` of the fall: the solution of `√(r₀³/8M)(η + sin η) = τ`. -/
def fallAngle (M r₀ τ : ℝ) : ℝ := cycloidParam (τ / fallScale M r₀)

/-- The radius `r(τ) = (r₀/2)(1 + cos η(τ))` of the fall from rest at `r₀`. -/
def fallRadius (M r₀ τ : ℝ) : ℝ := r₀ / 2 * (1 + Real.cos (fallAngle M r₀ τ))

/-- The radial velocity `dr/dτ = −(r₀/2) sin η / (√(r₀³/8M)(1 + cos η))` of the fall. -/
def fallVelocity (M r₀ τ : ℝ) : ℝ :=
  -(r₀ / 2) * Real.sin (fallAngle M r₀ τ) /
    (fallScale M r₀ * (1 + Real.cos (fallAngle M r₀ τ)))

theorem pos_of_two_mul_lt (hM : 0 < M) (hr : 2 * M < r₀) : 0 < r₀ := by linarith

theorem fallScale_pos (hM : 0 < M) (hr : 2 * M < r₀) : 0 < fallScale M r₀ := by
  have := pos_of_two_mul_lt hM hr
  exact Real.sqrt_pos.mpr (by positivity)

theorem fallScale_sq (hM : 0 < M) (hr : 2 * M < r₀) : fallScale M r₀ ^ 2 = r₀ ^ 3 / (8 * M) := by
  have := pos_of_two_mul_lt hM hr
  exact Real.sq_sqrt (by positivity)

theorem crunchTime_pos (hM : 0 < M) (hr : 2 * M < r₀) : 0 < crunchTime M r₀ :=
  mul_pos Real.pi_pos (fallScale_pos hM hr)

/-- The cycloid: `√(r₀³/8M)(η(τ) + sin η(τ)) = τ`. -/
theorem fallScale_mul_cycloidTime (hM : 0 < M) (hr : 2 * M < r₀) (τ : ℝ) :
    fallScale M r₀ * cycloidTime (fallAngle M r₀ τ) = τ := by
  rw [fallAngle, cycloidTime_cycloidParam]
  field_simp [(fallScale_pos hM hr).ne']

theorem div_fallScale_mem (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) : τ / fallScale M r₀ ∈ Ioo (-π) π := by
  have hA := fallScale_pos hM hr
  have h1 := hτ.1
  have h2 := hτ.2
  unfold crunchTime at h1 h2
  constructor
  · rw [lt_div_iff₀ hA]
    linarith
  · rw [div_lt_iff₀ hA]
    linarith

theorem fallAngle_mem (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) : fallAngle M r₀ τ ∈ Ioo (-π) π :=
  cycloidParam_mem_Ioo (div_fallScale_mem hM hr hτ)

theorem one_add_cos_fallAngle_pos (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    0 < 1 + Real.cos (fallAngle M r₀ τ) :=
  one_add_cos_pos (fallAngle_mem hM hr hτ)

/-- During the fall the radius is positive. -/
theorem fallRadius_pos (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) : 0 < fallRadius M r₀ τ := by
  have := one_add_cos_fallAngle_pos hM hr hτ
  have := pos_of_two_mul_lt hM hr
  unfold fallRadius
  positivity

/-- The radius never exceeds `r₀`. -/
theorem fallRadius_le (hM : 0 < M) (hr : 2 * M < r₀) (τ : ℝ) : fallRadius M r₀ τ ≤ r₀ := by
  have := pos_of_two_mul_lt hM hr
  unfold fallRadius
  nlinarith [Real.cos_le_one (fallAngle M r₀ τ)]

theorem cycloidParam_zero : cycloidParam 0 = 0 := by
  simpa [cycloidTime] using cycloidParam_cycloidTime 0

/-- At `τ = 0` the body is at `r₀`. -/
theorem fallRadius_zero : fallRadius M r₀ 0 = r₀ := by
  simp [fallRadius, fallAngle, cycloidParam_zero]
  ring

/-- At `τ = π √(r₀³/8M)` the cycloid reaches the centre. -/
theorem fallRadius_crunchTime (hM : 0 < M) (hr : 2 * M < r₀) :
    fallRadius M r₀ (crunchTime M r₀) = 0 := by
  have hA := (fallScale_pos hM hr).ne'
  have h : crunchTime M r₀ / fallScale M r₀ = cycloidTime π := by
    rw [cycloidTime_pi, crunchTime]
    field_simp
  rw [fallRadius, fallAngle, h, cycloidParam_cycloidTime, Real.cos_pi]
  ring

/-- The cycloid parameter is nonnegative after the start. -/
theorem fallAngle_nonneg (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ fallAngle M r₀ τ := by
  rw [← cycloidParam_zero, fallAngle]
  exact strictMono_cycloidParam.monotone (div_nonneg hτ (fallScale_pos hM hr).le)

/-- The cycloid parameter has the derivative `1/(√(r₀³/8M)(1 + cos η))`. -/
theorem hasDerivAt_fallAngle (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fallAngle M r₀) (fallScale M r₀ * (1 + Real.cos (fallAngle M r₀ τ)))⁻¹ τ := by
  have hA := (fallScale_pos hM hr).ne'
  have h := (hasDerivAt_cycloidParam (div_fallScale_mem hM hr hτ)).comp τ
    ((hasDerivAt_id τ).div_const (fallScale M r₀))
  refine h.congr_deriv ?_
  simp only [fallAngle, one_div, mul_inv]
  ring

/-- The radius has the derivative `fallVelocity`. -/
theorem hasDerivAt_fallRadius (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fallRadius M r₀) (fallVelocity M r₀ τ) τ := by
  have hc := (one_add_cos_fallAngle_pos hM hr hτ).ne'
  have hA := (fallScale_pos hM hr).ne'
  have h := (((hasDerivAt_fallAngle hM hr hτ).cos).const_add 1).const_mul (r₀ / 2)
  refine h.congr_deriv ?_
  rw [fallVelocity]
  field_simp

/-- **The radial equation of the fall**: `(dr/dτ)² = 2M/r − 2M/r₀`. -/
theorem fallVelocity_sq (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    fallVelocity M r₀ τ ^ 2 = 2 * M / fallRadius M r₀ τ - 2 * M / r₀ := by
  have hc := (one_add_cos_fallAngle_pos hM hr hτ).ne'
  have hA := fallScale_sq hM hr
  have h0 := (pos_of_two_mul_lt hM hr).ne'
  rw [fallVelocity, fallRadius, div_pow, mul_pow, mul_pow, hA, Real.sin_sq]
  field_simp
  ring

/-- `d/dη (sin η/(1 + cos η)) = 1/(1 + cos η)`. -/
theorem hasDerivAt_sin_div {η : ℝ} (hη : 0 < 1 + Real.cos η) :
    HasDerivAt (fun x => Real.sin x / (1 + Real.cos x)) (1 + Real.cos η)⁻¹ η := by
  have h := (Real.hasDerivAt_sin η).fun_div ((Real.hasDerivAt_cos η).const_add 1) hη.ne'
  refine h.congr_deriv ?_
  have hs := Real.sin_sq_add_cos_sq η
  field_simp
  linear_combination hs

/-- **The radial acceleration of the fall**: `d²r/dτ² = −M/r²`. -/
theorem hasDerivAt_fallVelocity (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fallVelocity M r₀) (-(M / fallRadius M r₀ τ ^ 2)) τ := by
  have hη := hasDerivAt_fallAngle hM hr hτ
  have hc := one_add_cos_fallAngle_pos hM hr hτ
  have hA := fallScale_pos hM hr
  have hA2 := fallScale_sq hM hr
  have h0 := (pos_of_two_mul_lt hM hr).ne'
  have hg := (hasDerivAt_sin_div hc).comp τ hη
  have h := hg.const_mul (-(r₀ / 2) / fallScale M r₀)
  have heq : fallVelocity M r₀ = fun y => -(r₀ / 2) / fallScale M r₀ *
      (Real.sin (fallAngle M r₀ y) / (1 + Real.cos (fallAngle M r₀ y))) := by
    funext y
    rw [fallVelocity, div_mul_div_comm]
  rw [heq]
  refine h.congr_deriv ?_
  have e1 : -(r₀ / 2) / fallScale M r₀ * ((1 + Real.cos (fallAngle M r₀ τ))⁻¹ *
      (fallScale M r₀ * (1 + Real.cos (fallAngle M r₀ τ)))⁻¹) =
      -(r₀ / 2) / (fallScale M r₀ ^ 2 * (1 + Real.cos (fallAngle M r₀ τ)) ^ 2) := by
    field_simp
  rw [e1, hA2, fallRadius]
  field_simp
  ring

/-- The radius is smooth during the fall from `r₀` to the centre. -/
theorem contDiffOn_fallRadius (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ ∞ (fallRadius M r₀) (Ioo (-crunchTime M r₀) (crunchTime M r₀)) := by
  intro τ hτ
  have h1 : ContDiffAt ℝ ∞ (fallAngle M r₀) τ :=
    (contDiffAt_cycloidParam (div_fallScale_mem hM hr hτ)).comp τ (contDiffAt_id.div_const _)
  exact (contDiffAt_const.mul (contDiffAt_const.add
    (Real.contDiff_cos.contDiffAt.comp τ h1))).contDiffWithinAt

/-- The body falls after the start: `dr/dτ ≤ 0` for `τ ≥ 0`. -/
theorem fallVelocity_nonpos (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ico 0 (crunchTime M r₀)) : fallVelocity M r₀ τ ≤ 0 := by
  have hτ' : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀) :=
    ⟨by linarith [hτ.1, crunchTime_pos hM hr], hτ.2⟩
  have hη := fallAngle_mem hM hr hτ'
  have h0 := fallAngle_nonneg hM hr hτ.1
  have hs : 0 ≤ Real.sin (fallAngle M r₀ τ) := Real.sin_nonneg_of_nonneg_of_le_pi h0 hη.2.le
  have hc := one_add_cos_fallAngle_pos hM hr hτ'
  have hA := fallScale_pos hM hr
  have h0' := pos_of_two_mul_lt hM hr
  unfold fallVelocity
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith

/-! ### The crossing of the sphere `r = 2M` -/

/-- The cycloid parameter `η_h = arccos(4M/r₀ − 1)` at which the fall reaches `r = 2M`. -/
def horizonAngle (M r₀ : ℝ) : ℝ := Real.arccos (4 * M / r₀ - 1)

/-- The proper time `τ_h = √(r₀³/8M)(η_h + sin η_h)` of the fall from rest at `r₀` to the sphere
`r = 2M`. -/
def horizonTime (M r₀ : ℝ) : ℝ := fallScale M r₀ * cycloidTime (horizonAngle M r₀)

theorem horizon_arg_mem (hM : 0 < M) (hr : 2 * M < r₀) : 4 * M / r₀ - 1 ∈ Ioo (-1) 1 := by
  have h0 := pos_of_two_mul_lt hM hr
  have h1 : 0 < 4 * M / r₀ := by positivity
  have h2 : 4 * M / r₀ < 2 := by
    rw [div_lt_iff₀ h0]
    linarith
  constructor <;> linarith

theorem horizonAngle_mem (hM : 0 < M) (hr : 2 * M < r₀) : horizonAngle M r₀ ∈ Ioo 0 π :=
  ⟨Real.arccos_pos.mpr (horizon_arg_mem hM hr).2, Real.arccos_lt_pi.mpr (horizon_arg_mem hM hr).1⟩

theorem cos_horizonAngle (hM : 0 < M) (hr : 2 * M < r₀) :
    Real.cos (horizonAngle M r₀) = 4 * M / r₀ - 1 :=
  Real.cos_arccos (horizon_arg_mem hM hr).1.le (horizon_arg_mem hM hr).2.le

theorem horizonTime_pos (hM : 0 < M) (hr : 2 * M < r₀) : 0 < horizonTime M r₀ := by
  have h := strictMono_cycloidTime (horizonAngle_mem hM hr).1
  rw [show cycloidTime 0 = 0 by simp [cycloidTime]] at h
  exact mul_pos (fallScale_pos hM hr) h

/-- The sphere `r = 2M` is reached before the centre: `τ_h < π √(r₀³/8M)`. -/
theorem horizonTime_lt_crunchTime (hM : 0 < M) (hr : 2 * M < r₀) :
    horizonTime M r₀ < crunchTime M r₀ := by
  have h := strictMono_cycloidTime (horizonAngle_mem hM hr).2
  rw [cycloidTime_pi] at h
  rw [horizonTime, crunchTime, mul_comm π]
  exact mul_lt_mul_of_pos_left h (fallScale_pos hM hr)

theorem horizon_subset (hM : 0 < M) (hr : 2 * M < r₀) :
    Ioo (-horizonTime M r₀) (horizonTime M r₀) ⊆ Ioo (-crunchTime M r₀) (crunchTime M r₀) := by
  have := horizonTime_lt_crunchTime hM hr
  exact Ioo_subset_Ioo (by linarith) this.le

theorem zero_mem_horizon (hM : 0 < M) (hr : 2 * M < r₀) :
    (0 : ℝ) ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀) :=
  ⟨by linarith [horizonTime_pos hM hr], horizonTime_pos hM hr⟩

theorem fallAngle_horizonTime (hM : 0 < M) (hr : 2 * M < r₀) :
    fallAngle M r₀ (horizonTime M r₀) = horizonAngle M r₀ := by
  rw [fallAngle, horizonTime, mul_div_cancel_left₀ _ (fallScale_pos hM hr).ne',
    cycloidParam_cycloidTime]

/-- At `τ_h` the falling body is at `r = 2M`. -/
theorem fallRadius_horizonTime (hM : 0 < M) (hr : 2 * M < r₀) :
    fallRadius M r₀ (horizonTime M r₀) = 2 * M := by
  have h0 := (pos_of_two_mul_lt hM hr).ne'
  rw [fallRadius, fallAngle_horizonTime hM hr, cos_horizonAngle hM hr]
  field_simp
  ring

theorem abs_fallAngle_lt (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    |fallAngle M r₀ τ| < horizonAngle M r₀ := by
  have hA := fallScale_pos hM hr
  have h1 := hτ.1
  have h2 := hτ.2
  unfold horizonTime at h1 h2
  rw [abs_lt]
  constructor
  · rw [← strictMono_cycloidTime.lt_iff_lt, fallAngle, cycloidTime_cycloidParam, cycloidTime_neg,
      lt_div_iff₀ hA]
    linarith
  · rw [← strictMono_cycloidTime.lt_iff_lt, fallAngle, cycloidTime_cycloidParam,
      div_lt_iff₀ hA]
    linarith

/-- **Outside the sphere `r = 2M` before `τ_h`**: for `|τ| < τ_h` the radius exceeds `2M`. -/
theorem two_mul_lt_fallRadius (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) : 2 * M < fallRadius M r₀ τ := by
  have h := abs_fallAngle_lt hM hr hτ
  have hh := horizonAngle_mem hM hr
  have hcos : Real.cos (horizonAngle M r₀) < Real.cos (fallAngle M r₀ τ) := by
    rw [← Real.cos_abs (fallAngle M r₀ τ)]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hh.2.le h
  rw [cos_horizonAngle hM hr] at hcos
  have h0 := pos_of_two_mul_lt hM hr
  have e : r₀ / 2 * (1 + (4 * M / r₀ - 1)) = 2 * M := by
    field_simp
    ring
  unfold fallRadius
  nlinarith

/-- The lapse `1 − 2M/r` is positive before `τ_h`. -/
theorem lapse_fall_pos (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    0 < 1 - 2 * M / fallRadius M r₀ τ := by
  have h := two_mul_lt_fallRadius hM hr hτ
  have h0 : 0 < fallRadius M r₀ τ := by linarith
  have : 2 * M / fallRadius M r₀ τ < 1 := (div_lt_one h0).mpr h
  linarith

/-! ### The Schwarzschild time along the fall -/

/-- The energy per unit mass `E = √(1 − 2M/r₀)` of the fall from rest at `r₀`. -/
def fallEnergy (M r₀ : ℝ) : ℝ := Real.sqrt (1 - 2 * M / r₀)

theorem fallEnergy_sq (hM : 0 < M) (hr : 2 * M < r₀) : fallEnergy M r₀ ^ 2 = 1 - 2 * M / r₀ := by
  have h0 := pos_of_two_mul_lt hM hr
  have : 2 * M / r₀ < 1 := (div_lt_one h0).mpr hr
  exact Real.sq_sqrt (by linarith)

theorem fallEnergy_pos (hM : 0 < M) (hr : 2 * M < r₀) : 0 < fallEnergy M r₀ := by
  have h0 := pos_of_two_mul_lt hM hr
  have : 2 * M / r₀ < 1 := (div_lt_one h0).mpr hr
  exact Real.sqrt_pos.mpr (by linarith)

/-- The rate `dt/dτ = E/(1 − 2M/r)` of the Schwarzschild time along the fall. -/
def fallTimeRate (M r₀ τ : ℝ) : ℝ := fallEnergy M r₀ / (1 - 2 * M / fallRadius M r₀ τ)

/-- The Schwarzschild time `t(τ) = ∫₀^τ E/(1 − 2M/r) dσ` along the fall, with `t(0) = 0`. -/
def fallTime (M r₀ τ : ℝ) : ℝ := ∫ σ in (0 : ℝ)..τ, fallTimeRate M r₀ σ

theorem hasDerivAt_fallTimeRate (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    HasDerivAt (fallTimeRate M r₀)
      (-(fallEnergy M r₀ * (2 * M * fallVelocity M r₀ τ / fallRadius M r₀ τ ^ 2)) /
        (1 - 2 * M / fallRadius M r₀ τ) ^ 2) τ := by
  have hτ' := horizon_subset hM hr hτ
  have hR := hasDerivAt_fallRadius hM hr hτ'
  have hr0 := (fallRadius_pos hM hr hτ').ne'
  have hf := (lapse_fall_pos hM hr hτ).ne'
  have hd : HasDerivAt (fun σ => 1 - 2 * M / fallRadius M r₀ σ)
      (2 * M * fallVelocity M r₀ τ / fallRadius M r₀ τ ^ 2) τ := by
    refine (((hasDerivAt_const τ (2 * M)).fun_div hR hr0).const_sub 1).congr_deriv ?_
    ring
  refine ((hasDerivAt_const τ (fallEnergy M r₀)).fun_div hd hf).congr_deriv ?_
  ring

theorem continuousOn_fallTimeRate (hM : 0 < M) (hr : 2 * M < r₀) :
    ContinuousOn (fallTimeRate M r₀) (Ioo (-horizonTime M r₀) (horizonTime M r₀)) :=
  fun _ hτ => (hasDerivAt_fallTimeRate hM hr hτ).continuousAt.continuousWithinAt

/-- The Schwarzschild time has the rate `dt/dτ = E/(1 − 2M/r)` before `τ_h`. -/
theorem hasDerivAt_fallTime (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    HasDerivAt (fallTime M r₀) (fallTimeRate M r₀ τ) τ := by
  have hc := continuousOn_fallTimeRate hM hr
  have hsub : uIcc 0 τ ⊆ Ioo (-horizonTime M r₀) (horizonTime M r₀) :=
    ordConnected_Ioo.uIcc_subset (zero_mem_horizon hM hr) hτ
  exact intervalIntegral.integral_hasDerivAt_right (hc.mono hsub).intervalIntegrable
    (hc.stronglyMeasurableAtFilter isOpen_Ioo τ hτ) (hc.continuousAt (isOpen_Ioo.mem_nhds hτ))

theorem contDiffOn_fallTimeRate (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ ∞ (fallTimeRate M r₀) (Ioo (-horizonTime M r₀) (horizonTime M r₀)) := by
  have hR := (contDiffOn_fallRadius hM hr).mono (horizon_subset hM hr)
  refine contDiffOn_const.div (contDiffOn_const.sub (contDiffOn_const.div hR ?_)) ?_
  · exact fun τ hτ => (fallRadius_pos hM hr (horizon_subset hM hr hτ)).ne'
  · exact fun τ hτ => (lapse_fall_pos hM hr hτ).ne'

theorem contDiffOn_fallTime (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ 2 (fallTime M r₀) (Ioo (-horizonTime M r₀) (horizonTime M r₀)) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun τ hτ => (hasDerivAt_fallTime hM hr hτ).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  exact ((contDiffOn_fallTimeRate hM hr).of_le (by norm_num)).congr
    fun τ hτ => (hasDerivAt_fallTime hM hr hτ).deriv

/-! ### The fall as a geodesic of the exterior field -/

/-- A point `(0, 2|M| + 1, π/2, 0)` of the exterior domain, for any mass. -/
def basePoint (M : ℝ) : MinkowskiModel 3 := ![0, 2 * |M| + 1, π / 2, 0]

theorem basePoint_mem (M : ℝ) : basePoint M ∈ SchwarzschildExterior.domain M := by
  refine ⟨?_, ?_, ?_⟩
  · change 2 * M < 2 * |M| + 1
    linarith [le_abs_self M]
  · change 0 < π / 2
    positivity
  · change π / 2 < π
    linarith [Real.pi_pos]

/-- A vector function `σ ↦ (a σ, b σ, c σ, e σ)` has the derivative `(a', b', c', e')`. -/
theorem hasDerivAt_vec {a b c e : ℝ → ℝ} {a' b' c' e' τ : ℝ} (ha : HasDerivAt a a' τ)
    (hb : HasDerivAt b b' τ) (hc : HasDerivAt c c' τ) (he : HasDerivAt e e' τ) :
    HasDerivAt (fun σ => (![a σ, b σ, c σ, e σ] : MinkowskiModel 3)) ![a', b', c', e'] τ := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i <;> simpa

/-- The co-ordinates `(t(τ), r(τ), θ₀, φ₀)` of the fall. -/
def fallPoint (M r₀ θ₀ φ₀ τ : ℝ) : MinkowskiModel 3 :=
  ![fallTime M r₀ τ, fallRadius M r₀ τ, θ₀, φ₀]

open Classical in
/-- **The radial fall from rest at `r₀`** in the exterior Schwarzschild co-ordinates
`(t(τ), r(τ), θ₀, φ₀)`, at the parameters where it lies in the exterior; elsewhere it is held at a
fixed point. -/
def fall (M r₀ θ₀ φ₀ : ℝ) (τ : ℝ) : SchwarzschildExterior.domain M :=
  if h : fallPoint M r₀ θ₀ φ₀ τ ∈ SchwarzschildExterior.domain M then ⟨_, h⟩
  else ⟨basePoint M, basePoint_mem M⟩

theorem fallPoint_mem (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    fallPoint M r₀ θ₀ φ₀ τ ∈ SchwarzschildExterior.domain M :=
  ⟨two_mul_lt_fallRadius hM hr hτ, hθ.1, hθ.2⟩

theorem fall_val (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) = fallPoint M r₀ θ₀ φ₀ τ := by
  simp [fall, fallPoint_mem hM hr hθ hτ]

/-- The second derivative of the Schwarzschild time along the fall. -/
def fallTimeAccel (M r₀ τ : ℝ) : ℝ :=
  -(fallEnergy M r₀ * (2 * M * fallVelocity M r₀ τ / fallRadius M r₀ τ ^ 2)) /
    (1 - 2 * M / fallRadius M r₀ τ) ^ 2

/-- **The radial fall from rest is a geodesic** of the exterior Schwarzschild field: the curve
`τ ↦ (t(τ), r(τ), θ₀, φ₀)`, with the cycloid `r = (r₀/2)(1 + cos η)`,
`τ = √(r₀³/8M)(η + sin η)` and `dt/dτ = E/(1 − 2M/r)`, satisfies the geodesic equation for
`|τ| < τ_h`. -/
theorem isGeodesicOn_fall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    (SchwarzschildExterior.metric hM.le).toLorentzMetric.IsGeodesicOn
      (Ioo (-horizonTime M r₀) (horizonTime M r₀)) (fall M r₀ θ₀ φ₀) := by
  set S := Ioo (-horizonTime M r₀) (horizonTime M r₀) with hS
  have hev (τ : ℝ) (hτ : τ ∈ S) :
      (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) =ᶠ[𝓝 τ] fallPoint M r₀ θ₀ φ₀ :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun σ hσ => fall_val hM hr hθ hσ
  have hd1 (τ : ℝ) (hτ : τ ∈ S) : HasDerivAt (fallPoint M r₀ θ₀ φ₀)
      ![fallTimeRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] τ :=
    hasDerivAt_vec (hasDerivAt_fallTime hM hr hτ)
      (hasDerivAt_fallRadius hM hr (horizon_subset hM hr hτ)) (hasDerivAt_const _ _)
      (hasDerivAt_const _ _)
  have hd2 (τ : ℝ) (hτ : τ ∈ S) : HasDerivAt
      (fun σ => (![fallTimeRate M r₀ σ, fallVelocity M r₀ σ, 0, 0] : MinkowskiModel 3))
      ![fallTimeAccel M r₀ τ, -(M / fallRadius M r₀ τ ^ 2), 0, 0] τ :=
    hasDerivAt_vec (hasDerivAt_fallTimeRate hM hr hτ)
      (hasDerivAt_fallVelocity hM hr (horizon_subset hM hr hτ)) (hasDerivAt_const _ _)
      (hasDerivAt_const _ _)
  have hderiv (τ : ℝ) (hτ : τ ∈ S) : deriv (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) τ =
      ![fallTimeRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] := by
    rw [(hev τ hτ).deriv_eq]
    exact (hd1 τ hτ).deriv
  have hderiv2 (τ : ℝ) (hτ : τ ∈ S) :
      deriv (deriv (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3))) τ =
        ![fallTimeAccel M r₀ τ, -(M / fallRadius M r₀ τ ^ 2), 0, 0] := by
    have h : deriv (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) =ᶠ[𝓝 τ]
        fun σ => ![fallTimeRate M r₀ σ, fallVelocity M r₀ σ, 0, 0] :=
      eventually_of_mem (isOpen_Ioo.mem_nhds hτ) hderiv
    rw [h.deriv_eq]
    exact (hd2 τ hτ).deriv
  have hc : ContDiffOn ℝ 2 (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) S := by
    have h : ContDiffOn ℝ 2 (fallPoint M r₀ θ₀ φ₀) S := by
      refine contDiffOn_pi.mpr fun i => ?_
      fin_cases i
      · simpa [fallPoint] using contDiffOn_fallTime hM hr
      · simpa [fallPoint] using
          ((contDiffOn_fallRadius hM hr).mono (horizon_subset hM hr)).of_le (by norm_num)
      · simpa [fallPoint] using contDiffOn_const
      · simpa [fallPoint] using contDiffOn_const
    exact h.congr fun τ hτ => fall_val hM hr hθ hτ
  rw [(SchwarzschildExterior.metric hM.le).isGeodesicOn_iff isOpen_Ioo hc]
  intro τ hτ k
  rw [hderiv2 τ hτ, hderiv τ hτ]
  simp only [EddingtonFinkelstein.sum_four,
    SchwarzschildExterior.christoffelOf_metric hM.le (fall M r₀ θ₀ φ₀ τ).property]
  rw [fall_val hM hr hθ hτ]
  have hv := fallVelocity_sq hM hr (horizon_subset hM hr hτ)
  have hE := fallEnergy_sq hM hr
  have h2 := two_mul_lt_fallRadius hM hr hτ
  have hr0 : fallRadius M r₀ τ ≠ 0 := by linarith
  have hr1 : fallRadius M r₀ τ - 2 * M ≠ 0 := by linarith
  have h0 := (pos_of_two_mul_lt hM hr).ne'
  have hf : 1 - 2 * M / fallRadius M r₀ τ ≠ 0 := (lapse_fall_pos hM hr hτ).ne'
  have key : fallTimeRate M r₀ τ * fallTimeRate M r₀ τ =
      (1 - 2 * M / r₀) / (1 - 2 * M / fallRadius M r₀ τ) ^ 2 := by
    rw [fallTimeRate, div_mul_div_comm, ← sq, hE, sq]
  have key2 : fallVelocity M r₀ τ * fallVelocity M r₀ τ =
      2 * M / fallRadius M r₀ τ - 2 * M / r₀ := by
    rw [← sq, hv]
  fin_cases k <;> simp [SchwarzschildExterior.christoffel, fallPoint]
  · rw [fallTimeAccel, fallTimeRate]
    field_simp
    ring
  · linear_combination (norm := skip)
      M * (fallRadius M r₀ τ - 2 * M) / fallRadius M r₀ τ ^ 3 * key -
        M / (fallRadius M r₀ τ * (fallRadius M r₀ τ - 2 * M)) * key2
    field_simp
    linear_combination (M * fallRadius M r₀ τ * r₀) * mul_inv_cancel₀ hr1

/-- The co-ordinate velocity of the fall is `(E/(1 − 2M/r), dr/dτ, 0, 0)`. -/
theorem deriv_fall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    HasDerivAt (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3))
      ![fallTimeRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] τ := by
  have hev : (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) =ᶠ[𝓝 τ] fallPoint M r₀ θ₀ φ₀ :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun σ hσ => fall_val hM hr hθ hσ
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  exact hasDerivAt_vec (hasDerivAt_fallTime hM hr hτ)
    (hasDerivAt_fallRadius hM hr (horizon_subset hM hr hτ)) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _)

/-- **The fall is parametrized by its proper time**: `g(γ̇, γ̇) = −1`. -/
theorem form_curveVelocity_fall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ}
    (hθ : θ₀ ∈ Ioo 0 π) (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    (SchwarzschildExterior.metric hM.le).toLorentzMetric.form (fall M r₀ θ₀ φ₀ τ)
      (LorentzMetric.curveVelocity (fall M r₀ θ₀ φ₀) τ)
      (LorentzMetric.curveVelocity (fall M r₀ θ₀ φ₀) τ) = -1 := by
  have hd := deriv_fall hM hr (φ₀ := φ₀) hθ hτ
  rw [SchwarzschildExterior.form_curveVelocity_eq_coord hM.le hd.differentiableAt, hd.deriv,
    fall_val hM hr hθ hτ]
  have hv := fallVelocity_sq hM hr (horizon_subset hM hr hτ)
  have hE := fallEnergy_sq hM hr
  have hf := (lapse_fall_pos hM hr hτ).ne'
  have h2 := two_mul_lt_fallRadius hM hr hτ
  have hr0 : fallRadius M r₀ τ ≠ 0 := by linarith
  simp [fallPoint]
  rw [fallTimeRate, div_pow, hE, hv]
  field_simp
  ring

/-- The fall is at rest at `τ = 0`, at the radius `r₀`. -/
theorem fall_rest (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ : ℝ} (hθ : θ₀ ∈ Ioo 0 π) :
    (fall M r₀ θ₀ φ₀ 0 : MinkowskiModel 3) 1 = r₀ ∧
      deriv (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) 0 1 = 0 := by
  have h0 := zero_mem_horizon hM hr
  refine ⟨?_, ?_⟩
  · rw [fall_val hM hr hθ h0]
    simp [fallPoint, fallRadius_zero]
  · rw [(deriv_fall hM hr hθ h0).deriv]
    simp [fallVelocity, fallAngle, cycloidParam_zero]

/-- The proper time of the fall from `τ = 0` to `τ` is `τ`. -/
theorem properTime_fall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    properTime (SchwarzschildExterior.metric hM.le).toLorentzMetric (fall M r₀ θ₀ φ₀) 0 τ = τ := by
  have hsub : uIcc 0 τ ⊆ Ioo (-horizonTime M r₀) (horizonTime M r₀) :=
    ordConnected_Ioo.uIcc_subset (zero_mem_horizon hM hr) hτ
  rw [properTime_geodesic _ fun s hs => isGeodesicOn_fall hM hr φ₀ hθ s (hsub hs), speedAlong,
    properSpeed, form_curveVelocity_fall hM hr hθ (zero_mem_horizon hM hr)]
  simp

/-- **The proper time of the fall from rest is finite** (Landau–Lifshitz, §102, the cycloid
(102.3)). A body that falls radially from rest at `r₀ > 2M` is the geodesic `fall`, parametrized by
its proper time, with `r = (r₀/2)(1 + cos η)`, `τ = √(r₀³/8M)(η + sin η)` and `dr/dτ = 0` at
`τ = 0`. It reaches the sphere `r = 2M` at the finite proper time
`τ_h = √(r₀³/8M)(η_h + sin η_h)`, `cos η_h = 4M/r₀ − 1`: the proper time elapsed along the
geodesic up to `τ < τ_h` is `τ`, and `r(τ) → 2M` as `τ → τ_h`. The cycloid continues to the
centre `r = 0`, which it reaches at `τ = π √(r₀³/8M) > τ_h`, and it satisfies the radial equation
`(dr/dτ)² = 2M/r − 2M/r₀` and `d²r/dτ² = −M/r²` on the whole fall from `r₀` to the centre. -/
theorem radialInfall_properTime (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    (∀ τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀),
      (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1 =
          r₀ / 2 * (1 + Real.cos (fallAngle M r₀ τ)) ∧
        τ = Real.sqrt (r₀ ^ 3 / (8 * M)) *
          (fallAngle M r₀ τ + Real.sin (fallAngle M r₀ τ)) ∧
        properTime (SchwarzschildExterior.metric hM.le).toLorentzMetric (fall M r₀ θ₀ φ₀) 0 τ =
          τ) ∧
      horizonTime M r₀ = Real.sqrt (r₀ ^ 3 / (8 * M)) *
        (Real.arccos (4 * M / r₀ - 1) + Real.sin (Real.arccos (4 * M / r₀ - 1))) ∧
      Tendsto (fun τ => (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1) (𝓝[<] horizonTime M r₀)
        (𝓝 (2 * M)) ∧
      horizonTime M r₀ < π * Real.sqrt (r₀ ^ 3 / (8 * M)) ∧
      (∀ τ ∈ Ioo (-(π * Real.sqrt (r₀ ^ 3 / (8 * M)))) (π * Real.sqrt (r₀ ^ 3 / (8 * M))),
        0 < fallRadius M r₀ τ ∧
          fallVelocity M r₀ τ ^ 2 = 2 * M / fallRadius M r₀ τ - 2 * M / r₀ ∧
          HasDerivAt (fallRadius M r₀) (fallVelocity M r₀ τ) τ ∧
          HasDerivAt (fallVelocity M r₀) (-(M / fallRadius M r₀ τ ^ 2)) τ) ∧
      Tendsto (fallRadius M r₀) (𝓝[<] (π * Real.sqrt (r₀ ^ 3 / (8 * M)))) (𝓝 0) := by
  have hcont : ContinuousOn (fallRadius M r₀) (Icc (-crunchTime M r₀) (crunchTime M r₀)) := by
    refine (continuous_const.mul (continuous_const.add
      (Real.continuous_cos.comp (continuous_cycloidParam.comp
        (continuous_id.div_const _))))).continuousOn
  refine ⟨fun τ hτ => ⟨?_, ?_, properTime_fall hM hr hθ hτ⟩, rfl, ?_,
    horizonTime_lt_crunchTime hM hr, fun τ hτ => ⟨fallRadius_pos hM hr hτ,
      fallVelocity_sq hM hr hτ, hasDerivAt_fallRadius hM hr hτ, hasDerivAt_fallVelocity hM hr hτ⟩,
    ?_⟩
  · rw [fall_val hM hr hθ hτ]
    rfl
  · exact (fallScale_mul_cycloidTime hM hr τ).symm
  · have hT := horizonTime_pos hM hr
    have hT' := horizonTime_lt_crunchTime hM hr
    have hlim : Tendsto (fallRadius M r₀) (𝓝 (horizonTime M r₀)) (𝓝 (2 * M)) := by
      rw [← fallRadius_horizonTime hM hr]
      exact (hcont.continuousAt (Icc_mem_nhds (by linarith) (horizonTime_lt_crunchTime hM hr)))
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show -horizonTime M r₀ < horizonTime M r₀ by linarith)]
      with τ hτ
    rw [fall_val hM hr hθ hτ]
    rfl
  · have hc : Tendsto (fallRadius M r₀) (𝓝 (crunchTime M r₀)) (𝓝 0) := by
      rw [← fallRadius_crunchTime hM hr]
      exact (continuous_const.mul (continuous_const.add
        (Real.continuous_cos.comp (continuous_cycloidParam.comp
          (continuous_id.div_const _))))).continuousAt
    exact hc.mono_left nhdsWithin_le_nhds

/-! ### The Schwarzschild time diverges at the sphere `r = 2M` -/

/-- Outside the sphere `r = 2M`, `dr/dτ > −1` along the fall. -/
theorem neg_one_lt_fallVelocity (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) : -1 < fallVelocity M r₀ τ := by
  have hv := fallVelocity_sq hM hr (horizon_subset hM hr hτ)
  have h2 := two_mul_lt_fallRadius hM hr hτ
  have h0 := pos_of_two_mul_lt hM hr
  have h3 : 2 * M / fallRadius M r₀ τ < 1 := (div_lt_one (by linarith)).mpr h2
  have h4 : 0 < 2 * M / r₀ := by positivity
  nlinarith

/-- `r(τ) − 2M ≤ τ_h − τ` for `0 ≤ τ ≤ τ_h`. -/
theorem fallRadius_sub_le (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Icc 0 (horizonTime M r₀)) : fallRadius M r₀ τ - 2 * M ≤ horizonTime M r₀ - τ := by
  have hT := horizonTime_pos hM hr
  have hT' := horizonTime_lt_crunchTime hM hr
  have hsub : Icc 0 (horizonTime M r₀) ⊆ Ioo (-crunchTime M r₀) (crunchTime M r₀) :=
    Icc_subset_Ioo (by linarith) hT'
  have hmono : MonotoneOn (fun σ => fallRadius M r₀ σ + σ) (Icc 0 (horizonTime M r₀)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (((contDiffOn_fallRadius hM hr).continuousOn.mono hsub).add continuousOn_id) ?_ ?_
    · rw [interior_Icc]
      exact fun σ hσ => ((hasDerivAt_fallRadius hM hr (hsub (Ioo_subset_Icc_self hσ))).fun_add
        (hasDerivAt_id' σ)).differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      rw [((hasDerivAt_fallRadius hM hr (hsub (Ioo_subset_Icc_self hσ))).fun_add
        (hasDerivAt_id' σ)).deriv]
      linarith [neg_one_lt_fallVelocity hM hr ⟨by linarith [hσ.1], hσ.2⟩]
  have h := hmono hτ ⟨hT.le, le_rfl⟩ hτ.2
  simp only [fallRadius_horizonTime hM hr] at h
  linarith

/-- The lower bound `t(τ) ≥ 2ME (log τ_h − log(τ_h − τ))` of the Schwarzschild time. -/
theorem fallTime_ge (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ico 0 (horizonTime M r₀)) :
    2 * M * fallEnergy M r₀ *
        (Real.log (horizonTime M r₀) - Real.log (horizonTime M r₀ - τ)) ≤ fallTime M r₀ τ := by
  have hT := horizonTime_pos hM hr
  have hE := fallEnergy_pos hM hr
  set c := 2 * M * fallEnergy M r₀ with hc
  have hsub : Ico 0 (horizonTime M r₀) ⊆ Ioo (-horizonTime M r₀) (horizonTime M r₀) :=
    fun σ hσ => ⟨by linarith [hσ.1], hσ.2⟩
  have hF (σ : ℝ) (hσ : σ ∈ Ico 0 (horizonTime M r₀)) :
      HasDerivAt (fun σ => fallTime M r₀ σ + c * Real.log (horizonTime M r₀ - σ))
        (fallTimeRate M r₀ σ + c * (-1 / (horizonTime M r₀ - σ))) σ :=
    (hasDerivAt_fallTime hM hr (hsub hσ)).fun_add
      ((((hasDerivAt_id' σ).const_sub (horizonTime M r₀)).log
        (sub_pos.mpr hσ.2).ne').const_mul c)
  have hmono : MonotoneOn (fun σ => fallTime M r₀ σ + c * Real.log (horizonTime M r₀ - σ))
      (Ico 0 (horizonTime M r₀)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico _ _)
      (fun σ hσ => (hF σ hσ).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ico]
      exact fun σ hσ => (hF σ (Ioo_subset_Ico_self hσ)).differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Ico] at hσ
      rw [(hF σ (Ioo_subset_Ico_self hσ)).deriv]
      have h1 := fallRadius_sub_le hM hr ⟨hσ.1.le, hσ.2.le⟩
      have h2 := two_mul_lt_fallRadius hM hr (hsub (Ioo_subset_Ico_self hσ))
      have hd : 0 < horizonTime M r₀ - σ := sub_pos.mpr hσ.2
      have hf : 1 - 2 * M / fallRadius M r₀ σ ≤ (horizonTime M r₀ - σ) / (2 * M) := by
        have hr0 : 0 < fallRadius M r₀ σ := by linarith
        rw [one_sub_div hr0.ne', div_le_div_iff₀ hr0 (by linarith)]
        nlinarith
      have hf0 := lapse_fall_pos hM hr (hsub (Ioo_subset_Ico_self hσ))
      have hrate : c / (horizonTime M r₀ - σ) ≤ fallTimeRate M r₀ σ := by
        rw [fallTimeRate, hc, div_le_div_iff₀ hd hf0]
        rw [le_div_iff₀ (by linarith)] at hf
        nlinarith
      have : c * (-1 / (horizonTime M r₀ - σ)) = -(c / (horizonTime M r₀ - σ)) := by ring
      linarith
  have h := hmono ⟨le_rfl, hT⟩ hτ hτ.1
  simp only [fallTime, intervalIntegral.integral_same, sub_zero, zero_add] at h
  simp only [fallTime]
  linarith

/-- **The Schwarzschild time diverges at the sphere `r = 2M`** (Landau–Lifshitz, §102): along
the fall from rest, `t(τ) → ∞` as `τ → τ_h`, while the proper time stays finite. -/
theorem tendsto_coordinateTime (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    Tendsto (fun τ => (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 0) (𝓝[<] horizonTime M r₀)
      atTop := by
  have hT := horizonTime_pos hM hr
  have hlog : Tendsto (fun τ => Real.log (horizonTime M r₀ - τ)) (𝓝[<] horizonTime M r₀)
      atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
    · have h : Tendsto (fun τ => horizonTime M r₀ - τ) (𝓝 (horizonTime M r₀))
          (𝓝 (horizonTime M r₀ - horizonTime M r₀)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact sub_pos.mpr hτ
  have hlow : Tendsto (fun τ => 2 * M * fallEnergy M r₀ *
      (Real.log (horizonTime M r₀) - Real.log (horizonTime M r₀ - τ)))
      (𝓝[<] horizonTime M r₀) atTop := by
    have h1 := tendsto_atTop_add_const_left _ (Real.log (horizonTime M r₀))
      (tendsto_neg_atBot_atTop.comp hlog)
    refine (h1.const_mul_atTop (mul_pos (mul_pos two_pos hM) (fallEnergy_pos hM hr))).congr
      fun τ => ?_
    simp [sub_eq_add_neg]
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [Ioo_mem_nhdsLT hT] with τ hτ
  rw [fall_val hM hr hθ ⟨by linarith [hτ.1], hτ.2⟩]
  exact fallTime_ge hM hr ⟨hτ.1.le, hτ.2⟩

/-! ### Outgoing radial light rays and the red shift of the falling surface -/

/-- The tortoise co-ordinate `r* = r + 2M log(r − 2M)` of the exterior, up to a constant. -/
def tortoise (M r : ℝ) : ℝ := r + 2 * M * Real.log (r - 2 * M)

/-- The rate `dt/dr = r/(r − 2M)` of an outgoing radial light ray. -/
def rayRate (M r : ℝ) : ℝ := r / (r - 2 * M)

theorem hasDerivAt_tortoise {r : ℝ} (h : 2 * M < r) :
    HasDerivAt (tortoise M) (rayRate M r) r := by
  have h1 : r - 2 * M ≠ 0 := by linarith
  have := (hasDerivAt_id' r).fun_add
    ((((hasDerivAt_id' r).sub_const (2 * M)).log h1).const_mul (2 * M))
  refine this.congr_deriv ?_
  rw [rayRate]
  field_simp
  ring

theorem hasDerivAt_rayRate {r : ℝ} (h : 2 * M < r) :
    HasDerivAt (rayRate M) (-(2 * M) / (r - 2 * M) ^ 2) r := by
  have h1 : r - 2 * M ≠ 0 := by linarith
  refine ((hasDerivAt_id' r).fun_div ((hasDerivAt_id' r).sub_const (2 * M)) h1).congr_deriv ?_
  field_simp
  ring

/-- The point `(t₁ + r*(r₁ + s) − r*(r₁), r₁ + s, θ₀, φ₀)` of the outgoing radial ray. -/
def rayPoint (M t₁ r₁ θ₀ φ₀ s : ℝ) : MinkowskiModel 3 :=
  ![t₁ + tortoise M (r₁ + s) - tortoise M r₁, r₁ + s, θ₀, φ₀]

open Classical in
/-- **The outgoing radial light ray** from the event `(t₁, r₁, θ₀, φ₀)` of the exterior: the
curve `s ↦ (t₁ + r*(r₁ + s) − r*(r₁), r₁ + s, θ₀, φ₀)` with the affine parameter `s = r − r₁`,
at the parameters where it lies in the exterior; elsewhere it is held at a fixed point. -/
def outgoingRay (M t₁ r₁ θ₀ φ₀ : ℝ) (s : ℝ) : SchwarzschildExterior.domain M :=
  if h : rayPoint M t₁ r₁ θ₀ φ₀ s ∈ SchwarzschildExterior.domain M then ⟨_, h⟩
  else ⟨basePoint M, basePoint_mem M⟩

theorem rayPoint_mem {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    rayPoint M t₁ r₁ θ₀ φ₀ s ∈ SchwarzschildExterior.domain M := by
  have h : 2 * M - r₁ < s := hs
  refine ⟨?_, hθ.1, hθ.2⟩
  change 2 * M < r₁ + s
  linarith

theorem outgoingRay_val {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    (outgoingRay M t₁ r₁ θ₀ φ₀ s : MinkowskiModel 3) = rayPoint M t₁ r₁ θ₀ φ₀ s := by
  simp [outgoingRay, rayPoint_mem hθ hs]

/-- The co-ordinate velocity of the ray is `(r/(r − 2M), 1, 0, 0)`. -/
theorem deriv_outgoingRay {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    HasDerivAt (fun s => (outgoingRay M t₁ r₁ θ₀ φ₀ s : MinkowskiModel 3))
      ![rayRate M (r₁ + s), 1, 0, 0] s := by
  have hev : (fun s => (outgoingRay M t₁ r₁ θ₀ φ₀ s : MinkowskiModel 3)) =ᶠ[𝓝 s]
      rayPoint M t₁ r₁ θ₀ φ₀ :=
    eventually_of_mem (isOpen_Ioi.mem_nhds hs) fun σ hσ => outgoingRay_val hθ hσ
  have h : 2 * M < r₁ + s := by
    have : 2 * M - r₁ < s := hs
    linarith
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  refine hasDerivAt_vec ?_ ?_ (hasDerivAt_const _ _) (hasDerivAt_const _ _)
  · have := (hasDerivAt_tortoise h).comp s ((hasDerivAt_id' s).const_add r₁)
    refine ((this.const_add t₁).sub_const (tortoise M r₁)).congr_deriv ?_
    simp
  · simpa using (hasDerivAt_id' s).const_add r₁

/-- **The outgoing radial rays are geodesics** of the exterior Schwarzschild field. -/
theorem isGeodesicOn_outgoingRay (hM : 0 ≤ M) (t₁ r₁ : ℝ) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    (SchwarzschildExterior.metric hM).toLorentzMetric.IsGeodesicOn (Ioi (2 * M - r₁))
      (outgoingRay M t₁ r₁ θ₀ φ₀) := by
  set S := Ioi (2 * M - r₁) with hS
  have hr (s : ℝ) (hs : s ∈ S) : 2 * M < r₁ + s := by
    have : 2 * M - r₁ < s := hs
    linarith
  have hd2 (s : ℝ) (hs : s ∈ S) : HasDerivAt
      (fun σ => (![rayRate M (r₁ + σ), 1, 0, 0] : MinkowskiModel 3))
      ![-(2 * M) / (r₁ + s - 2 * M) ^ 2, 0, 0, 0] s := by
    refine hasDerivAt_vec ?_ (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    have := (hasDerivAt_rayRate (hr s hs)).comp s ((hasDerivAt_id' s).const_add r₁)
    exact this.congr_deriv (mul_one _)
  have hderiv (s : ℝ) (hs : s ∈ S) :
      deriv (fun σ => (outgoingRay M t₁ r₁ θ₀ φ₀ σ : MinkowskiModel 3)) s =
        ![rayRate M (r₁ + s), 1, 0, 0] :=
    (deriv_outgoingRay hθ hs).deriv
  have hderiv2 (s : ℝ) (hs : s ∈ S) :
      deriv (deriv (fun σ => (outgoingRay M t₁ r₁ θ₀ φ₀ σ : MinkowskiModel 3))) s =
        ![-(2 * M) / (r₁ + s - 2 * M) ^ 2, 0, 0, 0] := by
    have h : deriv (fun σ => (outgoingRay M t₁ r₁ θ₀ φ₀ σ : MinkowskiModel 3)) =ᶠ[𝓝 s]
        fun σ => ![rayRate M (r₁ + σ), 1, 0, 0] :=
      eventually_of_mem (isOpen_Ioi.mem_nhds hs) hderiv
    rw [h.deriv_eq]
    exact (hd2 s hs).deriv
  have hc : ContDiffOn ℝ 2 (fun σ => (outgoingRay M t₁ r₁ θ₀ φ₀ σ : MinkowskiModel 3)) S := by
    have hlog : ContDiffOn ℝ 2 (fun σ => Real.log (r₁ + σ - 2 * M)) S :=
      ((contDiffOn_const.add contDiffOn_id).sub contDiffOn_const).log
        fun σ hσ => by have := hr σ hσ; simp only [id]; linarith
    have h : ContDiffOn ℝ 2 (rayPoint M t₁ r₁ θ₀ φ₀) S := by
      refine contDiffOn_pi.mpr fun i => ?_
      fin_cases i
      · simpa [rayPoint, tortoise] using ((contDiffOn_const.add
          ((contDiffOn_const.add contDiffOn_id).add (contDiffOn_const.mul hlog))).sub
            contDiffOn_const)
      · simpa [rayPoint] using contDiffOn_const.add contDiffOn_id
      · simpa [rayPoint] using contDiffOn_const
      · simpa [rayPoint] using contDiffOn_const
    exact h.congr fun s hs => outgoingRay_val hθ hs
  rw [(SchwarzschildExterior.metric hM).isGeodesicOn_iff isOpen_Ioi hc]
  intro s hs k
  rw [hderiv2 s hs, hderiv s hs]
  simp only [EddingtonFinkelstein.sum_four,
    SchwarzschildExterior.christoffelOf_metric hM (outgoingRay M t₁ r₁ θ₀ φ₀ s).property]
  rw [outgoingRay_val hθ hs]
  have h2 := hr s hs
  have hr0 : r₁ + s ≠ 0 := by linarith
  have hr1 : r₁ + s - 2 * M ≠ 0 := by linarith
  fin_cases k <;> simp [SchwarzschildExterior.christoffel, rayPoint, rayRate]
  · field_simp
    ring
  · field_simp
    ring

/-- **The outgoing radial rays are null**: `g(k, k) = 0`. -/
theorem form_outgoingRay_velocity (hM : 0 ≤ M) {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hs : s ∈ Ioi (2 * M - r₁)) :
    (SchwarzschildExterior.metric hM).toLorentzMetric.form (outgoingRay M t₁ r₁ θ₀ φ₀ s)
      (LorentzMetric.curveVelocity (outgoingRay M t₁ r₁ θ₀ φ₀) s)
      (LorentzMetric.curveVelocity (outgoingRay M t₁ r₁ θ₀ φ₀) s) = 0 := by
  have hd := deriv_outgoingRay (t₁ := t₁) (φ₀ := φ₀) hθ hs
  rw [SchwarzschildExterior.form_curveVelocity_eq_coord hM hd.differentiableAt, hd.deriv,
    outgoingRay_val hθ hs]
  have h2 : 2 * M < r₁ + s := by
    have : 2 * M - r₁ < s := hs
    linarith
  have hr0 : r₁ + s ≠ 0 := by linarith
  have hr1 : r₁ + s - 2 * M ≠ 0 := by linarith
  simp [rayPoint, rayRate]
  field_simp
  ring

/-- The frequency that a static observer measures on an outgoing radial ray at the radius
`r = r₁ + s` is `1/√(1 − 2M/r)`, in the red-shift convention `ω = −g(K/N, k)` of §88. -/
theorem observedFrequency_outgoingRay (hM : 0 ≤ M) (x₀ : SchwarzschildExterior.domain M)
    {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    (SchwarzschildExterior.metric hM).toLorentzMetric.observedFrequency
        (LorentzMetric.chartField (CoordinateMetric.physicalChart x₀) (Pi.single 0 1))
        (outgoingRay M t₁ r₁ θ₀ φ₀) s =
      1 / Real.sqrt (1 - 2 * M / (r₁ + s)) := by
  have hd := deriv_outgoingRay (t₁ := t₁) (φ₀ := φ₀) hθ hs
  have h2 : 2 * M < r₁ + s := by
    have : 2 * M - r₁ < s := hs
    linarith
  have hr0 : r₁ + s ≠ 0 := by linarith
  have hr1 : r₁ + s - 2 * M ≠ 0 := by linarith
  have hf : 0 < 1 - 2 * M / (r₁ + s) := by
    have : 2 * M / (r₁ + s) < 1 := (div_lt_one (by linarith)).mpr h2
    linarith
  have hN := LorentzMetric.killingNorm_mul_observedFrequency
    (SchwarzschildExterior.form_time_neg hM x₀ (outgoingRay M t₁ r₁ θ₀ φ₀ s))
  rw [SchwarzschildExterior.killingNorm_time hM x₀,
    (SchwarzschildExterior.metric hM).pairing_curveVelocity hd.differentiableAt x₀,
    SchwarzschildExterior.coefficient_eq_diagonal, hd.deriv, outgoingRay_val hθ hs] at hN
  simp [EddingtonFinkelstein.sum_four, Matrix.diagonal_apply,
    SchwarzschildExterior.diagonalCoefficients, rayPoint, rayRate] at hN
  have hpos : 0 < Real.sqrt (1 - 2 * M / (r₁ + s)) := Real.sqrt_pos.mpr hf
  rw [eq_div_iff hpos.ne', mul_comm, hN]
  field_simp

/-- The outgoing ray sent from the falling body at its proper time `τ`. -/
def emissionRay (M r₀ θ₀ φ₀ τ : ℝ) : ℝ → SchwarzschildExterior.domain M :=
  outgoingRay M (fallTime M r₀ τ) (fallRadius M r₀ τ) θ₀ φ₀

theorem zero_mem_emission (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    (0 : ℝ) ∈ Ioi (2 * M - fallRadius M r₀ τ) := by
  have := two_mul_lt_fallRadius hM hr hτ
  change 2 * M - fallRadius M r₀ τ < 0
  linarith

/-- The ray `emissionRay τ` starts at the event `fall τ`. -/
theorem emissionRay_zero (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    emissionRay M r₀ θ₀ φ₀ τ 0 = fall M r₀ θ₀ φ₀ τ := by
  apply Subtype.ext
  rw [emissionRay, outgoingRay_val hθ (zero_mem_emission hM hr hτ), fall_val hM hr hθ hτ]
  simp [rayPoint, fallPoint]

/-- The frequency `ω = −g(u, k)` of the signal `emissionRay τ` measured at its emission by the
falling body: the convention of `observedFrequency`, with the velocity `u` of the emitter in place
of a static velocity. It is written in the co-ordinates, with the co-ordinate velocities `u` of
the fall and `k` of the ray at the emission event and the form of the coordinate metric, which
are the native velocities and form (`CoordinateMetric.curveVelocity_val`,
`CoordinateMetric.toLorentzMetric_form`). -/
def emittedFrequency (hM : 0 ≤ M) (r₀ θ₀ φ₀ τ : ℝ) : ℝ :=
  -(SchwarzschildExterior.metric hM).form (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3)
    (deriv (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) τ)
    (deriv (fun s => (emissionRay M r₀ θ₀ φ₀ τ s : MinkowskiModel 3)) 0)

/-- The emitted frequency is `(E − dr/dτ)/(1 − 2M/r)`. -/
theorem emittedFrequency_eq (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    emittedFrequency hM.le r₀ θ₀ φ₀ τ =
      (fallEnergy M r₀ - fallVelocity M r₀ τ) / (1 - 2 * M / fallRadius M r₀ τ) := by
  have hd := deriv_fall hM hr (φ₀ := φ₀) hθ hτ
  have hk := deriv_outgoingRay (M := M) (t₁ := fallTime M r₀ τ) (φ₀ := φ₀) hθ
    (zero_mem_emission hM hr hτ)
  have h2 := two_mul_lt_fallRadius hM hr hτ
  have hr0 : fallRadius M r₀ τ ≠ 0 := by linarith
  have hr1 : fallRadius M r₀ τ - 2 * M ≠ 0 := by linarith
  have hf := (lapse_fall_pos hM hr hτ).ne'
  unfold emittedFrequency
  rw [CoordinateMetric.form_apply, hd.deriv, emissionRay, hk.deriv,
    SchwarzschildExterior.coefficient_eq_diagonal, fall_val hM hr hθ hτ]
  simp [EddingtonFinkelstein.sum_four, Matrix.diagonal_apply,
    SchwarzschildExterior.diagonalCoefficients, fallPoint, rayRate, fallTimeRate]
  field_simp
  ring

/-- **The red shift of the collapsing surface** (Landau–Lifshitz, §102). Signals sent outwards
along the radial light rays from the falling surface reach a static observer at the radius
`R > 2M` with the ratio `ω_received/ω_emitted → 0` of the frequencies as the surface approaches
the sphere `r = 2M`: the received frequency is `1/√(1 − 2M/R)` (the static observer's
`observedFrequency`, `ω = −g(K/N, k)`) and the emitted one, measured by the falling surface,
is `(E − dr/dτ)/(1 − 2M/r)`, so the ratio is `(1 − 2M/r)/(√(1 − 2M/R)(E − dr/dτ))`. -/
theorem tendsto_observedFrequency (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) (x₀ : SchwarzschildExterior.domain M) {R : ℝ} (hR : 2 * M < R) :
    Tendsto (fun τ => (SchwarzschildExterior.metric hM.le).toLorentzMetric.observedFrequency
        (LorentzMetric.chartField (CoordinateMetric.physicalChart x₀) (Pi.single 0 1))
        (emissionRay M r₀ θ₀ φ₀ τ) (R - fallRadius M r₀ τ) / emittedFrequency hM.le r₀ θ₀ φ₀ τ)
      (𝓝[<] horizonTime M r₀) (𝓝 0) := by
  have hT := horizonTime_pos hM hr
  have hT' := horizonTime_lt_crunchTime hM hr
  have hmem : horizonTime M r₀ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀) := ⟨by linarith, hT'⟩
  have hrc : ContinuousAt (fallRadius M r₀) (horizonTime M r₀) :=
    (hasDerivAt_fallRadius hM hr hmem).continuousAt
  have hvc : ContinuousAt (fallVelocity M r₀) (horizonTime M r₀) :=
    (hasDerivAt_fallVelocity hM hr hmem).continuousAt
  have hv0 : fallVelocity M r₀ (horizonTime M r₀) ≤ 0 := fallVelocity_nonpos hM hr ⟨hT.le, hT'⟩
  have hE := fallEnergy_pos hM hr
  have hR0 : 0 < R := by linarith
  have hN : 0 < Real.sqrt (1 - 2 * M / R) := by
    have : 2 * M / R < 1 := (div_lt_one hR0).mpr hR
    exact Real.sqrt_pos.mpr (by linarith)
  have hlim : Tendsto (fun τ => (1 - 2 * M / fallRadius M r₀ τ) /
      (Real.sqrt (1 - 2 * M / R) * (fallEnergy M r₀ - fallVelocity M r₀ τ)))
      (𝓝 (horizonTime M r₀)) (𝓝 0) := by
    have hr2 : fallRadius M r₀ (horizonTime M r₀) ≠ 0 := by
      rw [fallRadius_horizonTime hM hr]
      positivity
    have hden : Real.sqrt (1 - 2 * M / R) *
        (fallEnergy M r₀ - fallVelocity M r₀ (horizonTime M r₀)) ≠ 0 :=
      (mul_pos hN (by linarith)).ne'
    have h1 : Tendsto (fun τ => 1 - 2 * M / fallRadius M r₀ τ) (𝓝 (horizonTime M r₀))
        (𝓝 (1 - 2 * M / fallRadius M r₀ (horizonTime M r₀))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div hrc.tendsto hr2)
    have h3 : Tendsto (fun τ => Real.sqrt (1 - 2 * M / R) *
        (fallEnergy M r₀ - fallVelocity M r₀ τ)) (𝓝 (horizonTime M r₀))
        (𝓝 (Real.sqrt (1 - 2 * M / R) *
          (fallEnergy M r₀ - fallVelocity M r₀ (horizonTime M r₀)))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub hvc.tendsto)
    have h4 := h1.div h3 hden
    rwa [fallRadius_horizonTime hM hr, div_self (by positivity), sub_self, zero_div] at h4
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ τ in 𝓝[<] horizonTime M r₀, fallRadius M r₀ τ < R := by
    have h := hrc.tendsto
    rw [fallRadius_horizonTime hM hr] at h
    exact (h.mono_left nhdsWithin_le_nhds).eventually_lt_const hR
  filter_upwards [Ioo_mem_nhdsLT (show -horizonTime M r₀ < horizonTime M r₀ by linarith), hev]
    with τ hτ hRτ
  have hs : R - fallRadius M r₀ τ ∈ Ioi (2 * M - fallRadius M r₀ τ) := by
    change 2 * M - fallRadius M r₀ τ < R - fallRadius M r₀ τ
    linarith
  have hf := (lapse_fall_pos hM hr hτ).ne'
  have hEv : 0 < fallEnergy M r₀ - fallVelocity M r₀ τ := by
    have hv2 := fallVelocity_sq hM hr (horizon_subset hM hr hτ)
    have hE2 := fallEnergy_sq hM hr
    have h2 := two_mul_lt_fallRadius hM hr hτ
    have h3 : 2 * M / fallRadius M r₀ τ < 1 := (div_lt_one (by linarith)).mpr h2
    nlinarith
  rw [emissionRay, observedFrequency_outgoingRay hM.le x₀ hθ hs,
    emittedFrequency_eq hM hr hθ hτ, show fallRadius M r₀ τ + (R - fallRadius M r₀ τ) = R by ring]
  field_simp

/-! ### The fall continued through the sphere `r = 2M` -/

/-- The radial velocity is smooth during the fall from `r₀` to the centre. -/
theorem contDiffOn_fallVelocity (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ ∞ (fallVelocity M r₀) (Ioo (-crunchTime M r₀) (crunchTime M r₀)) := by
  intro τ hτ
  have h1 : ContDiffAt ℝ ∞ (fallAngle M r₀) τ :=
    (contDiffAt_cycloidParam (div_fallScale_mem hM hr hτ)).comp τ (contDiffAt_id.div_const _)
  have hc := (one_add_cos_fallAngle_pos hM hr hτ).ne'
  have hA := (fallScale_pos hM hr).ne'
  exact ((contDiffAt_const.mul (Real.contDiff_sin.contDiffAt.comp τ h1)).div
    (contDiffAt_const.mul (contDiffAt_const.add (Real.contDiff_cos.contDiffAt.comp τ h1)))
    (mul_ne_zero hA hc)).contDiffWithinAt

/-- After `−τ_h`, `E − dr/dτ > 0`, through the sphere `r = 2M` to the centre. -/
theorem fallEnergy_sub_fallVelocity_pos (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    0 < fallEnergy M r₀ - fallVelocity M r₀ τ := by
  have hE := fallEnergy_pos hM hr
  rcases le_or_gt 0 τ with h0 | h0
  · have := fallVelocity_nonpos hM hr ⟨h0, hτ.2⟩
    linarith
  · have hτ' : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀) :=
      ⟨hτ.1, h0.trans (horizonTime_pos hM hr)⟩
    have hv2 := fallVelocity_sq hM hr (horizon_subset hM hr hτ')
    have hE2 := fallEnergy_sq hM hr
    have h2 := two_mul_lt_fallRadius hM hr hτ'
    have h3 : 2 * M / fallRadius M r₀ τ < 1 := (div_lt_one (by linarith)).mpr h2
    nlinarith

/-- The rate `dv/dτ = 1/(E − dr/dτ)` of the advanced time along the fall. -/
def advancedRate (M r₀ τ : ℝ) : ℝ := (fallEnergy M r₀ - fallVelocity M r₀ τ)⁻¹

/-- The advanced time `v(τ) = v(0) + ∫₀^τ dσ/(E − dr/dτ)` of the fall, with
`v(0) = r₀ + 2M log(r₀/2M − 1)`. -/
def advancedTime (M r₀ τ : ℝ) : ℝ :=
  r₀ + 2 * M * Real.log (r₀ / (2 * M) - 1) + ∫ σ in (0 : ℝ)..τ, advancedRate M r₀ σ

theorem ioo_horizon_crunch_subset (hM : 0 < M) (hr : 2 * M < r₀) :
    Ioo (-horizonTime M r₀) (crunchTime M r₀) ⊆ Ioo (-crunchTime M r₀) (crunchTime M r₀) :=
  Ioo_subset_Ioo (by linarith [horizonTime_lt_crunchTime hM hr]) le_rfl

theorem hasDerivAt_advancedRate (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (advancedRate M r₀)
      (-(M / fallRadius M r₀ τ ^ 2) / (fallEnergy M r₀ - fallVelocity M r₀ τ) ^ 2) τ := by
  have h := ((hasDerivAt_fallVelocity hM hr (ioo_horizon_crunch_subset hM hr hτ)).const_sub
    (fallEnergy M r₀)).fun_inv (fallEnergy_sub_fallVelocity_pos hM hr hτ).ne'
  refine h.congr_deriv ?_
  ring

theorem hasDerivAt_advancedTime (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (advancedTime M r₀) (advancedRate M r₀ τ) τ := by
  have hc : ContinuousOn (advancedRate M r₀) (Ioo (-horizonTime M r₀) (crunchTime M r₀)) :=
    fun _ hσ => (hasDerivAt_advancedRate hM hr hσ).continuousAt.continuousWithinAt
  have h0 : (0 : ℝ) ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀) :=
    ⟨by linarith [horizonTime_pos hM hr], crunchTime_pos hM hr⟩
  have hsub : uIcc 0 τ ⊆ Ioo (-horizonTime M r₀) (crunchTime M r₀) :=
    ordConnected_Ioo.uIcc_subset h0 hτ
  exact (intervalIntegral.integral_hasDerivAt_right (hc.mono hsub).intervalIntegrable
    (hc.stronglyMeasurableAtFilter isOpen_Ioo τ hτ)
    (hc.continuousAt (isOpen_Ioo.mem_nhds hτ))).const_add _

theorem contDiffOn_advancedTime (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ 2 (advancedTime M r₀) (Ioo (-horizonTime M r₀) (crunchTime M r₀)) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun τ hτ => (hasDerivAt_advancedTime hM hr hτ).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  have hv := ((contDiffOn_fallVelocity hM hr).mono (ioo_horizon_crunch_subset hM hr)).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  exact ((contDiffOn_const.sub hv).inv fun τ hτ =>
    (fallEnergy_sub_fallVelocity_pos hM hr hτ).ne').congr
      fun τ hτ => (hasDerivAt_advancedTime hM hr hτ).deriv

/-- The co-ordinates `(v(τ), r(τ), θ₀, φ₀)` of the fall in the Eddington–Finkelstein chart. -/
def advancedPoint (M r₀ θ₀ φ₀ τ : ℝ) : MinkowskiModel 3 :=
  ![advancedTime M r₀ τ, fallRadius M r₀ τ, θ₀, φ₀]

theorem basePoint_mem_eddington : (![0, 1, π / 2, 0] : MinkowskiModel 3) ∈
    EddingtonFinkelstein.domain := by
  refine ⟨?_, ?_, ?_⟩
  · change (0 : ℝ) < 1
    norm_num
  · change 0 < π / 2
    positivity
  · change π / 2 < π
    linarith [Real.pi_pos]

open Classical in
/-- **The fall from rest in the Eddington–Finkelstein chart**, `τ ↦ (v(τ), r(τ), θ₀, φ₀)`, at the
parameters where it lies in the domain `r > 0`; elsewhere it is held at a fixed point. -/
def advancedFall (M r₀ θ₀ φ₀ : ℝ) (τ : ℝ) : EddingtonFinkelstein.domain :=
  if h : advancedPoint M r₀ θ₀ φ₀ τ ∈ EddingtonFinkelstein.domain then ⟨_, h⟩
  else ⟨_, basePoint_mem_eddington⟩

theorem advancedFall_val (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) = advancedPoint M r₀ θ₀ φ₀ τ := by
  have hmem : advancedPoint M r₀ θ₀ φ₀ τ ∈ EddingtonFinkelstein.domain :=
    ⟨fallRadius_pos hM hr (ioo_horizon_crunch_subset hM hr hτ), hθ.1, hθ.2⟩
  simp [advancedFall, hmem]

theorem deriv_advancedFall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3))
      ![advancedRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] τ := by
  have hev : (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) =ᶠ[𝓝 τ]
      advancedPoint M r₀ θ₀ φ₀ :=
    eventually_of_mem (isOpen_Ioo.mem_nhds hτ) fun σ hσ => advancedFall_val hM hr hθ hσ
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  exact hasDerivAt_vec (hasDerivAt_advancedTime hM hr hτ)
    (hasDerivAt_fallRadius hM hr (ioo_horizon_crunch_subset hM hr hτ)) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _)

/-- **The fall from rest crosses `r = 2M` as a geodesic** of the Eddington–Finkelstein metric:
the curve `advancedFall` satisfies the geodesic equation from `τ = −τ_h` to the crunch
`τ = π √(r₀³/8M)`. -/
theorem isGeodesicOn_advancedFall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    (EddingtonFinkelstein.metric M).toLorentzMetric.IsGeodesicOn
      (Ioo (-horizonTime M r₀) (crunchTime M r₀)) (advancedFall M r₀ θ₀ φ₀) := by
  set S := Ioo (-horizonTime M r₀) (crunchTime M r₀) with hS
  have hd2 (τ : ℝ) (hτ : τ ∈ S) : HasDerivAt
      (fun σ => (![advancedRate M r₀ σ, fallVelocity M r₀ σ, 0, 0] : MinkowskiModel 3))
      ![-(M / fallRadius M r₀ τ ^ 2) / (fallEnergy M r₀ - fallVelocity M r₀ τ) ^ 2,
        -(M / fallRadius M r₀ τ ^ 2), 0, 0] τ :=
    hasDerivAt_vec (hasDerivAt_advancedRate hM hr hτ)
      (hasDerivAt_fallVelocity hM hr (ioo_horizon_crunch_subset hM hr hτ)) (hasDerivAt_const _ _)
      (hasDerivAt_const _ _)
  have hderiv (τ : ℝ) (hτ : τ ∈ S) :
      deriv (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) τ =
        ![advancedRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] :=
    (deriv_advancedFall hM hr hθ hτ).deriv
  have hderiv2 (τ : ℝ) (hτ : τ ∈ S) :
      deriv (deriv (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3))) τ =
        ![-(M / fallRadius M r₀ τ ^ 2) / (fallEnergy M r₀ - fallVelocity M r₀ τ) ^ 2,
          -(M / fallRadius M r₀ τ ^ 2), 0, 0] := by
    have h : deriv (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) =ᶠ[𝓝 τ]
        fun σ => ![advancedRate M r₀ σ, fallVelocity M r₀ σ, 0, 0] :=
      eventually_of_mem (isOpen_Ioo.mem_nhds hτ) hderiv
    rw [h.deriv_eq]
    exact (hd2 τ hτ).deriv
  have hc : ContDiffOn ℝ 2 (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) S := by
    have h : ContDiffOn ℝ 2 (advancedPoint M r₀ θ₀ φ₀) S := by
      refine contDiffOn_pi.mpr fun i => ?_
      fin_cases i
      · simpa [advancedPoint] using contDiffOn_advancedTime hM hr
      · simpa [advancedPoint] using ((contDiffOn_fallRadius hM hr).mono
          (ioo_horizon_crunch_subset hM hr)).of_le (by norm_num)
      · simpa [advancedPoint] using contDiffOn_const
      · simpa [advancedPoint] using contDiffOn_const
    exact h.congr fun τ hτ => advancedFall_val hM hr hθ hτ
  rw [(EddingtonFinkelstein.metric M).isGeodesicOn_iff isOpen_Ioo hc]
  intro τ hτ k
  rw [hderiv2 τ hτ, hderiv τ hτ]
  simp only [EddingtonFinkelstein.sum_four,
    EddingtonFinkelstein.christoffelOf_eq (advancedFall M r₀ θ₀ φ₀ τ).property]
  rw [advancedFall_val hM hr hθ hτ]
  have hτ' := ioo_horizon_crunch_subset hM hr hτ
  have hv := fallVelocity_sq hM hr hτ'
  have hE := fallEnergy_sq hM hr
  have hr0 := (fallRadius_pos hM hr hτ').ne'
  have hw := (fallEnergy_sub_fallVelocity_pos hM hr hτ).ne'
  have h0 := (pos_of_two_mul_lt hM hr).ne'
  have hk : (fallEnergy M r₀ ^ 2 - fallVelocity M r₀ τ ^ 2) * fallRadius M r₀ τ =
      fallRadius M r₀ τ - 2 * M := by
    rw [hv, hE]
    field_simp
    ring
  fin_cases k <;> simp [EddingtonFinkelstein.christoffel, advancedPoint, advancedRate]
  · field_simp
    ring
  · field_simp
    linear_combination (-M) * hk

/-- The fall in the Eddington–Finkelstein chart is parametrized by its proper time. -/
theorem form_curveVelocity_advancedFall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ}
    (hθ : θ₀ ∈ Ioo 0 π) (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    (EddingtonFinkelstein.metric M).toLorentzMetric.form (advancedFall M r₀ θ₀ φ₀ τ)
      (LorentzMetric.curveVelocity (advancedFall M r₀ θ₀ φ₀) τ)
      (LorentzMetric.curveVelocity (advancedFall M r₀ θ₀ φ₀) τ) = -1 := by
  have hd := deriv_advancedFall hM hr (φ₀ := φ₀) hθ hτ
  rw [(EddingtonFinkelstein.metric M).form_curveVelocity hd.differentiableAt, hd.deriv,
    advancedFall_val hM hr hθ hτ]
  have hτ' := ioo_horizon_crunch_subset hM hr hτ
  have hv := fallVelocity_sq hM hr hτ'
  have hE := fallEnergy_sq hM hr
  have hr0 := (fallRadius_pos hM hr hτ').ne'
  have hw := (fallEnergy_sub_fallVelocity_pos hM hr hτ).ne'
  have h0 := (pos_of_two_mul_lt hM hr).ne'
  have hk : (fallEnergy M r₀ ^ 2 - fallVelocity M r₀ τ ^ 2) * fallRadius M r₀ τ =
      fallRadius M r₀ τ - 2 * M := by
    rw [hv, hE]
    field_simp
    ring
  simp [EddingtonFinkelstein.sum_four, EddingtonFinkelstein.coefficient_apply,
    EddingtonFinkelstein.form_apply, advancedPoint, advancedRate]
  field_simp
  linear_combination hk

/-- **The same body in the two charts**: for `|τ| < τ_h` the map `toEddington` of
`EddingtonFinkelstein` sends the fall in the exterior co-ordinates to the fall in the
Eddington–Finkelstein co-ordinates, `v = t + r + 2M log(r/2M − 1)`. -/
theorem toEddington_fall (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    EddingtonFinkelstein.toEddington M (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) =
      (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) := by
  have hsub : Ioo (-horizonTime M r₀) (horizonTime M r₀) ⊆
      Ioo (-horizonTime M r₀) (crunchTime M r₀) :=
    Ioo_subset_Ioo le_rfl (horizonTime_lt_crunchTime hM hr).le
  have hlog (σ : ℝ) (hσ : σ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
      HasDerivAt (fun s => fallTime M r₀ s + fallRadius M r₀ s +
        2 * M * Real.log (fallRadius M r₀ s / (2 * M) - 1)) (advancedRate M r₀ σ) σ := by
    have h2 := two_mul_lt_fallRadius hM hr hσ
    have hl : fallRadius M r₀ σ / (2 * M) - 1 ≠ 0 := by
      have : 1 < fallRadius M r₀ σ / (2 * M) := (one_lt_div (by positivity)).mpr h2
      linarith
    have hR := hasDerivAt_fallRadius hM hr (horizon_subset hM hr hσ)
    have h := ((hasDerivAt_fallTime hM hr hσ).fun_add hR).fun_add
      (((hR.div_const (2 * M)).sub_const 1).log hl |>.const_mul (2 * M))
    refine h.congr_deriv ?_
    have hv := fallVelocity_sq hM hr (horizon_subset hM hr hσ)
    have hE := fallEnergy_sq hM hr
    have hw := (fallEnergy_sub_fallVelocity_pos hM hr (hsub hσ)).ne'
    have hr0 : fallRadius M r₀ σ ≠ 0 := by linarith
    have hr1 : fallRadius M r₀ σ - 2 * M ≠ 0 := by linarith
    have hf := (lapse_fall_pos hM hr hσ).ne'
    have h0 := (pos_of_two_mul_lt hM hr).ne'
    have hk : (fallEnergy M r₀ ^ 2 - fallVelocity M r₀ σ ^ 2) * fallRadius M r₀ σ =
        fallRadius M r₀ σ - 2 * M := by
      rw [hv, hE]
      field_simp
      ring
    rw [fallTimeRate, advancedRate]
    field_simp
    linear_combination hk
  have heq := isOpen_Ioo.eqOn_of_deriv_eq (isPreconnected_Ioo)
    (fun σ hσ => (hlog σ hσ).differentiableAt.differentiableWithinAt)
    (fun σ hσ => (hasDerivAt_advancedTime hM hr (hsub hσ)).differentiableAt.differentiableWithinAt)
    (fun σ hσ => by rw [(hlog σ hσ).deriv, (hasDerivAt_advancedTime hM hr (hsub hσ)).deriv])
    (zero_mem_horizon hM hr) (by simp [fallTime, fallRadius_zero, advancedTime])
  rw [fall_val hM hr hθ hτ, advancedFall_val hM hr hθ (hsub hτ)]
  have := heq hτ
  simp only at this
  funext i
  fin_cases i
  · simp [EddingtonFinkelstein.toEddington, fallPoint, advancedPoint, ← this]
  · simp [EddingtonFinkelstein.toEddington, fallPoint, advancedPoint]
  · simp [EddingtonFinkelstein.toEddington, fallPoint, advancedPoint]
  · simp [EddingtonFinkelstein.toEddington, fallPoint, advancedPoint]

/-- **The fall from rest reaches the centre in finite proper time** (Landau–Lifshitz, §102): in
the Eddington–Finkelstein chart the fall is a geodesic parametrized by its proper time on
`−τ_h < τ < π √(r₀³/8M)`; it is inside the sphere `r = 2M` for `τ_h < τ`, and `r → 0` as
`τ → π √(r₀³/8M)`. -/
theorem advancedFall_properTime (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    (∀ τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀),
      properTime (EddingtonFinkelstein.metric M).toLorentzMetric (advancedFall M r₀ θ₀ φ₀) 0 τ =
        τ) ∧
      (∀ τ ∈ Ioo (horizonTime M r₀) (crunchTime M r₀),
        (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1 < 2 * M) ∧
      Tendsto (fun τ => (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1)
        (𝓝[<] crunchTime M r₀) (𝓝 0) := by
  have hT := horizonTime_pos hM hr
  have hT' := horizonTime_lt_crunchTime hM hr
  have h0 : (0 : ℝ) ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀) := ⟨by linarith, by linarith⟩
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_, ?_⟩
  · have hsub : uIcc 0 τ ⊆ Ioo (-horizonTime M r₀) (crunchTime M r₀) :=
      ordConnected_Ioo.uIcc_subset h0 hτ
    rw [properTime_geodesic _ fun s hs => isGeodesicOn_advancedFall hM hr φ₀ hθ s (hsub hs)]
    unfold speedAlong properSpeed
    rw [form_curveVelocity_advancedFall hM hr hθ h0]
    simp
  · have hτ' : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀) := ⟨by linarith [hτ.1], hτ.2⟩
    rw [advancedFall_val hM hr hθ hτ']
    change fallRadius M r₀ τ < 2 * M
    -- the cycloid parameter exceeds `η_h`, so the radius is below `2M`
    have hA := fallScale_pos hM hr
    have hη : horizonAngle M r₀ < fallAngle M r₀ τ := by
      rw [← strictMono_cycloidTime.lt_iff_lt, fallAngle, cycloidTime_cycloidParam,
        lt_div_iff₀ hA, mul_comm]
      exact hτ.1
    have hπ := (fallAngle_mem hM hr (ioo_horizon_crunch_subset hM hr hτ')).2
    have hh := horizonAngle_mem hM hr
    have hcos : Real.cos (fallAngle M r₀ τ) < Real.cos (horizonAngle M r₀) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hh.1.le hπ.le hη
    rw [cos_horizonAngle hM hr] at hcos
    have hr0 := pos_of_two_mul_lt hM hr
    have e : r₀ / 2 * (1 + (4 * M / r₀ - 1)) = 2 * M := by
      field_simp
      ring
    unfold fallRadius
    nlinarith
  · have hc : Tendsto (fallRadius M r₀) (𝓝 (crunchTime M r₀)) (𝓝 0) := by
      rw [← fallRadius_crunchTime hM hr]
      exact (continuous_const.mul (continuous_const.add
        (Real.continuous_cos.comp (continuous_cycloidParam.comp
          (continuous_id.div_const _))))).continuousAt
    refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show -horizonTime M r₀ < crunchTime M r₀ by linarith)]
      with τ hτ
    rw [advancedFall_val hM hr hθ hτ]
    rfl

/-! ### Centrally symmetric metrics in a comoving frame -/

/-- **The data of a centrally symmetric metric in a comoving synchronous frame**
`ds² = −dτ² + e^λ dR² + r² (dθ² + sin²θ dφ²)` (Landau–Lifshitz, (103.1)), in the co-ordinates
`(τ, R, θ, φ)`: an open domain where `sin θ > 0`, the coefficient `A = e^λ` and the areal
radius `r`, smooth and positive on the domain. -/
structure ComovingData where
  /-- The domain of the co-ordinates `(τ, R, θ, φ)`. -/
  domain : Opens (MinkowskiModel 3)
  /-- The radial coefficient `A = e^λ = g_{RR}`. -/
  A : MinkowskiModel 3 → ℝ
  /-- The areal radius `r`. -/
  r : MinkowskiModel 3 → ℝ
  /-- The radial coefficient is smooth on the domain. -/
  contDiffOn_A : ContDiffOn ℝ ∞ A domain
  /-- The areal radius is smooth on the domain. -/
  contDiffOn_r : ContDiffOn ℝ ∞ r domain
  /-- The radial coefficient is positive on the domain. -/
  A_pos : ∀ x ∈ domain, 0 < A x
  /-- The areal radius is positive on the domain. -/
  r_pos : ∀ x ∈ domain, 0 < r x
  /-- The domain avoids the axis: `sin θ > 0`. -/
  sin_pos : ∀ x ∈ domain, 0 < Real.sin (x 2)

namespace ComovingData

variable (D : ComovingData)

/-- The diagonal coefficients `(−1, A, r², r² sin²θ)`. -/
def coefficients (x : MinkowskiModel 3) : Fin 4 → ℝ :=
  ![-1, D.A x, D.r x ^ 2, D.r x ^ 2 * Real.sin (x 2) ^ 2]

theorem contDiffOn_coefficients (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => D.coefficients x i) D.domain := by
  have hsin : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => Real.sin (x 2) ^ 2 :=
    (Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ => ℝ) 2)).pow 2
  fin_cases i
  · simpa [coefficients] using contDiffOn_const
  · simpa [coefficients] using D.contDiffOn_A
  · simpa [coefficients] using D.contDiffOn_r.pow 2
  · simpa [coefficients] using (D.contDiffOn_r.pow 2).mul hsin.contDiffOn

/-- **The comoving metric** `ds² = −dτ² + A dR² + r² (dθ² + sin²θ dφ²)` on the domain. -/
def metric : CoordinateMetric .timeNegative 3 D.domain :=
  CoordinateMetric.ofDiagonal D.coefficients D.contDiffOn_coefficients
    (fun x _ => by simp [coefficients])
    (fun x hx α => by
      have hA := D.A_pos x hx
      have hr := D.r_pos x hx
      have hs := D.sin_pos x hx
      fin_cases α <;> simp [coefficients] <;> positivity)

theorem coefficient_metric (x : MinkowskiModel 3) :
    D.metric.coefficient x = Matrix.diagonal (D.coefficients x) :=
  CoordinateMetric.coefficient_ofDiagonal _ _ _ _ x

theorem metric_form_apply (x v w : MinkowskiModel 3) :
    D.metric.form x v w = -(v 0 * w 0) + D.A x * (v 1 * w 1) + D.r x ^ 2 * (v 2 * w 2) +
      D.r x ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3) := by
  rw [metric, CoordinateMetric.ofDiagonal_form, CoordinateMetric.diagonalForm_apply,
    EddingtonFinkelstein.sum_four]
  simp [coefficients]
  ring

/-- The comoving frame is synchronous: `g_{ττ} = −1`, `g_{τα} = 0`. -/
theorem isSynchronous : D.metric.IsSynchronous := by
  intro z _
  refine ⟨by simp [coefficient_metric, coefficients], fun α => ?_⟩
  rw [coefficient_metric, Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero α).symm]

/-- The comoving shells `R = const` are an orthogonal slicing. -/
theorem isOrthogonalSlicing : D.metric.IsOrthogonalSlicing 1 :=
  CoordinateMetric.isOrthogonalSlicing_ofDiagonal _ _ _ _ 1

/-- The rate `∂_R r / e^{λ/2}` of a shell; it is `√(1 + f(R))` in the notation (103.2) of
Landau–Lifshitz, the energy per unit mass of the shell. -/
def shellEnergy (x : MinkowskiModel 3) : ℝ :=
  fderiv ℝ D.r x (Pi.single 1 1) / Real.sqrt (D.A x)

/-- The induced metric of the shell `R = const` is `−dτ² + r² (dθ² + sin²θ dφ²)`. -/
theorem inducedMetric_eq (x : MinkowskiModel 3) :
    D.metric.inducedMetric 1 x =
      Matrix.diagonal ![-1, D.r x ^ 2, D.r x ^ 2 * Real.sin (x 2) ^ 2] := by
  rw [metric, CoordinateMetric.inducedMetric_ofDiagonal]
  congr 1
  funext a
  fin_cases a <;> rfl

/-- **The second fundamental form of a comoving shell** `R = const`, for the normal
`ε e^{−λ/2} ∂_R`: `K = ε (∂_R r/e^{λ/2}) r (dθ² + sin²θ dφ²)`, with no `dτ²` term since the
shells move along geodesics. -/
theorem secondFundamental_eq {x : MinkowskiModel 3} (hx : x ∈ D.domain) (ε : ℝ) :
    D.metric.secondFundamental 1 ε x =
      Matrix.diagonal ![0, ε * D.shellEnergy x * D.r x,
        ε * D.shellEnergy x * D.r x * Real.sin (x 2) ^ 2] := by
  have hA := D.A_pos x hx
  have hr : DifferentiableAt ℝ D.r x :=
    (D.contDiffOn_r.contDiffAt (D.domain.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hsq : HasFDerivAt (fun w => D.r w ^ 2) ((2 * D.r x) • fderiv ℝ D.r x) x := by
    simpa using hr.hasFDerivAt.pow 2
  have hsin : HasFDerivAt (fun w : MinkowskiModel 3 => Real.sin (w 2) ^ 2)
      ((2 * Real.sin (x 2) * Real.cos (x 2)) • (ContinuousLinearMap.proj 2 :
        MinkowskiModel 3 →L[ℝ] ℝ)) x := by
    have h := (SchwarzschildExterior.hasFDerivAt_coord 2 (Real.hasDerivAt_sin (x 2))).pow 2
    convert h using 1
    ext v
    simp
    ring
  rw [metric, CoordinateMetric.secondFundamental_ofDiagonal]
  congr 1
  funext a
  have hc1 : D.coefficients x 1 = D.A x := rfl
  rw [hc1, abs_of_pos hA]
  have hsA : Real.sqrt (D.A x) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
  fin_cases a
  · simp [coefficients]
  · change ε / (2 * Real.sqrt (D.A x)) *
      fderiv ℝ (fun w => D.r w ^ 2) x (Pi.single 1 1) = _
    rw [hsq.fderiv]
    simp [shellEnergy]
    field_simp
  · change ε / (2 * Real.sqrt (D.A x)) *
      fderiv ℝ (fun w => D.r w ^ 2 * Real.sin (w 2) ^ 2) x (Pi.single 1 1) = _
    rw [(hsq.fun_mul hsin).fderiv]
    simp [shellEnergy]
    field_simp

/-- **The junction of two comoving frames** on two shells: where the shells have the same areal
radius and the same rate `∂_R r/e^{λ/2}`, at the same `τ` and `θ`, their induced metrics and their
second fundamental forms agree (the conditions of Darmois and Israel). -/
theorem junction {D₁ D₂ : ComovingData} {x₁ x₂ : MinkowskiModel 3} (hx₁ : x₁ ∈ D₁.domain)
    (hx₂ : x₂ ∈ D₂.domain) (hθ : x₁ 2 = x₂ 2) (hr : D₁.r x₁ = D₂.r x₂)
    (hE : D₁.shellEnergy x₁ = D₂.shellEnergy x₂) (ε : ℝ) :
    D₁.metric.inducedMetric 1 x₁ = D₂.metric.inducedMetric 1 x₂ ∧
      D₁.metric.secondFundamental 1 ε x₁ = D₂.metric.secondFundamental 1 ε x₂ := by
  rw [inducedMetric_eq, inducedMetric_eq, secondFundamental_eq _ hx₁, secondFundamental_eq _ hx₂,
    hθ, hr, hE]
  exact ⟨rfl, rfl⟩

/-- The induced metrics of two shells at the same `θ` agree exactly when their areal radii do. -/
theorem inducedMetric_eq_iff {D₁ D₂ : ComovingData} {x₁ x₂ : MinkowskiModel 3}
    (hx₁ : x₁ ∈ D₁.domain) (hx₂ : x₂ ∈ D₂.domain) (hθ : x₁ 2 = x₂ 2) :
    D₁.metric.inducedMetric 1 x₁ = D₂.metric.inducedMetric 1 x₂ ↔ D₁.r x₁ = D₂.r x₂ := by
  rw [inducedMetric_eq, inducedMetric_eq, hθ]
  constructor
  · intro h
    have h1 := congrFun (congrFun h 1) 1
    simp only [Matrix.diagonal_apply_eq] at h1
    have h1' : D₁.r x₁ ^ 2 = D₂.r x₂ ^ 2 := h1
    exact (pow_left_inj₀ (D₁.r_pos x₁ hx₁).le (D₂.r_pos x₂ hx₂).le two_ne_zero).mp h1'
  · intro h
    rw [h]

end ComovingData

/-! ### The Lemaître chart -/

/-- The domain `R > τ`, `0 < θ < π` of the Lemaître co-ordinates `(τ, R, θ, φ)`. -/
def lemaitreDomain : Opens (MinkowskiModel 3) :=
  ⟨{x | x 0 < x 1 ∧ 0 < x 2 ∧ x 2 < π},
    (isOpen_lt (continuous_apply 0) (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const))⟩

/-- The areal radius `r = ((3/2)(R − τ))^{2/3} (2M)^{1/3} = ((9/2) M (R − τ)²)^{1/3}` of the
Lemaître co-ordinates (Landau–Lifshitz, (102.3) with `r_g = 2M`). -/
def lemaitreRadius (M : ℝ) (x : MinkowskiModel 3) : ℝ :=
  (9 / 2 * M * (x 1 - x 0) ^ 2) ^ (1 / 3 : ℝ)

theorem lemaitreBase_pos (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    0 < 9 / 2 * M * (x 1 - x 0) ^ 2 := by
  have : 0 < x 1 - x 0 := sub_pos.mpr hx
  positivity

theorem lemaitreRadius_pos (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    0 < lemaitreRadius M x :=
  Real.rpow_pos_of_pos (lemaitreBase_pos hM hx) _

/-- `r³ = (9/2) M (R − τ)²`. -/
theorem lemaitreRadius_cube (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    lemaitreRadius M x ^ 3 = 9 / 2 * M * (x 1 - x 0) ^ 2 := by
  rw [lemaitreRadius, ← Real.rpow_natCast, ← Real.rpow_mul (lemaitreBase_pos hM hx).le]
  norm_num

/-- The radius has the differential `dr = (2r/(3(R − τ)))(dR − dτ)`. -/
theorem hasFDerivAt_lemaitreRadius (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    HasFDerivAt (lemaitreRadius M)
      ((2 / 3 * lemaitreRadius M x / (x 1 - x 0)) •
        ((ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) -
          ContinuousLinearMap.proj 0)) x := by
  have hb := (lemaitreBase_pos hM hx).ne'
  have hd : (x 1 - x 0) ≠ 0 := (sub_pos.mpr hx).ne'
  have h1 : HasFDerivAt (fun y : MinkowskiModel 3 => y 1)
      (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) x := hasFDerivAt_apply 1 x
  have h0 : HasFDerivAt (fun y : MinkowskiModel 3 => y 0)
      (ContinuousLinearMap.proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) x := hasFDerivAt_apply 0 x
  have h := (((h1.fun_sub h0).pow 2).const_mul (9 / 2 * M)).rpow_const (p := 1 / 3) (Or.inl hb)
  refine h.congr_fderiv ?_
  ext v
  simp
  rw [Real.rpow_sub_one hb]
  simp only [lemaitreRadius]
  field_simp

theorem contDiffOn_lemaitreRadius (hM : 0 < M) :
    ContDiffOn ℝ ∞ (lemaitreRadius M) lemaitreDomain := by
  have hb : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => 9 / 2 * M * (x 1 - x 0) ^ 2 :=
    contDiff_const.mul (((contDiff_apply ℝ (fun _ => ℝ) 1).sub
      (contDiff_apply ℝ (fun _ => ℝ) 0)).pow 2)
  exact hb.contDiffOn.rpow_const_of_ne fun x hx => (lemaitreBase_pos hM hx.1).ne'

/-- `√(2M/r) = 2r/(3(R − τ))`: the speed of the Lemaître observers. -/
theorem sqrt_two_mul_div_lemaitreRadius (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    Real.sqrt (2 * M / lemaitreRadius M x) = 2 / 3 * lemaitreRadius M x / (x 1 - x 0) := by
  have hr := lemaitreRadius_pos hM hx
  have hd := sub_pos.mpr hx
  have h3 := lemaitreRadius_cube hM hx
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  field_simp
  linear_combination 2 * h3

/-- **The Lemaître chart** of the Schwarzschild field (Landau–Lifshitz, (102.2)):
`ds² = −dτ² + (2M/r) dR² + r² (dθ² + sin²θ dφ²)` with `r = ((9/2) M (R − τ)²)^{1/3}`, on the
domain `R > τ`, `0 < θ < π`, through the sphere `r = 2M`. The shells `R = const` are the
radial observers that fall freely from rest at infinity. -/
def lemaitre (hM : 0 < M) : ComovingData where
  domain := lemaitreDomain
  A x := 2 * M / lemaitreRadius M x
  r := lemaitreRadius M
  contDiffOn_A := contDiffOn_const.div (contDiffOn_lemaitreRadius hM)
    fun x hx => (lemaitreRadius_pos hM hx.1).ne'
  contDiffOn_r := contDiffOn_lemaitreRadius hM
  A_pos x hx := div_pos (by positivity) (lemaitreRadius_pos hM hx.1)
  r_pos x hx := lemaitreRadius_pos hM hx.1
  sin_pos x hx := Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2

/-- The Lemaître shells have the energy `∂_R r/e^{λ/2} = 1` per unit mass: they fall from rest at
infinity (`f = 0` in (103.2)). -/
theorem shellEnergy_lemaitre (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    (lemaitre hM).shellEnergy x = 1 := by
  have hr := (lemaitreRadius_pos hM hx).ne'
  have hd := (sub_pos.mpr hx).ne'
  rw [ComovingData.shellEnergy]
  change fderiv ℝ (lemaitreRadius M) x (Pi.single 1 1) /
    Real.sqrt (2 * M / lemaitreRadius M x) = 1
  rw [(hasFDerivAt_lemaitreRadius hM hx).fderiv, sqrt_two_mul_div_lemaitreRadius hM hx]
  simp
  exact ⟨hr, hd⟩

/-- The sphere `r = 2M` of the Lemaître chart is `R − τ = 4M/3`. -/
theorem lemaitreRadius_lt_iff (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    lemaitreRadius M x < 2 * M ↔ 3 * (x 1 - x 0) < 4 * M := by
  have hr := lemaitreRadius_pos hM hx
  have hd := sub_pos.mpr hx
  have h3 := lemaitreRadius_cube hM hx
  constructor
  · intro h
    have h' : lemaitreRadius M x ^ 3 < (2 * M) ^ 3 := pow_lt_pow_left₀ h hr.le three_ne_zero
    rw [h3] at h'
    by_contra hc
    have hc' : 4 * M ≤ 3 * (x 1 - x 0) := le_of_not_gt hc
    have : (4 * M) ^ 2 ≤ (3 * (x 1 - x 0)) ^ 2 := pow_le_pow_left₀ (by positivity) hc' 2
    nlinarith
  · intro h
    have : (3 * (x 1 - x 0)) ^ 2 < (4 * M) ^ 2 := pow_lt_pow_left₀ h (by positivity) two_ne_zero
    have h' : lemaitreRadius M x ^ 3 < (2 * M) ^ 3 := by
      rw [h3]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 3 (by positivity) h'

/-- **Inside the sphere `r = 2M` every causal vector points to decreasing `r`** in the Lemaître
chart (Landau–Lifshitz, §102): at a point with `r < 2M`, every vector `u` with `g(u, u) ≤ 0` that
is future directed for the time function `τ`, `u^τ > 0`, has `dr(u) < 0`. No particle and no
light ray can stay at constant `r` or move outwards there. -/
theorem radius_deriv_neg_of_causal (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ lemaitreDomain)
    (hr : lemaitreRadius M x < 2 * M) {u : MinkowskiModel 3}
    (hu : (lemaitre hM).metric.form x u u ≤ 0) (hu₀ : 0 < u 0) :
    fderiv ℝ (lemaitreRadius M) x u < 0 := by
  have hr0 := lemaitreRadius_pos hM hx.1
  have hd := sub_pos.mpr hx.1
  rw [(hasFDerivAt_lemaitreRadius hM hx.1).fderiv]
  change 2 / 3 * lemaitreRadius M x / (x 1 - x 0) * (u 1 - u 0) < 0
  rw [ComovingData.metric_form_apply] at hu
  change -(u 0 * u 0) + 2 * M / lemaitreRadius M x * (u 1 * u 1) +
    lemaitreRadius M x ^ 2 * (u 2 * u 2) +
    lemaitreRadius M x ^ 2 * Real.sin (x 2) ^ 2 * (u 3 * u 3) ≤ 0 at hu
  have hq2 : 0 ≤ lemaitreRadius M x ^ 2 * (u 2 * u 2) :=
    mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
  have hq3 : 0 ≤ lemaitreRadius M x ^ 2 * Real.sin (x 2) ^ 2 * (u 3 * u 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_self_nonneg _)
  have hk : 1 < 2 * M / lemaitreRadius M x := (one_lt_div hr0).mpr hr
  have h1 : u 1 < u 0 := by
    by_contra h
    have h' : u 0 ≤ u 1 := le_of_not_gt h
    have h00 : u 0 * u 0 ≤ u 1 * u 1 := by nlinarith
    have h11 : 0 < u 1 * u 1 := by nlinarith
    have := mul_lt_mul_of_pos_right hk h11
    linarith
  have hc : 0 < 2 / 3 * lemaitreRadius M x / (x 1 - x 0) := by positivity
  nlinarith

/- The hypotheses of `radius_deriv_neg_of_causal` hold: for `M = 1` the point `(0, 1, π/2, 0)`
has `R − τ = 1 < 4/3`, so it lies inside the sphere `r = 2`, and there the vector `(1, 0, 0, 0)`
of the time function is timelike, `g(u, u) = −1`. -/
example : (![0, 1, π / 2, 0] : MinkowskiModel 3) ∈ lemaitreDomain ∧
    lemaitreRadius 1 ![0, 1, π / 2, 0] < 2 * 1 ∧
    (lemaitre one_pos).metric.form ![0, 1, π / 2, 0] ![1, 0, 0, 0] ![1, 0, 0, 0] = -1 ∧
    (0 : ℝ) < (![1, 0, 0, 0] : MinkowskiModel 3) 0 := by
  have hmem : (![0, 1, π / 2, 0] : MinkowskiModel 3) ∈ lemaitreDomain := by
    refine ⟨?_, ?_, ?_⟩
    · change (0 : ℝ) < 1
      norm_num
    · change 0 < π / 2
      positivity
    · change π / 2 < π
      linarith [Real.pi_pos]
  refine ⟨hmem, ?_, ?_, ?_⟩
  · rw [lemaitreRadius_lt_iff one_pos hmem.1]
    norm_num
  · rw [ComovingData.metric_form_apply]
    simp
  · change (0 : ℝ) < 1
    norm_num

open Classical in
/-- The Lemaître observer `τ ↦ (τ, R₀, θ₀, φ₀)` for `τ < R₀`, a body that falls radially from
rest at infinity; for `τ ≥ R₀`, where it has reached the centre, it is held at a fixed point. -/
def lemaitreObserver (R₀ θ₀ φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) (τ : ℝ) : lemaitreDomain :=
  if h : τ < R₀ then ⟨![τ, R₀, θ₀, φ₀], h, hθ.1, hθ.2⟩
  else ⟨![R₀ - 1, R₀, θ₀, φ₀], show R₀ - 1 < R₀ by linarith, hθ.1, hθ.2⟩

theorem lemaitreObserver_val {R₀ θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hτ : τ < R₀) :
    (lemaitreObserver R₀ θ₀ φ₀ hθ τ : MinkowskiModel 3) = ![τ, R₀, θ₀, φ₀] := by
  simp [lemaitreObserver, hτ]

/-- **A radial fall through `r = 2M` to the centre in finite proper time** (Landau–Lifshitz,
§102). The Lemaître observer `R = R₀` is a geodesic parametrized by its proper time `τ`; it crosses
the sphere `r = 2M` at `τ = R₀ − 4M/3` and reaches `r = 0` at `τ = R₀`, and the proper time from
`τ₁` to `τ₂` is `τ₂ − τ₁`. -/
theorem lemaitreObserver_properTime (hM : 0 < M) (R₀ : ℝ) {θ₀ : ℝ} (φ₀ : ℝ)
    (hθ : θ₀ ∈ Ioo 0 π) :
    (lemaitre hM).metric.toLorentzMetric.IsGeodesicOn (Iio R₀)
        (lemaitreObserver R₀ θ₀ φ₀ hθ) ∧
      (∀ τ₁ τ₂ : ℝ, τ₁ < R₀ → τ₂ < R₀ →
        properTime (lemaitre hM).metric.toLorentzMetric (lemaitreObserver R₀ θ₀ φ₀ hθ) τ₁ τ₂ =
          τ₂ - τ₁) ∧
      (∀ τ < R₀, lemaitreRadius M (lemaitreObserver R₀ θ₀ φ₀ hθ τ) < 2 * M ↔
        R₀ - 4 * M / 3 < τ) ∧
      Tendsto (fun τ => lemaitreRadius M (lemaitreObserver R₀ θ₀ φ₀ hθ τ)) (𝓝[<] R₀)
        (𝓝 0) := by
  have hline (τ : ℝ) (hτ : τ ∈ Iio R₀) : (lemaitreObserver R₀ θ₀ φ₀ hθ τ : MinkowskiModel 3) =
      ![0, R₀, θ₀, φ₀] + τ • Pi.single 0 1 := by
    rw [lemaitreObserver_val hθ hτ]
    funext i
    fin_cases i <;> simp
  have hg := (lemaitre hM).isSynchronous.isGeodesicOn_timeLine isOpen_Iio hline
  refine ⟨hg.1, fun τ₁ τ₂ h₁ h₂ => ?_, fun τ hτ => ?_, ?_⟩
  · have hsub : uIcc τ₁ τ₂ ⊆ Iio R₀ := fun s hs => lt_of_le_of_lt hs.2 (max_lt h₁ h₂)
    rw [properTime_geodesic _ fun s hs => hg.1 s (hsub hs)]
    unfold speedAlong properSpeed
    rw [(hg.2 τ₁ h₁).1]
    simp
  · have hx : (lemaitreObserver R₀ θ₀ φ₀ hθ τ : MinkowskiModel 3) 0 <
        (lemaitreObserver R₀ θ₀ φ₀ hθ τ : MinkowskiModel 3) 1 := by
      rw [lemaitreObserver_val hθ hτ]
      exact hτ
    rw [lemaitreRadius_lt_iff hM hx, lemaitreObserver_val hθ hτ]
    change 3 * (R₀ - τ) < 4 * M ↔ _
    constructor <;> intro h <;> linarith
  · have hc : Tendsto (fun τ : ℝ => (9 / 2 * M * (R₀ - τ) ^ 2) ^ (1 / 3 : ℝ)) (𝓝 R₀)
        (𝓝 ((9 / 2 * M * (R₀ - R₀) ^ 2) ^ (1 / 3 : ℝ))) := by
      have hb : Continuous fun τ : ℝ => 9 / 2 * M * (R₀ - τ) ^ 2 := by fun_prop
      exact ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
        hb.continuousAt).tendsto
    rw [sub_self, zero_pow two_ne_zero, mul_zero, Real.zero_rpow (by norm_num)] at hc
    refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [lemaitreRadius, lemaitreObserver_val hθ hτ]
    rfl

/-! ### The Lemaître chart is the Schwarzschild field -/

/-- The shift `h(r) = r − 2√(2M) √r + 4M log(√r + √(2M))` of the advanced time, with
`h'(r) = 1/(1 + √(2M/r))`: the Eddington–Finkelstein time is `v = τ + h(r)`. -/
def lemaitreShift (M r : ℝ) : ℝ :=
  r - 2 * Real.sqrt (2 * M) * Real.sqrt r + 4 * M * Real.log (Real.sqrt r + Real.sqrt (2 * M))

theorem hasDerivAt_lemaitreShift (hM : 0 < M) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (lemaitreShift M) (1 / (1 + Real.sqrt (2 * M / r))) r := by
  have hs := Real.sqrt_pos.mpr hr
  have hc := Real.sqrt_pos.mpr (show 0 < 2 * M by positivity)
  have hs2 := Real.sq_sqrt hr.le
  have hc2 := Real.sq_sqrt (show 0 ≤ 2 * M by positivity)
  have hsum : Real.sqrt r + Real.sqrt (2 * M) ≠ 0 := by positivity
  have hsq := Real.hasDerivAt_sqrt hr.ne'
  have h := ((hasDerivAt_id' r).fun_sub (hsq.const_mul (2 * Real.sqrt (2 * M)))).fun_add
    (((hsq.add_const (Real.sqrt (2 * M))).log hsum).const_mul (4 * M))
  refine h.congr_deriv ?_
  rw [Real.sqrt_div' _ hr.le]
  field_simp
  linear_combination (-2 : ℝ) * hc2

/-- The map `(τ, R, θ, φ) ↦ (τ + h(r), r, θ, φ)` from the Lemaître co-ordinates to the ingoing
Eddington–Finkelstein co-ordinates `(v, r, θ, φ)`. -/
def lemaitreToEddington (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![x 0 + lemaitreShift M (lemaitreRadius M x), lemaitreRadius M x, x 2, x 3]

/-- The linear map `v ↦ (v₀ + (β/(1 + β))(v₁ − v₀), β(v₁ − v₀), v₂, v₃)`. -/
def lemaitreToEddingtonLinear (β : ℝ) : MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 where
  toFun v := ![v 0 + β / (1 + β) * (v 1 - v 0), β * (v 1 - v 0), v 2, v 3]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The Jacobian of `lemaitreToEddington`, with `β = 2r/(3(R − τ)) = √(2M/r)`. -/
def lemaitreToEddingtonDeriv (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  LinearMap.toContinuousLinearMap
    (lemaitreToEddingtonLinear (2 / 3 * lemaitreRadius M x / (x 1 - x 0)))

theorem lemaitreToEddingtonDeriv_apply (x v : MinkowskiModel 3) :
    lemaitreToEddingtonDeriv M x v =
      ![v 0 + 2 / 3 * lemaitreRadius M x / (x 1 - x 0) /
          (1 + 2 / 3 * lemaitreRadius M x / (x 1 - x 0)) * (v 1 - v 0),
        2 / 3 * lemaitreRadius M x / (x 1 - x 0) * (v 1 - v 0), v 2, v 3] := rfl

/-- The map sends the Lemaître domain into the Eddington–Finkelstein domain `r > 0`. -/
theorem lemaitreToEddington_mem (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ lemaitreDomain) :
    lemaitreToEddington M x ∈ EddingtonFinkelstein.domain :=
  ⟨lemaitreRadius_pos hM hx.1, hx.2.1, hx.2.2⟩

/-- The derivative of `lemaitreToEddington` is `lemaitreToEddingtonDeriv`. -/
theorem hasFDerivAt_lemaitreToEddington (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    HasFDerivAt (lemaitreToEddington M) (lemaitreToEddingtonDeriv M x) x := by
  have hr := hasFDerivAt_lemaitreRadius hM hx
  have hr0 := lemaitreRadius_pos hM hx
  have hβ := sqrt_two_mul_div_lemaitreRadius hM hx
  have hd := sub_pos.mpr hx
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · have h := (hasFDerivAt_apply 0 x).fun_add
      ((hasDerivAt_lemaitreShift hM hr0).comp_hasFDerivAt x hr)
    refine h.congr_fderiv ?_
    ext w
    simp [lemaitreToEddingtonDeriv_apply, hβ]
    field_simp
  · refine hr.congr_fderiv ?_
    ext w
    simp [lemaitreToEddingtonDeriv_apply]
  · refine (hasFDerivAt_apply 2 x).congr_fderiv ?_
    ext w
    simp [lemaitreToEddingtonDeriv_apply]
  · refine (hasFDerivAt_apply 3 x).congr_fderiv ?_
    ext w
    simp [lemaitreToEddingtonDeriv_apply]

/-- **The Lemaître metric is the pullback of the Eddington–Finkelstein metric** by
`lemaitreToEddington` (Landau–Lifshitz, §102): `g_EF(J v, J w) = g_L(v, w)` on the whole domain
`R > τ`, with the Jacobian `J`. With `EddingtonFinkelstein.form_toEddington`, the Lemaître chart
is the Schwarzschild field, through the sphere `r = 2M`, and a vacuum metric there
(`EddingtonFinkelstein.ricciOf_eq_zero`). -/
theorem form_lemaitreToEddington (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1)
    (v w : MinkowskiModel 3) :
    EddingtonFinkelstein.form M (lemaitreToEddington M x) (lemaitreToEddingtonDeriv M x v)
        (lemaitreToEddingtonDeriv M x w) =
      (lemaitre hM).metric.form x v w := by
  have hr0 := lemaitreRadius_pos hM hx
  have hd := sub_pos.mpr hx
  have hβ := sqrt_two_mul_div_lemaitreRadius hM hx
  have hβ2 : 2 * M / lemaitreRadius M x = (2 / 3 * lemaitreRadius M x / (x 1 - x 0)) ^ 2 := by
    rw [← hβ, Real.sq_sqrt (by positivity)]
  rw [EddingtonFinkelstein.form_apply, ComovingData.metric_form_apply,
    lemaitreToEddingtonDeriv_apply, lemaitreToEddingtonDeriv_apply]
  change _ = -(v 0 * w 0) + 2 * M / lemaitreRadius M x * (v 1 * w 1) +
    lemaitreRadius M x ^ 2 * (v 2 * w 2) + lemaitreRadius M x ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3)
  simp [lemaitreToEddington]
  rw [hβ2]
  set β := 2 / 3 * lemaitreRadius M x / (x 1 - x 0)
  have hβ0 : 0 < β := by positivity
  have h1 : 1 + β ≠ 0 := by positivity
  field_simp
  ring

/-! ### The interior: a collapsing ball of flat dust -/

variable {τc : ℝ}

/-- The scale factor `a(τ) = ((τ_c − τ)/τ_c)^{2/3}` of the collapsing flat dust model, with
`a(0) = 1`; it vanishes at the time `τ_c` of the crunch. -/
def dustScale (τc τ : ℝ) : ℝ := ((τc - τ) / τc) ^ (2 / 3 : ℝ)

theorem dustBase_pos (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) : 0 < (τc - τ) / τc :=
  div_pos (sub_pos.mpr hτ) hτc

theorem dustScale_pos (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) : 0 < dustScale τc τ :=
  Real.rpow_pos_of_pos (dustBase_pos hτc hτ) _

/-- `a³ = ((τ_c − τ)/τ_c)²`. -/
theorem dustScale_cube (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    dustScale τc τ ^ 3 = ((τc - τ) / τc) ^ 2 := by
  rw [dustScale, ← Real.rpow_natCast, ← Real.rpow_mul (dustBase_pos hτc hτ).le]
  norm_num

/-- `ȧ = −(2/3) a/(τ_c − τ)`. -/
theorem hasDerivAt_dustScale (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    HasDerivAt (dustScale τc) (-(2 / 3) * dustScale τc τ / (τc - τ)) τ := by
  have hb := (dustBase_pos hτc hτ).ne'
  have hd := (sub_pos.mpr hτ).ne'
  have h := (((hasDerivAt_id' τ).const_sub τc).div_const τc).rpow_const (p := 2 / 3) (Or.inl hb)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hb, dustScale]
  field_simp

theorem contDiffOn_dustScale (hτc : 0 < τc) : ContDiffOn ℝ ∞ (dustScale τc) (Iio τc) :=
  ((contDiffOn_const.sub contDiffOn_id).div_const τc).rpow_const_of_ne
    fun _ hτ => (dustBase_pos hτc hτ).ne'

/-- `ä = −(2/9) a/(τ_c − τ)²`. -/
theorem hasDerivAt_deriv_dustScale (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    HasDerivAt (deriv (dustScale τc)) (-(2 / 9) * dustScale τc τ / (τc - τ) ^ 2) τ := by
  have hd := (sub_pos.mpr hτ).ne'
  have hev : deriv (dustScale τc) =ᶠ[𝓝 τ] fun σ => -(2 / 3) * dustScale τc σ / (τc - σ) :=
    eventually_of_mem (isOpen_Iio.mem_nhds hτ) fun σ hσ => (hasDerivAt_dustScale hτc hσ).deriv
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  refine (((hasDerivAt_dustScale hτc hτ).const_mul (-(2 / 3))).fun_div
    ((hasDerivAt_id' τ).const_sub τc) hd).congr_deriv ?_
  field_simp
  ring

/-- The domain `τ < τ_c`, `χ > 0`, `0 < θ < π` of the comoving co-ordinates `(τ, χ, θ, φ)`. -/
def dustDomain (τc : ℝ) : Opens (MinkowskiModel 3) :=
  ⟨{x | x 0 < τc ∧ 0 < x 1 ∧ 0 < x 2 ∧ x 2 < π},
    (isOpen_lt (continuous_apply 0) continuous_const).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        ((isOpen_lt continuous_const (continuous_apply 2)).inter
          (isOpen_lt (continuous_apply 2) continuous_const)))⟩

/-- **The collapsing flat dust ball** in comoving spherical co-ordinates `(τ, χ, θ, φ)`:
`ds² = −dτ² + a(τ)² (dχ² + χ² (dθ² + sin²θ dφ²))` with `a = ((τ_c − τ)/τ_c)^{2/3}`, the isotropic
model `k = 0` of `FLRW` in spherical co-ordinates (Landau–Lifshitz, §§103, 112). -/
def dustInterior (hτc : 0 < τc) : ComovingData where
  domain := dustDomain τc
  A x := dustScale τc (x 0) ^ 2
  r x := dustScale τc (x 0) * x 1
  contDiffOn_A := ((contDiffOn_dustScale hτc).comp
    (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hx => hx.1).pow 2
  contDiffOn_r := ((contDiffOn_dustScale hτc).comp
    (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hx => hx.1).mul
      (contDiff_apply ℝ (fun _ => ℝ) 1).contDiffOn
  A_pos _ hx := pow_pos (dustScale_pos hτc hx.1) 2
  r_pos _ hx := mul_pos (dustScale_pos hτc hx.1) hx.2.1
  sin_pos _ hx := Real.sin_pos_of_pos_of_lt_pi hx.2.2.1 hx.2.2.2

/-- The comoving dust shells have the energy `∂_χ r/e^{λ/2} = 1` per unit mass, the value `f = 0`
of the flat model. -/
theorem shellEnergy_dustInterior (hτc : 0 < τc) {x : MinkowskiModel 3}
    (hx : x ∈ dustDomain τc) : (dustInterior hτc).shellEnergy x = 1 := by
  have ha := dustScale_pos hτc hx.1
  have hr : HasFDerivAt (fun y : MinkowskiModel 3 => dustScale τc (y 0) * y 1)
      (dustScale τc (x 0) • (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
        x 1 • ((-(2 / 3) * dustScale τc (x 0) / (τc - x 0)) •
          (ContinuousLinearMap.proj 0 : MinkowskiModel 3 →L[ℝ] ℝ))) x :=
    (SchwarzschildExterior.hasFDerivAt_coord 0 (hasDerivAt_dustScale hτc hx.1)).fun_mul
      (hasFDerivAt_apply 1 x)
  rw [ComovingData.shellEnergy]
  change fderiv ℝ (fun y : MinkowskiModel 3 => dustScale τc (y 0) * y 1) x (Pi.single 1 1) /
    Real.sqrt (dustScale τc (x 0) ^ 2) = 1
  rw [hr.fderiv, Real.sqrt_sq ha.le]
  simp [ha.ne']

/-- The isotropic model of `FLRW` with `N = 1`, `k = 0` and the scale factor `dustScale`. -/
def dustData (hτc : 0 < τc) : FLRW.Data where
  I := Iio τc
  N := fun _ => 1
  a := dustScale τc
  k := 0
  isOpen_I := isOpen_Iio
  contDiffOn_N := contDiffOn_const
  contDiffOn_a := contDiffOn_dustScale hτc
  N_pos := fun _ _ => one_pos
  a_pos := fun _ hτ => dustScale_pos hτc hτ

/-- The density `ρ = 4/(3κ(τ_c − τ)²)` of the dust. -/
def dustDensity (κ τc τ : ℝ) : ℝ := 4 / (3 * κ * (τc - τ) ^ 2)

/-- **The interior is a solution with dust**: the isotropic model `dustData` with the comoving dust
of density `dustDensity` and pressure `p = 0` satisfies the Einstein equations
`G_{ik} = κ T_{ik}` (the Friedmann equations `H² = κρ/3`, `2ä/a + H² = 0`). -/
theorem isEinstein_dustData (hτc : 0 < τc) {κ : ℝ} (hκ : κ ≠ 0) :
    (FLRW.metric (dustData hτc)).IsEinstein κ 0
      (FLRW.perfectFluidStress (dustData hτc) (dustDensity κ τc) fun _ => 0) := by
  rw [FLRW.isEinstein_iff_friedmann]
  intro τ hτ
  have hτ' : τ < τc := hτ
  have hN : ∀ s ∈ (dustData hτc).I, (dustData hτc).N s = 1 := fun _ _ => rfl
  have ha := (dustScale_pos hτc hτ').ne'
  have hd := (sub_pos.mpr hτ').ne'
  have hda : deriv (dustData hτc).a τ = -(2 / 3) * dustScale τc τ / (τc - τ) :=
    (hasDerivAt_dustScale hτc hτ').deriv
  have hdda : deriv (deriv (dustData hτc).a) τ = -(2 / 9) * dustScale τc τ / (τc - τ) ^ 2 :=
    (hasDerivAt_deriv_dustScale hτc hτ').deriv
  refine ⟨(FLRW.firstFriedmann_iff_of_lapse_eq_one hN hτ κ 0 _).mpr ?_,
    (FLRW.secondFriedmann_iff_of_lapse_eq_one hN hτ κ 0 _).mpr ?_⟩
  · rw [FLRW.hubble, hda]
    change (-(2 / 3) * dustScale τc τ / (τc - τ) / dustScale τc τ) ^ 2 + 0 / dustScale τc τ ^ 2 =
      κ * dustDensity κ τc τ / 3 + 0 / 3
    rw [dustDensity]
    field_simp
    ring
  · rw [hda, hdda]
    change 2 * (-(2 / 9) * dustScale τc τ / (τc - τ) ^ 2 / dustScale τc τ) +
      (-(2 / 3) * dustScale τc τ / (τc - τ) / dustScale τc τ) ^ 2 + 0 / dustScale τc τ ^ 2 =
        -κ * 0 + 0
    field_simp
    ring

/-- Spherical co-ordinates: `(τ, χ, θ, φ) ↦ (τ, χ sin θ cos φ, χ sin θ sin φ, χ cos θ)`. -/
def toCartesian (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![x 0, x 1 * Real.sin (x 2) * Real.cos (x 3), x 1 * Real.sin (x 2) * Real.sin (x 3),
    x 1 * Real.cos (x 2)]

/-- The Jacobian of the spherical co-ordinates at `x`, as a linear map. -/
def toCartesianLinear (x : MinkowskiModel 3) : MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 where
  toFun v := ![v 0,
    v 1 * Real.sin (x 2) * Real.cos (x 3) + x 1 * Real.cos (x 2) * Real.cos (x 3) * v 2 -
      x 1 * Real.sin (x 2) * Real.sin (x 3) * v 3,
    v 1 * Real.sin (x 2) * Real.sin (x 3) + x 1 * Real.cos (x 2) * Real.sin (x 3) * v 2 +
      x 1 * Real.sin (x 2) * Real.cos (x 3) * v 3,
    v 1 * Real.cos (x 2) - x 1 * Real.sin (x 2) * v 2]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The Jacobian of the spherical co-ordinates at `x`. -/
def toCartesianDeriv (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  LinearMap.toContinuousLinearMap (toCartesianLinear x)

theorem toCartesianDeriv_apply (x v : MinkowskiModel 3) :
    toCartesianDeriv x v = ![v 0,
      v 1 * Real.sin (x 2) * Real.cos (x 3) + x 1 * Real.cos (x 2) * Real.cos (x 3) * v 2 -
        x 1 * Real.sin (x 2) * Real.sin (x 3) * v 3,
      v 1 * Real.sin (x 2) * Real.sin (x 3) + x 1 * Real.cos (x 2) * Real.sin (x 3) * v 2 +
        x 1 * Real.sin (x 2) * Real.cos (x 3) * v 3,
      v 1 * Real.cos (x 2) - x 1 * Real.sin (x 2) * v 2] := rfl

/-- The spherical co-ordinates have the Jacobian `toCartesianDeriv`. -/
theorem hasFDerivAt_toCartesian (x : MinkowskiModel 3) :
    HasFDerivAt toCartesian (toCartesianDeriv x) x := by
  have h1 : HasFDerivAt (fun y : MinkowskiModel 3 => y 1)
      (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) x := hasFDerivAt_apply 1 x
  have hs2 := SchwarzschildExterior.hasFDerivAt_coord 2 (Real.hasDerivAt_sin (x 2))
  have hc2 := SchwarzschildExterior.hasFDerivAt_coord 2 (Real.hasDerivAt_cos (x 2))
  have hs3 := SchwarzschildExterior.hasFDerivAt_coord 3 (Real.hasDerivAt_sin (x 3))
  have hc3 := SchwarzschildExterior.hasFDerivAt_coord 3 (Real.hasDerivAt_cos (x 3))
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · refine (hasFDerivAt_apply 0 x).congr_fderiv ?_
    ext w
    simp [toCartesianDeriv_apply]
  · refine ((h1.fun_mul hs2).fun_mul hc3).congr_fderiv ?_
    ext w
    simp [toCartesianDeriv_apply]
    ring
  · refine ((h1.fun_mul hs2).fun_mul hs3).congr_fderiv ?_
    ext w
    simp [toCartesianDeriv_apply]
    ring
  · refine (h1.fun_mul hc2).congr_fderiv ?_
    ext w
    simp [toCartesianDeriv_apply]
    ring

/-- The spherical co-ordinates send the comoving domain into the domain of `dustData`. -/
theorem toCartesian_mem (hτc : 0 < τc) {x : MinkowskiModel 3} (hx : x ∈ dustDomain τc) :
    toCartesian x ∈ FLRW.domain (dustData hτc) :=
  ⟨hx.1, by simp [FLRW.psi, dustData]⟩

/-- **The interior is the isotropic dust model in spherical co-ordinates**: the comoving metric
`dustInterior` is the pullback of the isotropic metric `FLRW.metric (dustData hτc)` (the flat
model `k = 0` in the co-ordinates `(t, x¹, x², x³)`, a solution with dust by
`isEinstein_dustData`) by the spherical co-ordinates: `g_FLRW(J v, J w) = g(v, w)`. -/
theorem form_toCartesian (hτc : 0 < τc) (x v w : MinkowskiModel 3) :
    (FLRW.metric (dustData hτc)).form (toCartesian x) (toCartesianDeriv x v)
        (toCartesianDeriv x w) =
      (dustInterior hτc).metric.form x v w := by
  have hX := Real.sin_sq_add_cos_sq (x 3)
  have hY := Real.sin_sq_add_cos_sq (x 2)
  rw [CoordinateMetric.form_apply, FLRW.coefficient_metric, ComovingData.metric_form_apply,
    toCartesianDeriv_apply, toCartesianDeriv_apply]
  change _ = -(v 0 * w 0) + dustScale τc (x 0) ^ 2 * (v 1 * w 1) +
    (dustScale τc (x 0) * x 1) ^ 2 * (v 2 * w 2) +
    (dustScale τc (x 0) * x 1) ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3)
  simp [EddingtonFinkelstein.sum_four, Matrix.diagonal_apply, FLRW.coefficients, FLRW.psi,
    dustData, toCartesian]
  set a := dustScale τc (x 0)
  set s := Real.sin (x 2)
  set c := Real.cos (x 2)
  linear_combination a ^ 2 * (v 1 * w 1 * s ^ 2 + x 1 ^ 2 * v 2 * w 2 * c ^ 2 +
      x 1 ^ 2 * s ^ 2 * v 3 * w 3 + x 1 * s * c * (v 1 * w 2 + v 2 * w 1)) * hX +
    a ^ 2 * (v 1 * w 1 + x 1 ^ 2 * v 2 * w 2) * hY

/-! ### The junction of Oppenheimer and Snyder -/

/-- The mass relation `2M = (κ/3) ρ(0) χ_b³` is `9 M τ_c² = 2 χ_b³`. -/
theorem mass_iff (hτc : 0 < τc) {κ M χb : ℝ} (hκ : κ ≠ 0) :
    2 * M = κ / 3 * dustDensity κ τc 0 * χb ^ 3 ↔ 9 * M * τc ^ 2 = 2 * χb ^ 3 := by
  have h := hτc.ne'
  rw [dustDensity, sub_zero]
  constructor <;> intro h' <;> field_simp at h' ⊢ <;> linarith

/-- The radius `a(τ) χ_b` of the boundary of the dust ball is the Lemaître radius of the shell
`R = τ_c` when `9 M τ_c² = 2 χ_b³`. -/
theorem dustScale_mul_eq_lemaitreRadius (hM : 0 < M) (hτc : 0 < τc) {χb : ℝ} (hχ : 0 < χb)
    (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3) {τ θ φ : ℝ} (hτ : τ < τc) :
    lemaitreRadius M ![τ, τc, θ, φ] = dustScale τc τ * χb := by
  have hx : (![τ, τc, θ, φ] : MinkowskiModel 3) 0 < (![τ, τc, θ, φ] : MinkowskiModel 3) 1 := hτ
  have h1 := lemaitreRadius_pos hM hx
  have h2 := mul_pos (dustScale_pos hτc hτ) hχ
  refine (pow_left_inj₀ h1.le h2.le three_ne_zero).mp ?_
  rw [lemaitreRadius_cube hM hx, mul_pow, dustScale_cube hτc hτ]
  have hτc' := hτc.ne'
  change 9 / 2 * M * (τc - τ) ^ 2 = ((τc - τ) / τc) ^ 2 * χb ^ 3
  have hd := (sub_pos.mpr hτ).ne'
  field_simp
  linear_combination hmass

/-- **The junction conditions of the Oppenheimer–Snyder collapse** (Landau–Lifshitz, §103, the
homogeneous dust ball matched to the field outside). The boundary of the ball is the comoving
shell `χ = χ_b` of the collapsing flat dust model (`dustInterior`) and the comoving shell
`R = R_b` of the Lemaître chart of the Schwarzschild field of mass `M` (`lemaitre`), both
co-ordinate hypersurfaces with the proper time `τ` and the angles `(θ, φ)` as co-ordinates.

* The induced metrics agree at all times `τ < min(R_b, τ_c)` exactly when `R_b = τ_c` (the
  boundary reaches `r = 0` at the crunch `τ_c` of the dust) and `r_g = 2M = (κ/3) ρ(0) χ_b³`
  (with `κ = 8π`, `M = (4π/3) ρ r_b³`: the mass of the dust inside the boundary).
* Then for every `τ < τ_c` the induced metrics and the second fundamental forms, for the normals
  `ε e^{−λ/2} ∂_R`, agree (the conditions of Darmois and Israel, with no surface layer), and
  `2M = (κ/3) ρ(τ) r_b(τ)³` holds at every time, with the areal radius `r_b = a χ_b` of the
  boundary. -/
theorem junction_oppenheimerSnyder (hM : 0 < M) {χb Rb : ℝ} (hτc : 0 < τc) (hχ : 0 < χb)
    {κ : ℝ} (hκ : κ ≠ 0) {θ : ℝ} (φ : ℝ) (hθ : θ ∈ Ioo 0 π) (ε : ℝ) :
    ((∀ τ < min Rb τc, (lemaitre hM).metric.inducedMetric 1 ![τ, Rb, θ, φ] =
        (dustInterior hτc).metric.inducedMetric 1 ![τ, χb, θ, φ]) ↔
      Rb = τc ∧ 2 * M = κ / 3 * dustDensity κ τc 0 * χb ^ 3) ∧
    (Rb = τc → 2 * M = κ / 3 * dustDensity κ τc 0 * χb ^ 3 → ∀ τ < τc,
      (lemaitre hM).metric.inducedMetric 1 ![τ, Rb, θ, φ] =
          (dustInterior hτc).metric.inducedMetric 1 ![τ, χb, θ, φ] ∧
        (lemaitre hM).metric.secondFundamental 1 ε ![τ, Rb, θ, φ] =
          (dustInterior hτc).metric.secondFundamental 1 ε ![τ, χb, θ, φ] ∧
        κ / 3 * dustDensity κ τc τ * (dustScale τc τ * χb) ^ 3 = 2 * M) := by
  have hmemL {τ : ℝ} (hτ : τ < Rb) : (![τ, Rb, θ, φ] : MinkowskiModel 3) ∈ lemaitreDomain :=
    ⟨hτ, hθ.1, hθ.2⟩
  have hmemI {τ : ℝ} (hτ : τ < τc) : (![τ, χb, θ, φ] : MinkowskiModel 3) ∈ dustDomain τc :=
    ⟨hτ, hχ, hθ.1, hθ.2⟩
  have hiff {τ : ℝ} (hτ : τ < min Rb τc) :
      (lemaitre hM).metric.inducedMetric 1 ![τ, Rb, θ, φ] =
          (dustInterior hτc).metric.inducedMetric 1 ![τ, χb, θ, φ] ↔
        lemaitreRadius M ![τ, Rb, θ, φ] = dustScale τc τ * χb :=
    ComovingData.inducedMetric_eq_iff (hmemL (lt_of_lt_of_le hτ (min_le_left _ _)))
      (hmemI (lt_of_lt_of_le hτ (min_le_right _ _))) rfl
  refine ⟨⟨fun h => ?_, fun ⟨hR, hm⟩ τ hτ => ?_⟩, fun hR hm τ hτ => ?_⟩
  · -- the cubes of the radii agree at three times, so the two quadratics in `τ` agree
    have hc (τ : ℝ) (hτ : τ < min Rb τc) :
        9 / 2 * M * τc ^ 2 * (Rb - τ) ^ 2 = χb ^ 3 * (τc - τ) ^ 2 := by
      have hr := (hiff hτ).mp (h τ hτ)
      have hτR : τ < Rb := lt_of_lt_of_le hτ (min_le_left _ _)
      have hτC : τ < τc := lt_of_lt_of_le hτ (min_le_right _ _)
      have h3 := congrArg (· ^ 3) hr
      rw [lemaitreRadius_cube hM (show (![τ, Rb, θ, φ] : MinkowskiModel 3) 0 < _ from hτR),
        mul_pow, dustScale_cube hτc hτC] at h3
      change 9 / 2 * M * (Rb - τ) ^ 2 = ((τc - τ) / τc) ^ 2 * χb ^ 3 at h3
      have hτc' := hτc.ne'
      field_simp at h3
      linear_combination (1 / 2 : ℝ) * h3
    set m := min Rb τc
    have e1 := hc (m - 1) (by linarith)
    have e2 := hc (m - 2) (by linarith)
    have e3 := hc (m - 3) (by linarith)
    have hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3 := by linear_combination e1 - 2 * e2 + e3
    have hR : 9 * M * τc ^ 2 * (τc - Rb) = 0 := by
      linear_combination (e1 - e2) + (2 * τc - 2 * m + 3) / 2 * hmass
    refine ⟨?_, (mass_iff hτc hκ).mpr hmass⟩
    have hne : 9 * M * τc ^ 2 ≠ 0 := by positivity
    have := (mul_eq_zero.mp hR).resolve_left hne
    linarith
  · subst hR
    exact (hiff hτ).mpr (dustScale_mul_eq_lemaitreRadius hM hτc hχ ((mass_iff hτc hκ).mp hm)
      (lt_of_lt_of_le hτ (min_le_right _ _)))
  · subst hR
    have hmass := (mass_iff hτc hκ).mp hm
    have hr := dustScale_mul_eq_lemaitreRadius hM hτc hχ hmass (θ := θ) (φ := φ) hτ
    have hj := ComovingData.junction (D₁ := lemaitre hM) (D₂ := dustInterior hτc) (hmemL hτ)
      (hmemI hτ) rfl hr
      (by rw [shellEnergy_lemaitre hM (show (![τ, Rb, θ, φ] : MinkowskiModel 3) 0 < _ from hτ),
        shellEnergy_dustInterior hτc (hmemI hτ)]) ε
    refine ⟨hj.1, hj.2, ?_⟩
    rw [mul_pow, dustScale_cube hτc hτ, dustDensity]
    have hτc' := hτc.ne'
    have hd := (sub_pos.mpr hτ).ne'
    field_simp
    linear_combination (-2 : ℝ) * hmass


/- The hypotheses of `junction_oppenheimerSnyder` hold: for `κ = 1`, `τ_c = R_b = 1`, `χ_b = 1`
and `M = 2/9`, the mass relation `2M = (κ/3) ρ(0) χ_b³` is satisfied. -/
example : (1 : ℝ) = 1 ∧ 2 * (2 / 9 : ℝ) = 1 / 3 * dustDensity 1 1 0 * 1 ^ 3 := by
  refine ⟨rfl, ?_⟩
  rw [dustDensity]
  norm_num

/-! ### The closed model does not match the Lemaître chart -/

/-- The second fundamental forms of two comoving shells with the same areal radius and the same
`θ` agree, for `ε ≠ 0`, exactly when their rates `∂_R r/e^{λ/2}` agree. -/
theorem ComovingData.secondFundamental_eq_iff {D₁ D₂ : ComovingData} {x₁ x₂ : MinkowskiModel 3}
    (hx₁ : x₁ ∈ D₁.domain) (hx₂ : x₂ ∈ D₂.domain) (hθ : x₁ 2 = x₂ 2) (hr : D₁.r x₁ = D₂.r x₂)
    {ε : ℝ} (hε : ε ≠ 0) :
    D₁.metric.secondFundamental 1 ε x₁ = D₂.metric.secondFundamental 1 ε x₂ ↔
      D₁.shellEnergy x₁ = D₂.shellEnergy x₂ := by
  rw [ComovingData.secondFundamental_eq _ hx₁, ComovingData.secondFundamental_eq _ hx₂, hθ, hr]
  constructor
  · intro h
    have h1 := congrFun (congrFun h 1) 1
    simp only [Matrix.diagonal_apply_eq] at h1
    have h1' : ε * D₁.shellEnergy x₁ * D₂.r x₂ = ε * D₂.shellEnergy x₂ * D₂.r x₂ := h1
    have hr2 := (D₂.r_pos x₂ hx₂).ne'
    have := mul_right_cancel₀ hr2 h1'
    exact mul_left_cancel₀ hε this
  · intro h
    rw [h]

/-- The domain `τ ∈ I`, `0 < χ < π`, `0 < θ < π` of the comoving co-ordinates of the closed
model. -/
def closedDomain (I : Set ℝ) (hI : IsOpen I) : Opens (MinkowskiModel 3) :=
  ⟨{x | x 0 ∈ I ∧ 0 < x 1 ∧ x 1 < π ∧ 0 < x 2 ∧ x 2 < π},
    (hI.preimage (continuous_apply 0)).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        ((isOpen_lt (continuous_apply 1) continuous_const).inter
          ((isOpen_lt continuous_const (continuous_apply 2)).inter
            (isOpen_lt (continuous_apply 2) continuous_const))))⟩

/-- **The closed isotropic model `k = +1` in comoving spherical co-ordinates**
`ds² = −dτ² + a(τ)² (dχ² + sin²χ (dθ² + sin²θ dφ²))`, for any scale factor `a` smooth and
positive on an open set `I` of times (Landau–Lifshitz, (111.1), (112.2)). -/
def closedInterior (I : Set ℝ) (hI : IsOpen I) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a I)
    (hpos : ∀ τ ∈ I, 0 < a τ) : ComovingData where
  domain := closedDomain I hI
  A x := a (x 0) ^ 2
  r x := a (x 0) * Real.sin (x 1)
  contDiffOn_A := (ha.comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hx => hx.1).pow 2
  contDiffOn_r := (ha.comp (contDiff_apply ℝ (fun _ => ℝ) 0).contDiffOn fun _ hx => hx.1).mul
    (Real.contDiff_sin.comp (contDiff_apply ℝ (fun _ => ℝ) 1)).contDiffOn
  A_pos _ hx := pow_pos (hpos _ hx.1) 2
  r_pos _ hx := mul_pos (hpos _ hx.1) (Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2.1)
  sin_pos _ hx := Real.sin_pos_of_pos_of_lt_pi hx.2.2.2.1 hx.2.2.2.2

/-- The shells of the closed model have the rate `∂_χ r/e^{λ/2} = cos χ`, that is `f = −sin²χ` in
(103.2): they are bound. -/
theorem shellEnergy_closedInterior {I : Set ℝ} {hI : IsOpen I} {a : ℝ → ℝ}
    {ha : ContDiffOn ℝ ∞ a I} {hpos : ∀ τ ∈ I, 0 < a τ} {x : MinkowskiModel 3}
    (hx : x ∈ closedDomain I hI) :
    (closedInterior I hI a ha hpos).shellEnergy x = Real.cos (x 1) := by
  have ha0 := hpos _ hx.1
  have hdiff : DifferentiableAt ℝ a (x 0) :=
    (ha.contDiffAt (hI.mem_nhds hx.1)).differentiableAt (by simp)
  have hr : HasFDerivAt (fun y : MinkowskiModel 3 => a (y 0) * Real.sin (y 1))
      (a (x 0) • (Real.cos (x 1) • (ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) +
        Real.sin (x 1) • (deriv a (x 0) •
          (ContinuousLinearMap.proj 0 : MinkowskiModel 3 →L[ℝ] ℝ))) x :=
    (SchwarzschildExterior.hasFDerivAt_coord 0 hdiff.hasDerivAt).fun_mul
      (SchwarzschildExterior.hasFDerivAt_coord 1 (Real.hasDerivAt_sin (x 1)))
  rw [ComovingData.shellEnergy]
  change fderiv ℝ (fun y : MinkowskiModel 3 => a (y 0) * Real.sin (y 1)) x (Pi.single 1 1) /
    Real.sqrt (a (x 0) ^ 2) = Real.cos (x 1)
  rw [hr.fderiv, Real.sqrt_sq ha0.le]
  simp
  field_simp

/-- **The closed dust ball cannot be matched to the Lemaître chart.** For the closed model
`k = +1` with any scale factor, and a shell `R = R_b` of the Lemaître chart, at points where the
induced metrics of the boundaries `χ = χ_b` and `R = R_b` agree, the second fundamental forms
differ (for `ε ≠ 0`): the Lemaître shells have the rate `∂_R r/e^{λ/2} = 1` (they fall from rest
at infinity) and the closed shells `cos χ_b < 1` (they fall from rest at a finite radius). The
exterior of a closed dust ball needs a comoving chart of the Schwarzschild field with bound
shells (`f(R_b) = −sin²χ_b`). -/
theorem secondFundamental_closedInterior_ne_lemaitre (hM : 0 < M) {I : Set ℝ} {hI : IsOpen I}
    {a : ℝ → ℝ} {ha : ContDiffOn ℝ ∞ a I} {hpos : ∀ τ ∈ I, 0 < a τ}
    {xL xI : MinkowskiModel 3} (hxL : xL ∈ lemaitreDomain) (hxI : xI ∈ closedDomain I hI)
    (hθ : xL 2 = xI 2)
    (h : (lemaitre hM).metric.inducedMetric 1 xL =
      (closedInterior I hI a ha hpos).metric.inducedMetric 1 xI) {ε : ℝ} (hε : ε ≠ 0) :
    (lemaitre hM).metric.secondFundamental 1 ε xL ≠
      (closedInterior I hI a ha hpos).metric.secondFundamental 1 ε xI := by
  have hr := (ComovingData.inducedMetric_eq_iff hxL hxI hθ).mp h
  rw [Ne, ComovingData.secondFundamental_eq_iff hxL hxI hθ hr hε, shellEnergy_lemaitre hM hxL.1,
    shellEnergy_closedInterior hxI]
  intro hc
  have hlt : Real.cos π < Real.cos (xI 1) := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hxI.2.1.le le_rfl hxI.2.2.1
  have h0 : Real.cos (xI 1) < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hxI.2.2.1.le hxI.2.1
  rw [Real.cos_zero] at h0
  linarith

/- The hypotheses of `secondFundamental_closedInterior_ne_lemaitre` hold: for `M = 1` and the
constant scale factor `a = r_L/sin(π/2)` at the point `(0, 1, π/2, 0)`, the boundaries `R = 1`
and `χ = π/2` have the same induced metric. -/
example : (lemaitre one_pos).metric.inducedMetric 1 ![0, 1, π / 2, 0] =
    (closedInterior univ isOpen_univ (fun _ => lemaitreRadius 1 ![0, 1, π / 2, 0])
      contDiffOn_const (fun _ _ => lemaitreRadius_pos one_pos (by simp))).metric.inducedMetric 1
        ![0, π / 2, π / 2, 0] := by
  rw [ComovingData.inducedMetric_eq, ComovingData.inducedMetric_eq]
  simp [lemaitre, closedInterior]

end ProjectAinos.GeneralRelativity.Collapse
