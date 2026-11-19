/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildCircular
public import ProjectAinos.GeneralRelativity.SchwarzschildRotations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp

/-!
# The integrals of the motion in the Schwarzschild field

Let `γ` be a geodesic of the exterior Schwarzschild metric of `SchwarzschildExterior`, given on
an open convex set `s` of parameters, with the co-ordinates `(t, r, θ, φ)` and the co-ordinate
velocity `(ṫ, ṙ, θ̇, φ̇)`. The Killing fields `∂_t` and the rotations give the integrals of the
motion of Landau–Lifshitz, §101, (101.1)–(101.5).

* `energy`, `energy_eq`, `energy_eq_coord`: the energy `E = −g(∂_t, γ̇)` is constant along the
  geodesic and equals `(1 − 2M/r) ṫ`; `timeRate_eq`: `ṫ = E/(1 − 2M/r)`.
* `angularMomentumSq`, `angularMomentumSq_eq`, `angularMomentumSq_eq_coord`: the square
  `L² = J₀² + J₁² + J₂²` of the angular momentum is constant and equals `r⁴ (θ̇² + sin²θ φ̇²)`.
* `normalization`, `normalization_eq`, `form_curveVelocity_eq_coord`: `κ = −g(γ̇, γ̇)` is
  constant, with `g(γ̇, γ̇) = −(1 − 2M/r) ṫ² + ṙ²/(1 − 2M/r) + r² θ̇² + r² sin²θ φ̇²`.
* `radial_sq_eq`: **the radial equation** (101.4), `ṙ² = E² − (1 − 2M/r)(κ + L²/r²)`, with the
  constants `E`, `κ`, `L` of the geodesic; `κ = 1` for a body parametrized by its proper time
  and `κ = 0` for light.
* `sweptAngle`, `hasDerivAt_sweptAngle_eq_div`: the angle `∫ √(θ̇² + sin²θ φ̇²)` swept in the
  plane of the motion has the derivative `L/r²`, the second equation of (101.4);
  `sweptAngle_equatorial`: for a motion in the equatorial plane with `φ̇ ≥ 0` it is the increase
  of `φ`.
* `radial_sq_eq_circular`: for the circular orbits of `SchwarzschildCircular`, `ṙ = 0` and the
  radial equation reduces to `E² = V(R)`, in agreement with `effectivePotential_circular`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski
open LorentzMetric (chartField curveVelocity)
open CoordinateMetric (physicalChart)

variable {M : ℝ}

/-! ### Technical facts on the domain and on geodesics -/

private theorem radius_pos_of_mem_domain (hM : 0 ≤ M) {y : MinkowskiModel 3}
    (hy : y ∈ domain M) : 0 < y 1 := by
  have : 2 * M < y 1 := hy.1
  linarith

private theorem sub_pos_of_mem_domain {y : MinkowskiModel 3} (hy : y ∈ domain M) :
    0 < y 1 - 2 * M := by
  have : 2 * M < y 1 := hy.1
  linarith

private theorem lapse_pos_of_mem_domain (hM : 0 ≤ M) {y : MinkowskiModel 3}
    (hy : y ∈ domain M) : 0 < 1 - 2 * M / y 1 := by
  have h0 := radius_pos_of_mem_domain hM hy
  have : 2 * M / y 1 < 1 := (div_lt_one h0).mpr hy.1
  linarith

private theorem contDiffAt_of_isGeodesicOn {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    ContDiffAt ℝ 2 (fun t => (γ t : MinkowskiModel 3)) τ :=
  CoordinateMetric.contMDiffAt_iff_contDiffAt_val.mp (hγ τ hτ).1

private theorem differentiableAt_of_isGeodesicOn {hM : 0 ≤ M} {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ :=
  (contDiffAt_of_isGeodesicOn hγ hτ).differentiableAt (by norm_num)

private theorem contDiffOn_of_isGeodesicOn {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) :
    ContDiffOn ℝ 2 (fun t => (γ t : MinkowskiModel 3)) s :=
  fun _ ht => (contDiffAt_of_isGeodesicOn hγ ht).contDiffWithinAt

private theorem continuousOn_deriv_of_isGeodesicOn {hM : 0 ≤ M} {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) :
    ContinuousOn (deriv (fun t => (γ t : MinkowskiModel 3))) s :=
  (contDiffOn_of_isGeodesicOn hγ).continuousOn_deriv_of_isOpen hso (by norm_num)

/-! ### The energy -/

/-- The energy `E = −g(∂_t, γ̇)` of a curve: minus the pairing of its velocity with the Killing
field `∂_t`. -/
def energy (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) : ℝ :=
  -(metric hM).toLorentzMetric.form (γ τ) (chartField (physicalChart x₀) (Pi.single 0 1) (γ τ))
    (curveVelocity γ τ)

/-- **The conservation of energy** (Landau–Lifshitz, §101). Along a geodesic, given on a convex
set of parameters, the energy `E = −g(∂_t, γ̇)` is constant. -/
theorem energy_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) : energy hM x₀ γ τ₁ = energy hM x₀ γ τ₂ := by
  unfold energy
  rw [(isKillingField_time hM x₀).pairing_eq
    (fun y => CoordinateMetric.chartField_mdifferentiableAt x₀ y _) hγ hs h₁ h₂]

/-- In co-ordinates the energy is `E = (1 − 2M/r) ṫ`. -/
theorem energy_eq_coord (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    energy hM x₀ γ τ = (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) *
      deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 := by
  have h0 := (radius_pos_of_mem_domain hM (γ τ).property).ne'
  unfold energy
  rw [(metric hM).pairing_curveVelocity hγ x₀, coefficient_eq_diagonal]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagonalCoefficients]
  exact Or.inl (by rw [sub_div, div_self h0])

/-- The rate of the co-ordinate time is `ṫ = E/(1 − 2M/r)`. -/
theorem timeRate_eq_of_differentiableAt (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {τ : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 =
      energy hM x₀ γ τ / (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) := by
  rw [energy_eq_coord hM x₀ hγ,
    mul_div_cancel_left₀ _ (lapse_pos_of_mem_domain hM (γ τ).property).ne']

/-- **The rate of the co-ordinate time** along a geodesic: `ṫ(τ) = E/(1 − 2M/r(τ))`, with the
constant energy `E` read at any parameter `τ₀` of a convex set. -/
theorem timeRate_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 =
      energy hM x₀ γ τ₀ / (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) := by
  rw [energy_eq hM x₀ hγ hs h₀ hτ]
  exact timeRate_eq_of_differentiableAt hM x₀ (differentiableAt_of_isGeodesicOn hγ hτ)

/-! ### The square of the angular momentum -/

/-- The square `L² = J₀² + J₁² + J₂²` of the angular momentum of a curve. -/
def angularMomentumSq (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) : ℝ :=
  angularMomentum hM x₀ γ τ 0 ^ 2 + angularMomentum hM x₀ γ τ 1 ^ 2 +
    angularMomentum hM x₀ γ τ 2 ^ 2

/-- The square of the angular momentum is nonnegative. -/
theorem angularMomentumSq_nonneg (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) :
    0 ≤ angularMomentumSq hM x₀ γ τ := by
  unfold angularMomentumSq
  positivity

/-- Along a geodesic, given on a convex set of parameters, `L²` is constant. -/
theorem angularMomentumSq_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) :
    angularMomentumSq hM x₀ γ τ₁ = angularMomentumSq hM x₀ γ τ₂ := by
  unfold angularMomentumSq
  rw [angularMomentum_eq hM x₀ hγ hs h₁ h₂ 0, angularMomentum_eq hM x₀ hγ hs h₁ h₂ 1,
    angularMomentum_eq hM x₀ hγ hs h₁ h₂ 2]

/-- In co-ordinates `L² = r⁴ (θ̇² + sin²θ φ̇²)`. -/
theorem angularMomentumSq_eq_coord (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    angularMomentumSq hM x₀ γ τ =
      (γ τ : MinkowskiModel 3) 1 ^ 4 * (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2) :=
  sum_angularMomentum_sq hM x₀ hγ

/-! ### The normalization of the velocity -/

/-- The normalization `κ = −g(γ̇, γ̇)` of the velocity of a curve: `κ = 1` for a body
parametrized by its proper time and `κ = 0` for light. -/
def normalization (hM : 0 ≤ M) (γ : ℝ → domain M) (τ : ℝ) : ℝ :=
  -(metric hM).toLorentzMetric.form (γ τ) (curveVelocity γ τ) (curveVelocity γ τ)

/-- Along a geodesic, given on a convex set of parameters, `κ = −g(γ̇, γ̇)` is constant. -/
theorem normalization_eq (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) : normalization hM γ τ₁ = normalization hM γ τ₂ := by
  unfold normalization
  rw [hγ.metric_velocity_eq hs h₁ h₂]

/-- In co-ordinates
`g(γ̇, γ̇) = −(1 − 2M/r) ṫ² + ṙ²/(1 − 2M/r) + r² θ̇² + r² sin²θ φ̇²`. -/
theorem form_curveVelocity_eq_coord (hM : 0 ≤ M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    (metric hM).toLorentzMetric.form (γ τ) (curveVelocity γ τ) (curveVelocity γ τ) =
      -(1 - 2 * M / (γ τ : MinkowskiModel 3) 1) *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 ^ 2 +
        deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 /
          (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) +
        (γ τ : MinkowskiModel 3) 1 ^ 2 * deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        (γ τ : MinkowskiModel 3) 1 ^ 2 * Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2 := by
  have h0 := (radius_pos_of_mem_domain hM (γ τ).property).ne'
  have h1 := (sub_pos_of_mem_domain (γ τ).property).ne'
  rw [(metric hM).form_curveVelocity hγ, coefficient_eq_diagonal]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagonalCoefficients]
  field_simp
  ring

/-! ### The radial equation -/

/-- The radial equation at one parameter: `ṙ² = E² − (1 − 2M/r)(κ + L²/r²)`, with the energy
`E`, the normalization `κ` and `L = √(J₀² + J₁² + J₂²)` read at the same parameter. -/
theorem radial_sq_eq_of_differentiableAt (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {τ : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ ^ 2 - effectivePotential M (normalization hM γ τ)
        (Real.sqrt (angularMomentumSq hM x₀ γ τ)) ((γ τ : MinkowskiModel 3) 1) := by
  have h0 := (radius_pos_of_mem_domain hM (γ τ).property).ne'
  have hA := (lapse_pos_of_mem_domain hM (γ τ).property).ne'
  rw [effectivePotential, Real.sq_sqrt (angularMomentumSq_nonneg hM x₀ γ τ),
    angularMomentumSq_eq_coord hM x₀ hγ, energy_eq_coord hM x₀ hγ, normalization,
    form_curveVelocity_eq_coord hM hγ]
  set A := 1 - 2 * M / (γ τ : MinkowskiModel 3) 1
  field_simp
  ring

/-- **The radial equation** (Landau–Lifshitz, §101, (101.4)). Along a geodesic, given on a
convex set of parameters, `ṙ² = E² − V(r)` with the effective potential
`V(r) = (1 − 2M/r)(κ + L²/r²)`, where the energy `E`, the normalization `κ = −g(γ̇, γ̇)` and the
angular momentum `L = √(J₀² + J₁² + J₂²)` are the constants of the geodesic, read at any
parameter `τ₀`. -/
theorem radial_sq_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ₀ ^ 2 - effectivePotential M (normalization hM γ τ₀)
        (Real.sqrt (angularMomentumSq hM x₀ γ τ₀)) ((γ τ : MinkowskiModel 3) 1) := by
  rw [energy_eq hM x₀ hγ hs h₀ hτ, normalization_eq hM hγ hs h₀ hτ,
    angularMomentumSq_eq hM x₀ hγ hs h₀ hτ]
  exact radial_sq_eq_of_differentiableAt hM x₀ (differentiableAt_of_isGeodesicOn hγ hτ)

/-! ### The angle swept in the plane of the motion -/

/-- The angle `∫_{τ₀}^{τ} √(θ̇² + sin²θ φ̇²) dσ` swept by the radius in the plane of the motion. -/
def sweptAngle (γ : ℝ → domain M) (τ₀ τ : ℝ) : ℝ :=
  ∫ σ in τ₀..τ, Real.sqrt (deriv (fun t => (γ t : MinkowskiModel 3)) σ 2 ^ 2 +
    Real.sin ((γ σ : MinkowskiModel 3) 2) ^ 2 * deriv (fun t => (γ t : MinkowskiModel 3)) σ 3 ^ 2)

private theorem continuousOn_sweptIntegrand {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) :
    ContinuousOn (fun σ => Real.sqrt (deriv (fun t => (γ t : MinkowskiModel 3)) σ 2 ^ 2 +
      Real.sin ((γ σ : MinkowskiModel 3) 2) ^ 2 *
        deriv (fun t => (γ t : MinkowskiModel 3)) σ 3 ^ 2)) s := by
  have hd := continuousOn_deriv_of_isGeodesicOn hγ hso
  have hc := (contDiffOn_of_isGeodesicOn hγ).continuousOn
  have h2 : ContinuousOn (fun σ => deriv (fun t => (γ t : MinkowskiModel 3)) σ 2) s :=
    (continuous_apply 2).comp_continuousOn hd
  have h3 : ContinuousOn (fun σ => deriv (fun t => (γ t : MinkowskiModel 3)) σ 3) s :=
    (continuous_apply 3).comp_continuousOn hd
  have hθ : ContinuousOn (fun σ => Real.sin ((γ σ : MinkowskiModel 3) 2)) s :=
    Real.continuous_sin.comp_continuousOn ((continuous_apply 2).comp_continuousOn hc)
  exact ((h2.pow 2).add ((hθ.pow 2).mul (h3.pow 2))).sqrt

/-- The angle swept in the plane of the motion has the derivative `√(θ̇² + sin²θ φ̇²)` at every
parameter of a geodesic given on an open convex set. -/
theorem hasDerivAt_sweptAngle (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    HasDerivAt (sweptAngle γ τ₀)
      (Real.sqrt (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2)) τ := by
  have hf := continuousOn_sweptIntegrand hγ hso
  exact intervalIntegral.integral_hasDerivAt_right
    ((hf.mono (hsc.ordConnected.uIcc_subset h₀ hτ)).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter hso τ hτ) (hf.continuousAt (hso.mem_nhds hτ))

/-- `√(θ̇² + sin²θ φ̇²) = L/r²` with `L = √(J₀² + J₁² + J₂²)`. -/
theorem sqrt_angular_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    Real.sqrt (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2) =
      Real.sqrt (angularMomentumSq hM x₀ γ τ) / (γ τ : MinkowskiModel 3) 1 ^ 2 := by
  have h0 := radius_pos_of_mem_domain hM (γ τ).property
  rw [angularMomentumSq_eq_coord hM x₀ hγ, Real.sqrt_mul (by positivity),
    show (γ τ : MinkowskiModel 3) 1 ^ 4 = ((γ τ : MinkowskiModel 3) 1 ^ 2) ^ 2 by ring,
    Real.sqrt_sq (by positivity), mul_div_cancel_left₀ _ (by positivity)]

/-- **The angular equation** (Landau–Lifshitz, §101, (101.4)). Along a geodesic, given on an open
convex set of parameters, the angle swept in the plane of the motion has the derivative `L/r²`,
with the constant angular momentum `L = √(J₀² + J₁² + J₂²)` read at `τ₀`. -/
theorem hasDerivAt_sweptAngle_eq_div (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s)
    (hsc : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    HasDerivAt (sweptAngle γ τ₀)
      (Real.sqrt (angularMomentumSq hM x₀ γ τ₀) / (γ τ : MinkowskiModel 3) 1 ^ 2) τ := by
  rw [angularMomentumSq_eq hM x₀ hγ hsc h₀ hτ,
    ← sqrt_angular_eq hM x₀ (differentiableAt_of_isGeodesicOn hγ hτ)]
  exact hasDerivAt_sweptAngle hM hγ hso hsc h₀ hτ

/-- **The equatorial motion.** For a geodesic, given on an open convex set of parameters, that
stays in the equatorial plane `θ = π/2` with `φ̇ ≥ 0`, the swept angle is the increase
`φ(τ) − φ(τ₀)` of the co-ordinate `φ`. -/
theorem sweptAngle_equatorial (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    (hθ : ∀ σ ∈ s, (γ σ : MinkowskiModel 3) 2 = Real.pi / 2)
    (hφ : ∀ σ ∈ s, 0 ≤ deriv (fun t => (γ t : MinkowskiModel 3)) σ 3) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    sweptAngle γ τ₀ τ = (γ τ : MinkowskiModel 3) 3 - (γ τ₀ : MinkowskiModel 3) 3 := by
  have hsub : uIcc τ₀ τ ⊆ s := hsc.ordConnected.uIcc_subset h₀ hτ
  have hpi (σ : ℝ) (hσ : σ ∈ s) (k : Fin 4) :
      HasDerivAt (fun t => (γ t : MinkowskiModel 3) k)
        (deriv (fun t => (γ t : MinkowskiModel 3)) σ k) σ :=
    hasDerivAt_pi.mp (differentiableAt_of_isGeodesicOn hγ hσ).hasDerivAt k
  have hθd (σ : ℝ) (hσ : σ ∈ s) : deriv (fun t => (γ t : MinkowskiModel 3)) σ 2 = 0 := by
    have heq : (fun t => (γ t : MinkowskiModel 3) 2) =ᶠ[𝓝 σ] fun _ => Real.pi / 2 :=
      eventually_of_mem (hso.mem_nhds hσ) hθ
    exact (hpi σ hσ 2).unique ((hasDerivAt_const σ (Real.pi / 2)).congr_of_eventuallyEq heq)
  unfold sweptAngle
  rw [intervalIntegral.integral_congr (g := fun σ => deriv (fun t => (γ t : MinkowskiModel 3)) σ 3)
    fun σ hσ => ?_]
  · have h3 : ContinuousOn (fun σ => deriv (fun t => (γ t : MinkowskiModel 3)) σ 3) s :=
      (continuous_apply 3).comp_continuousOn (continuousOn_deriv_of_isGeodesicOn hγ hso)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ hσ => hpi σ (hsub hσ) 3)
      ((h3.mono hsub).intervalIntegrable)
  · simp only
    rw [hθd σ (hsub hσ), hθ σ (hsub hσ), Real.sin_pi_div_two]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow, one_mul,
      zero_add]
    exact Real.sqrt_sq (hφ σ (hsub hσ))

/-! ### Regression: the circular orbits -/

private theorem hasDerivAt_circularOrbit (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (τ : ℝ) :
    HasDerivAt (fun t => (circularOrbit hM hR t : MinkowskiModel 3))
      ![circularTimeRate M R, 0, 0, circularAngleRate M R] τ := by
  have he : (fun t => (circularOrbit hM hR t : MinkowskiModel 3)) = fun t =>
      ![0, R, Real.pi / 2, 0] + t • ![circularTimeRate M R, 0, 0, circularAngleRate M R] :=
    funext (circularOrbit_eq_line hM hR)
  rw [he]
  simpa using ((hasDerivAt_id τ).smul_const
    (![circularTimeRate M R, 0, 0, circularAngleRate M R] : MinkowskiModel 3)).const_add
    (![0, R, Real.pi / 2, 0] : MinkowskiModel 3)

/-- The energy of the circular orbit is `E = (1 − 2M/R) α`. -/
theorem energy_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    energy hM x₀ (circularOrbit hM hR) τ = (1 - 2 * M / R) * circularTimeRate M R := by
  rw [energy, pairing_time_circular hM hR x₀ τ, neg_neg]

/-- The circular orbit is parametrized by its proper time: `κ = 1`. -/
theorem normalization_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (τ : ℝ) :
    normalization hM (circularOrbit hM hR) τ = 1 := by
  rw [normalization, form_curveVelocity_circular hM hR τ, neg_neg]

/-- The angular momentum of the circular orbit is `L = √(J₀² + J₁² + J₂²) = R² Ω`. -/
theorem sqrt_angularMomentumSq_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R)
    (x₀ : domain M) (τ : ℝ) :
    Real.sqrt (angularMomentumSq hM x₀ (circularOrbit hM hR) τ) =
      R ^ 2 * circularAngleRate M R := by
  have hd := hasDerivAt_circularOrbit hM hR τ
  rw [angularMomentumSq_eq_coord hM x₀ hd.differentiableAt, hd.deriv]
  have hΩ : 0 ≤ circularAngleRate M R := by
    unfold circularAngleRate circularTimeRate
    positivity
  have h2 : (circularOrbit hM hR τ : MinkowskiModel 3) 2 = Real.pi / 2 := rfl
  have h1 : (circularOrbit hM hR τ : MinkowskiModel 3) 1 = R := rfl
  rw [h1, h2, Real.sin_pi_div_two]
  simp only [Matrix.cons_val, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    one_pow, one_mul, zero_add]
  rw [show R ^ 4 * circularAngleRate M R ^ 2 = (R ^ 2 * circularAngleRate M R) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- **A regression instance of the radial equation.** Along the circular orbit of radius
`R > 3M` (a geodesic on the whole line), `ṙ = 0`, and `radial_sq_eq` reduces to
`E² = V(R) = (1 − 2M/R)(1 + L²/R²)` with `L = √(J₀² + J₁² + J₂²)`. -/
theorem radial_sq_eq_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M)
    (τ : ℝ) :
    deriv (fun t => (circularOrbit hM hR t : MinkowskiModel 3)) τ 1 = 0 ∧
      energy hM x₀ (circularOrbit hM hR) τ ^ 2 = effectivePotential M 1
        (Real.sqrt (angularMomentumSq hM x₀ (circularOrbit hM hR) τ)) R := by
  have hd : deriv (fun t => (circularOrbit hM hR t : MinkowskiModel 3)) τ 1 = 0 := by
    rw [(hasDerivAt_circularOrbit hM hR τ).deriv]
    rfl
  refine ⟨hd, ?_⟩
  have h := radial_sq_eq hM x₀ (isGeodesicOn_circular hM hR) convex_univ (mem_univ τ)
    (mem_univ τ)
  rw [hd, normalization_circular hM hR τ] at h
  have h1 : (circularOrbit hM hR τ : MinkowskiModel 3) 1 = R := rfl
  rw [h1] at h
  linarith

/- The regression agrees with `effectivePotential_circular` of `SchwarzschildCircular`: with
`E = (1 − 2M/R) α` and `L = R² Ω`, the reduced radial equation is that identity. -/
example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    effectivePotential M 1 (R ^ 2 * circularAngleRate M R) R =
      ((1 - 2 * M / R) * circularTimeRate M R) ^ 2 := by
  have h := (radial_sq_eq_circular hM hR x₀ τ).2
  rw [energy_circular, sqrt_angularMomentumSq_circular] at h
  exact h.symm

/- With `circularEnergy_sq`, the energy of the circular orbit satisfies
`E² = (1 − 2M/R)²/(1 − 3M/R)`. -/
example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    energy hM x₀ (circularOrbit hM hR) τ ^ 2 = (1 - 2 * M / R) ^ 2 / (1 - 3 * M / R) := by
  rw [energy_circular, circularEnergy_sq hM hR]

/- The swept angle of the circular orbit is `Ω (τ − τ₀)`, and its rate `L/R²` is `Ω`: the
hypotheses of `sweptAngle_equatorial` and `hasDerivAt_sweptAngle_eq_div` are satisfiable. -/
example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ₀ τ : ℝ) :
    sweptAngle (circularOrbit hM hR) τ₀ τ = circularAngleRate M R * (τ - τ₀) ∧
      HasDerivAt (sweptAngle (circularOrbit hM hR) τ₀) (circularAngleRate M R) τ := by
  have hR0 : 0 < R := by linarith
  have hΩ : 0 ≤ circularAngleRate M R := by
    unfold circularAngleRate circularTimeRate
    positivity
  have hd (σ : ℝ) := (hasDerivAt_circularOrbit hM hR σ).deriv
  refine ⟨?_, ?_⟩
  · rw [sweptAngle_equatorial hM (isGeodesicOn_circular hM hR) isOpen_univ convex_univ
      (fun σ _ => rfl) (fun σ _ => by rw [hd σ]; exact hΩ) (mem_univ τ₀) (mem_univ τ)]
    change circularAngleRate M R * τ - circularAngleRate M R * τ₀ = _
    ring
  · have h := hasDerivAt_sweptAngle_eq_div hM x₀ (isGeodesicOn_circular hM hR) isOpen_univ
      convex_univ (mem_univ τ₀) (mem_univ τ)
    rw [sqrt_angularMomentumSq_circular] at h
    convert h using 1
    change _ = R ^ 2 * circularAngleRate M R / R ^ 2
    field_simp

/- The angular momentum `L` of the circular orbit is the pairing `g(∂_φ, γ̇)` of
`pairing_angle_circular`. -/
example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    Real.sqrt (angularMomentumSq hM x₀ (circularOrbit hM hR) τ) =
      (metric hM).toLorentzMetric.form (circularOrbit hM hR τ)
        (chartField (physicalChart x₀) (Pi.single 3 1) (circularOrbit hM hR τ))
        (curveVelocity (circularOrbit hM hR) τ) := by
  rw [sqrt_angularMomentumSq_circular, pairing_angle_circular]

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
