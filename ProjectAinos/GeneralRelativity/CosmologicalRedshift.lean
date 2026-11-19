/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.FLRW
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
public import ProjectAinos.SmoothGeometry.Lorentzian.Killing
public import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The red shift in the isotropic model

Landau–Lifshitz, §114, for the isotropic metric `ds² = −N(t)² dt² + a(t)² ψ_k⁻² dx²` of
`FLRW.metric`, every curvature `k` and `c = 1`. The comoving observers move along
`∂_t = chartField (physicalChart x₀) (Pi.single 0 1)`, and measure the frequency
`ω = −g(u, γ̇)`, `u = ∂_t/N`, of a ray `γ` (`LorentzMetric.observedFrequency`); `ẋ⁰` is the
time component of the co-ordinate velocity of `γ`.

* `comoving_isGeodesicOn`: in the cosmic time `N = 1` the comoving observers `x = const` are
  geodesics in their proper time (`CoordinateMetric.IsSynchronous.isGeodesicOn_timeLine`); those
  of de Sitter space are an instance (`isGeodesicOn_deSitterObserver`).
* `killingNorm_timeField`, `observedFrequency_eq`: the norm of `∂_t` is `N`, and the measured
  frequency is `ω = N ẋ⁰`; in the cosmic time `ω = ṫ` (`observedFrequency_eq_timeVelocity`).
* `geodesic_time`: the time component of the geodesic equation,
  `ẍ⁰ + (Ṅ/N)(ẋ⁰)² + aȧ/(N²ψ²) Σ (ẋ^α)² = 0` (from `Γ⁰₀₀ = Ṅ/N`, `Γ⁰_{αβ} = aȧ/(N²ψ²) δ_{αβ}`);
  `form_velocity`: `g(γ̇, γ̇) = −N²(ẋ⁰)² + a²/ψ² Σ (ẋ^α)²`.
* `hasDerivAt_scale_mul_frequency`, `scale_mul_lapse_mul_velocity_eq`, `scale_mul_frequency_eq`:
  **along a null geodesic on a convex set of parameters `a ω` is constant**, for every lapse:
  `d(aNẋ⁰)/dλ = −(ȧ/N) g(γ̇, γ̇) = 0`, and the ray is null at all parameters once it is null at
  one. In the cosmic time `a(t(λ)) ṫ(λ)` is constant (`scale_mul_timeVelocity_eq`).
* `redshift`, `redshift_eq`: **the red shift** `1 + z = ω(λ₁)/ω(λ₂) = a(t(λ₂))/a(t(λ₁))` of a ray
  emitted at `λ₁` and received at `λ₂` (Landau–Lifshitz, (114.2));
  `observedFrequency_ne_zero`: a null ray with a nonzero velocity has `ω ≠ 0`.
* The instance: in de Sitter space in the flat slicing (`Data.deSitter`, `a = eᵗ`, `k = 0`) the
  curve `λ ↦ (log λ, c − 1/λ, 0, 0)` on `λ > 0` is a null geodesic (`deSitterRay`,
  `isGeodesicOn_deSitterRay`, `form_deSitterRay_velocity`) with `a(t(λ)) = λ` and `ω = 1/λ`
  (`scale_deSitterRay`, `observedFrequency_deSitterRay`, `scale_mul_frequency_deSitterRay`), and
  its red shift is `1 + z = λ₂/λ₁` (`redshift_deSitterRay`).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.CosmologicalRedshift

open SmoothGeometry CoordinateMetric LorentzMetric FLRW

local notation "E" => MinkowskiModel 3

variable {D : Data}

/-! ### The comoving observers -/

/-- **The comoving observers are free** (Landau–Lifshitz, §§97, 114): with `N = 1`, a curve of
the domain that is at rest in the co-ordinates on an open set of times, `x(t) = z₀ + t e₀`, is a
geodesic, its parameter is the proper time and it is orthogonal to the slices `t = const`. -/
theorem comoving_isGeodesicOn (hN : ∀ t ∈ D.I, D.N t = 1) {γ : ℝ → domain D} {s : Set ℝ}
    (hs : IsOpen s) {z₀ : E} (hγ : ∀ t ∈ s, (γ t : E) = z₀ + t • Pi.single 0 1) :
    (metric D).toLorentzMetric.IsGeodesicOn s γ ∧ ∀ t ∈ s,
      (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = -1 ∧
        ∀ α : Fin 3,
          (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (Pi.single α.succ 1) = 0 :=
  (isSynchronous hN).isGeodesicOn_timeLine hs hγ

/-- **An instance of `comoving_isGeodesicOn`**: the comoving observers `t ↦ z₀ + t e₀` of de
Sitter space in the flat slicing are geodesics for all times. -/
theorem isGeodesicOn_deSitterObserver (z₀ : E) :
    (metric Data.deSitter).toLorentzMetric.IsGeodesicOn univ
      (fun t => (⟨z₀ + t • Pi.single 0 1, mem_domain_deSitter _⟩ : domain Data.deSitter)) :=
  (comoving_isGeodesicOn (fun _ _ => rfl) isOpen_univ fun _ _ => rfl).1

/-! ### The frequency measured by the comoving observers -/

/-- `g(∂_t, w) = −N² w⁰`. -/
theorem form_timeField (x₀ y : domain D) (w : TangentSpace 𝓘(ℝ, E) y) :
    (metric D).toLorentzMetric.form y (chartField (physicalChart x₀) (Pi.single 0 1) y) w =
      -(D.N ((y : E) 0) ^ 2) * (w : E) 0 := by
  rw [toLorentzMetric_form, physicalChart_chartField]
  refine ((metric D).form_apply y (Pi.single 0 1) (w : E)).trans ?_
  rw [coefficient_metric]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, coefficients]

/-- **The norm of `∂_t` is the lapse**: `√(−g(∂_t, ∂_t)) = N`. -/
theorem killingNorm_timeField (x₀ y : domain D) :
    (metric D).toLorentzMetric.killingNorm (chartField (physicalChart x₀) (Pi.single 0 1)) y =
      D.N ((y : E) 0) := by
  rw [killingNorm, form_timeField, physicalChart_chartField]
  simpa using Real.sqrt_sq (N_pos_of_mem y.property).le

/-- **The frequency measured by the comoving observers** is `ω = −g(∂_t/N, γ̇) = N ẋ⁰`. -/
theorem observedFrequency_eq (x₀ : domain D) {γ : ℝ → domain D} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t) :
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
        γ t =
      D.N ((γ t : E) 0) * deriv (fun t => (γ t : E)) t 0 := by
  have hN := (N_pos_of_mem (γ t).property).ne'
  rw [observedFrequency, stationaryVelocity, map_smul, _root_.smul_apply,
    form_timeField, killingNorm_timeField,
    curveVelocity_val (mdifferentiableAt_iff_differentiableAt_val.mpr hγ), smul_eq_mul]
  field_simp

/-- In the cosmic time `N = 1` the measured frequency is `ω = ṫ`. -/
theorem observedFrequency_eq_timeVelocity (hN : ∀ t ∈ D.I, D.N t = 1) (x₀ : domain D)
    {γ : ℝ → domain D} {t : ℝ} (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t) :
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
        γ t =
      deriv (fun t => (γ t : E)) t 0 := by
  rw [observedFrequency_eq x₀ hγ, hN _ (time_mem (γ t).property), one_mul]

/-! ### The time component of the geodesic equation -/

/-- The quadratic term of the time component of the geodesic equation:
`Γ⁰_{ij} vⁱ vʲ = (Ṅ/N)(v⁰)² + aȧ/(N²ψ²) Σ (v^α)²`. -/
theorem sum_christoffel_zero (x v : E) :
    ∑ i, ∑ j, FLRW.christoffel D x 0 i j * v i * v j =
      gammaLapse D x * v 0 ^ 2 + gammaSpatial D x * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by
  simp [SphericalAnsatz.sum_four, FLRW.christoffel]
  ring

/-- **The time component of the geodesic equation** (Landau–Lifshitz, (87.3)) in the isotropic
metric: `ẍ⁰ + (Ṅ/N)(ẋ⁰)² + aȧ/(N²ψ²) Σ (ẋ^α)² = 0`. -/
theorem geodesic_time {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) {t : ℝ} (ht : t ∈ s) :
    deriv (deriv (fun t => (γ t : E))) t 0 +
        gammaLapse D (γ t) * deriv (fun t => (γ t : E)) t 0 ^ 2 +
        gammaSpatial D (γ t) * (deriv (fun t => (γ t : E)) t 1 ^ 2 +
          deriv (fun t => (γ t : E)) t 2 ^ 2 + deriv (fun t => (γ t : E)) t 3 ^ 2) = 0 := by
  have h := ((metric D).covariantAlong_curveVelocity_eq_zero_iff
    (contDiffAt_val (hγ t ht).1)).mp (hγ t ht).2 0
  simp only [christoffelOf_eq (γ t).property] at h
  rw [sum_christoffel_zero (γ t : E) (deriv (fun t => (γ t : E)) t)] at h
  linear_combination h

/-- **The squared velocity of a curve**: `g(γ̇, γ̇) = −N²(ẋ⁰)² + a²/ψ² Σ (ẋ^α)²`. -/
theorem form_velocity {γ : ℝ → domain D} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t) :
    (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
      -(D.N ((γ t : E) 0) ^ 2) * deriv (fun t => (γ t : E)) t 0 ^ 2 +
        D.a ((γ t : E) 0) ^ 2 / psi D.k (γ t) ^ 2 * (deriv (fun t => (γ t : E)) t 1 ^ 2 +
          deriv (fun t => (γ t : E)) t 2 ^ 2 + deriv (fun t => (γ t : E)) t 3 ^ 2) := by
  rw [(metric D).form_curveVelocity hγ, coefficient_metric]
  simp [SphericalAnsatz.sum_four, Matrix.diagonal_apply, coefficients]
  ring

/-! ### The conservation of `a ω` along a light ray -/

/-- **Along a null geodesic `aNẋ⁰` has zero derivative**: `d(aNẋ⁰)/dλ = −(ȧ/N) g(γ̇, γ̇)`, by
the time component of the geodesic equation. -/
theorem hasDerivAt_scale_mul_frequency {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) {t : ℝ} (ht : t ∈ s)
    (hnull : (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0) :
    HasDerivAt (fun r => D.a ((γ r : E) 0) *
      (D.N ((γ r : E) 0) * deriv (fun t => (γ t : E)) r 0)) 0 t := by
  have hc : ContDiffAt ℝ 2 (fun t => (γ t : E)) t := contDiffAt_val (hγ t ht).1
  have hd : HasDerivAt (fun t => (γ t : E)) (deriv (fun t => (γ t : E)) t) t :=
    (hc.differentiableAt (by norm_num)).hasDerivAt
  have hv : ContDiffAt ℝ 1 (deriv (fun t => (γ t : E))) t := hc.derivWithin (by norm_num)
  have hdd : HasDerivAt (deriv (fun t => (γ t : E))) (deriv (deriv (fun t => (γ t : E))) t) t :=
    (hv.differentiableAt (by norm_num)).hasDerivAt
  have hx0 := hasDerivAt_pi.mp hd 0
  have hv0 := hasDerivAt_pi.mp hdd 0
  have hT := time_mem (γ t).property
  have ha' : HasDerivAt (fun r => D.a ((γ r : E) 0))
      (deriv D.a ((γ t : E) 0) * deriv (fun t => (γ t : E)) t 0) t :=
    (hasDerivAt_a hT).comp t hx0
  have hN' : HasDerivAt (fun r => D.N ((γ r : E) 0))
      (deriv D.N ((γ t : E) 0) * deriv (fun t => (γ t : E)) t 0) t :=
    (hasDerivAt_N hT).comp t hx0
  have hv0' : HasDerivAt (fun r => deriv (fun t => (γ t : E)) r 0)
      (deriv (deriv (fun t => (γ t : E))) t 0) t := hv0
  have hprod := ha'.fun_mul (hN'.fun_mul hv0')
  refine hprod.congr_deriv ?_
  have hgeo := geodesic_time hγ ht
  rw [form_velocity hd.differentiableAt] at hnull
  have hN := (N_pos_of_mem (γ t).property).ne'
  have hψ := (psi_pos (γ t).property).ne'
  simp only [gammaLapse, gammaSpatial] at hgeo
  linear_combination (norm := skip) (D.a ((γ t : E) 0) * D.N ((γ t : E) 0)) * hgeo -
    (deriv D.a ((γ t : E) 0) / D.N ((γ t : E) 0)) * hnull
  field_simp
  ring

/-- `a(t(λ)) N(t(λ)) ẋ⁰(λ)` is constant along a null geodesic on a convex set of parameters; the
ray is null at one parameter, hence at all. -/
theorem scale_mul_lapse_mul_velocity_eq {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull :
      (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    D.a ((γ t₁ : E) 0) * (D.N ((γ t₁ : E) 0) * deriv (fun t => (γ t : E)) t₁ 0) =
      D.a ((γ t₂ : E) 0) * (D.N ((γ t₂ : E) 0) * deriv (fun t => (γ t : E)) t₂ 0) := by
  let f : ℝ → ℝ := fun r =>
    D.a ((γ r : E) 0) * (D.N ((γ r : E) 0) * deriv (fun t => (γ t : E)) r 0)
  have hd (t : ℝ) (ht : t ∈ s) : HasDerivAt f 0 t :=
    hasDerivAt_scale_mul_frequency hγ ht ((hγ.null_norm_iff hs ht₀ ht).mp hnull)
  apply hs.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (f := f)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) _ ht₁ ht₂
  intro t ht
  by_cases hu : UniqueDiffWithinAt ℝ s t
  · have hf : HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) t := by
      rw [hasFDerivAt_iff_hasDerivAt]
      exact hd t ht
    exact hf.hasFDerivWithinAt.fderivWithin hu
  · exact fderivWithin_zero_of_not_uniqueDiffWithinAt hu

/-- The co-ordinates of a geodesic are differentiable on its set of parameters. -/
theorem differentiableAt_of_isGeodesicOn {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) {t : ℝ} (ht : t ∈ s) :
    DifferentiableAt ℝ (fun t => (γ t : E)) t :=
  (contDiffAt_val (hγ t ht).1).differentiableAt (by norm_num)

/-- **The frequency of a light ray decreases as the universe expands** (Landau–Lifshitz, §114):
along a null geodesic on a convex set of parameters, the frequency `ω` measured by the comoving
observers satisfies `a(t(λ₁)) ω(λ₁) = a(t(λ₂)) ω(λ₂)`. -/
theorem scale_mul_frequency_eq (x₀ : domain D) {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull :
      (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    D.a ((γ t₁ : E) 0) * (metric D).toLorentzMetric.observedFrequency
        (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₁ =
      D.a ((γ t₂ : E) 0) * (metric D).toLorentzMetric.observedFrequency
        (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₂ := by
  rw [observedFrequency_eq x₀ (differentiableAt_of_isGeodesicOn hγ ht₁),
    observedFrequency_eq x₀ (differentiableAt_of_isGeodesicOn hγ ht₂)]
  exact scale_mul_lapse_mul_velocity_eq hγ hs ht₀ hnull ht₁ ht₂

/-- **In the cosmic time `a(t(λ)) ṫ(λ)` is constant** along a null geodesic on a convex set of
parameters. -/
theorem scale_mul_timeVelocity_eq (hN : ∀ t ∈ D.I, D.N t = 1) {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull :
      (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s) :
    D.a ((γ t₁ : E) 0) * deriv (fun t => (γ t : E)) t₁ 0 =
      D.a ((γ t₂ : E) 0) * deriv (fun t => (γ t : E)) t₂ 0 := by
  have h := scale_mul_lapse_mul_velocity_eq hγ hs ht₀ hnull ht₁ ht₂
  rwa [hN _ (time_mem (γ t₁).property), hN _ (time_mem (γ t₂).property), one_mul,
    one_mul] at h

/-! ### The red shift -/

variable (D) in
/-- **The red shift** `z = ω(λ₁)/ω(λ₂) − 1` of a ray `γ` emitted at `γ(λ₁)` and received at
`γ(λ₂)`, with the frequencies measured by the comoving observers. -/
def redshift (x₀ : domain D) (γ : ℝ → domain D) (t₁ t₂ : ℝ) : ℝ :=
  (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
      γ t₁ /
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
      γ t₂ - 1

/-- **The red shift of the isotropic model** (Landau–Lifshitz, (114.2)): for a ray along a null
geodesic on a convex set of parameters, emitted at `λ₁` and received at `λ₂` with `ω(λ₂) ≠ 0`,
`1 + z = a(t(λ₂))/a(t(λ₁))`. -/
theorem redshift_eq (x₀ : domain D) {γ : ℝ → domain D} {s : Set ℝ}
    (hγ : (metric D).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnull :
      (metric D).toLorentzMetric.form (γ t₀) (curveVelocity γ t₀) (curveVelocity γ t₀) = 0)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ s) (ht₂ : t₂ ∈ s)
    (hω : (metric D).toLorentzMetric.observedFrequency
      (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₂ ≠ 0) :
    1 + redshift D x₀ γ t₁ t₂ = D.a ((γ t₂ : E) 0) / D.a ((γ t₁ : E) 0) := by
  have h := scale_mul_frequency_eq x₀ hγ hs ht₀ hnull ht₁ ht₂
  have ha := (a_pos_of_mem (γ t₁).property).ne'
  have he : 1 + redshift D x₀ γ t₁ t₂ =
      (metric D).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₁ /
        (metric D).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) γ t₂ := by
    unfold redshift
    ring
  rw [he, div_eq_div_iff hω ha]
  linear_combination h

/-- **A light ray with a nonzero velocity has a nonzero frequency**: if `g(γ̇, γ̇) = 0` and
`γ̇ ≠ 0`, then `ω = Nẋ⁰ ≠ 0`. -/
theorem observedFrequency_ne_zero (x₀ : domain D) {γ : ℝ → domain D} {t : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : E)) t)
    (hnull : (metric D).toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0)
    (hv : curveVelocity (d := 3) γ t ≠ 0) :
    (metric D).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
      γ t ≠ 0 := by
  rw [observedFrequency_eq x₀ hγ]
  intro h0
  have hv0 : deriv (fun t => (γ t : E)) t 0 = 0 :=
    (mul_eq_zero.mp h0).resolve_left (N_pos_of_mem (γ t).property).ne'
  rw [form_velocity hγ, hv0] at hnull
  have hc : 0 < D.a ((γ t : E) 0) ^ 2 / psi D.k (γ t) ^ 2 :=
    div_pos (pow_pos (a_pos_of_mem (γ t).property) 2) (pow_pos (psi_pos (γ t).property) 2)
  have hS : deriv (fun t => (γ t : E)) t 1 ^ 2 + deriv (fun t => (γ t : E)) t 2 ^ 2 +
      deriv (fun t => (γ t : E)) t 3 ^ 2 = 0 := by
    have h : D.a ((γ t : E) 0) ^ 2 / psi D.k (γ t) ^ 2 * (deriv (fun t => (γ t : E)) t 1 ^ 2 +
        deriv (fun t => (γ t : E)) t 2 ^ 2 + deriv (fun t => (γ t : E)) t 3 ^ 2) = 0 := by
      linear_combination hnull
    exact (mul_eq_zero.mp h).resolve_left hc.ne'
  have h1 := sq_nonneg (deriv (fun t => (γ t : E)) t 1)
  have h2 := sq_nonneg (deriv (fun t => (γ t : E)) t 2)
  have h3 := sq_nonneg (deriv (fun t => (γ t : E)) t 3)
  have e1 : deriv (fun t => (γ t : E)) t 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
  have e2 : deriv (fun t => (γ t : E)) t 2 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
  have e3 : deriv (fun t => (γ t : E)) t 3 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by linarith)
  have hzero : deriv (fun t => (γ t : E)) t = 0 := by
    funext i
    fin_cases i <;> simp [hv0, e1, e2, e3]
  exact hv ((curveVelocity_val (mdifferentiableAt_iff_differentiableAt_val.mpr hγ)).trans hzero)

/-! ### Regression: a light ray in de Sitter space -/

/-- **A radial light ray of de Sitter space** in the flat slicing (`Data.deSitter`, `a = eᵗ`):
`λ ↦ (log λ, c − 1/λ, 0, 0)`, a curve of the domain for every `λ`; it is a null geodesic on
`λ > 0` (`isGeodesicOn_deSitterRay`, `form_deSitterRay_velocity`). -/
def deSitterRay (c r : ℝ) : domain Data.deSitter :=
  ⟨![Real.log r, c - r⁻¹, 0, 0], mem_domain_deSitter _⟩

/-- The co-ordinates of the ray. -/
theorem deSitterRay_val (c r : ℝ) : (deSitterRay c r : E) = ![Real.log r, c - r⁻¹, 0, 0] := rfl

/-- The velocity of the ray is `(1/λ, 1/λ², 0, 0)` for `λ > 0`. -/
theorem hasDerivAt_deSitterRay (c : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => (deSitterRay c r : E)) ![r⁻¹, (r ^ 2)⁻¹, 0, 0] r := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · exact Real.hasDerivAt_log hr.ne'
  · exact ((hasDerivAt_inv hr.ne').const_sub c).congr_deriv (neg_neg _)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)

/-- The acceleration of the ray is `(−1/λ², −2/λ³, 0, 0)`. -/
theorem hasDerivAt_deSitterRayVelocity {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => (![r⁻¹, (r ^ 2)⁻¹, 0, 0] : E))
      ![-(r ^ 2)⁻¹, -(2 / r ^ 3), 0, 0] r := by
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  · show HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r
    exact hasDerivAt_inv hr
  · show HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-(2 / r ^ 3)) r
    refine ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).congr_deriv ?_
    push_cast
    field_simp
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)

/-- **The ray is a geodesic** of de Sitter space on `λ > 0`. -/
theorem isGeodesicOn_deSitterRay (c : ℝ) :
    (metric Data.deSitter).toLorentzMetric.IsGeodesicOn (Ioi 0) (deSitterRay c) := by
  have hc : ContDiffOn ℝ 2 (fun r => (deSitterRay c r : E)) (Ioi 0) := by
    refine contDiffOn_pi.mpr fun i => ?_
    fin_cases i
    · exact fun r hr => (Real.contDiffAt_log.mpr (ne_of_gt hr)).contDiffWithinAt
    · exact fun r hr =>
        (contDiffAt_const.sub (contDiffAt_inv (𝕜 := ℝ) (ne_of_gt hr))).contDiffWithinAt
    · exact contDiffOn_const
    · exact contDiffOn_const
  have hderiv (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      deriv (fun r => (deSitterRay c r : E)) r = ![r⁻¹, (r ^ 2)⁻¹, 0, 0] :=
    (hasDerivAt_deSitterRay c hr).deriv
  rw [(metric Data.deSitter).isGeodesicOn_iff isOpen_Ioi hc]
  intro r hr k
  have hr' : (0 : ℝ) < r := hr
  have hdd : deriv (deriv (fun r => (deSitterRay c r : E))) r =
      ![-(r ^ 2)⁻¹, -(2 / r ^ 3), 0, 0] := by
    have h : deriv (fun r => (deSitterRay c r : E)) =ᶠ[𝓝 r]
        fun r => (![r⁻¹, (r ^ 2)⁻¹, 0, 0] : E) :=
      eventually_of_mem (isOpen_Ioi.mem_nhds hr) hderiv
    rw [h.deriv_eq]
    exact (hasDerivAt_deSitterRayVelocity hr'.ne').deriv
  rw [hdd, hderiv r hr]
  simp only [christoffelOf_eq (deSitterRay c r).property, SphericalAnsatz.sum_four]
  fin_cases k <;>
    simp [FLRW.christoffel, gammaLapse, gammaSpatial, gammaExpansion, gammaConformal,
      Data.deSitter, psi, deSitterRay_val, Real.exp_log hr'] <;>
    field_simp <;>
    ring

/-- **The ray is null**: `g(γ̇, γ̇) = −1/λ² + λ² · 1/λ⁴ = 0` on `λ > 0`. -/
theorem form_deSitterRay_velocity (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (metric Data.deSitter).toLorentzMetric.form (deSitterRay c r)
      (curveVelocity (deSitterRay c) r) (curveVelocity (deSitterRay c) r) = 0 := by
  have hd := hasDerivAt_deSitterRay c hr
  rw [form_velocity hd.differentiableAt, hd.deriv]
  simp [Data.deSitter, psi, deSitterRay_val, Real.exp_log hr]
  field_simp
  ring

/-- Along the ray the scale factor is the parameter: `a(t(λ)) = e^{log λ} = λ`. -/
theorem scale_deSitterRay (c : ℝ) {r : ℝ} (hr : 0 < r) :
    Data.deSitter.a ((deSitterRay c r : E) 0) = r := by
  simp [Data.deSitter, deSitterRay_val, Real.exp_log hr]

/-- The comoving observers measure the frequency `ω = 1/λ` of the ray. -/
theorem observedFrequency_deSitterRay (x₀ : domain Data.deSitter) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (metric Data.deSitter).toLorentzMetric.observedFrequency
      (chartField (physicalChart x₀) (Pi.single 0 1)) (deSitterRay c) r = r⁻¹ := by
  have hd := hasDerivAt_deSitterRay c hr
  rw [observedFrequency_eq_timeVelocity (fun _ _ => rfl) x₀ hd.differentiableAt, hd.deriv]
  simp

/-- **The conserved product along the ray**: `a(t(λ)) ω(λ) = λ · 1/λ = 1`. -/
theorem scale_mul_frequency_deSitterRay (x₀ : domain Data.deSitter) (c : ℝ) {r : ℝ}
    (hr : 0 < r) :
    Data.deSitter.a ((deSitterRay c r : E) 0) *
        (metric Data.deSitter).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) (deSitterRay c) r = 1 := by
  rw [scale_deSitterRay c hr, observedFrequency_deSitterRay x₀ c hr, mul_inv_cancel₀ hr.ne']

/-- **An instance of `redshift_eq`**: the ray of de Sitter space emitted at `λ₁ > 0` and
received at `λ₂ > 0` has the red shift `1 + z = a(t(λ₂))/a(t(λ₁)) = λ₂/λ₁`. -/
theorem redshift_deSitterRay (x₀ : domain Data.deSitter) (c : ℝ) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) : 1 + redshift Data.deSitter x₀ (deSitterRay c) r₁ r₂ = r₂ / r₁ := by
  rw [redshift_eq x₀ (isGeodesicOn_deSitterRay c) (convex_Ioi 0) hr₁
      (form_deSitterRay_velocity c hr₁) hr₁ hr₂
      (by rw [observedFrequency_deSitterRay x₀ c hr₂]; exact inv_ne_zero hr₂.ne'),
    scale_deSitterRay c hr₁, scale_deSitterRay c hr₂]

end ProjectAinos.GeneralRelativity.CosmologicalRedshift
