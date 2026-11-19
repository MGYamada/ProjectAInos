/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildOrbit
public import ProjectAinos.GeneralRelativity.PerihelionIntegral
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The perihelion advance of a bound orbit

Let `γ` be a geodesic of the exterior Schwarzschild metric, parametrized by its proper time
(`κ = −g(γ̇, γ̇) = 1`), given on a convex set `s` of parameters, with the co-ordinates
`(t, r, θ, φ)`. Let `τ₁ < τ₂` be parameters in `s` with `ṙ(τ₁) = ṙ(τ₂) = 0` and `ṙ > 0` between
them: the body moves from the perihelion `r_min = r(τ₁)` to the aphelion `r_max = r(τ₂)`. With
the inverse radius `u = 1/r`, `u₁ = 1/r_min` and `u₂ = 1/r_max`, this file derives the angle
between the apsides and the advance of the perihelion of Landau–Lifshitz, §101, (101.6)–(101.7),
from the radial equation `radial_sq_eq` and the angular equation `sqrt_angular_eq`.

* `cubic_eq_factor_of_roots`: the cubic `P(u) = E² − (1 − 2Mu)(1 + L²u²)` with the two roots
  `u₁ ≠ u₂` is `L²(u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))`.
* `radial_sq_eq_inv`: the radial equation `ṙ² = P(1/r)` for `κ = 1`.
* `inverseRadius_lt_of_apsides`, `radial_sq_eq_factor`, `hasDerivAt_inv_radius`,
  `inv_radius_rate_neg`, `inv_radius_rate_sq_eq`: `u₂ < u₁`, `L > 0`, the factorized radial
  equation, `u̇ = −ṙ/r² < 0` and `u̇² = L²u⁴(u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))`.
* `simple_apsides_le`, `simple_apsides_lt`: the orbit forces the simple-apsides condition
  `2M(2u₁ + u₂) < 1`.
* `angle_between_apsides`: the angle swept from the perihelion to the aphelion is
  `Perihelion.apsidalAngle M u₂ u₁`, (101.6).
* `perihelion_advance_bounds`, `perihelion_advance_bounds_semiMajor`: the bounds of
  `apsidalAngle_bounds` and `apsidalAngle_bounds_semiMajor` for the geodesic, (101.7).
* `return_half`, `sweptAngle_between_perihelia`, `perihelion_advance_between_perihelia`: the
  angle swept on the way back from the aphelion to the next perihelion is the same integral, so
  the advance between successive perihelia is `2 · apsidalAngle − 2π` without any assumption of
  symmetry of the orbit.

The condition `2M(2u₁ + u₂) < 1` says that the third root `1/(2M) − u₁ − u₂` of `P` is not
`u₁`. It is derived, not assumed: the third root is not below `u₁` since `ṙ² ≥ 0` just after the
perihelion (`simple_apsides_le`), and it is not `u₁` since a double root cannot be reached in a
finite proper time, by Grönwall's inequality (`simple_apsides_lt`).

The existence of a non-circular bound geodesic is not constructed: the orbit is given. The
regression at the end of the file shows that the algebraic hypotheses of
`cubic_eq_factor_of_roots` hold for explicit constants with `M > 0` and `2M(2u₁ + u₂) = 1/4`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Real Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

variable {M : ℝ}

/-! ### The cubic of the radial equation -/

/-- **The factorization of the radial cubic** (Landau–Lifshitz, §101). If the cubic
`P(u) = E² − (1 − 2Mu)(1 + L²u²)` vanishes at two distinct points `u₁ ≠ u₂`, then
`P(u) = L²(u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))` for every `u`. -/
theorem cubic_eq_factor_of_roots {E L u₁ u₂ : ℝ} (hu : u₁ ≠ u₂)
    (h₁ : E ^ 2 - (1 - 2 * M * u₁) * (1 + L ^ 2 * u₁ ^ 2) = 0)
    (h₂ : E ^ 2 - (1 - 2 * M * u₂) * (1 + L ^ 2 * u₂ ^ 2) = 0) (u : ℝ) :
    E ^ 2 - (1 - 2 * M * u) * (1 + L ^ 2 * u ^ 2) =
      L ^ 2 * (u₁ - u) * (u - u₂) * (1 - 2 * M * (u₁ + u₂ + u)) := by
  have hne : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr hu.symm
  refine mul_left_cancel₀ hne ?_
  linear_combination (u₂ - u) * h₁ + (u - u₁) * h₂

/-! ### Technical facts on geodesics -/

private theorem differentiableAt_val {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ :=
  (CoordinateMetric.contMDiffAt_iff_contDiffAt_val.mp (hγ τ hτ).1).differentiableAt
    (by norm_num)

private theorem hasDerivAt_radius {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    HasDerivAt (fun t => (γ t : MinkowskiModel 3) 1)
      (deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) τ :=
  hasDerivAt_pi.mp (differentiableAt_val hγ hτ).hasDerivAt 1

private theorem radius_pos' (hM : 0 ≤ M) (y : domain M) : 0 < (y : MinkowskiModel 3) 1 := by
  have : 2 * M < (y : MinkowskiModel 3) 1 := y.property.1
  linarith

private theorem continuousOn_inv_radius_sq {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (L : ℝ) :
    ContinuousOn (fun σ => L * (1 / (γ σ : MinkowskiModel 3) 1) ^ 2) s := by
  have hr : ContinuousOn (fun σ => (γ σ : MinkowskiModel 3) 1) s := fun σ hσ =>
    (hasDerivAt_radius hγ hσ).continuousAt.continuousWithinAt
  exact continuousOn_const.mul ((continuousOn_const.div hr fun σ _ =>
    (radius_pos' hM (γ σ)).ne').pow 2)

/-- The inverse radius `u = 1/r` of a geodesic has the derivative `u̇ = −ṙ/r²`. -/
theorem hasDerivAt_inv_radius (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    HasDerivAt (fun t => 1 / (γ t : MinkowskiModel 3) 1)
      (-deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2) τ := by
  simpa only [one_div] using (hasDerivAt_radius hγ hτ).fun_inv (radius_pos' hM (γ τ)).ne'

/-- **The radial equation for the inverse radius.** Along a geodesic with `κ = 1`, given on a
convex set of parameters, `ṙ² = E² − (1 − 2Mu)(1 + L²u²)` with `u = 1/r`, where the energy `E`
and `L = √(J₀² + J₁² + J₂²)` are read at `τ₀`. -/
theorem radial_sq_eq_inv (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) (hκ : normalization hM γ τ₀ = 1) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ₀ ^ 2 - (1 - 2 * M * (1 / (γ τ : MinkowskiModel 3) 1)) *
        (1 + Real.sqrt (angularMomentumSq hM x₀ γ τ₀) ^ 2 *
          (1 / (γ τ : MinkowskiModel 3) 1) ^ 2) := by
  rw [radial_sq_eq hM x₀ hγ hs h₀ hτ, hκ, effectivePotential]
  ring

/-! ### The apsides -/

/-- The data of an arc from a perihelion to an aphelion: `u₂ > 0`, `u₂ < u₁`, `L > 0` and the
factorized radial equation on all of `s`. -/
private theorem apsidal_data (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    0 < 1 / (γ τ₂ : MinkowskiModel 3) 1 ∧
      1 / (γ τ₂ : MinkowskiModel 3) 1 < 1 / (γ τ₁ : MinkowskiModel 3) 1 ∧
      0 < Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) ∧
      ∀ τ ∈ s, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
        Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) ^ 2 *
          (1 / (γ τ₁ : MinkowskiModel 3) 1 - 1 / (γ τ : MinkowskiModel 3) 1) *
          (1 / (γ τ : MinkowskiModel 3) 1 - 1 / (γ τ₂ : MinkowskiModel 3) 1) *
          (1 - 2 * M * (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1 +
            1 / (γ τ : MinkowskiModel 3) 1)) := by
  set E := energy hM.le x₀ γ τ₁
  set L := Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) with hLdef
  set u₁ := 1 / (γ τ₁ : MinkowskiModel 3) 1
  set u₂ := 1 / (γ τ₂ : MinkowskiModel 3) 1
  have hrad := fun τ (hτ' : τ ∈ s) => radial_sq_eq_inv hM.le x₀ hγ hsc h₁ hτ' hκ
  have P₁ : E ^ 2 - (1 - 2 * M * u₁) * (1 + L ^ 2 * u₁ ^ 2) = 0 := by
    have h := hrad τ₁ h₁
    rw [hr₁] at h
    linarith
  have P₂ : E ^ 2 - (1 - 2 * M * u₂) * (1 + L ^ 2 * u₂ ^ 2) = 0 := by
    have h := hrad τ₂ h₂
    rw [hr₂] at h
    linarith
  have hsub : Icc τ₁ τ₂ ⊆ s := hsc.ordConnected.out h₁ h₂
  have hlt : (γ τ₁ : MinkowskiModel 3) 1 < (γ τ₂ : MinkowskiModel 3) 1 :=
    Mechanics.lt_of_hasDerivAt_pos hτ (fun t ht => hasDerivAt_radius hγ (hsub ht)) hpos
  have hu : u₂ < u₁ := one_div_lt_one_div_of_lt (radius_pos' hM.le (γ τ₁)) hlt
  have hu₂ : 0 < u₂ := one_div_pos.mpr (radius_pos' hM.le (γ τ₂))
  have hL : 0 < L := by
    refine lt_of_le_of_ne (Real.sqrt_nonneg _) fun hL0 => ?_
    have h : 2 * M * (u₁ - u₂) = 0 := by
      rw [← hL0] at P₁ P₂
      linear_combination P₁ - P₂
    have : 0 < 2 * M * (u₁ - u₂) := mul_pos (mul_pos two_pos hM) (sub_pos.mpr hu)
    exact this.ne' h
  refine ⟨hu₂, hu, hL, fun τ hτ' => ?_⟩
  rw [hrad τ hτ', cubic_eq_factor_of_roots hu.ne' P₁ P₂]

/-- **The apsides** (Landau–Lifshitz, §101). On an arc from a perihelion `τ₁` to an aphelion `τ₂`
of a geodesic with `κ = 1` (`ṙ(τ₁) = ṙ(τ₂) = 0` and `ṙ > 0` between them), the inverse radii
satisfy `0 < u₂ = 1/r(τ₂) < u₁ = 1/r(τ₁)`, and `L = √(J₀² + J₁² + J₂²) > 0` since `M > 0`. -/
theorem inverseRadius_lt_of_apsides (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂)
    (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    0 < 1 / (γ τ₂ : MinkowskiModel 3) 1 ∧
      1 / (γ τ₂ : MinkowskiModel 3) 1 < 1 / (γ τ₁ : MinkowskiModel 3) 1 ∧
      0 < Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) :=
  let h := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The factorized radial equation** (Landau–Lifshitz, §101, (101.6)). On a geodesic with an
arc from a perihelion `τ₁` to an aphelion `τ₂`, at every parameter of `s`,
`ṙ² = L²(u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))` with `u = 1/r`, `u₁ = 1/r(τ₁)`,
`u₂ = 1/r(τ₂)`. -/
theorem radial_sq_eq_factor (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    {τ : ℝ} (hτs : τ ∈ s) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) ^ 2 *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 - 1 / (γ τ : MinkowskiModel 3) 1) *
        (1 / (γ τ : MinkowskiModel 3) 1 - 1 / (γ τ₂ : MinkowskiModel 3) 1) *
        (1 - 2 * M * (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1 +
          1 / (γ τ : MinkowskiModel 3) 1)) :=
  (apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos).2.2.2 τ hτs

/-- Where the radius increases, the inverse radius decreases: `u̇ = −ṙ/r² < 0`. -/
theorem inv_radius_rate_neg (hM : 0 ≤ M) (γ : ℝ → domain M) {τ : ℝ}
    (hpos : 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    -deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2 < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos hpos) (pow_pos (radius_pos' hM (γ τ)) 2)

/-- **The orbit equation for the inverse radius** (Landau–Lifshitz, §101). On a geodesic with an
arc from a perihelion `τ₁` to an aphelion `τ₂`, at every parameter of `s`, the rate
`u̇ = −ṙ/r²` of `u = 1/r` satisfies `u̇² = L²u⁴(u₁ − u)(u − u₂)(1 − 2M(u₁ + u₂ + u))`. -/
theorem inv_radius_rate_sq_eq (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    {τ : ℝ} (hτs : τ ∈ s) :
    (-deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2) ^ 2 =
      Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) ^ 2 * (1 / (γ τ : MinkowskiModel 3) 1) ^ 4 *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 - 1 / (γ τ : MinkowskiModel 3) 1) *
        (1 / (γ τ : MinkowskiModel 3) 1 - 1 / (γ τ₂ : MinkowskiModel 3) 1) *
        (1 - 2 * M * (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1 +
          1 / (γ τ : MinkowskiModel 3) 1)) := by
  have h := radial_sq_eq_factor hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos hτs
  rw [show (-deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2) ^ 2
      = deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 * (1 / (γ τ : MinkowskiModel 3) 1) ^ 4
      by ring, h]
  ring

/-- **The simple-apsides condition is almost forced.** On an arc from a perihelion `τ₁` to an
aphelion `τ₂`, `2M(2u₁ + u₂) ≤ 1`: otherwise the factor `1 − 2M(u₁ + u₂ + u)` would be negative
near the perihelion, where `ṙ² ≥ 0`. -/
theorem simple_apsides_le (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) ≤ 1 := by
  obtain ⟨hu₂, hu, hL, hfac⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  set L := Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁)
  set u₁ := 1 / (γ τ₁ : MinkowskiModel 3) 1
  set u₂ := 1 / (γ τ₂ : MinkowskiModel 3) 1
  set u : ℝ → ℝ := fun t => 1 / (γ t : MinkowskiModel 3) 1 with hudef
  by_contra hlt'
  have hlt := not_le.mp hlt'
  set c := 2 * M * (2 * u₁ + u₂) - 1
  have hc : 0 < c := by linarith
  have hsub : Icc τ₁ τ₂ ⊆ s := hsc.ordConnected.out h₁ h₂
  have hcont : ContinuousAt u τ₁ := (hasDerivAt_inv_radius hM.le hγ h₁).continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (c / (2 * M)) (by positivity)
  set τ := τ₁ + min δ (τ₂ - τ₁) / 2
  have hm : 0 < min δ (τ₂ - τ₁) := lt_min hδ (by linarith)
  have hmle : min δ (τ₂ - τ₁) ≤ τ₂ - τ₁ := min_le_right _ _
  have hτI : τ ∈ Ioo τ₁ τ₂ := ⟨by simp only [τ]; linarith, by simp only [τ]; linarith⟩
  have hdist : dist τ τ₁ < δ := by
    rw [Real.dist_eq, show τ - τ₁ = min δ (τ₂ - τ₁) / 2 by simp only [τ]; ring,
      abs_of_pos (by linarith)]
    linarith [min_le_left δ (τ₂ - τ₁)]
  have hclose := hball hdist
  rw [Real.dist_eq] at hclose
  have hgap : u₁ - u τ < c / (2 * M) := by
    have := (abs_lt.mp hclose).1
    change -(c / (2 * M)) < u τ - u₁ at this
    linarith
  have hneg := fun t (ht : t ∈ Ioo τ₁ τ₂) => inv_radius_rate_neg hM.le γ (hpos t ht)
  have hx : ∀ a b, Icc a b ⊆ Icc τ₁ τ₂ → ∀ t ∈ Icc a b, HasDerivAt u
      (-deriv (fun t => (γ t : MinkowskiModel 3)) t 1 / (γ t : MinkowskiModel 3) 1 ^ 2) t :=
    fun a b hab t ht => hasDerivAt_inv_radius hM.le hγ (hsub (hab ht))
  have hlo : u τ < u₁ :=
    Mechanics.lt_of_hasDerivAt_neg (x := u) hτI.1 (hx τ₁ τ (Icc_subset_Icc le_rfl hτI.2.le))
      fun t ht => hneg t ⟨ht.1, ht.2.trans hτI.2⟩
  have hhi : u₂ < u τ :=
    Mechanics.lt_of_hasDerivAt_neg (x := u) hτI.2 (hx τ τ₂ (Icc_subset_Icc hτI.1.le le_rfl))
      fun t ht => hneg t ⟨hτI.1.trans ht.1, ht.2⟩
  have hf : 1 - 2 * M * (u₁ + u₂ + u τ) < 0 := by
    have h2M : 0 < 2 * M := by linarith
    have : 2 * M * (u₁ - u τ) < c := by
      have := (lt_div_iff₀ h2M).mp hgap
      linarith
    simp only [c] at this
    linarith
  have hprod : 0 < L ^ 2 * (u₁ - u τ) * (u τ - u₂) :=
    mul_pos (mul_pos (pow_pos hL 2) (sub_pos.mpr hlo)) (sub_pos.mpr hhi)
  have h := hfac τ (hsub (Ioo_subset_Icc_self hτI))
  have : deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 < 0 := by
    rw [h]
    exact mul_neg_of_pos_of_neg hprod hf
  exact absurd this (not_lt.mpr (sq_nonneg _))

/-- On an arc from a perihelion `τ₁` to an aphelion `τ₂`, `u₂ ≤ u ≤ u₁` on `[τ₁, τ₂]`. -/
private theorem inv_radius_mem_Icc (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    {τ : ℝ} (hτ : τ ∈ Icc τ₁ τ₂) :
    1 / (γ τ₂ : MinkowskiModel 3) 1 ≤ 1 / (γ τ : MinkowskiModel 3) 1 ∧
      1 / (γ τ : MinkowskiModel 3) 1 ≤ 1 / (γ τ₁ : MinkowskiModel 3) 1 := by
  have hsub : Icc τ₁ τ₂ ⊆ s := hsc.ordConnected.out h₁ h₂
  have hx : ∀ a b, Icc a b ⊆ Icc τ₁ τ₂ → ∀ t ∈ Icc a b,
      HasDerivAt (fun t => 1 / (γ t : MinkowskiModel 3) 1)
        (-deriv (fun t => (γ t : MinkowskiModel 3)) t 1 / (γ t : MinkowskiModel 3) 1 ^ 2) t :=
    fun a b hab t ht => hasDerivAt_inv_radius hM hγ (hsub (hab ht))
  have hneg := fun t (ht : t ∈ Ioo τ₁ τ₂) => inv_radius_rate_neg hM γ (hpos t ht)
  constructor
  · rcases hτ.2.eq_or_lt with h | h
    · rw [h]
    · exact (Mechanics.lt_of_hasDerivAt_neg h (hx τ τ₂ (Icc_subset_Icc hτ.1 le_rfl))
        fun t ht => hneg t ⟨hτ.1.trans_lt ht.1, ht.2⟩).le
  · rcases hτ.1.eq_or_lt with h | h
    · rw [h]
    · exact (Mechanics.lt_of_hasDerivAt_neg h (hx τ₁ τ (Icc_subset_Icc le_rfl hτ.2))
        fun t ht => hneg t ⟨ht.1, ht.2.trans_le hτ.2⟩).le

/-- **The simple-apsides condition** (Landau–Lifshitz, §101). On an arc from a perihelion `τ₁`
to an aphelion `τ₂`, `2M(2u₁ + u₂) < 1`. In the case of equality the third root
`1/(2M) − u₁ − u₂` of the cubic would be `u₁`, so that `|u̇| ≤ K(u₁ − u)` on `[τ₁, τ₂]` for a
constant `K`; by Grönwall's inequality `u₁ − u` would then vanish on `[τ₁, τ₂]`, against
`u(τ₂) = u₂ < u₁`. -/
theorem simple_apsides_lt (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) < 1 := by
  refine (simple_apsides_le hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos).lt_of_ne fun heq => ?_
  obtain ⟨hu₂, hu, -, -⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  set L := Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁)
  set u₁ := 1 / (γ τ₁ : MinkowskiModel 3) 1
  set u₂ := 1 / (γ τ₂ : MinkowskiModel 3) 1
  have hsub : Icc τ₁ τ₂ ⊆ s := hsc.ordConnected.out h₁ h₂
  set C := 2 * M * L ^ 2 * u₁ ^ 4 * (u₁ - u₂)
  have hC : 0 ≤ C := by have := hM.le; have := hu.le; positivity
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun t => u₁ - 1 / (γ t : MinkowskiModel 3) 1)
    (f' := fun t => -(-deriv (fun t => (γ t : MinkowskiModel 3)) t 1 /
      (γ t : MinkowskiModel 3) 1 ^ 2)) (K := Real.sqrt C)
    (fun t ht => ((hasDerivAt_inv_radius hM.le hγ (hsub ht)).const_sub u₁).continuousAt
      |>.continuousWithinAt)
    (fun t ht => ((hasDerivAt_inv_radius hM.le hγ
      (hsub (Ico_subset_Icc_self ht))).const_sub u₁).hasDerivWithinAt)
    (sub_self u₁) (fun t ht => ?_) τ₂ (right_mem_Icc.mpr hτ.le)
  · exact hu.ne' (sub_eq_zero.mp hzero)
  have htI := Ico_subset_Icc_self ht
  obtain ⟨hlo, hhi⟩ := inv_radius_mem_Icc hM.le hγ hsc h₁ h₂ hpos htI
  set u := 1 / (γ t : MinkowskiModel 3) 1
  have hu0 : 0 < u := lt_of_lt_of_le hu₂ hlo
  have hsq : (-deriv (fun t => (γ t : MinkowskiModel 3)) t 1 / (γ t : MinkowskiModel 3) 1 ^ 2)
      ^ 2 ≤ (Real.sqrt C * (u₁ - u)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC, inv_radius_rate_sq_eq hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
      (hsub htI)]
    have h3 : 1 - 2 * M * (u₁ + u₂ + u) = 2 * M * (u₁ - u) := by linear_combination -heq
    rw [h3]
    have hu4 : u ^ 4 ≤ u₁ ^ 4 := pow_le_pow_left₀ hu0.le hhi 4
    have hd : u - u₂ ≤ u₁ - u₂ := by linarith
    have hM2 : 0 ≤ 2 * M * L ^ 2 := by have := hM.le; positivity
    have hA : 0 ≤ (u₁ - u) ^ 2 := sq_nonneg _
    have hB : 0 ≤ u - u₂ := by linarith
    calc L ^ 2 * u ^ 4 * (u₁ - u) * (u - u₂) * (2 * M * (u₁ - u))
        = 2 * M * L ^ 2 * (u ^ 4 * (u - u₂)) * (u₁ - u) ^ 2 := by ring
      _ ≤ 2 * M * L ^ 2 * (u₁ ^ 4 * (u₁ - u₂)) * (u₁ - u) ^ 2 := by
        gcongr
      _ = C * (u₁ - u) ^ 2 := by simp only [C]; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  calc _ ≤ |Real.sqrt C * (u₁ - u)| := (sq_le_sq.mp hsq)
    _ = Real.sqrt C * |u₁ - u| := by rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/-! ### The angle between the apsides -/

/-- The swept angle as the integral of `L u²`. -/
private theorem sweptAngle_eq_integral (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s)
    {τ₀ τa τb : ℝ} (h₀ : τ₀ ∈ s) (ha : τa ∈ s) (hb : τb ∈ s) :
    sweptAngle γ τa τb = ∫ σ in τa..τb,
      Real.sqrt (angularMomentumSq hM x₀ γ τ₀) * (1 / (γ σ : MinkowskiModel 3) 1) ^ 2 := by
  unfold sweptAngle
  refine intervalIntegral.integral_congr fun σ hσ => ?_
  have hσs : σ ∈ s := hsc.ordConnected.uIcc_subset ha hb hσ
  rw [sqrt_angular_eq hM x₀ (differentiableAt_val hγ hσs),
    ← angularMomentumSq_eq hM x₀ hγ hsc h₀ hσs]
  ring

/-- The regularized integral `∫ L u² du / √((u − u₂)(u₁ − u) L²u⁴(1 − 2M(u₁ + u₂ + u)))` is the
apsidal angle. -/
private theorem integral_eq_apsidalAngle {L u₁ u₂ : ℝ} (hL : 0 < L) (hu₂ : 0 < u₂)
    (hu : u₂ < u₁) :
    ∫ u in u₂..u₁, L * u ^ 2 /
        √((u - u₂) * (u₁ - u) * (L ^ 2 * u ^ 4 * (1 - 2 * M * (u₁ + u₂ + u)))) =
      Perihelion.apsidalAngle M u₂ u₁ := by
  rw [Mechanics.integral_div_sqrt_turning hu, Perihelion.apsidalAngle]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  obtain ⟨hv₁, hv₂⟩ := Perihelion.turningParam_mem_Icc_of_le hu.le θ
  set v := Mechanics.turningParam u₂ u₁ θ
  have hv : 0 < v := lt_of_lt_of_le hu₂ hv₁
  have hLv : 0 < L * v ^ 2 := by positivity
  rw [show L ^ 2 * v ^ 4 * (1 - 2 * M * (u₁ + u₂ + v)) =
      (L * v ^ 2) ^ 2 * (1 - 2 * M * (u₁ + u₂ + v)) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hLv.le, ← div_div, div_self hLv.ne']

/-- The hypotheses of the quadrature on `[u₂, u₁]`. -/
private theorem turning_hyps {L u₁ u₂ : ℝ} (hM : 0 < M) (hL : 0 < L) (hu₂ : 0 < u₂)
    (hsimple : 2 * M * (2 * u₁ + u₂) < 1) :
    ContinuousOn (fun u : ℝ => L * u ^ 2) (Icc u₂ u₁) ∧
      ContinuousOn (fun u : ℝ => L ^ 2 * u ^ 4 * (1 - 2 * M * (u₁ + u₂ + u))) (Icc u₂ u₁) ∧
      ∀ u ∈ Icc u₂ u₁, 0 < L ^ 2 * u ^ 4 * (1 - 2 * M * (u₁ + u₂ + u)) := by
  refine ⟨by fun_prop, by fun_prop, fun u hu => ?_⟩
  have hu0 : 0 < u := lt_of_lt_of_le hu₂ hu.1
  have : 2 * M * (u₁ + u₂ + u) ≤ 2 * M * (2 * u₁ + u₂) :=
    mul_le_mul_of_nonneg_left (by linarith [hu.2]) (by linarith)
  exact mul_pos (by positivity) (by linarith)

/-- **The angle between the apsides** (Landau–Lifshitz, §101, (101.6)). Let `γ` be a geodesic
with `κ = 1` on a convex set `s`, and `τ₁ < τ₂` in `s` with `ṙ(τ₁) = ṙ(τ₂) = 0` and
`ṙ > 0` on `(τ₁, τ₂)`. With `u₁ = 1/r(τ₁)` and `u₂ = 1/r(τ₂)`, the angle swept from the
perihelion to the aphelion is `∫₀^π dθ / √(1 − 2M(u₁ + u₂ + u(θ)))` with
`u(θ) = (u₁ + u₂)/2 + (u₁ − u₂)/2 · cos θ`. -/
theorem angle_between_apsides (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    sweptAngle γ τ₁ τ₂ = Perihelion.apsidalAngle M (1 / (γ τ₂ : MinkowskiModel 3) 1)
      (1 / (γ τ₁ : MinkowskiModel 3) 1) := by
  obtain ⟨hu₂, hu, hL, hfac⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  obtain ⟨hw, hG, hGpos⟩ :=
    turning_hyps hM hL hu₂ (simple_apsides_lt hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos)
  have hsub : Icc τ₁ τ₂ ⊆ s := hsc.ordConnected.out h₁ h₂
  rw [sweptAngle_eq_integral hM.le x₀ hγ hsc h₁ h₁ h₂,
    ← integral_eq_apsidalAngle (M := M) hL hu₂ hu]
  refine Mechanics.integral_comp_eq_integral_div_sqrt_turning_of_neg
    (x := fun t => 1 / (γ t : MinkowskiModel 3) 1)
    (x' := fun t => -deriv (fun t => (γ t : MinkowskiModel 3)) t 1 /
      (γ t : MinkowskiModel 3) 1 ^ 2)
    (w := fun u => Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) * u ^ 2) hτ hu
    (fun t ht => hasDerivAt_inv_radius hM.le hγ (hsub ht))
    (fun t ht => inv_radius_rate_neg hM.le γ (hpos t ht)) rfl rfl (fun t ht => ?_) hw hG hGpos
  rw [inv_radius_rate_sq_eq hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos (hsub (Ioo_subset_Icc_self ht))]
  ring

/-- **The return half of the orbit.** On the arc `[τ₂, τ₃]` after the aphelion `τ₂`, with
`ṙ < 0` on `(τ₂, τ₃)` and `r(τ₃) = r(τ₁)`, the swept angle is the same integral
`Perihelion.apsidalAngle M u₂ u₁`, whether or not the orbit is symmetric. -/
theorem return_half (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s)
    {τ₁ τ₂ τ₃ : ℝ} (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (h₃ : τ₃ ∈ s) (hτ : τ₁ < τ₂) (hτ' : τ₂ < τ₃)
    (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hneg : ∀ τ ∈ Ioo τ₂ τ₃, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 < 0)
    (hr₃ : (γ τ₃ : MinkowskiModel 3) 1 = (γ τ₁ : MinkowskiModel 3) 1) :
    sweptAngle γ τ₂ τ₃ = Perihelion.apsidalAngle M (1 / (γ τ₂ : MinkowskiModel 3) 1)
      (1 / (γ τ₁ : MinkowskiModel 3) 1) := by
  obtain ⟨hu₂, hu, hL, hfac⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  obtain ⟨hw, hG, hGpos⟩ :=
    turning_hyps hM hL hu₂ (simple_apsides_lt hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos)
  have hsub : Icc τ₂ τ₃ ⊆ s := hsc.ordConnected.out h₂ h₃
  rw [sweptAngle_eq_integral hM.le x₀ hγ hsc h₁ h₂ h₃,
    ← integral_eq_apsidalAngle (M := M) hL hu₂ hu]
  refine Mechanics.integral_comp_eq_integral_div_sqrt_turning
    (x := fun t => 1 / (γ t : MinkowskiModel 3) 1)
    (x' := fun t => -deriv (fun t => (γ t : MinkowskiModel 3)) t 1 /
      (γ t : MinkowskiModel 3) 1 ^ 2)
    (w := fun u => Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) * u ^ 2) hτ' hu
    (fun t ht => hasDerivAt_inv_radius hM.le hγ (hsub ht))
    (fun t ht => div_pos (neg_pos.mpr (hneg t ht)) (pow_pos (radius_pos' hM.le (γ t)) 2)) rfl
    (by simp only [hr₃]) (fun t ht => ?_) hw hG hGpos
  rw [inv_radius_rate_sq_eq hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos (hsub (Ioo_subset_Icc_self ht))]
  ring

/-- **The angle between successive perihelia.** From the perihelion `τ₁` through the aphelion
`τ₂` to the next perihelion `τ₃` the swept angle is `2 · apsidalAngle M u₂ u₁`. -/
theorem sweptAngle_between_perihelia (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s)
    {τ₁ τ₂ τ₃ : ℝ} (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (h₃ : τ₃ ∈ s) (hτ : τ₁ < τ₂) (hτ' : τ₂ < τ₃)
    (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hneg : ∀ τ ∈ Ioo τ₂ τ₃, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 < 0)
    (hr₃ : (γ τ₃ : MinkowskiModel 3) 1 = (γ τ₁ : MinkowskiModel 3) 1) :
    sweptAngle γ τ₁ τ₃ = 2 * Perihelion.apsidalAngle M (1 / (γ τ₂ : MinkowskiModel 3) 1)
      (1 / (γ τ₁ : MinkowskiModel 3) 1) := by
  have hc := continuousOn_inv_radius_sq hγ (Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁))
  have hadd : sweptAngle γ τ₁ τ₃ = sweptAngle γ τ₁ τ₂ + sweptAngle γ τ₂ τ₃ := by
    rw [sweptAngle_eq_integral hM.le x₀ hγ hsc h₁ h₁ h₃,
      sweptAngle_eq_integral hM.le x₀ hγ hsc h₁ h₁ h₂,
      sweptAngle_eq_integral hM.le x₀ hγ hsc h₁ h₂ h₃]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((hc.mono (hsc.ordConnected.uIcc_subset h₁ h₂)).intervalIntegrable)
      ((hc.mono (hsc.ordConnected.uIcc_subset h₂ h₃)).intervalIntegrable)).symm
  rw [hadd, angle_between_apsides hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos,
    return_half hM x₀ hγ hsc h₁ h₂ h₃ hτ hτ' hκ hr₁ hr₂ hpos hneg hr₃]
  ring

/-! ### The perihelion advance -/

/-- **The perihelion advance** (Landau–Lifshitz, §101, (101.7)). On an arc from a perihelion `τ₁`
to an aphelion `τ₂` of a geodesic with `κ = 1`, if `2M(2u₁ + u₂) ≤ 1/4`, then
`0 ≤ 2 · sweptAngle − 2π − 3πM(u₁ + u₂) ≤ 4πM²(2u₁ + u₂)²`. -/
theorem perihelion_advance_bounds (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hsmall : 2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) +
      1 / (γ τ₂ : MinkowskiModel 3) 1) ≤ 1 / 4) :
    0 ≤ 2 * sweptAngle γ τ₁ τ₂ - 2 * π - 3 * π * M *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ∧
      2 * sweptAngle γ τ₁ τ₂ - 2 * π - 3 * π * M *
          (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ≤
        4 * π * M ^ 2 *
          (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) ^ 2 := by
  obtain ⟨hu₂, hu, -, -⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  rw [angle_between_apsides hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos]
  exact Perihelion.apsidalAngle_bounds hM.le hu₂.le hu.le hsmall

/-- **The perihelion advance in terms of the orbital elements** (Landau–Lifshitz, §101, (101.7)).
On an arc from a perihelion `r(τ₁) = a(1 − e)` to an aphelion `r(τ₂) = a(1 + e)` of a geodesic
with `κ = 1`, if `8M(3 + e) ≤ a(1 − e²)`, then
`2 · sweptAngle − 2π = 6πM/(a(1 − e²)) + δ` with `0 ≤ δ ≤ 4πM²((3 + e)/(a(1 − e²)))²`. The
ranges `a > 0` and `0 < e < 1` follow from the orbit. -/
theorem perihelion_advance_bounds_semiMajor (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s)
    {τ₁ τ₂ : ℝ} (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂)
    (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    {a e : ℝ} (ha₁ : (γ τ₁ : MinkowskiModel 3) 1 = a * (1 - e))
    (ha₂ : (γ τ₂ : MinkowskiModel 3) 1 = a * (1 + e))
    (hsmall : 8 * M * (3 + e) ≤ a * (1 - e ^ 2)) :
    0 ≤ 2 * sweptAngle γ τ₁ τ₂ - 2 * π - 6 * π * M / (a * (1 - e ^ 2)) ∧
      2 * sweptAngle γ τ₁ τ₂ - 2 * π - 6 * π * M / (a * (1 - e ^ 2)) ≤
        4 * π * M ^ 2 * ((3 + e) / (a * (1 - e ^ 2))) ^ 2 := by
  obtain ⟨hu₂, hu, -, -⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  have hp₁ := radius_pos' hM.le (γ τ₁)
  have hp₂ := radius_pos' hM.le (γ τ₂)
  have hlt : (γ τ₁ : MinkowskiModel 3) 1 < (γ τ₂ : MinkowskiModel 3) 1 := by
    have := (one_div_lt_one_div hp₂ hp₁).mp hu
    exact this
  have ha : 0 < a := by linarith
  have he : 0 < e := pos_of_mul_pos_right (show 0 < a * e by linarith) ha.le
  have he1 : e < 1 := by
    have : 0 < a * (1 - e) := by linarith
    have := pos_of_mul_pos_right this ha.le
    linarith
  rw [angle_between_apsides hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos, ha₁, ha₂]
  exact Perihelion.apsidalAngle_bounds_semiMajor hM.le ha he.le he1 hsmall

/-- **The advance between successive perihelia** (Landau–Lifshitz, §101, (101.7)). From the
perihelion `τ₁` through the aphelion `τ₂` to the next perihelion `τ₃`, if
`2M(2u₁ + u₂) ≤ 1/4`, then `0 ≤ sweptAngle γ τ₁ τ₃ − 2π − 3πM(u₁ + u₂) ≤ 4πM²(2u₁ + u₂)²`. -/
theorem perihelion_advance_between_perihelia (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s)
    {τ₁ τ₂ τ₃ : ℝ} (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (h₃ : τ₃ ∈ s) (hτ : τ₁ < τ₂) (hτ' : τ₂ < τ₃)
    (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hneg : ∀ τ ∈ Ioo τ₂ τ₃, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 < 0)
    (hr₃ : (γ τ₃ : MinkowskiModel 3) 1 = (γ τ₁ : MinkowskiModel 3) 1)
    (hsmall : 2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) +
      1 / (γ τ₂ : MinkowskiModel 3) 1) ≤ 1 / 4) :
    0 ≤ sweptAngle γ τ₁ τ₃ - 2 * π - 3 * π * M *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ∧
      sweptAngle γ τ₁ τ₃ - 2 * π - 3 * π * M *
          (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ≤
        4 * π * M ^ 2 *
          (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) ^ 2 := by
  obtain ⟨hu₂, hu, -, -⟩ := apsidal_data hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos
  rw [sweptAngle_between_perihelia hM x₀ hγ hsc h₁ h₂ h₃ hτ hτ' hκ hr₁ hr₂ hpos hneg hr₃]
  exact Perihelion.apsidalAngle_bounds hM.le hu₂.le hu.le hsmall

/-! ### Regression: the algebraic hypotheses can hold -/

/- For `M = 1/40`, `L² = 1/53`, `E² = 513/530`, `u₁ = 2` and `u₂ = 1` (so `r_min = 1/2 > 2M`,
`r_max = 1`), the cubic `P(u) = E² − (1 − 2Mu)(1 + L²u²)` vanishes at `u₁` and `u₂`, the orbit
is bound (`E² < 1`), and `2M(2u₁ + u₂) = 1/4`: the hypotheses of `cubic_eq_factor_of_roots`
and the smallness condition of `perihelion_advance_bounds` hold together. -/
example :
    Real.sqrt (513 / 530) ^ 2 - (1 - 2 * (1 / 40) * 2) * (1 + Real.sqrt (1 / 53) ^ 2 * 2 ^ 2)
        = 0 ∧
      Real.sqrt (513 / 530) ^ 2 - (1 - 2 * (1 / 40) * 1) *
        (1 + Real.sqrt (1 / 53) ^ 2 * 1 ^ 2) = 0 ∧
      Real.sqrt (513 / 530) ^ 2 < 1 ∧ 2 * (1 / 40 : ℝ) * (2 * 2 + 1) = 1 / 4 := by
  rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

/- With these constants the factorization reads
`P(u) = (1/53)(2 − u)(u − 1)(1 − (3 + u)/20)`. -/
example (u : ℝ) :
    Real.sqrt (513 / 530) ^ 2 - (1 - 2 * (1 / 40) * u) * (1 + Real.sqrt (1 / 53) ^ 2 * u ^ 2) =
      Real.sqrt (1 / 53) ^ 2 * (2 - u) * (u - 1) * (1 - 2 * (1 / 40) * (2 + 1 + u)) := by
  refine cubic_eq_factor_of_roots (by norm_num) ?_ ?_ u <;>
  · rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
    norm_num

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
