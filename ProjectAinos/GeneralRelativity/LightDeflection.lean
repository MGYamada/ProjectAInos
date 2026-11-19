/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildOrbit
public import ProjectAinos.GeneralRelativity.DeflectionIntegral

/-!
# The deflection of a ray of light by the Schwarzschild field

Landau–Lifshitz, §101, (101.8)–(101.9), in units `G = c = 1`. Let `γ` be a null geodesic
(`normalization = 0`) of the exterior Schwarzschild metric, given on an open convex set `s` of
parameters that contains `[τ₀, ∞)`, with the closest approach to the centre at `τ₀`
(`ṙ(τ₀) = 0`), the radius increasing after it (`ṙ > 0` on `(τ₀, ∞)`) and tending to infinity.
Let `E > 0` be its energy, `L = √(J₀² + J₁² + J₂²) > 0` its angular momentum and `ρ = L/E`
(`impactParameter`) its impact parameter. The ray is given: for `M > 0` its existence is not
constructed here.

* `radial_sq_eq_speedSq`, `radial_sq_eq_light`: the radial equation of light is
  `ṙ² = E² (1 − u² + (2M/ρ) u³)` with `u = ρ/r`, which is `speedSq (fun u => −u³) ρ E (2M/ρ) r`
  of the small-angle scattering library, with the speed `v∞ = E` at infinity, (101.8).
* `tendsto_sweptAngle_atTop`: the angle swept in the plane of the motion from the closest
  approach to infinity is `∫_{r₀}^∞ (L/r²) dr/√(ṙ²)`, the angle density of Landau–Lifshitz
  (18.4) with `ℓ = ρ E = L`. `tendsto_two_mul_sweptAngle_atTop`: twice this angle is `π − χ`,
  with the angle of deflection `χ = deflectionAngle (ρ E) (speedSq …) r₀`.
* `radicand_pos_light`, `closest_eq`: `ρ/r₀` is the first positive zero of the radicand, so it
  is the closest approach `c` of `IsClosest (fun u => −u³) (2M/ρ) c` whenever this exists;
  `exists_isClosest_light`: for `2M/ρ ≤ δ` it exists, so `IsClosest (fun u => −u³) (2M/ρ) (ρ/r₀)`.
* `deflection_bound`: for `2M/ρ ≤ δ`, `|χ + 4M/ρ| ≤ C (M/ρ)²`; `deflection_bound_sweptAngle`:
  with the angle `Φ` swept from the closest approach to infinity,
  `|2Φ − π − 4M/ρ| ≤ C (M/ρ)²`. The library measures `χ` with the sign of Landau–Lifshitz §20,
  negative for an attraction: the ray is turned towards the centre by `4M/ρ`, which is
  `4kM/(c²ρ)` in ordinary units, (101.9).

* `exists_ray_zero_mass`: a regression instance. Without a mass the straight null line
  `τ ↦ (τ, √(1 + τ²), π/2, arctan τ)` satisfies every hypothesis above with `τ₀ = 0`, `E = 1`,
  `L = 1`, and sweeps the angle `π/2` to infinity; through `deflection_bound` its angle of
  deflection is `0`. For `M > 0` no ray is constructed.

Only the outgoing half `[τ₀, ∞)` of the ray is used. Its incoming half sweeps the same angle by
the reflection `τ ↦ 2τ₀ − τ`, which is not formalized here; the total angle `π − χ` of
Landau–Lifshitz is twice the angle of the outgoing half.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Real ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski
open Mechanics.Scattering Mechanics.Scattering.SmallAngle

variable {M : ℝ}

/-- The impact parameter `ρ = L/E` of a curve at the parameter `τ`, with the angular momentum
`L = √(J₀² + J₁² + J₂²)` and the energy `E`. -/
def impactParameter (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) : ℝ :=
  √(angularMomentumSq hM x₀ γ τ) / energy hM x₀ γ τ

/-! ### Technical facts -/

private theorem radius_pos_light (hM : 0 ≤ M) (y : domain M) : 0 < (y : MinkowskiModel 3) 1 := by
  have : 2 * M < (y : MinkowskiModel 3) 1 := y.property.1
  linarith

private theorem hasDerivAt_radius_light {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    HasDerivAt (fun t => (γ t : MinkowskiModel 3) 1)
      (deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) τ :=
  hasDerivAt_pi.mp ((CoordinateMetric.contMDiffAt_iff_contDiffAt_val.mp
    (hγ τ hτ).1).differentiableAt (by norm_num)).hasDerivAt 1

private theorem continuousOn_radius_light {hM : 0 ≤ M} {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) :
    ContinuousOn (fun t => (γ t : MinkowskiModel 3) 1) s :=
  fun _ hτ => (hasDerivAt_radius_light hγ hτ).continuousAt.continuousWithinAt

private theorem contDiff_neg_cube : ContDiff ℝ ∞ fun u : ℝ => -u ^ 3 := by
  fun_prop

private theorem impactParameter_mul_energy (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
    {τ : ℝ} (hE : energy hM x₀ γ τ ≠ 0) :
    impactParameter hM x₀ γ τ * energy hM x₀ γ τ = √(angularMomentumSq hM x₀ γ τ) := by
  rw [impactParameter, div_mul_cancel₀ _ hE]

private theorem impactParameter_pos (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) {τ : ℝ}
    (hE : 0 < energy hM x₀ γ τ) (hL : 0 < angularMomentumSq hM x₀ γ τ) :
    0 < impactParameter hM x₀ γ τ :=
  div_pos (Real.sqrt_pos.mpr hL) hE

/-! ### The radial equation of light -/

/-- **The radial equation of light** (Landau–Lifshitz, §101, (101.8)). Along a null geodesic,
given on a convex set of parameters, with the energy `E ≠ 0` and the impact parameter `ρ = L/E`
read at `τ₀`, `ṙ² = speedSq (fun u => −u³) ρ E (2M/ρ) r`, that is
`ṙ² = E² (1 − ρ²/r² + (2M/ρ) ρ³/r³) = E² − (1 − 2M/r) L²/r²`. -/
theorem radial_sq_eq_speedSq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) (hκ : normalization hM γ τ₀ = 0)
    (hE : energy hM x₀ γ τ₀ ≠ 0) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
        (2 * M / impactParameter hM x₀ γ τ₀) ((γ τ : MinkowskiModel 3) 1) := by
  have hr := (radius_pos_light hM (γ τ)).ne'
  rw [radial_sq_eq hM x₀ hγ hs h₀ hτ, hκ, effectivePotential, speedSq, radicand,
    impactParameter]
  set E := energy hM x₀ γ τ₀
  set L := √(angularMomentumSq hM x₀ γ τ₀)
  set r := (γ τ : MinkowskiModel 3) 1
  rcases eq_or_ne L 0 with hL | hL
  · rw [hL]
    simp
  · simp only
    field_simp
    ring

/-- The radial equation of light in the variable `u = ρ/r` of the small-angle scattering
library: `ṙ² = E² h(2M/ρ, ρ/r)` with `h(ε, u) = 1 − u² + ε u³`. -/
theorem radial_sq_eq_light (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ}
    (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) (hκ : normalization hM γ τ₀ = 0)
    (hE : energy hM x₀ γ τ₀ ≠ 0) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ₀ ^ 2 * radicand (fun u => -u ^ 3)
        (2 * M / impactParameter hM x₀ γ τ₀,
          impactParameter hM x₀ γ τ₀ / (γ τ : MinkowskiModel 3) 1) :=
  radial_sq_eq_speedSq hM x₀ hγ hs h₀ hτ hκ hE

/-! ### The angle swept from the closest approach to infinity -/

private theorem integrableOn_angleDensity_light (ρ E ε ℓ : ℝ) (hE : 0 < E) :
    ∃ R : ℝ, IntegrableOn (angleDensity ℓ (speedSq (fun u => -u ^ 3) ρ E ε)) (Ioi R) := by
  have hlim := tendsto_speedSq_atTop contDiff_neg_cube (by norm_num) ρ E ε
  have hlt : (E / 2) ^ 2 < E ^ 2 := by nlinarith
  obtain ⟨R', hR'⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_nhds hlt))
  refine ⟨max R' 1, integrableOn_angleDensity_Ioi (lt_of_lt_of_le one_pos (le_max_right _ _))
    (half_pos hE) (fun x hx => ?_) (fun x hx => hR' x ((le_max_left _ _).trans hx)) ℓ⟩
  have hx0 : x ≠ 0 :=
    (lt_of_lt_of_le one_pos ((le_max_right R' 1).trans (mem_Ici.mp hx))).ne'
  exact (hasDerivAt_speedSq contDiff_neg_cube ρ E ε hx0).continuousAt.continuousWithinAt

/-- **The angle swept by a ray from the closest approach to infinity** (Landau–Lifshitz, §101,
with (18.4)). Let `γ` be a null geodesic, given on an open convex set `s ⊇ [τ₀, ∞)`, with the
energy `E > 0` at `τ₀`, the radius increasing after `τ₀` and tending to infinity. With the
impact parameter `ρ = L/E`, the angle density `(ℓ/r²)/√F(r)` for `ℓ = ρ E = L` and
`F = speedSq (fun u => −u³) ρ E (2M/ρ)` is integrable on `(r(τ₀), ∞)`, and the angle swept in
the plane of the motion tends to its integral. -/
theorem tendsto_sweptAngle_atTop (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    {τ₀ : ℝ} (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0)
    (hE : 0 < energy hM x₀ γ τ₀)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) :
    IntegrableOn (angleDensity (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
        (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
          (2 * M / impactParameter hM x₀ γ τ₀))) (Ioi ((γ τ₀ : MinkowskiModel 3) 1)) ∧
      Tendsto (fun τ => sweptAngle γ τ₀ τ) atTop
        (𝓝 (∫ r in Ioi ((γ τ₀ : MinkowskiModel 3) 1),
          angleDensity (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
            (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
              (2 * M / impactParameter hM x₀ γ τ₀)) r)) := by
  set E := energy hM x₀ γ τ₀ with hEdef
  set ρ := impactParameter hM x₀ γ τ₀ with hρdef
  have hℓ : ρ * E = √(angularMomentumSq hM x₀ γ τ₀) :=
    impactParameter_mul_energy hM x₀ γ hE.ne'
  have h₀ : τ₀ ∈ s := hs self_mem_Ici
  have hmem : ∀ t : ℝ, 0 ≤ t → τ₀ + t ∈ s := fun t ht =>
    hs (mem_Ici.mpr (le_add_of_nonneg_right ht))
  have hrd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t => (γ (τ₀ + t) : MinkowskiModel 3) 1)
      (deriv (fun t => (γ t : MinkowskiModel 3)) (τ₀ + t) 1) t := fun t ht =>
    (hasDerivAt_radius_light hγ (hmem t ht)).comp_const_add τ₀ t
  have hφd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t => sweptAngle γ τ₀ (τ₀ + t))
      (ρ * E / (γ (τ₀ + t) : MinkowskiModel 3) 1 ^ 2) t := fun t ht => by
    rw [hℓ]
    exact (hasDerivAt_sweptAngle_eq_div hM x₀ hγ hso hsc h₀ (hmem t ht)).comp_const_add τ₀ t
  have hshift : Tendsto (fun t : ℝ => τ₀ + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop τ₀ tendsto_id
  obtain ⟨R, htail⟩ := integrableOn_angleDensity_light ρ E (2 * M / ρ) (ρ * E) hE
  have hmain := ProjectAinos.Mechanics.Scattering.tendsto_angle_atTop
    (r := fun t => (γ (τ₀ + t) : MinkowskiModel 3) 1)
    (v := fun t => deriv (fun t => (γ t : MinkowskiModel 3)) (τ₀ + t) 1)
    (φ := fun t => sweptAngle γ τ₀ (τ₀ + t))
    (fun t ht => (hrd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hrd t ht.le) (fun t ht => hv _ (lt_add_of_pos_right τ₀ ht))
    (fun t ht => radial_sq_eq_speedSq hM x₀ hγ hsc h₀ (hmem t ht.le) hκ hE.ne')
    (radius_pos_light hM _)
    (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hφd t ht.le) (hinf.comp hshift) htail
  have hzero : sweptAngle γ τ₀ (τ₀ + 0) = 0 := by
    rw [add_zero, sweptAngle, intervalIntegral.integral_same]
  simp only [add_zero] at hmain
  rw [show sweptAngle γ τ₀ τ₀ = 0 by simpa using hzero, zero_add] at hmain
  refine ⟨hmain.1, ?_⟩
  have hback : Tendsto (fun τ : ℝ => τ - τ₀) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-τ₀) tendsto_id
  refine (hmain.2.comp hback).congr fun τ => ?_
  simp

/-- The angle swept by the two halves of the ray: twice the angle from the closest approach to
infinity tends to `π − χ`, with the angle of deflection
`χ = deflectionAngle (ρ E) (speedSq (fun u => −u³) ρ E (2M/ρ)) r(τ₀)` of Landau–Lifshitz
(18.1). The incoming half is not formalized: it sweeps the same angle by the reflection of the
parameter. -/
theorem tendsto_two_mul_sweptAngle_atTop (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s)
    (hsc : Convex ℝ s) {τ₀ : ℝ} (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0)
    (hE : 0 < energy hM x₀ γ τ₀)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) :
    Tendsto (fun τ => 2 * sweptAngle γ τ₀ τ) atTop
      (𝓝 (π - deflectionAngle (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
        (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
          (2 * M / impactParameter hM x₀ γ τ₀)) ((γ τ₀ : MinkowskiModel 3) 1))) := by
  rw [deflectionAngle, sub_sub_cancel]
  exact (tendsto_sweptAngle_atTop hM x₀ hγ hso hsc hs hκ hE hv hinf).2.const_mul 2

/-! ### The closest approach -/

/-- The radicand `h(2M/ρ, u) = 1 − u² + (2M/ρ) u³` of a ray is positive for
`0 ≤ u < ρ/r(τ₀)`: the values `u = ρ/r(τ)` with `τ > τ₀` cover `(0, ρ/r(τ₀))`, and there
`ṙ² = E² h > 0`. -/
theorem radicand_pos_light (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₀ : ℝ}
    (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0) (hE : 0 < energy hM x₀ γ τ₀)
    (hL : 0 < angularMomentumSq hM x₀ γ τ₀)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) {u : ℝ}
    (hu : u ∈ Ico 0 (impactParameter hM x₀ γ τ₀ / (γ τ₀ : MinkowskiModel 3) 1)) :
    0 < radicand (fun u => -u ^ 3) (2 * M / impactParameter hM x₀ γ τ₀, u) := by
  set ρ := impactParameter hM x₀ γ τ₀
  have hρ : 0 < ρ := impactParameter_pos hM x₀ γ hE hL
  have hr₀ := radius_pos_light hM (γ τ₀)
  rcases hu.1.eq_or_lt with h0 | hu0
  · rw [← h0]
    simp [radicand]
  have hgt : (γ τ₀ : MinkowskiModel 3) 1 < ρ / u := by
    rw [lt_div_iff₀ hu0, mul_comm, ← lt_div_iff₀ hr₀]
    exact hu.2
  obtain ⟨τ, hτ, hτr⟩ := intermediate_value_Ici ((continuousOn_radius_light hγ).mono hs) hinf
    (mem_Ici.mpr hgt.le)
  have hτ₀ : τ₀ < τ := by
    refine lt_of_le_of_ne (mem_Ici.mp hτ) fun h => ?_
    rw [← h] at hτr
    exact (ne_of_lt hgt) hτr
  have hsq := radial_sq_eq_light hM x₀ hγ hsc (hs self_mem_Ici) (hs hτ) hκ hE.ne'
  have hu' : ρ / (γ τ : MinkowskiModel 3) 1 = u := by
    change ρ / (fun t => (γ t : MinkowskiModel 3) 1) τ = u
    rw [hτr]
    field_simp
  rw [hu'] at hsq
  have hpos : 0 < energy hM x₀ γ τ₀ ^ 2 *
      radicand (fun u => -u ^ 3) (2 * M / ρ, u) := by
    rw [← hsq]
    exact pow_pos (hv τ hτ₀) 2
  exact pos_of_mul_pos_right hpos (sq_nonneg _)

/-- **The closest approach of a ray** (Landau–Lifshitz, §101). For a ray with `ṙ(τ₀) = 0`,
increasing radius after `τ₀` and `r → ∞`, the value `u₀ = ρ/r(τ₀)` is the first positive zero of
the radicand `1 − u² + (2M/ρ) u³`; so every closest approach `c` of the small-angle scattering
library, `IsClosest (fun u => −u³) (2M/ρ) c`, is `u₀`. -/
theorem closest_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₀ : ℝ}
    (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0) (hE : 0 < energy hM x₀ γ τ₀)
    (hL : 0 < angularMomentumSq hM x₀ γ τ₀)
    (hr₀ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) {c : ℝ}
    (hc : IsClosest (fun u => -u ^ 3) (2 * M / impactParameter hM x₀ γ τ₀) c) :
    c = impactParameter hM x₀ γ τ₀ / (γ τ₀ : MinkowskiModel 3) 1 := by
  set ρ := impactParameter hM x₀ γ τ₀
  have hρ : 0 < ρ := impactParameter_pos hM x₀ γ hE hL
  have hpos0 := radius_pos_light hM (γ τ₀)
  have hzero : radicand (fun u => -u ^ 3) (2 * M / ρ, ρ / (γ τ₀ : MinkowskiModel 3) 1) = 0 := by
    have hsq := radial_sq_eq_light hM x₀ hγ hsc (hs self_mem_Ici) (hs self_mem_Ici) hκ hE.ne'
    rw [hr₀, zero_pow two_ne_zero] at hsq
    have hE2 : energy hM x₀ γ τ₀ ^ 2 ≠ 0 := pow_ne_zero 2 hE.ne'
    exact (mul_eq_zero.mp hsq.symm).resolve_left hE2
  rcases lt_trichotomy c (ρ / (γ τ₀ : MinkowskiModel 3) 1) with hlt | heq | hgt
  · have h := radicand_pos_light hM x₀ hγ hsc hs hκ hE hL hv hinf ⟨hc.pos.le, hlt⟩
    rw [hc.radicand_eq_zero] at h
    exact absurd h (lt_irrefl 0)
  · exact heq
  · have h := hc.radicand_pos contDiff_neg_cube ⟨(div_pos hρ hpos0).le, hgt⟩
    rw [hzero] at h
    exact absurd h (lt_irrefl 0)

/-- **The closest approach is a root of the small-angle library** (Landau–Lifshitz, §101). There
is `δ > 0` such that for every ray as in `closest_eq` with `2M/ρ ≤ δ`, the value `ρ/r(τ₀)` is
the closest approach: `IsClosest (fun u => −u³) (2M/ρ) (ρ/r(τ₀))`. The `δ` is that of
`deflection_bound`. -/
theorem exists_isClosest_light :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
      (s : Set ℝ) (τ₀ : ℝ), (metric hM).toLorentzMetric.IsGeodesicOn s γ → Convex ℝ s →
      Ici τ₀ ⊆ s → normalization hM γ τ₀ = 0 → 0 < energy hM x₀ γ τ₀ →
      0 < angularMomentumSq hM x₀ γ τ₀ →
      deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0 →
      (∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) →
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop →
      2 * M / impactParameter hM x₀ γ τ₀ ≤ δ →
      IsClosest (fun u => -u ^ 3) (2 * M / impactParameter hM x₀ γ τ₀)
        (impactParameter hM x₀ γ τ₀ / (γ τ₀ : MinkowskiModel 3) 1) := by
  obtain ⟨δ, hδ, C, hC⟩ := LightDeflection.exists_abs_deflectionAngle_schwarzschild_add_le
  refine ⟨δ, hδ, fun M hM x₀ γ s τ₀ hγ hsc hs hκ hE hL hr₀ hv hinf hε => ?_⟩
  obtain ⟨c, hc, -⟩ := hC M (impactParameter hM x₀ γ τ₀) (impactParameter_pos hM x₀ γ hE hL)
    hM hε
  rwa [← closest_eq hM x₀ hγ hsc hs hκ hE hL hr₀ hv hinf hc]

/-! ### The deflection of light -/

/-- **The deflection of light** (Landau–Lifshitz, §101, (101.9)), in units `G = c = 1`. There
are `δ > 0` and `C` such that for every ray of the Schwarzschild field of a mass `M ≥ 0`, with
the closest approach at `τ₀` (`ṙ(τ₀) = 0`, `ṙ > 0` after it, `r → ∞`), the energy `E > 0`, the
angular momentum `L > 0` and the impact parameter `ρ = L/E` with `2M/ρ ≤ δ`, the angle of
deflection `χ = deflectionAngle (ρ E) (speedSq (fun u => −u³) ρ E (2M/ρ)) r(τ₀)` satisfies
`|χ + 4M/ρ| ≤ C (M/ρ)²`. The angle `χ` is negative for an attraction: the ray is turned towards
the centre by `4M/ρ`. For `M > 0` the existence of such a ray is not constructed here;
`exists_ray_zero_mass` gives one for `M = 0`. -/
theorem deflection_bound :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (M : ℝ) (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
      (s : Set ℝ) (τ₀ : ℝ), (metric hM).toLorentzMetric.IsGeodesicOn s γ → Convex ℝ s →
      Ici τ₀ ⊆ s → normalization hM γ τ₀ = 0 → 0 < energy hM x₀ γ τ₀ →
      0 < angularMomentumSq hM x₀ γ τ₀ →
      deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0 →
      (∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) →
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop →
      2 * M / impactParameter hM x₀ γ τ₀ ≤ δ →
      |deflectionAngle (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
          (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
            (2 * M / impactParameter hM x₀ γ τ₀)) ((γ τ₀ : MinkowskiModel 3) 1) +
        4 * M / impactParameter hM x₀ γ τ₀| ≤ C * (M / impactParameter hM x₀ γ τ₀) ^ 2 := by
  obtain ⟨δ, hδ, C, hC⟩ := LightDeflection.exists_abs_deflectionAngle_schwarzschild_add_le
  refine ⟨δ, hδ, C, fun M hM x₀ γ s τ₀ hγ hsc hs hκ hE hL hr₀ hv hinf hε => ?_⟩
  have hρ := impactParameter_pos hM x₀ γ hE hL
  obtain ⟨c, hc, hbound⟩ := hC M (impactParameter hM x₀ γ τ₀) hρ hM hε
  have hceq := closest_eq hM x₀ hγ hsc hs hκ hE hL hr₀ hv hinf hc
  have hr : impactParameter hM x₀ γ τ₀ / c = (γ τ₀ : MinkowskiModel 3) 1 := by
    rw [hceq]
    field_simp
  have h := hbound (energy hM x₀ γ τ₀) hE
  rwa [hr] at h

/-- **The deflection of light as the angle swept by the ray** (Landau–Lifshitz, §101, (101.9)).
There are `δ > 0` and `C` such that for every ray as in `deflection_bound`, given on an open
convex set, the angle `Φ` swept in the plane of the motion from the closest approach to infinity
exists and satisfies `|2Φ − π − 4M/ρ| ≤ C (M/ρ)²`: the two halves of the ray sweep `π + 4M/ρ`,
more than the angle `π` of a straight line. -/
theorem deflection_bound_sweptAngle :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (M : ℝ) (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
      (s : Set ℝ) (τ₀ : ℝ), (metric hM).toLorentzMetric.IsGeodesicOn s γ → IsOpen s →
      Convex ℝ s → Ici τ₀ ⊆ s → normalization hM γ τ₀ = 0 → 0 < energy hM x₀ γ τ₀ →
      0 < angularMomentumSq hM x₀ γ τ₀ →
      deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0 →
      (∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) →
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop →
      2 * M / impactParameter hM x₀ γ τ₀ ≤ δ →
      ∃ Φ : ℝ, Tendsto (fun τ => sweptAngle γ τ₀ τ) atTop (𝓝 Φ) ∧
        |2 * Φ - π - 4 * M / impactParameter hM x₀ γ τ₀| ≤
          C * (M / impactParameter hM x₀ γ τ₀) ^ 2 := by
  obtain ⟨δ, hδ, C, hC⟩ := deflection_bound
  refine ⟨δ, hδ, C, fun M hM x₀ γ s τ₀ hγ hso hsc hs hκ hE hL hr₀ hv hinf hε => ?_⟩
  have h := hC M hM x₀ γ s τ₀ hγ hsc hs hκ hE hL hr₀ hv hinf hε
  refine ⟨_, (tendsto_sweptAngle_atTop hM x₀ hγ hso hsc hs hκ hE hv hinf).2, ?_⟩
  rw [deflectionAngle] at h
  rw [← abs_neg]
  convert h using 2
  ring

/-! ### Regression: the straight ray without a mass -/

private theorem mem_domain_straightRay (t : ℝ) :
    (![t, √(1 + t ^ 2), π / 2, Real.arctan t] : MinkowskiModel 3) ∈ domain 0 :=
  ⟨by simp; positivity, by simp; positivity, by simp; linarith [Real.pi_pos]⟩

private def straightRay (t : ℝ) : domain 0 :=
  ⟨![t, √(1 + t ^ 2), π / 2, Real.arctan t], mem_domain_straightRay t⟩

private def straightRayVel (t : ℝ) : MinkowskiModel 3 :=
  ![1, t / √(1 + t ^ 2), 0, 1 / (1 + t ^ 2)]

private def straightRayAcc (t : ℝ) : MinkowskiModel 3 :=
  ![0, 1 / ((1 + t ^ 2) * √(1 + t ^ 2)), 0, -(2 * t) / (1 + t ^ 2) ^ 2]

private theorem hasDerivAt_sqrt_one_add_sq (t : ℝ) :
    HasDerivAt (fun t : ℝ => √(1 + t ^ 2)) (t / √(1 + t ^ 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add 1
  have h := h1.sqrt (by positivity)
  convert h using 1
  field_simp

private theorem hasDerivAt_straightRay (t : ℝ) :
    HasDerivAt (fun t => (straightRay t : MinkowskiModel 3)) (straightRayVel t) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [straightRay, straightRayVel] using hasDerivAt_id' t
  · simpa [straightRay, straightRayVel] using hasDerivAt_sqrt_one_add_sq t
  · simpa [straightRay, straightRayVel] using hasDerivAt_const t (π / 2)
  · simpa [straightRay, straightRayVel] using Real.hasDerivAt_arctan t

private theorem hasDerivAt_straightRayVel (t : ℝ) :
    HasDerivAt straightRayVel (straightRayAcc t) t := by
  have hs := (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + t ^ 2)).ne'
  have hq : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).pow 2).const_add 1
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [straightRayVel, straightRayAcc] using hasDerivAt_const t (1 : ℝ)
  · have h := (hasDerivAt_id' t).div (hasDerivAt_sqrt_one_add_sq t) hs
    change HasDerivAt (fun x => x / √(1 + x ^ 2)) (1 / ((1 + t ^ 2) * √(1 + t ^ 2))) t
    refine h.congr_deriv ?_
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    linear_combination Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + t ^ 2)
  · simpa [straightRayVel, straightRayAcc] using hasDerivAt_const t (0 : ℝ)
  · have h : HasDerivAt (fun x => (1 + x ^ 2)⁻¹) (-(2 * t) / (1 + t ^ 2) ^ 2) t := h1.inv hq
    change HasDerivAt (fun x => 1 / (1 + x ^ 2)) (-(2 * t) / (1 + t ^ 2) ^ 2) t
    simpa only [one_div] using h

private theorem deriv_straightRay :
    deriv (fun t => (straightRay t : MinkowskiModel 3)) = straightRayVel :=
  funext fun t => (hasDerivAt_straightRay t).deriv

private theorem isGeodesicOn_straightRay :
    (metric (le_refl (0 : ℝ))).toLorentzMetric.IsGeodesicOn univ straightRay := by
  have hc : ContDiff ℝ 2 (fun t => (straightRay t : MinkowskiModel 3)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · exact contDiff_id
    · simp only [straightRay]
      exact (contDiff_const.add (contDiff_id.pow 2)).sqrt fun t => by positivity
    · simpa [straightRay] using contDiff_const
    · simpa [straightRay] using Real.contDiff_arctan
  rw [(metric (le_refl (0 : ℝ))).isGeodesicOn_iff isOpen_univ hc.contDiffOn]
  intro t _ k
  rw [deriv_straightRay, (hasDerivAt_straightRayVel t).deriv]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [christoffelOf_metric (le_refl (0 : ℝ)) (straightRay t).2]]
  have hs := (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + t ^ 2)).ne'
  have hq : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have hsq : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  fin_cases k <;> simp [Fin.sum_univ_four, christoffel, straightRay, straightRayVel,
    straightRayAcc]
  · field_simp
    linear_combination (-1 : ℝ) * hsq
  · field_simp
    linear_combination (-2 * t) * hsq

private theorem radius_straightRay (t : ℝ) :
    (straightRay t : MinkowskiModel 3) 1 = √(1 + t ^ 2) := rfl

private theorem radialRate_straightRay (t : ℝ) :
    deriv (fun t => (straightRay t : MinkowskiModel 3)) t 1 = t / √(1 + t ^ 2) := by
  rw [deriv_straightRay]
  rfl

/-- **A regression instance of the deflection of light**: the straight null line
`τ ↦ (τ, √(1 + τ²), π/2, arctan τ)` of the field of the mass `M = 0`, a ray with the closest
approach `r = 1` at `τ = 0`, the energy `E = 1` and `L² = 1`, so `ρ = 1`. It satisfies every
hypothesis of `deflection_bound` and `deflection_bound_sweptAngle` with `s = univ` and `τ₀ = 0`,
and the angle it sweeps from the closest approach to infinity is `π/2`. -/
theorem exists_ray_zero_mass :
    ∃ (x₀ : domain 0) (γ : ℝ → domain 0),
      (metric (le_refl (0 : ℝ))).toLorentzMetric.IsGeodesicOn univ γ ∧
      normalization (le_refl (0 : ℝ)) γ 0 = 0 ∧ energy (le_refl (0 : ℝ)) x₀ γ 0 = 1 ∧
      angularMomentumSq (le_refl (0 : ℝ)) x₀ γ 0 = 1 ∧
      deriv (fun t => (γ t : MinkowskiModel 3)) 0 1 = 0 ∧
      (∀ τ, 0 < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) ∧
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop ∧
      Tendsto (fun τ => sweptAngle γ 0 τ) atTop (𝓝 (π / 2)) := by
  have hd (t : ℝ) := (hasDerivAt_straightRay t).differentiableAt
  refine ⟨straightRay 0, straightRay, isGeodesicOn_straightRay, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normalization, form_curveVelocity_eq_coord (le_refl (0 : ℝ)) (hd 0), deriv_straightRay]
    simp [straightRay, straightRayVel]
  · rw [energy_eq_coord (le_refl (0 : ℝ)) _ (hd 0), deriv_straightRay]
    simp [straightRayVel]
  · rw [angularMomentumSq_eq_coord (le_refl (0 : ℝ)) _ (hd 0), deriv_straightRay]
    simp [straightRay, straightRayVel]
  · rw [radialRate_straightRay]
    simp
  · intro τ hτ
    rw [radialRate_straightRay]
    positivity
  · refine tendsto_atTop_mono (fun τ => ?_) tendsto_id
    rw [radius_straightRay]
    calc τ ≤ |τ| := le_abs_self τ
      _ = √(τ ^ 2) := (Real.sqrt_sq_eq_abs τ).symm
      _ ≤ √(1 + τ ^ 2) := Real.sqrt_le_sqrt (by linarith)
  · have h (τ : ℝ) : sweptAngle straightRay 0 τ = Real.arctan τ := by
      rw [sweptAngle_equatorial (le_refl (0 : ℝ)) isGeodesicOn_straightRay isOpen_univ
        convex_univ (fun σ _ => rfl) (fun σ _ => ?_) (mem_univ 0) (mem_univ τ)]
      · simp [straightRay]
      · rw [deriv_straightRay]
        change 0 ≤ 1 / (1 + σ ^ 2)
        positivity
    simp only [h]
    exact Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds

/- The regression through `deflection_bound`: the straight ray has the impact parameter `ρ = 1`
and the angle of deflection `χ = 0`, that is `∫_1^∞ dr/(r² √(1 − 1/r²)) = π/2`. -/
example : ∃ (x₀ : domain 0) (γ : ℝ → domain 0),
    impactParameter (le_refl (0 : ℝ)) x₀ γ 0 = 1 ∧
      deflectionAngle (impactParameter (le_refl (0 : ℝ)) x₀ γ 0 * energy (le_refl (0 : ℝ)) x₀ γ 0)
        (speedSq (fun u => -u ^ 3) (impactParameter (le_refl (0 : ℝ)) x₀ γ 0)
          (energy (le_refl (0 : ℝ)) x₀ γ 0) (2 * 0 / impactParameter (le_refl (0 : ℝ)) x₀ γ 0))
        ((γ 0 : MinkowskiModel 3) 1) = 0 := by
  obtain ⟨x₀, γ, hγ, hκ, hE, hL, hr₀, hv, hinf, -⟩ := exists_ray_zero_mass
  obtain ⟨δ, hδ, C, hC⟩ := deflection_bound
  have hρ : impactParameter (le_refl (0 : ℝ)) x₀ γ 0 = 1 := by
    rw [impactParameter, hE, hL, Real.sqrt_one, div_one]
  refine ⟨x₀, γ, hρ, ?_⟩
  have h := hC 0 (le_refl 0) x₀ γ univ 0 hγ convex_univ (subset_univ _) hκ
    (by rw [hE]; exact one_pos) (by rw [hL]; exact one_pos) hr₀ hv hinf
    (by rw [hρ]; simpa using hδ.le)
  simp only [mul_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, abs_nonpos_iff] at h
  simpa only [mul_zero, zero_div] using h

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
