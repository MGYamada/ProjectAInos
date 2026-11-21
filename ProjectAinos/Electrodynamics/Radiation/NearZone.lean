/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Basic
import Mathlib.Tactic

/-!
# The field of the radiation at near distances

The exact field of a point dipole at the origin whose moment `d(t)` depends on the time
(Landau–Lifshitz, *The Classical Theory of Fields*, §72), in the units of the project: `c = 1` and
`div E = k⁰`, so that the potentials carry the factor `1/4π`. A point of space-time is `(t, x)` with
`r = ‖x‖`. On the open set `offOrigin` of the points with `r ≠ 0` all the functions below are
smooth; the definitions are global, with Lean's `x/0 = 0`, so the statements are made off the
origin.

* `radialProfile g k = g(t − r)/rᵏ` and the outgoing spherical wave
  `sphericalWave g = g(t − r)/4πr`, with their derivatives off the origin
  (`partialAt_radialProfile_zero`, `partialAt_radialProfile_succ`,
  `partialAt_partialAt_sphericalWave_succ`), and `box_sphericalWave`: **the spherical wave solves
  the wave equation** `box ψ = 0` off the origin, for `g` of class `C²`.
* `dipolePotential d`: the potential `φ = −div (d(t − r)/4πr)`, `𝐚 = ḋ(t − r)/4πr` of the dipole.
  `lorenz_dipolePotential`: the gauge of Lorenz `∂ₜφ + div 𝐚 = 0`; `box_dipolePotential`: every
  component solves the wave equation; `maxwell_dipolePotential`: **the field satisfies the
  equations of Maxwell in the vacuum** at every point with `r ≠ 0` (`maxwell_iff_box_of_lorenz` on
  `offOrigin`).
* `electricField_dipolePotential`, `magneticField_dipolePotential`: **the field at all
  distances**. At `x = rn` with `r > 0` and `‖n‖ = 1`, with `d, ḋ, d̈` at the retarded time `t − r`,
  `E = (1/4π) ((3n⟨n, d⟩ − d)/r³ + (3n⟨n, ḋ⟩ − ḋ)/r² + (n⟨n, d̈⟩ − d̈)/r)` and
  `B = (1/4π) (d̈/r + ḋ/r²) × n`. Every point off the origin has this form
  (`exists_eq_vector_smul`).
* `sphereFlux_eq`: **the flux through a sphere**. For `R > 0` the flux of the vector of Poynting
  through the sphere of radius `R` is the radiated power `(2/3)(1/4π) |d̈(t − R)|²` plus the
  derivative of `Q_R(t) = (1/6π) (|ḋ|²/R + ⟨d, ḋ⟩/R² + |d|²/2R³)` at `t − R` (`nearZoneEnergy`).
  On the sphere `S · n = (1/4π)² (⟨P, W⟩ − ⟨n, P⟩⟨n, W⟩)` with `P = d/R³ + ḋ/R² + d̈/R` and
  `W = d̈/R + ḋ/R²` (`poyntingVector_inner_dipolePotential`), and the second moment of the sphere
  gives `R² ∫ S · n dσ = (1/6π) ⟨d/R² + ḋ/R + d̈, d̈ + ḋ/R⟩`
  (`sphereFlux_dipolePotential_eq_inner`). The energy of the near zone is
  `Q_R = (1/12πR³) (|d + Rḋ|² + R²|ḋ|²) ≥ 0` (`nearZoneEnergy_eq`, `nearZoneEnergy_nonneg`).
* `tendsto_sphereFlux`: **the radiation limit**, at a fixed retarded time `u` the flux through the
  sphere of radius `R` at the time `u + R` tends to `(1/6π) |d̈(u)|²` as `R → ∞`.
* `integral_sphereFlux_eq`: for a moment of compact support in the time the energy that crosses
  the sphere of radius `R > 0` is `(1/6π) ∫ |d̈(u)|² du`, independent of `R`.
* Instances: `oscillatingMoment_instance`, for `d(t) = cos t · e₃` with `d̈ ≠ 0`, and
  `pulseMoment_instance`, for the pulse `d(t) = χ(t) e₃` of a smooth bump `χ`, whose radiated
  energy is positive.

The dipole is a point source given by its potential; the comparison with the retarded potential
of an extended source of small size is not made here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace ProjectAinos.Electrodynamics.Radiation.NearZone

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The radial calculus off the origin -/

/-- The set `r ≠ 0` of space-time off the world line of the origin. -/
def offOrigin : Set Spacetime := {v | space v ≠ 0}

/-- The set off the origin is open. -/
theorem isOpen_offOrigin : IsOpen offOrigin :=
  isOpen_ne_fun (space : Spacetime →L[ℝ] E3).continuous continuous_const

/-- The axis of the time has no spatial part. -/
theorem space_single_zero : space (Pi.single 0 1 : Spacetime) = 0 := by
  ext j
  simp [Fin.succ_ne_zero]

/-- The axis `i + 1` of space-time is the axis `eᵢ` of space. -/
theorem space_single_succ (i : Fin 3) :
    space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply, Fin.succ_inj]

/-- The derivative of a co-ordinate. -/
theorem partialAt_coord (ν μ : Fin 4) (v : Spacetime) :
    partialAt (fun w : Spacetime => w ν) μ v = (Pi.single μ 1 : Spacetime) ν := by
  rw [partialAt, show (fun w : Spacetime => w ν) =
    ⇑(ContinuousLinearMap.proj ν : Spacetime →L[ℝ] ℝ) from rfl, ContinuousLinearMap.fderiv]
  rfl

/-- The derivative of the distance `r = ‖x‖` off the origin. -/
theorem hasFDerivAt_radius {v : Spacetime} (hv : space v ≠ 0) :
    HasFDerivAt (fun w : Spacetime => ‖space w‖)
      ((‖space v‖⁻¹ • innerSL ℝ (space v)).comp (space : Spacetime →L[ℝ] E3)) v :=
  (Wave.hasFDerivAt_norm_of_ne_zero hv).comp v (space : Spacetime →L[ℝ] E3).hasFDerivAt

/-- The derivative of the retarded time `t − r` off the origin. -/
theorem hasFDerivAt_retardedTime {v : Spacetime} (hv : space v ≠ 0) :
    HasFDerivAt (fun w : Spacetime => w 0 - ‖space w‖)
      ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ) -
        (‖space v‖⁻¹ • innerSL ℝ (space v)).comp (space : Spacetime →L[ℝ] E3)) v :=
  (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).hasFDerivAt.sub (hasFDerivAt_radius hv)

/-- The profile `g(t − r)/rᵏ` of an outgoing spherical wave, with `r = ‖x‖`. -/
def radialProfile (g : ℝ → ℝ) (k : ℕ) (v : Spacetime) : ℝ :=
  g (v 0 - ‖space v‖) / ‖space v‖ ^ k

/-- The profile `g(t − r)/rᵏ` is differentiable off the origin, with the derivatives along the
axes of `partialAt_radialProfile_zero` and `partialAt_radialProfile_succ`. -/
theorem hasFDerivAt_radialProfile {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    ∃ L : Spacetime →L[ℝ] ℝ, HasFDerivAt (radialProfile g k) L v ∧
      L (Pi.single 0 1) = deriv g (v 0 - ‖space v‖) / ‖space v‖ ^ k ∧
      ∀ i : Fin 3, L (Pi.single i.succ 1) = -v i.succ *
        (deriv g (v 0 - ‖space v‖) / ‖space v‖ ^ (k + 1) +
          k * g (v 0 - ‖space v‖) / ‖space v‖ ^ (k + 2)) := by
  have hr : ‖space v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu := hg.hasDerivAt.comp_hasFDerivAt v (hasFDerivAt_retardedTime hv)
  have hp := ((hasDerivAt_inv (pow_ne_zero k hr)).comp_hasFDerivAt v
    ((hasFDerivAt_radius hv).pow k))
  have h := hu.mul hp
  refine ⟨_, h.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_), ?_, fun i => ?_⟩
  · simp only [radialProfile, Function.comp_apply, div_eq_mul_inv, Pi.mul_apply]
  · simp [space_single_zero]
    field_simp
  · obtain _ | m := k
    · simp [space_single_succ, EuclideanSpace.inner_single_right]
      field_simp
    · simp [space_single_succ, EuclideanSpace.inner_single_right]
      field_simp
      ring

/-- The derivative `∂ₜ (g(t − r)/rᵏ) = ġ(t − r)/rᵏ`. -/
theorem partialAt_radialProfile_zero {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    partialAt (radialProfile g k) 0 v = radialProfile (deriv g) k v := by
  obtain ⟨L, hL, h0, -⟩ := hasFDerivAt_radialProfile k hv hg
  rw [partialAt, hL.fderiv, h0]
  rfl

/-- The derivative `∂ᵢ (g(t − r)/rᵏ) = −xᵢ (ġ(t − r)/rᵏ⁺¹ + k g(t − r)/rᵏ⁺²)`. -/
theorem partialAt_radialProfile_succ {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) (i : Fin 3) :
    partialAt (radialProfile g k) i.succ v =
      -v i.succ * (radialProfile (deriv g) (k + 1) v + k * radialProfile g (k + 2) v) := by
  obtain ⟨L, hL, -, hi⟩ := hasFDerivAt_radialProfile k hv hg
  rw [partialAt, hL.fderiv, hi, radialProfile, radialProfile, mul_div_assoc]

/-- The profile `g(t − r)/rᵏ` is differentiable off the origin. -/
theorem differentiableAt_radialProfile {g : ℝ → ℝ} (k : ℕ) {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    DifferentiableAt ℝ (radialProfile g k) v :=
  (hasFDerivAt_radialProfile k hv hg).choose_spec.1.differentiableAt

/-- The distance `r = ‖x‖` is smooth off the origin. -/
theorem contDiffAt_radius {n : ℕ∞ω} {v : Spacetime} (hv : space v ≠ 0) :
    ContDiffAt ℝ n (fun w : Spacetime => ‖space w‖) v :=
  (contDiffAt_norm ℝ hv).comp v (space : Spacetime →L[ℝ] E3).contDiff.contDiffAt

/-- The profile `g(t − r)/rᵏ` of a `Cⁿ` function is `Cⁿ` off the origin. -/
theorem contDiffAt_radialProfile {n : ℕ∞ω} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) (k : ℕ)
    {v : Spacetime} (hv : space v ≠ 0) : ContDiffAt ℝ n (radialProfile g k) v := by
  have hr := contDiffAt_radius (n := n) hv
  have ht : ContDiffAt ℝ n (fun w : Spacetime => w 0) v :=
    (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).contDiff.contDiffAt
  exact (hg.contDiffAt.comp v (ht.sub hr)).div (hr.pow k)
    (pow_ne_zero k (norm_ne_zero_iff.mpr hv))

/-- `‖x‖² = Σᵢ xᵢ²` in the co-ordinates of space-time. -/
theorem norm_space_sq (v : Spacetime) : ‖space v‖ ^ 2 = ∑ i : Fin 3, v i.succ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-! ### The outgoing spherical wave -/

/-- The outgoing spherical wave `g(t − r)/(4πr)`, with `r = ‖x‖`. -/
def sphericalWave (g : ℝ → ℝ) (v : Spacetime) : ℝ :=
  g (v 0 - ‖space v‖) / (4 * π * ‖space v‖)

/-- The spherical wave is `(1/4π) g(t − r)/r`. -/
theorem sphericalWave_eq (g : ℝ → ℝ) :
    sphericalWave g = fun v => (4 * π)⁻¹ * radialProfile g 1 v := by
  funext v
  rw [sphericalWave, radialProfile, pow_one, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- The spherical wave of a `Cⁿ` function is `Cⁿ` off the origin. -/
theorem contDiffAt_sphericalWave {n : ℕ∞ω} {g : ℝ → ℝ} (hg : ContDiff ℝ n g) {v : Spacetime}
    (hv : space v ≠ 0) : ContDiffAt ℝ n (sphericalWave g) v := by
  rw [sphericalWave_eq]
  exact contDiffAt_const.mul (contDiffAt_radialProfile hg 1 hv)

/-- `∂ₜ (g(t − r)/4πr) = ġ(t − r)/4πr`. -/
theorem partialAt_sphericalWave_zero {g : ℝ → ℝ} {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) :
    partialAt (sphericalWave g) 0 v = sphericalWave (deriv g) v := by
  rw [sphericalWave_eq, sphericalWave_eq,
    partialAt_const_mul _ (differentiableAt_radialProfile 1 hv hg),
    partialAt_radialProfile_zero 1 hv hg]

/-- `∂ᵢ (g(t − r)/4πr) = −(1/4π) xᵢ (ġ(t − r)/r² + g(t − r)/r³)`. -/
theorem partialAt_sphericalWave_succ {g : ℝ → ℝ} {v : Spacetime} (hv : space v ≠ 0)
    (hg : DifferentiableAt ℝ g (v 0 - ‖space v‖)) (i : Fin 3) :
    partialAt (sphericalWave g) i.succ v =
      -(4 * π)⁻¹ * (v i.succ * (radialProfile (deriv g) 2 v + radialProfile g 3 v)) := by
  rw [sphericalWave_eq, partialAt_const_mul _ (differentiableAt_radialProfile 1 hv hg),
    partialAt_radialProfile_succ 1 hv hg]
  push_cast
  ring

/-- Near a point off the origin, `∂ₜ (g(t − r)/4πr) = ġ(t − r)/4πr`. -/
theorem partialAt_sphericalWave_zero_eventuallyEq {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {v : Spacetime} (hv : space v ≠ 0) :
    partialAt (sphericalWave g) 0 =ᶠ[𝓝 v] sphericalWave (deriv g) :=
  Filter.eventuallyEq_of_mem (isOpen_offOrigin.mem_nhds hv) fun _ hw =>
    partialAt_sphericalWave_zero hw (hg _)

/-- Near a point off the origin, `∂ᵢ (g(t − r)/4πr) = −(1/4π) xᵢ (ġ/r² + g/r³)`. -/
theorem partialAt_sphericalWave_succ_eventuallyEq {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {v : Spacetime} (hv : space v ≠ 0) (i : Fin 3) :
    partialAt (sphericalWave g) i.succ =ᶠ[𝓝 v] fun w =>
      -(4 * π)⁻¹ * (w i.succ * (radialProfile (deriv g) 2 w + radialProfile g 3 w)) :=
  Filter.eventuallyEq_of_mem (isOpen_offOrigin.mem_nhds hv) fun _ hw =>
    partialAt_sphericalWave_succ hw (hg _) i

/-- The second spatial derivatives of the spherical wave:
`∂ⱼ∂ᵢ (g(t − r)/4πr) = (1/4π) (xᵢxⱼ (g̈/r³ + 3ġ/r⁴ + 3g/r⁵) − δᵢⱼ (ġ/r² + g/r³))`. -/
theorem partialAt_partialAt_sphericalWave_succ {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {v : Spacetime} (hv : space v ≠ 0) (i j : Fin 3) :
    partialAt (partialAt (sphericalWave g) i.succ) j.succ v =
      (4 * π)⁻¹ * (v i.succ * v j.succ * (radialProfile (deriv (deriv g)) 3 v +
          3 * radialProfile (deriv g) 4 v + 3 * radialProfile g 5 v) -
        (if i = j then 1 else 0) * (radialProfile (deriv g) 2 v + radialProfile g 3 v)) := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg2 : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hc : DifferentiableAt ℝ (fun w : Spacetime => w i.succ) v :=
    (ContinuousLinearMap.proj i.succ : Spacetime →L[ℝ] ℝ).differentiableAt
  have h1 := differentiableAt_radialProfile 2 hv (hg2 _)
  have h2 := differentiableAt_radialProfile 3 hv (hg1 _)
  have h12 : DifferentiableAt ℝ (fun w => radialProfile (deriv g) 2 w + radialProfile g 3 w) v :=
    h1.add h2
  have hf : DifferentiableAt ℝ
      (fun w : Spacetime => w i.succ * (radialProfile (deriv g) 2 w + radialProfile g 3 w)) v :=
    hc.mul h12
  rw [partialAt_congr_of_eventuallyEq (partialAt_sphericalWave_succ_eventuallyEq hg1 hv i),
    partialAt_const_mul _ hf, partialAt_mul hc h12, partialAt_add h1 h2, partialAt_coord,
    partialAt_radialProfile_succ 2 hv (hg2 _), partialAt_radialProfile_succ 3 hv (hg1 _)]
  simp only [Pi.single_apply, Fin.succ_inj]
  push_cast
  ring

/-- `∂ₜ² (g(t − r)/4πr) = g̈(t − r)/4πr`. -/
theorem partialAt_partialAt_sphericalWave_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {v : Spacetime} (hv : space v ≠ 0) :
    partialAt (partialAt (sphericalWave g) 0) 0 v = sphericalWave (deriv (deriv g)) v := by
  rw [partialAt_congr_of_eventuallyEq
      (partialAt_sphericalWave_zero_eventuallyEq (hg.differentiable (by norm_num)) hv),
    partialAt_sphericalWave_zero hv (hg.differentiable_deriv_two _)]

/-- **The outgoing spherical wave solves the wave equation off the origin**:
`box (g(t − r)/4πr) = 0` for `r ≠ 0` and `g` of class `C²`. -/
theorem box_sphericalWave {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {v : Spacetime}
    (hv : space v ≠ 0) : box (sphericalWave g) v = 0 := by
  have hr : ‖space v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hn := norm_space_sq v
  rw [box, partialAt_partialAt_sphericalWave_zero hg hv]
  simp only [partialAt_partialAt_sphericalWave_succ hg hv, ↓reduceIte, one_mul]
  rw [Fin.sum_univ_three] at hn ⊢
  simp only [sphericalWave, radialProfile]
  field_simp
  linear_combination (-deriv (deriv g) (v 0 - ‖space v‖) * ‖space v‖ ^ 2 -
    3 * deriv g (v 0 - ‖space v‖) * ‖space v‖ - 3 * g (v 0 - ‖space v‖)) * hn

/-! ### The potential of a point dipole -/

/-- The components `dⱼ` of a `Cⁿ` curve in space are `Cⁿ`. -/
theorem contDiff_coord {n : ℕ∞ω} {d : ℝ → E3} (hd : ContDiff ℝ n d) (j : Fin 3) :
    ContDiff ℝ n fun s => d s j :=
  (EuclideanSpace.proj j : E3 →L[ℝ] ℝ).contDiff.comp hd

/-- The derivative of a component of a curve is the component of its derivative. -/
theorem deriv_coord {d : ℝ → E3} (hd : Differentiable ℝ d) (j : Fin 3) :
    deriv (fun s => d s j) = fun s => deriv d s j := by
  funext s
  exact ((EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
    (hd s).hasDerivAt).deriv

/-- The potential of a point dipole with the moment `d(t)` at the origin (Landau–Lifshitz, §72),
in the units of the project: `φ = −div (d(t − r)/4πr)` and `𝐚 = ḋ(t − r)/4πr`. -/
def dipolePotential (d : ℝ → E3) : Potential :=
  potentialOf (fun v => -divergence3 (fun j => sphericalWave fun s => d s j) v)
    fun v i => sphericalWave (fun s => deriv d s i) v

/-- The time component `A₀ = −φ = div (d(t − r)/4πr)` of the potential of the dipole. -/
theorem potentialComponent_dipolePotential_zero (d : ℝ → E3) :
    potentialComponent (dipolePotential d) 0 =
      fun v => ∑ j : Fin 3, partialAt (sphericalWave fun s => d s j) j.succ v := by
  rw [dipolePotential, CavityModes.potentialComponent_potentialOf_zero]
  funext v
  rw [neg_neg]
  rfl

/-- The spatial components `aᵢ = ḋᵢ(t − r)/4πr` of the potential of the dipole. -/
theorem potentialComponent_dipolePotential_succ (d : ℝ → E3) (i : Fin 3) :
    potentialComponent (dipolePotential d) i.succ = sphericalWave fun s => deriv d s i :=
  CavityModes.potentialComponent_potentialOf_succ _ _ i

/-- The potential of a smooth moment is smooth off the origin. -/
theorem contDiffAt_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime}
    (hv : space v ≠ 0) : ContDiffAt ℝ ∞ (dipolePotential d) v := by
  have hd' : ContDiff ℝ ∞ (deriv d) := (contDiff_infty_iff_deriv.mp hd).2
  have hφ : ContDiffAt ℝ ∞
      (fun w => -divergence3 (fun j => sphericalWave fun s => d s j) w) v := by
    simp only [divergence3]
    exact (ContDiffAt.sum fun j _ => contDiffAt_partialAt
      (contDiffAt_sphericalWave (contDiff_coord hd j) hv) (by simp) j.succ).neg
  have ha : ∀ i : Fin 3, ContDiffAt ℝ ∞ (fun w => sphericalWave (fun s => deriv d s i) w) v :=
    fun i => contDiffAt_sphericalWave (contDiff_coord hd' i) hv
  unfold dipolePotential potentialOf
  exact oneCovector.symm.contDiff.contDiffAt.comp v
    ((hφ.neg.smul contDiffAt_const).add (ContDiffAt.sum fun i _ => (ha i).smul contDiffAt_const))

/-- **The gauge of Lorenz** off the origin: `∂ₜφ + div 𝐚 = 0`, since
`∂ₜ div (d(t − r)/4πr) = div (ḋ(t − r)/4πr)`. -/
theorem lorenz_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime}
    (hv : space v ≠ 0) : lorenzDivergence (dipolePotential d) v = 0 := by
  have hdd : Differentiable ℝ d := hd.differentiable (by simp)
  have hψ : ∀ j : Fin 3, ContDiffAt ℝ ∞ (sphericalWave fun s => d s j) v := fun j =>
    contDiffAt_sphericalWave (contDiff_coord hd j) hv
  have hdiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (partialAt (sphericalWave fun s => d s j) j.succ) v := fun j =>
    (contDiffAt_partialAt (m := 1) (hψ j) (by simp) j.succ).differentiableAt one_ne_zero
  have hcomm : ∀ j : Fin 3, partialAt (partialAt (sphericalWave fun s => d s j) j.succ) 0 v =
      partialAt (sphericalWave fun s => deriv d s j) j.succ v := fun j => by
    rw [partialAt_partialAt_comm ((hψ j).of_le (by simp)) 0 j.succ,
      partialAt_congr_of_eventuallyEq (partialAt_sphericalWave_zero_eventuallyEq
        ((contDiff_coord hd j).differentiable (by simp)) hv), deriv_coord hdd j]
  rw [lorenzDivergence, potentialComponent_dipolePotential_zero,
    partialAt_sum _ fun j _ => hdiff j]
  simp only [potentialComponent_dipolePotential_succ, hcomm]
  ring

/-- Every component of the potential of the dipole solves the wave equation off the origin. -/
theorem box_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime}
    (hv : space v ≠ 0) (ν : Fin 4) : box (potentialComponent (dipolePotential d) ν) v = 0 := by
  have hd' : ContDiff ℝ ∞ (deriv d) := (contDiff_infty_iff_deriv.mp hd).2
  refine Fin.cases ?_ (fun i => ?_) ν
  · have hψ : ∀ j : Fin 3, ContDiffAt ℝ ∞ (sphericalWave fun s => d s j) v := fun j =>
      contDiffAt_sphericalWave (contDiff_coord hd j) hv
    have hp : ∀ j : Fin 3,
        ContDiffAt ℝ 2 (partialAt (sphericalWave fun s => d s j) j.succ) v := fun j =>
      contDiffAt_partialAt (hψ j) (by simp) j.succ
    have hb : ∀ j : Fin 3, box (partialAt (sphericalWave fun s => d s j) j.succ) v = 0 :=
      fun j => by
        have hev : box (sphericalWave fun s => d s j) =ᶠ[𝓝 v] fun _ => 0 :=
          Filter.eventuallyEq_of_mem (isOpen_offOrigin.mem_nhds hv) fun _ hw =>
            box_sphericalWave ((contDiff_coord hd j).of_le (by simp)) hw
        rw [box_partialAt ((hψ j).of_le (by simp)), partialAt_congr_of_eventuallyEq hev,
          partialAt_const]
    rw [potentialComponent_dipolePotential_zero]
    simp only [Fin.sum_univ_three]
    rw [box_add ((hp 0).add (hp 1)) (hp 2), box_add (hp 0) (hp 1), hb, hb, hb]
    ring
  · rw [potentialComponent_dipolePotential_succ]
    exact box_sphericalWave ((contDiff_coord hd' i).of_le (by simp)) hv

/-- **The equations of Maxwell in the vacuum off the origin**: the field of the potential of the
dipole satisfies `div B = 0`, `∂ₜB + curl E = 0`, `div E = 0` and `curl B − ∂ₜE = 0` at every
point with `r ≠ 0`. -/
theorem maxwell_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime}
    (hv : space v ≠ 0) : CavityModes.VacuumMaxwellAt (dipolePotential d) v := by
  have h := maxwell_iff_box_of_lorenz isOpen_offOrigin (A := dipolePotential d)
    (fun y hy => ((contDiffAt_dipolePotential hd hy).of_le (by simp)).contDiffWithinAt)
    (fun y hy => lorenz_dipolePotential hd hy) (fun _ => 0)
  have hm := h.mpr (fun y hy => ⟨by simpa using box_dipolePotential hd hy 0,
    fun i => by simpa using box_dipolePotential hd hy i.succ⟩) v hv
  simpa [CavityModes.VacuumMaxwellAt] using hm

/-! ### The field of the dipole at all distances -/

/-- The inner product of space in the co-ordinates. -/
theorem inner_eq_sum (x y : E3) : ⟪x, y⟫ = ∑ j : Fin 3, x j * y j := by
  simp [PiLp.inner_apply, mul_comm]

/-- The electric field `Eᵢ = ∂ᵢA₀ − ∂ₜaᵢ` of the dipole in the co-ordinates of space-time. -/
theorem electricField_dipolePotential_apply {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {v : Spacetime}
    (hv : space v ≠ 0) (i : Fin 3) :
    electricField (fieldTensor (dipolePotential d)) i v =
      ∑ j : Fin 3, (4 * π)⁻¹ * (v j.succ * v i.succ *
          (radialProfile (fun s => deriv (deriv d) s j) 3 v +
            3 * radialProfile (fun s => deriv d s j) 4 v +
            3 * radialProfile (fun s => d s j) 5 v) -
        (if j = i then 1 else 0) *
          (radialProfile (fun s => deriv d s j) 2 v + radialProfile (fun s => d s j) 3 v)) -
      sphericalWave (fun s => deriv (deriv d) s i) v := by
  have hA := contDiffAt_dipolePotential hd hv
  have hdd : Differentiable ℝ d := hd.differentiable (by simp)
  have hd' : ContDiff ℝ ∞ (deriv d) := (contDiff_infty_iff_deriv.mp hd).2
  have hdd' : Differentiable ℝ (deriv d) := hd'.differentiable (by simp)
  have hdiff : ∀ j : Fin 3,
      DifferentiableAt ℝ (partialAt (sphericalWave fun s => d s j) j.succ) v := fun j =>
    (contDiffAt_partialAt (m := 1) (contDiffAt_sphericalWave (contDiff_coord hd j) hv)
      (by simp) j.succ).differentiableAt one_ne_zero
  rw [(electricField_fieldTensor_eventuallyEq (hA.of_le (by simp)) i).eq_of_nhds]
  dsimp only
  rw [potentialComponent_dipolePotential_zero, potentialComponent_dipolePotential_succ,
    partialAt_sum _ fun j _ => hdiff j,
    partialAt_sphericalWave_zero hv ((contDiff_coord hd' i).differentiable (by simp) _),
    deriv_coord hdd' i]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialAt_partialAt_sphericalWave_succ ((contDiff_coord hd j).of_le (by simp)) hv j i,
    deriv_coord hdd j, deriv_coord hdd' j]

/-- Every point off the origin is `(t, rn)` with `r > 0` and `‖n‖ = 1`. -/
theorem exists_eq_vector_smul {v : Spacetime} (hv : space v ≠ 0) :
    ∃ r : ℝ, ∃ n : E3, 0 < r ∧ ‖n‖ = 1 ∧ v = vector (v 0) (r • n) := by
  have hr : ‖space v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨‖space v‖, ‖space v‖⁻¹ • space v, norm_pos_iff.mpr hv, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr]
  · rw [smul_inv_smul₀ hr]
    exact (vector_time_space v).symm

/-- At `(t, rn)` with `r > 0` and `‖n‖ = 1` the distance is `r`. -/
theorem space_vector_smul {r : ℝ} (hr : 0 < r) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    ‖space (vector t (r • n))‖ = r ∧ space (vector t (r • n)) ≠ 0 := by
  have hrn : ‖r • n‖ = r := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hn, mul_one]
  rw [space_vector]
  refine ⟨hrn, fun h => ?_⟩
  rw [h, norm_zero] at hrn
  linarith

/-- **The electric field of the dipole at all distances** (Landau–Lifshitz, §72): at the point
`x = rn` with `r > 0` and `‖n‖ = 1`, with the moment and its derivatives at the retarded time
`t − r`,
`E = (1/4π) ((3n⟨n, d⟩ − d)/r³ + (3n⟨n, ḋ⟩ − ḋ)/r² + (n⟨n, d̈⟩ − d̈)/r)`. -/
theorem electricField_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {r : ℝ} (hr : 0 < r)
    {n : E3} (hn : ‖n‖ = 1) (t : ℝ) (i : Fin 3) :
    electricField (fieldTensor (dipolePotential d)) i (vector t (r • n)) =
      (4 * π)⁻¹ * ((3 * ⟪n, d (t - r)⟫ * n i - d (t - r) i) / r ^ 3 +
        (3 * ⟪n, deriv d (t - r)⟫ * n i - deriv d (t - r) i) / r ^ 2 +
        (⟪n, deriv (deriv d) (t - r)⟫ * n i - deriv (deriv d) (t - r) i) / r) := by
  obtain ⟨hrn, hv⟩ := space_vector_smul hr hn t
  rw [electricField_dipolePotential_apply hd hv i]
  simp only [radialProfile, sphericalWave, hrn, vector_zero, vector_succ, PiLp.smul_apply,
    smul_eq_mul, inner_eq_sum, Fin.sum_univ_three]
  have hr0 : r ≠ 0 := hr.ne'
  fin_cases i <;> simp <;> field_simp <;> ring

/-- **The magnetic field of the dipole at all distances** (Landau–Lifshitz, §72): at the point
`x = rn` with `r > 0` and `‖n‖ = 1`, with the derivatives of the moment at the retarded time
`t − r`, `B = (1/4π) (d̈/r + ḋ/r²) × n`. -/
theorem magneticField_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {r : ℝ} (hr : 0 < r)
    {n : E3} (hn : ‖n‖ = 1) (t : ℝ) (i : Fin 3) :
    magneticField (fieldTensor (dipolePotential d)) i (vector t (r • n)) =
      (4 * π)⁻¹ * crossProduct
        (WithLp.ofLp (r⁻¹ • deriv (deriv d) (t - r) + (r ^ 2)⁻¹ • deriv d (t - r)))
        (WithLp.ofLp n) i := by
  obtain ⟨hrn, hv⟩ := space_vector_smul hr hn t
  have hA := contDiffAt_dipolePotential hd hv
  have hd' : ContDiff ℝ ∞ (deriv d) := (contDiff_infty_iff_deriv.mp hd).2
  have hdd' : Differentiable ℝ (deriv d) := hd'.differentiable (by simp)
  have ha : ∀ k j : Fin 3,
      partialAt (potentialComponent (dipolePotential d) k.succ) j.succ (vector t (r • n)) =
        -(4 * π)⁻¹ * (r * n j *
          (deriv (deriv d) (t - r) k / r ^ 2 + deriv d (t - r) k / r ^ 3)) := fun k j => by
    rw [potentialComponent_dipolePotential_succ,
      partialAt_sphericalWave_succ hv ((contDiff_coord hd' k).differentiable (by simp) _),
      deriv_coord hdd' k]
    simp only [radialProfile, hrn, vector_zero, vector_succ, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨h0, h1, h2⟩ := magneticField_fieldTensor_eventuallyEq (hA.of_le (by simp))
  have hr0 : r ≠ 0 := hr.ne'
  fin_cases i
  · refine h0.eq_of_nhds.trans ?_
    show partialAt (potentialComponent _ (Fin.succ 2)) (Fin.succ 1) _ -
      partialAt (potentialComponent _ (Fin.succ 1)) (Fin.succ 2) _ = _
    rw [ha, ha]
    simp [cross_apply]
    field_simp
    ring
  · refine h1.eq_of_nhds.trans ?_
    show partialAt (potentialComponent _ (Fin.succ 0)) (Fin.succ 2) _ -
      partialAt (potentialComponent _ (Fin.succ 2)) (Fin.succ 0) _ = _
    rw [ha, ha]
    simp [cross_apply]
    field_simp
    ring
  · refine h2.eq_of_nhds.trans ?_
    show partialAt (potentialComponent _ (Fin.succ 1)) (Fin.succ 0) _ -
      partialAt (potentialComponent _ (Fin.succ 0)) (Fin.succ 1) _ = _
    rw [ha, ha]
    simp [cross_apply]
    field_simp
    ring

/-! ### The flux through a sphere -/

/-- The normal component of the vector of Poynting of the dipole on the sphere of radius `R`:
`S · n = (1/4π)² (⟨P, W⟩ − ⟨n, P⟩⟨n, W⟩)` with `P = d/R³ + ḋ/R² + d̈/R` and `W = d̈/R + ḋ/R²` at the
retarded time `t − R`, since `E = (1/4π) (n⟨n, 3d/R³ + 3ḋ/R² + d̈/R⟩ − P)` and
`B = (1/4π) W × n`. -/
theorem poyntingVector_inner_dipolePotential {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {R : ℝ}
    (hR : 0 < R) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    ∑ i : Fin 3, poyntingVector (fieldTensor (dipolePotential d)) i (vector t (R • n)) * n i =
      (4 * π)⁻¹ ^ 2 *
        (⟪(R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) + R⁻¹ • deriv (deriv d) (t - R),
            R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)⟫ -
          ⟪n, (R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) +
            R⁻¹ • deriv (deriv d) (t - R)⟫ *
          ⟪n, R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)⟫) := by
  have hn2 : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq n
    rw [hn, Fin.sum_univ_three] at h
    linarith
  simp only [Fin.sum_univ_three, poyntingVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    electricField_dipolePotential hd hR hn, magneticField_dipolePotential hd hR hn]
  set a := d (t - R)
  set b := deriv d (t - R)
  set c := deriv (deriv d) (t - R)
  simp only [cross_apply, inner_eq_sum, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (4 * π)⁻¹ ^ 2 *
    (((R ^ 3)⁻¹ * a 0 + (R ^ 2)⁻¹ * b 0 + R⁻¹ * c 0) * (R⁻¹ * c 0 + (R ^ 2)⁻¹ * b 0) +
      ((R ^ 3)⁻¹ * a 1 + (R ^ 2)⁻¹ * b 1 + R⁻¹ * c 1) * (R⁻¹ * c 1 + (R ^ 2)⁻¹ * b 1) +
      ((R ^ 3)⁻¹ * a 2 + (R ^ 2)⁻¹ * b 2 + R⁻¹ * c 2) * (R⁻¹ * c 2 + (R ^ 2)⁻¹ * b 2)) * hn2

/-- The flux of the vector of Poynting of the dipole through the sphere of radius `R` is
`R² (1/6π) ⟨P, W⟩`, from the moments `∫ dσ = 4π` and `∫ ⟨n, P⟩⟨n, W⟩ dσ = (4π/3) ⟨P, W⟩`. -/
theorem sphereFlux_dipolePotential_eq_inner {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {R : ℝ}
    (hR : 0 < R) (t : ℝ) :
    sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      R ^ 2 * ((6 * π)⁻¹ *
        ⟪(R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) + R⁻¹ • deriv (deriv d) (t - R),
          R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)⟫) := by
  set P := (R ^ 3)⁻¹ • d (t - R) + (R ^ 2)⁻¹ • deriv d (t - R) + R⁻¹ • deriv (deriv d) (t - R)
  set W := R⁻¹ • deriv (deriv d) (t - R) + (R ^ 2)⁻¹ • deriv d (t - R)
  have hpt : ∀ n : sphere (0 : E3) 1,
      ∑ i : Fin 3, poyntingVector (fieldTensor (dipolePotential d)) i (vector t (R • (n : E3))) *
        (n : E3) i = (4 * π)⁻¹ ^ 2 * (⟪P, W⟫ - ⟪(n : E3), P⟫ * ⟪(n : E3), W⟫) := fun n =>
    poyntingVector_inner_dipolePotential hd hR (mem_sphere_zero_iff_norm.mp n.2) t
  have hint : Integrable (fun n : sphere (0 : E3) 1 => ⟪(n : E3), P⟫ * ⟪(n : E3), W⟫)
      sphereMeasure := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    fun_prop
  rw [sphereFlux, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_sub (integrable_const _) hint, integral_const, integral_inner_mul_inner,
    sphereMeasure_real_univ, smul_eq_mul]
  field_simp
  ring

/-- The energy `Q_R(t) = (1/6π) (|ḋ|²/R + ⟨d, ḋ⟩/R² + |d|²/2R³)` of the near zone of the sphere of
radius `R`, with the moment and its derivative at the retarded time `t − R`. -/
def nearZoneEnergy (d : ℝ → E3) (R t : ℝ) : ℝ :=
  (6 * π)⁻¹ * (‖deriv d (t - R)‖ ^ 2 / R + ⟪d (t - R), deriv d (t - R)⟫ / R ^ 2 +
    ‖d (t - R)‖ ^ 2 / (2 * R ^ 3))

/-- The energy of the near zone is a sum of squares,
`Q_R = (1/12πR³) (|d + Rḋ|² + R²|ḋ|²)`, so it is not negative for `R > 0`. -/
theorem nearZoneEnergy_eq {d : ℝ → E3} {R : ℝ} (hR : 0 < R) (t : ℝ) :
    nearZoneEnergy d R t = (12 * π * R ^ 3)⁻¹ *
      (‖d (t - R) + R • deriv d (t - R)‖ ^ 2 + R ^ 2 * ‖deriv d (t - R)‖ ^ 2) := by
  rw [nearZoneEnergy, norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs,
    abs_of_pos hR]
  field_simp
  ring

/-- The energy of the near zone is not negative. -/
theorem nearZoneEnergy_nonneg {d : ℝ → E3} {R : ℝ} (hR : 0 < R) (t : ℝ) :
    0 ≤ nearZoneEnergy d R t := by
  rw [nearZoneEnergy_eq hR]
  positivity

/-- The derivative of the energy of the near zone,
`dQ_R/dt = (1/6π) (2⟨ḋ, d̈⟩/R + (|ḋ|² + ⟨d, d̈⟩)/R² + ⟨d, ḋ⟩/R³)` at the retarded time `t − R`. -/
theorem hasDerivAt_nearZoneEnergy {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) (R t : ℝ) :
    HasDerivAt (nearZoneEnergy d R)
      ((6 * π)⁻¹ * (2 * ⟪deriv d (t - R), deriv (deriv d) (t - R)⟫ / R +
        (‖deriv d (t - R)‖ ^ 2 + ⟪d (t - R), deriv (deriv d) (t - R)⟫) / R ^ 2 +
        ⟪d (t - R), deriv d (t - R)⟫ / R ^ 3)) t := by
  have hdd : Differentiable ℝ d := hd.differentiable (by simp)
  have hdd' : Differentiable ℝ (deriv d) :=
    (contDiff_infty_iff_deriv.mp hd).2.differentiable (by simp)
  have h0 : HasDerivAt (fun s => d (s - R)) (deriv d (t - R)) t :=
    (hdd _).hasDerivAt.comp_sub_const t R
  have h1 : HasDerivAt (fun s => deriv d (s - R)) (deriv (deriv d) (t - R)) t :=
    (hdd' _).hasDerivAt.comp_sub_const t R
  have h := (((h1.norm_sq.div_const R).fun_add ((h0.inner ℝ h1).div_const (R ^ 2))).fun_add
    (h0.norm_sq.div_const (2 * R ^ 3))).const_mul (6 * π)⁻¹
  refine h.congr_deriv ?_
  rw [real_inner_self_eq_norm_sq]
  ring

/-- **The flux of the dipole through a sphere** (Landau–Lifshitz, §72): for `R > 0` the flux of
the vector of Poynting through the sphere of radius `R` is the power `(2/3)(1/4π) |d̈(t − R)|²`
radiated at the retarded time, `(2/3)(1/4π) = 1/6π`, plus the derivative of the energy
`Q_R` of the near zone (`nearZoneEnergy`). -/
theorem sphereFlux_eq {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      2 / 3 * (4 * π)⁻¹ * ‖deriv (deriv d) (t - R)‖ ^ 2 + deriv (nearZoneEnergy d R) t := by
  rw [sphereFlux_dipolePotential_eq_inner hd hR t, (hasDerivAt_nearZoneEnergy hd R t).deriv]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, RCLike.conj_to_real,
    real_inner_comm (deriv (deriv d) (t - R)) (deriv d (t - R))]
  field_simp
  ring

/-- **The radiation limit**: at a fixed retarded time `u`, the flux through the sphere of radius
`R` at the time `u + R` tends to the radiated power `(1/6π) |d̈(u)|²` as `R → ∞`; the derivative of
the energy of the near zone is `O(1/R)`. -/
theorem tendsto_sphereFlux {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) (u : ℝ) :
    Tendsto (fun R => sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) (u + R) R)
      atTop (𝓝 ((6 * π)⁻¹ * ‖deriv (deriv d) u‖ ^ 2)) := by
  set A := 2 * ⟪deriv d u, deriv (deriv d) u⟫
  set B := ‖deriv d u‖ ^ 2 + ⟪d u, deriv (deriv d) u⟫
  set C := ⟪d u, deriv d u⟫
  have h : ∀ᶠ R in atTop,
      2 / 3 * (4 * π)⁻¹ * ‖deriv (deriv d) u‖ ^ 2 +
          (6 * π)⁻¹ * (A * R⁻¹ + B * R⁻¹ ^ 2 + C * R⁻¹ ^ 3) =
        sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) (u + R) R := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sphereFlux_eq hd hR, (hasDerivAt_nearZoneEnergy hd R _).deriv, add_sub_cancel_right]
    ring
  refine Tendsto.congr' h ?_
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h0 := ((tendsto_const_nhds (x := A)).mul hi).add
    (((tendsto_const_nhds (x := B)).mul (hi.pow 2)).add
      ((tendsto_const_nhds (x := C)).mul (hi.pow 3)))
  have h1 := (tendsto_const_nhds (x := 2 / 3 * (4 * π)⁻¹ * ‖deriv (deriv d) u‖ ^ 2)).add
    (h0.const_mul (6 * π)⁻¹)
  convert h1 using 2
  · ring
  · simp only [mul_zero, add_zero, zero_pow two_ne_zero, zero_pow three_ne_zero]
    ring

/-- **The energy radiated by a pulse** (Landau–Lifshitz, §72): for a moment of compact support in
the time, the flux through the sphere of radius `R > 0` integrated over all times is
`(1/6π) ∫ |d̈(u)|² du`, independent of `R`; the energy `Q_R` of the near zone integrates out. -/
theorem integral_sphereFlux_eq {d : ℝ → E3} (hd : ContDiff ℝ ∞ d) (hc : HasCompactSupport d)
    {R : ℝ} (hR : 0 < R) :
    ∫ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      (6 * π)⁻¹ * ∫ u, ‖deriv (deriv d) u‖ ^ 2 := by
  have hd' : ContDiff ℝ ∞ (deriv d) := (contDiff_infty_iff_deriv.mp hd).2
  have hd'' : ContDiff ℝ ∞ (deriv (deriv d)) := (contDiff_infty_iff_deriv.mp hd').2
  have h0 : Continuous d := hd.continuous
  have h1 : Continuous (deriv d) := hd'.continuous
  have h2 : Continuous (deriv (deriv d)) := hd''.continuous
  have hz : ∀ u, u ∉ tsupport d → d u = 0 ∧ deriv d u = 0 ∧ deriv (deriv d) u = 0 :=
    fun u hu => ⟨image_eq_zero_of_notMem_tsupport hu,
      image_eq_zero_of_notMem_tsupport fun h => hu (tsupport_deriv_subset h),
      image_eq_zero_of_notMem_tsupport fun h => hu (tsupport_deriv_subset
        (tsupport_deriv_subset h))⟩
  have hf : Integrable fun u => ‖deriv (deriv d) u‖ ^ 2 := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hc.mono' fun u hu => ?_)
    by_contra hn
    exact hu (by simp [(hz u hn).2.2])
  set q' : ℝ → ℝ := fun u => (6 * π)⁻¹ * (2 * ⟪deriv d u, deriv (deriv d) u⟫ / R +
    (‖deriv d u‖ ^ 2 + ⟪d u, deriv (deriv d) u⟫) / R ^ 2 + ⟪d u, deriv d u⟫ / R ^ 3) with hq'_def
  set q : ℝ → ℝ := fun u => (6 * π)⁻¹ * (‖deriv d u‖ ^ 2 / R + ⟪d u, deriv d u⟫ / R ^ 2 +
    ‖d u‖ ^ 2 / (2 * R ^ 3)) with hq_def
  have hq' : Integrable q' := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hc.mono' fun u hu => ?_)
    by_contra hn
    obtain ⟨e0, e1, e2⟩ := hz u hn
    exact hu (by simp [hq'_def, e0, e1, e2])
  have hq : Integrable q := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hc.mono' fun u hu => ?_)
    by_contra hn
    obtain ⟨e0, e1, -⟩ := hz u hn
    exact hu (by simp [hq_def, e0, e1])
  have hflux : ∀ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential d))) t R =
      2 / 3 * (4 * π)⁻¹ * ‖deriv (deriv d) (t - R)‖ ^ 2 + q' (t - R) := fun t => by
    rw [sphereFlux_eq hd hR t, (hasDerivAt_nearZoneEnergy hd R t).deriv]
  have hQ : ∫ t, q' (t - R) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable (f := nearZoneEnergy d R)
      (fun t => hasDerivAt_nearZoneEnergy hd R t) (hq'.comp_sub_right R) (hq.comp_sub_right R)
  rw [integral_congr_ae (Eventually.of_forall hflux),
    integral_add ((hf.comp_sub_right R).const_mul _) (hq'.comp_sub_right R), hQ,
    integral_const_mul, integral_sub_right_eq_self (fun u => ‖deriv (deriv d) u‖ ^ 2) R]
  ring

/-! ### Instances -/

/-- The oscillating moment `d(t) = cos t · e₃`. -/
def oscillatingMoment (t : ℝ) : E3 := Real.cos t • EuclideanSpace.single 2 1

/-- The oscillating moment is smooth. -/
theorem contDiff_oscillatingMoment : ContDiff ℝ ∞ oscillatingMoment :=
  Real.contDiff_cos.smul contDiff_const

/-- `ḋ = −sin t · e₃`. -/
theorem deriv_oscillatingMoment :
    deriv oscillatingMoment = fun t => -Real.sin t • EuclideanSpace.single 2 1 := by
  funext t
  exact ((Real.hasDerivAt_cos t).smul_const _).deriv

/-- `d̈ = −cos t · e₃`. -/
theorem deriv_deriv_oscillatingMoment :
    deriv (deriv oscillatingMoment) = fun t => -Real.cos t • EuclideanSpace.single 2 1 := by
  rw [deriv_oscillatingMoment]
  funext t
  exact ((Real.hasDerivAt_sin t).fun_neg.smul_const _).deriv

/-- **An instance**: the oscillating moment `d(t) = cos t · e₃`, whose second derivative
`d̈ = −cos t · e₃` is not zero. Off the origin its potential is in the gauge of Lorenz and its
field satisfies the equations of Maxwell in the vacuum, and the flux through the sphere of radius
`R > 0` is `(2/3)(1/4π) cos²(t − R) + dQ_R/dt`. -/
theorem oscillatingMoment_instance :
    deriv (deriv oscillatingMoment) ≠ 0 ∧
      (∀ v : Spacetime, space v ≠ 0 →
        lorenzDivergence (dipolePotential oscillatingMoment) v = 0 ∧
          CavityModes.VacuumMaxwellAt (dipolePotential oscillatingMoment) v) ∧
      ∀ R : ℝ, 0 < R → ∀ t : ℝ,
        sphereFlux (poyntingVector (fieldTensor (dipolePotential oscillatingMoment))) t R =
          2 / 3 * (4 * π)⁻¹ * Real.cos (t - R) ^ 2 +
            deriv (nearZoneEnergy oscillatingMoment R) t := by
  refine ⟨fun h => ?_, fun v hv => ⟨lorenz_dipolePotential contDiff_oscillatingMoment hv,
    maxwell_dipolePotential contDiff_oscillatingMoment hv⟩, fun R hR t => ?_⟩
  · have h0 := congrArg (fun x : E3 => x 2) (congrFun h 0)
    simp [deriv_deriv_oscillatingMoment] at h0
  · rw [sphereFlux_eq contDiff_oscillatingMoment hR, deriv_deriv_oscillatingMoment]
    simp [norm_smul]

/-- A function on the line with compact support and the derivative zero vanishes. -/
theorem eq_zero_of_deriv_eq_zero {g : ℝ → ℝ} (hg : Differentiable ℝ g) (hc : HasCompactSupport g)
    (h : ∀ x, deriv g x = 0) (x : ℝ) : g x = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, y ∉ tsupport g := by
    by_contra hn
    push Not at hn
    exact hc.isCompact.ne_univ (eq_univ_of_forall hn)
  rw [is_const_of_deriv_eq_zero hg h x y]
  exact image_eq_zero_of_notMem_tsupport hy

/-- A smooth bump `χ` on the line, `χ = 1` on `[−1, 1]` with the support in `[−2, 2]`. -/
def timeBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The second derivative of the bump is not identically zero. -/
theorem exists_deriv_deriv_timeBump_ne_zero : ∃ x, deriv (deriv timeBump) x ≠ 0 := by
  by_contra hn
  push Not at hn
  have hs : ContDiff ℝ ∞ timeBump := timeBump.contDiff
  have h1 := eq_zero_of_deriv_eq_zero
    ((contDiff_infty_iff_deriv.mp hs).2.differentiable (by simp)) timeBump.hasCompactSupport.deriv
    hn
  have h0 := eq_zero_of_deriv_eq_zero (hs.differentiable (by simp)) timeBump.hasCompactSupport h1 0
  rw [timeBump.one_of_mem_closedBall (by simp [timeBump])] at h0
  exact one_ne_zero h0

/-- The pulse `d(t) = χ(t) · e₃`, a moment of compact support in the time. -/
def pulseMoment (t : ℝ) : E3 := timeBump t • EuclideanSpace.single 2 1

/-- The pulse is smooth. -/
theorem contDiff_pulseMoment : ContDiff ℝ ∞ pulseMoment :=
  timeBump.contDiff.smul contDiff_const

/-- The pulse has compact support in the time. -/
theorem hasCompactSupport_pulseMoment : HasCompactSupport pulseMoment :=
  timeBump.hasCompactSupport.smul_right

/-- `d̈ = χ̈(t) e₃`. -/
theorem deriv_deriv_pulseMoment :
    deriv (deriv pulseMoment) = fun t => deriv (deriv timeBump) t • EuclideanSpace.single 2 1 := by
  have hs : ContDiff ℝ ∞ timeBump := timeBump.contDiff
  have hs' : ContDiff ℝ ∞ (deriv timeBump) := (contDiff_infty_iff_deriv.mp hs).2
  have h1 : deriv pulseMoment = fun t => deriv timeBump t • EuclideanSpace.single 2 1 := by
    funext t
    exact deriv_smul_const ((hs.differentiable (by simp)) t) _
  rw [h1]
  funext t
  exact deriv_smul_const ((hs'.differentiable (by simp)) t) _

/-- **An instance of the energy radiated by a pulse**: for the pulse `d(t) = χ(t) · e₃` and every
`R > 0`, the flux through the sphere of radius `R` integrated over all times is
`(1/6π) ∫ |d̈|²`, and it is positive. -/
theorem pulseMoment_instance {R : ℝ} (hR : 0 < R) :
    ∫ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential pulseMoment))) t R =
        (6 * π)⁻¹ * ∫ u, ‖deriv (deriv pulseMoment) u‖ ^ 2 ∧
      0 < ∫ t, sphereFlux (poyntingVector (fieldTensor (dipolePotential pulseMoment))) t R := by
  have h := integral_sphereFlux_eq contDiff_pulseMoment hasCompactSupport_pulseMoment hR
  refine ⟨h, ?_⟩
  rw [h]
  obtain ⟨x, hx⟩ := exists_deriv_deriv_timeBump_ne_zero
  have hs : ContDiff ℝ ∞ timeBump := timeBump.contDiff
  have hs'' : ContDiff ℝ ∞ (deriv (deriv timeBump)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hs).2).2
  have hc : Continuous fun u => ‖deriv (deriv pulseMoment) u‖ ^ 2 := by
    rw [deriv_deriv_pulseMoment]
    exact (hs''.continuous.smul continuous_const).norm.pow 2
  have hint : Integrable fun u => ‖deriv (deriv pulseMoment) u‖ ^ 2 :=
    hc.integrable_of_hasCompactSupport
      (hasCompactSupport_pulseMoment.deriv.deriv.comp_left (g := fun y : E3 => ‖y‖ ^ 2) (by simp))
  refine mul_pos (by positivity) ?_
  rw [integral_pos_iff_support_of_nonneg (fun u => by positivity) hint]
  refine IsOpen.measure_pos volume hc.isOpen_support ⟨x, ?_⟩
  simp [deriv_deriv_pulseMoment, norm_smul, hx]

end ProjectAinos.Electrodynamics.Radiation.NearZone
