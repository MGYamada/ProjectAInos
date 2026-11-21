/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Basic
public import ProjectAinos.SmoothGeometry.Wave.FarField
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# The field of a system of charges at large distances

The units have `div E = k⁰` and `c = 1`. A current `k` on space-time is **localized** if, written
in `(t, x)`, it vanishes for `‖x‖ > a` at all times (`Wave.LocalizedSupport`). At the point
`(u + R, Rn)` at the distance `R` in the direction `n` of the unit sphere and the retarded time
`u`, the field `F = dA` of the retarded potential is, to leading order in `1/R`, the field of a
plane wave (Landau–Lifshitz, *The Classical Theory of Fields*, §66):

  `R B → ∂ᵤÃ × n = −n × ∂ᵤÃ`,  `R E → n⟨n, ∂ᵤÃ⟩ − ∂ᵤÃ = n × (n × ∂ᵤÃ)`,

with the spatial components `∂ᵤÃᵢ = radiationAmplitude (currentRate k) u n (i + 1)`
(`amplitudeRate`). The limits are `farMagnetic` and `farElectric`.

* `radiationAmplitude_currentRate_zero`: **the conservation of the charge** gives
  `∂ᵤφ̃ = ⟨n, ∂ᵤÃ⟩` for the time component.
* `electricField_retardedPotential`, `magneticField_retardedPotential`: `E = −∇φ − ∂ₜ𝐚` and
  `B = curl 𝐚` with the derivatives of the retarded integrals.
* `tendstoUniformlyOn_mul_electricField`, `tendstoUniformlyOn_mul_magneticField`: the limits,
  uniformly for `u` in a compact set and `n` on the unit sphere.
* `farElectric_eq_cross`: `E = B × n` to leading order, so `E ⊥ n`, `B ⊥ n`, `|E| = |B|` and the
  vector of Poynting `S = E × B = |B|² n` points outwards: its radial component `radialCross` is
  `|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩² = |n × ∂ᵤÃ|²` (`farPoynting_eq`).
* `tendsto_sphereFlux_poynting`: **the radiated power**, the flux of the vector of Poynting
  through the sphere of radius `R` at the time `u + R` tends to `radiatedPower k u` as `R → ∞`.
* `exists_bound_mul_electricField_sub`, `exists_bound_mul_magneticField_sub`: the remainders of
  `R E` and `R B` are `O(1/R)`, uniformly, and `exists_bound_electricField_sub_cross`:
  `E − B × n = O(1/R²)`, uniformly.
* An instance: `circulatingCurrent` has localized support (`localizedSupport_circulatingCurrent`)
  and the theorems apply to it (`tendstoUniformlyOn_mul_field_circulatingCurrent`,
  `tendsto_sphereFlux_poynting_circulatingCurrent`,
  `exists_bound_electricField_sub_cross_circulatingCurrent`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The far fields -/

/-- The component `k^μ(t, x)` of a current, written as a function of time and space. -/
def splitComponent (k : Spacetime → Spacetime) (μ : Fin 4) : ℝ × E3 → ℝ := fun p =>
  k (Wave.timeSpaceEquiv.symm p) μ

/-- The spatial components `∂ᵤÃᵢ(u, n)` of the amplitude of the far field of `∂₀k`. -/
def amplitudeRate (k : Spacetime → Spacetime) (u : ℝ) (n : E3) : Fin 3 → ℝ := fun i =>
  radiationAmplitude (currentRate k) u n i.succ

/-- The magnetic far field `∂ᵤÃ × n = −n × ∂ᵤÃ`, the limit of `R B`. -/
def farMagnetic (k : Spacetime → Spacetime) (u : ℝ) (n : E3) : Fin 3 → ℝ :=
  crossProduct (amplitudeRate k u n) ⇑n

/-- The electric far field `n⟨n, ∂ᵤÃ⟩ − ∂ᵤÃ`, the limit of `R E`; it is `n × (n × ∂ᵤÃ)` for a
unit vector `n`. -/
def farElectric (k : Spacetime → Spacetime) (u : ℝ) (n : E3) : Fin 3 → ℝ := fun i =>
  n i * ∑ j, n j * amplitudeRate k u n j - amplitudeRate k u n i

/-- The sum of the squares of the components of a unit vector is `1`. -/
theorem sum_sq_of_norm_eq_one {n : E3} (hn : ‖n‖ = 1) : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq n
  rw [hn, Fin.sum_univ_three] at h
  rw [← h]
  norm_num

/-- **The far field is transverse**: `E = B × n` to leading order, for a unit vector `n`. -/
theorem farElectric_eq_cross (k : Spacetime → Spacetime) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    farElectric k u n = crossProduct (farMagnetic k u n) ⇑n := by
  have h := sum_sq_of_norm_eq_one hn
  funext i
  fin_cases i
  · simp only [farElectric, farMagnetic, cross_apply, Fin.sum_univ_three]
    simp
    linear_combination amplitudeRate k u n 0 * h
  · simp only [farElectric, farMagnetic, cross_apply, Fin.sum_univ_three]
    simp
    linear_combination amplitudeRate k u n 1 * h
  · simp only [farElectric, farMagnetic, cross_apply, Fin.sum_univ_three]
    simp
    linear_combination amplitudeRate k u n 2 * h

/-- The radial component `⟨e × b, n⟩` of the cross product of two vectors. -/
def radialCross (e b : Fin 3 → ℝ) (n : E3) : ℝ := ∑ i, crossProduct e b i * n i

/-- The radial component of the cross product in components. -/
theorem radialCross_eq (e b : Fin 3 → ℝ) (n : E3) :
    radialCross e b n = (e 1 * b 2 - e 2 * b 1) * n 0 + (e 2 * b 0 - e 0 * b 2) * n 1 +
      (e 0 * b 1 - e 1 * b 0) * n 2 := by
  simp [radialCross, cross_apply, Fin.sum_univ_three]

/-- The bound `|⟨e × b, n⟩| ≤ 6XY` for `|eᵢ| ≤ X`, `|bᵢ| ≤ Y` and `|nᵢ| ≤ 1`. -/
private theorem abs_radialCross_le {e b : Fin 3 → ℝ} {n : E3} {X Y : ℝ}
    (he : ∀ i, |e i| ≤ X) (hb : ∀ i, |b i| ≤ Y) (hn : ∀ i, |n i| ≤ 1) :
    |radialCross e b n| ≤ 6 * (X * Y) := by
  have hX : 0 ≤ X := (abs_nonneg _).trans (he 0)
  have hY : 0 ≤ Y := (abs_nonneg _).trans (hb 0)
  have h : ∀ i j l, |e i * b j * n l| ≤ X * Y := by
    intro i j l
    rw [abs_mul, abs_mul]
    exact (mul_le_mul (mul_le_mul (he i) (hb j) (abs_nonneg _) hX) (hn l) (abs_nonneg _)
      (mul_nonneg hX hY)).trans_eq (mul_one _)
  have hP : radialCross e b n = e 1 * b 2 * n 0 - e 2 * b 1 * n 0 + e 2 * b 0 * n 1 -
      e 0 * b 2 * n 1 + e 0 * b 1 * n 2 - e 1 * b 0 * n 2 := by
    rw [radialCross_eq]
    ring
  rw [hP, abs_le]
  have h1 := abs_le.mp (h 1 2 0)
  have h2 := abs_le.mp (h 2 1 0)
  have h3 := abs_le.mp (h 2 0 1)
  have h4 := abs_le.mp (h 0 2 1)
  have h5 := abs_le.mp (h 0 1 2)
  have h6 := abs_le.mp (h 1 0 2)
  constructor <;> linarith

/-- The radial component of the cross product of convergent vectors converges. -/
private theorem tendsto_radialCross {ι : Type*} {l : Filter ι} {e b : ι → Fin 3 → ℝ}
    (e₀ b₀ : Fin 3 → ℝ) (n : E3) (he : ∀ i, Tendsto (fun x => e x i) l (𝓝 (e₀ i)))
    (hb : ∀ i, Tendsto (fun x => b x i) l (𝓝 (b₀ i))) :
    Tendsto (fun x => radialCross (e x) (b x) n) l (𝓝 (radialCross e₀ b₀ n)) := by
  simp only [radialCross_eq]
  exact (((((he 1).mul (hb 2)).sub ((he 2).mul (hb 1))).mul tendsto_const_nhds).add
    ((((he 2).mul (hb 0)).sub ((he 0).mul (hb 2))).mul tendsto_const_nhds)).add
    ((((he 0).mul (hb 1)).sub ((he 1).mul (hb 0))).mul tendsto_const_nhds)

/-- **The radiated flux in a direction**: the radial component of the vector of Poynting of the far
field is `⟨E × B, n⟩ = |∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩² = |n × ∂ᵤÃ|²` for a unit vector `n`. -/
theorem farPoynting_eq (k : Spacetime → Spacetime) (u : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    radialCross (farElectric k u n) (farMagnetic k u n) n =
      (∑ i : Fin 3, radiationAmplitude (currentRate k) u n i.succ ^ 2) -
        (∑ i : Fin 3, n i * radiationAmplitude (currentRate k) u n i.succ) ^ 2 := by
  have h := sum_sq_of_norm_eq_one hn
  rw [radialCross_eq]
  simp only [farElectric, farMagnetic, cross_apply, Fin.sum_univ_three, amplitudeRate]
  simp
  linear_combination (radiationAmplitude (currentRate k) u n 1 ^ 2 +
    radiationAmplitude (currentRate k) u n 2 ^ 2 + radiationAmplitude (currentRate k) u n 3 ^ 2) * h

/-! ### The fields of the retarded potential in time and space -/

/-- The derivative along the axis of the time of the retarded integral on space-time is the time
derivative of the retarded integral in `(t, x)`. -/
theorem partialAt_retardedScalar_zero {g : Spacetime → ℝ} (hg : ContDiff ℝ 1 g) {ρ v₀ : ℝ}
    (hs : Wave.SubluminalSupport ρ v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (v : Spacetime) :
    partialAt (retardedScalar g) 0 v =
      Wave.timeDeriv (Wave.retardedIntegral fun p => g (Wave.timeSpaceEquiv.symm p))
        (Wave.timeSpaceEquiv v) :=
  congrFun (Wave.fderiv_comp_timeSpaceEquiv_zero fun p =>
    (Wave.hasFDerivAt_retardedIntegral (hg.comp Wave.timeSpaceEquiv.symm.contDiff) hs
      p).differentiableAt) v

/-- The derivative along the axis `i + 1` of the retarded integral on space-time is the spatial
derivative `∂ᵢ` of the retarded integral in `(t, x)`. -/
theorem partialAt_retardedScalar_succ {g : Spacetime → ℝ} (hg : ContDiff ℝ 1 g) {ρ v₀ : ℝ}
    (hs : Wave.SubluminalSupport ρ v₀ fun p => g (Wave.timeSpaceEquiv.symm p)) (i : Fin 3)
    (v : Spacetime) :
    partialAt (retardedScalar g) i.succ v =
      Wave.spaceDeriv i (Wave.retardedIntegral fun p => g (Wave.timeSpaceEquiv.symm p))
        (Wave.timeSpaceEquiv v) :=
  congrFun (Wave.fderiv_comp_timeSpaceEquiv_succ (fun p =>
    (Wave.hasFDerivAt_retardedIntegral (hg.comp Wave.timeSpaceEquiv.symm.contDiff) hs
      p).differentiableAt) i) v

/-- The time derivative of a function of space-time written in `(t, x)`. -/
theorem timeDeriv_comp_symm {g : Spacetime → ℝ} (hg : Differentiable ℝ g) (p : ℝ × E3) :
    Wave.timeDeriv (fun q => g (Wave.timeSpaceEquiv.symm q)) p =
      partialAt g 0 (Wave.timeSpaceEquiv.symm p) := by
  rw [Wave.timeDeriv, fderiv_comp_timeSpaceEquiv_symm hg, partialAt,
    ← Wave.timeSpaceEquiv_single_zero, ContinuousLinearEquiv.symm_apply_apply]

/-- The spatial derivative `∂ᵢ` of a function of space-time written in `(t, x)`. -/
theorem spaceDeriv_comp_symm {g : Spacetime → ℝ} (hg : Differentiable ℝ g) (i : Fin 3)
    (p : ℝ × E3) :
    Wave.spaceDeriv i (fun q => g (Wave.timeSpaceEquiv.symm q)) p =
      partialAt g i.succ (Wave.timeSpaceEquiv.symm p) := by
  rw [Wave.spaceDeriv, fderiv_comp_timeSpaceEquiv_symm hg, partialAt,
    ← Wave.timeSpaceEquiv_single_succ, ContinuousLinearEquiv.symm_apply_apply]

/-- The components of a `Cⁿ` current are `Cⁿ` in time and space. -/
theorem contDiff_splitComponent {n : ℕ∞ω} {k : Spacetime → Spacetime} (hk : ContDiff ℝ n k)
    (μ : Fin 4) : ContDiff ℝ n (splitComponent k μ) :=
  ((ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk).comp
    Wave.timeSpaceEquiv.symm.contDiff

/-- The components of a localized current are localized. -/
theorem localizedSupport_splitComponent {k : Spacetime → Spacetime} {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) (μ : Fin 4) :
    Wave.LocalizedSupport a (splitComponent k μ) :=
  hloc.comp (g := fun x : Spacetime => x μ) rfl

/-- The time derivative of a component in `(t, x)` is the component of `∂₀k`. -/
theorem timeDeriv_splitComponent {k : Spacetime → Spacetime} (hk : Differentiable ℝ k)
    (μ : Fin 4) (p : ℝ × E3) :
    Wave.timeDeriv (splitComponent k μ) p = currentRate k (Wave.timeSpaceEquiv.symm p) μ :=
  timeDeriv_comp_symm ((ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).differentiable.comp hk) p

/-- The spatial derivative `∂ᵢ` of a component in `(t, x)` is its derivative along the axis
`i + 1`. -/
theorem spaceDeriv_splitComponent {k : Spacetime → Spacetime} (hk : Differentiable ℝ k)
    (μ : Fin 4) (i : Fin 3) (p : ℝ × E3) :
    Wave.spaceDeriv i (splitComponent k μ) p =
      partialAt (fun w => k w μ) i.succ (Wave.timeSpaceEquiv.symm p) :=
  spaceDeriv_comp_symm ((ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).differentiable.comp hk)
    i p

/-- The far amplitude of the time derivative of a component is the amplitude of the component of
`∂₀k`. -/
theorem farAmplitude_timeDeriv_splitComponent {k : Spacetime → Spacetime}
    (hk : Differentiable ℝ k) (μ : Fin 4) (u : ℝ) (n : E3) :
    Wave.farAmplitude (Wave.timeDeriv (splitComponent k μ)) u n =
      radiationAmplitude (currentRate k) u n μ := by
  simp only [Wave.farAmplitude, radiationAmplitude, timeDeriv_splitComponent hk]
  rfl

/-- **The electric field of the retarded potential**: `Eᵢ = −∂ᵢφ − ∂ₜaᵢ` with the derivatives of
the retarded integrals `φ = R k⁰` and `aᵢ = R kⁱ`. -/
theorem electricField_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {ρ v₀ : ℝ} (hs : Wave.SubluminalSupport ρ v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (i : Fin 3) (t : ℝ) (x : E3) :
    electricField (fieldTensor (retardedPotential k)) i (vector t x) =
      -Wave.spaceDeriv i (Wave.retardedIntegral (splitComponent k 0)) (t, x) -
        Wave.timeDeriv (Wave.retardedIntegral (splitComponent k i.succ)) (t, x) := by
  have hA : ContDiff ℝ 1 (retardedPotential k) :=
    (contDiff_retardedPotential hk hs).of_le (by norm_num)
  have hc : ∀ μ : Fin 4, ContDiff ℝ 1 fun w => k w μ := fun μ =>
    ((ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk).of_le (by norm_num)
  have hv : Wave.timeSpaceEquiv (vector t x) = (t, x) :=
    Wave.timeSpaceEquiv.apply_symm_apply (t, x)
  rw [(electricField_fieldTensor_eventuallyEq hA.contDiffAt i).eq_of_nhds]
  rw [potentialComponent_retardedPotential_zero, partialAt_neg,
    potentialComponent_retardedPotential_succ,
    partialAt_retardedScalar_succ (hc 0) (subluminalSupport_component hs 0),
    partialAt_retardedScalar_zero (hc i.succ) (subluminalSupport_component hs i.succ), hv]
  rfl

/-- **The magnetic field of the retarded potential**: `B = curl 𝐚` with the derivatives of the
retarded integrals `aᵢ = R kⁱ`. -/
theorem magneticField_retardedPotential {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {ρ v₀ : ℝ} (hs : Wave.SubluminalSupport ρ v₀ fun p => k (Wave.timeSpaceEquiv.symm p))
    (t : ℝ) (x : E3) :
    magneticField (fieldTensor (retardedPotential k)) 0 (vector t x) =
        Wave.spaceDeriv 1 (Wave.retardedIntegral (splitComponent k 3)) (t, x) -
          Wave.spaceDeriv 2 (Wave.retardedIntegral (splitComponent k 2)) (t, x) ∧
      magneticField (fieldTensor (retardedPotential k)) 1 (vector t x) =
        Wave.spaceDeriv 2 (Wave.retardedIntegral (splitComponent k 1)) (t, x) -
          Wave.spaceDeriv 0 (Wave.retardedIntegral (splitComponent k 3)) (t, x) ∧
      magneticField (fieldTensor (retardedPotential k)) 2 (vector t x) =
        Wave.spaceDeriv 0 (Wave.retardedIntegral (splitComponent k 2)) (t, x) -
          Wave.spaceDeriv 1 (Wave.retardedIntegral (splitComponent k 1)) (t, x) := by
  have hA : ContDiff ℝ 1 (retardedPotential k) :=
    (contDiff_retardedPotential hk hs).of_le (by norm_num)
  have hc : ∀ μ : Fin 4, ContDiff ℝ 1 fun w => k w μ := fun μ =>
    ((ContinuousLinearMap.proj μ : Spacetime →L[ℝ] ℝ).contDiff.comp hk).of_le (by norm_num)
  have hv : Wave.timeSpaceEquiv (vector t x) = (t, x) :=
    Wave.timeSpaceEquiv.apply_symm_apply (t, x)
  have hp : ∀ j l : Fin 3,
      partialAt (potentialComponent (retardedPotential k) j.succ) l.succ (vector t x) =
        Wave.spaceDeriv l (Wave.retardedIntegral (splitComponent k j.succ)) (t, x) := by
    intro j l
    rw [potentialComponent_retardedPotential_succ,
      partialAt_retardedScalar_succ (hc j.succ) (subluminalSupport_component hs j.succ), hv]
    rfl
  obtain ⟨h0, h1, h2⟩ := CavityModes.magneticField_fieldTensor_apply hA (vector t x)
  exact ⟨h0.trans (congrArg₂ (· - ·) (hp 2 1) (hp 1 2)),
    h1.trans (congrArg₂ (· - ·) (hp 0 2) (hp 2 0)),
    h2.trans (congrArg₂ (· - ·) (hp 1 0) (hp 0 1))⟩

/-- **The conservation of the charge in the far field**: for a conserved localized current of
class `C²`, the time component of the amplitude of `∂₀k` is `∂ᵤφ̃ = ⟨n, ∂ᵤÃ⟩`. -/
theorem radiationAmplitude_currentRate_zero {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {a : ℝ} (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (u : ℝ) (n : E3) :
    radiationAmplitude (currentRate k) u n 0 = ∑ i, n i * amplitudeRate k u n i := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hd : Differentiable ℝ k := hk1.differentiable (by norm_num)
  have hg : ∀ μ, ContDiff ℝ 1 (splitComponent k μ) := fun μ => contDiff_splitComponent hk1 μ
  have hl := localizedSupport_splitComponent hloc
  have hcons : Wave.timeDeriv (splitComponent k 0) =
      fun p => -∑ i : Fin 3, Wave.spaceDeriv i (splitComponent k i.succ) p := by
    funext p
    have h := hdiv (Wave.timeSpaceEquiv.symm p)
    rw [divergence4_eq_sum_partialAt (hd _), Fin.sum_univ_succ] at h
    rw [timeDeriv_splitComponent hd]
    simp only [spaceDeriv_splitComponent hd]
    rw [currentRate]
    linarith
  have hs : ∀ i : Fin 3, Continuous (Wave.spaceDeriv i (splitComponent k i.succ)) := fun i =>
    (Wave.contDiff_spaceDeriv (n := 0) (by simpa using hg i.succ) i).continuous
  have hsum : Wave.farAmplitude
      (fun p => -∑ i : Fin 3, Wave.spaceDeriv i (splitComponent k i.succ) p) u n =
        -∑ i : Fin 3, Wave.farAmplitude (Wave.spaceDeriv i (splitComponent k i.succ)) u n := by
    simp only [Wave.farAmplitude]
    rw [integral_neg, integral_finsetSum _ fun i _ =>
      Wave.integrable_farIntegrand (hs i) ((hl _).spaceDeriv i) u n, mul_neg, Finset.mul_sum]
  rw [← farAmplitude_timeDeriv_splitComponent hd, hcons, hsum]
  simp only [Wave.farAmplitude_spaceDeriv (hg _) (hl _), farAmplitude_timeDeriv_splitComponent hd,
    amplitudeRate, Finset.sum_neg_distrib, neg_neg]

/-! ### The limits of the fields -/

/-- **The electric far field**: for a conserved localized current of class `C²`, the field of the
retarded potential at the point `(u + R, Rn)` has `R E → n⟨n, ∂ᵤÃ⟩ − ∂ᵤÃ = n × (n × ∂ᵤÃ)` as
`R → ∞`, uniformly for `u` in a compact set and `n` on the unit sphere. -/
theorem tendstoUniformlyOn_mul_electricField {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {a : ℝ} (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * electricField (fieldTensor (retardedPotential k)) i (vector (p.1 + R) (R • p.2)))
      (fun p => farElectric k p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hd : Differentiable ℝ k := hk1.differentiable (by norm_num)
  have h1 := Wave.tendstoUniformlyOn_mul_spaceDeriv_retardedIntegral
    (contDiff_splitComponent hk1 0) (localizedSupport_splitComponent hloc 0) hK i
  have h2 := Wave.tendstoUniformlyOn_mul_timeDeriv_retardedIntegral
    (contDiff_splitComponent hk1 i.succ) (localizedSupport_splitComponent hloc i.succ) hK
  have hF : (fun R (p : ℝ × E3) =>
      R * electricField (fieldTensor (retardedPotential k)) i (vector (p.1 + R) (R • p.2))) =
        fun R p =>
          -(R * Wave.spaceDeriv i (Wave.retardedIntegral (splitComponent k 0)) (p.1 + R, R • p.2)) -
            R * Wave.timeDeriv (Wave.retardedIntegral (splitComponent k i.succ))
              (p.1 + R, R • p.2) := by
    funext R p
    rw [electricField_retardedPotential hk hloc.subluminalSupport]
    ring
  have hG : (fun p : ℝ × E3 => farElectric k p.1 p.2 i) = fun p =>
      -(-(p.2 i * Wave.farAmplitude (Wave.timeDeriv (splitComponent k 0)) p.1 p.2)) -
        Wave.farAmplitude (Wave.timeDeriv (splitComponent k i.succ)) p.1 p.2 := by
    funext p
    rw [farAmplitude_timeDeriv_splitComponent hd, farAmplitude_timeDeriv_splitComponent hd,
      radiationAmplitude_currentRate_zero hk hloc hdiv, farElectric]
    simp only [amplitudeRate]
    ring
  rw [hF, hG]
  exact h1.fun_neg.fun_sub h2

/-- The limit of `R (∂ⱼaₘ)` for the components of a localized current. -/
theorem tendstoUniformlyOn_mul_spaceDeriv_splitComponent {k : Spacetime → Spacetime}
    (hk : ContDiff ℝ 1 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) {K : Set ℝ}
    (hK : IsCompact K) (j : Fin 3) (μ : Fin 4) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (p.1 + R, R • p.2))
      (fun p => -(p.2 j * radiationAmplitude (currentRate k) p.1 p.2 μ)) atTop
      (K ×ˢ sphere (0 : E3) 1) := by
  have h := Wave.tendstoUniformlyOn_mul_spaceDeriv_retardedIntegral
    (contDiff_splitComponent hk μ) (localizedSupport_splitComponent hloc μ) hK j
  simp only [farAmplitude_timeDeriv_splitComponent (hk.differentiable (by norm_num))] at h
  exact h

/-- **The magnetic far field**: for a localized current of class `C²`, the field of the retarded
potential at the point `(u + R, Rn)` has `R B → ∂ᵤÃ × n = −n × ∂ᵤÃ` as `R → ∞`, uniformly for `u`
in a compact set and `n` on the unit sphere. -/
theorem tendstoUniformlyOn_mul_magneticField {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {a : ℝ} (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) i (vector (p.1 + R) (R • p.2)))
      (fun p => farMagnetic k p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hS := tendstoUniformlyOn_mul_spaceDeriv_splitComponent hk1 hloc hK
  have hs := hloc.subluminalSupport
  have c0 : TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) 0 (vector (p.1 + R) (R • p.2)))
      (fun p => farMagnetic k p.1 p.2 0) atTop (K ×ˢ sphere (0 : E3) 1) := by
    have hF : (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) 0 (vector (p.1 + R) (R • p.2))) =
          fun R p =>
            R * Wave.spaceDeriv 1 (Wave.retardedIntegral (splitComponent k 3)) (p.1 + R, R • p.2) -
              R * Wave.spaceDeriv 2 (Wave.retardedIntegral (splitComponent k 2))
                (p.1 + R, R • p.2) := by
      funext R p
      rw [(magneticField_retardedPotential hk hs _ _).1]
      ring
    have hG : (fun p : ℝ × E3 => farMagnetic k p.1 p.2 0) = fun p =>
        -(p.2 1 * radiationAmplitude (currentRate k) p.1 p.2 3) -
          -(p.2 2 * radiationAmplitude (currentRate k) p.1 p.2 2) := by
      funext p
      simp only [farMagnetic, cross_apply, amplitudeRate]
      simp
      ring
    rw [hF, hG]
    exact (hS 1 3).fun_sub (hS 2 2)
  have c1 : TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) 1 (vector (p.1 + R) (R • p.2)))
      (fun p => farMagnetic k p.1 p.2 1) atTop (K ×ˢ sphere (0 : E3) 1) := by
    have hF : (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) 1 (vector (p.1 + R) (R • p.2))) =
          fun R p =>
            R * Wave.spaceDeriv 2 (Wave.retardedIntegral (splitComponent k 1)) (p.1 + R, R • p.2) -
              R * Wave.spaceDeriv 0 (Wave.retardedIntegral (splitComponent k 3))
                (p.1 + R, R • p.2) := by
      funext R p
      rw [(magneticField_retardedPotential hk hs _ _).2.1]
      ring
    have hG : (fun p : ℝ × E3 => farMagnetic k p.1 p.2 1) = fun p =>
        -(p.2 2 * radiationAmplitude (currentRate k) p.1 p.2 1) -
          -(p.2 0 * radiationAmplitude (currentRate k) p.1 p.2 3) := by
      funext p
      simp only [farMagnetic, cross_apply, amplitudeRate]
      simp
      ring
    rw [hF, hG]
    exact (hS 2 1).fun_sub (hS 0 3)
  have c2 : TendstoUniformlyOn
      (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) 2 (vector (p.1 + R) (R • p.2)))
      (fun p => farMagnetic k p.1 p.2 2) atTop (K ×ˢ sphere (0 : E3) 1) := by
    have hF : (fun R (p : ℝ × E3) =>
        R * magneticField (fieldTensor (retardedPotential k)) 2 (vector (p.1 + R) (R • p.2))) =
          fun R p =>
            R * Wave.spaceDeriv 0 (Wave.retardedIntegral (splitComponent k 2)) (p.1 + R, R • p.2) -
              R * Wave.spaceDeriv 1 (Wave.retardedIntegral (splitComponent k 1))
                (p.1 + R, R • p.2) := by
      funext R p
      rw [(magneticField_retardedPotential hk hs _ _).2.2]
      ring
    have hG : (fun p : ℝ × E3 => farMagnetic k p.1 p.2 2) = fun p =>
        -(p.2 0 * radiationAmplitude (currentRate k) p.1 p.2 2) -
          -(p.2 1 * radiationAmplitude (currentRate k) p.1 p.2 1) := by
      funext p
      simp only [farMagnetic, cross_apply, amplitudeRate]
      simp
      ring
    rw [hF, hG]
    exact (hS 0 2).fun_sub (hS 1 1)
  fin_cases i
  · exact c0
  · exact c1
  · exact c2

/-! ### The radiated power -/

/-- A unit vector has components of absolute value at most `1`. -/
theorem abs_apply_le_one {n : E3} (hn : n ∈ sphere (0 : E3) 1) (i : Fin 3) : |n i| ≤ 1 := by
  have h := PiLp.norm_apply_le n i
  rw [Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp hn] at h
  exact h

/-- The amplitude `∂ᵤÃ` of a localized current of class `C²` is bounded on the unit sphere. -/
theorem exists_bound_amplitudeRate {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) (u : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ n ∈ sphere (0 : E3) 1, ∀ j, |amplitudeRate k u n j| ≤ M := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hA : ∀ j : Fin 3, ∃ M, ∀ n ∈ sphere (0 : E3) 1, |amplitudeRate k u n j| ≤ M := by
    intro j
    have hc1 : ContDiff ℝ (0 + 1) (splitComponent k j.succ) := by
      simpa using contDiff_splitComponent hk1 j.succ
    have hc : Continuous (Wave.timeDeriv (splitComponent k j.succ)) :=
      (Wave.contDiff_timeDeriv (n := 0) hc1).continuous
    obtain ⟨M, hM⟩ := Wave.exists_bound_farAmplitude hc
      (localizedSupport_splitComponent hloc j.succ).timeDeriv (isCompact_singleton (x := u))
    refine ⟨M, fun n hn => ?_⟩
    have h := hM u rfl n hn
    rwa [farAmplitude_timeDeriv_splitComponent (hk1.differentiable (by norm_num))] at h
  choose M hM using hA
  refine ⟨∑ j, |M j|, Finset.sum_nonneg fun j _ => abs_nonneg _, fun n hn j => ?_⟩
  exact (hM j n hn).trans ((le_abs_self _).trans (Finset.single_le_sum
    (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))

/-- The electric far field is bounded by `4M` for `|∂ᵤÃⱼ| ≤ M` on the unit sphere. -/
private theorem abs_farElectric_le {k : Spacetime → Spacetime} {u M : ℝ} {n : E3}
    (hn : n ∈ sphere (0 : E3) 1) (hM : ∀ j, |amplitudeRate k u n j| ≤ M) (i : Fin 3) :
    |farElectric k u n i| ≤ 4 * M := by
  have hN := abs_apply_le_one hn
  have hp : ∀ j, |n j * amplitudeRate k u n j| ≤ M := fun j => by
    rw [abs_mul]
    nlinarith [abs_nonneg (n j), abs_nonneg (amplitudeRate k u n j), hN j, hM j]
  have hs : |∑ j, n j * amplitudeRate k u n j| ≤ 3 * M := by
    rw [Fin.sum_univ_three, abs_le]
    have h0 := abs_le.mp (hp 0)
    have h1 := abs_le.mp (hp 1)
    have h2 := abs_le.mp (hp 2)
    constructor <;> linarith
  have hm : |n i * ∑ j, n j * amplitudeRate k u n j| ≤ 3 * M := by
    rw [abs_mul]
    nlinarith [abs_nonneg (n i), abs_nonneg (∑ j, n j * amplitudeRate k u n j), hN i]
  have h := abs_sub (n i * ∑ j, n j * amplitudeRate k u n j) (amplitudeRate k u n i)
  rw [farElectric]
  linarith [hM i]

/-- The magnetic far field is bounded by `2M` for `|∂ᵤÃⱼ| ≤ M` on the unit sphere. -/
private theorem abs_farMagnetic_le {k : Spacetime → Spacetime} {u M : ℝ} {n : E3}
    (hn : n ∈ sphere (0 : E3) 1) (hM : ∀ j, |amplitudeRate k u n j| ≤ M) (i : Fin 3) :
    |farMagnetic k u n i| ≤ 2 * M := by
  have hN := abs_apply_le_one hn
  have hp : ∀ j l, |amplitudeRate k u n j * n l| ≤ M := fun j l => by
    rw [abs_mul]
    nlinarith [abs_nonneg (n l), abs_nonneg (amplitudeRate k u n j), hN l, hM j]
  have hc : ∀ j l j' l', |amplitudeRate k u n j * n l - amplitudeRate k u n j' * n l'| ≤ 2 * M :=
    fun j l j' l' => by
      have h := abs_sub (amplitudeRate k u n j * n l) (amplitudeRate k u n j' * n l')
      linarith [hp j l, hp j' l']
  fin_cases i <;>
  · simp only [farMagnetic, cross_apply]
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    exact hc _ _ _ _

/-- **The radiated power** (Landau–Lifshitz §66): for a conserved localized current of class `C²`,
the flux of the vector of Poynting of the retarded field through the sphere of radius `R` at the
time `u + R` tends to the power `radiatedPower k u = ∫ |n × ∂ᵤÃ|² dσ` radiated at the retarded
time `u`. -/
theorem tendsto_sphereFlux_poynting {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) (u : ℝ) :
    Tendsto (fun R => sphereFlux (poyntingVector (fieldTensor (retardedPotential k))) (u + R) R)
      atTop (𝓝 (radiatedPower k u)) := by
  set F := fieldTensor (retardedPotential k) with hFdef
  have hFc : ContDiff ℝ 1 F := DifferentialForm.exteriorDerivative_contDiff (r := 1)
    (contDiff_retardedPotential hk hloc.subluminalSupport)
  have hEc : ∀ i, Continuous (electricField F i) := fun i =>
    (contDiff_electricField hFc i).continuous
  have hBc : ∀ i, Continuous (magneticField F i) := fun i =>
    (contDiff_magneticField hFc i).continuous
  have hv : ∀ R, Continuous fun n : sphere (0 : E3) 1 => vector (u + R) (R • (n : E3)) :=
    fun R => by
      have h : Continuous fun n : sphere (0 : E3) 1 => ((u + R : ℝ), R • (n : E3)) :=
        continuous_const.prodMk (continuous_subtype_val.const_smul R)
      exact Wave.timeSpaceEquiv.symm.continuous.comp h
  obtain ⟨M, hM0, hM⟩ := exists_bound_amplitudeRate hk hloc u
  have hu : IsCompact ({u} : Set ℝ) := isCompact_singleton
  have hE := fun i => tendstoUniformlyOn_mul_electricField hk hloc hdiv hu i
  have hB := fun i => tendstoUniformlyOn_mul_magneticField hk hloc hu i
  have hEe : ∀ i, ∀ᶠ R in atTop, ∀ n ∈ sphere (0 : E3) 1,
      |R * electricField F i (vector (u + R) (R • n))| ≤ 4 * M + 1 := by
    intro i
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hE i) 1 one_pos] with R hR n hn
    have h1 := hR (u, n) ⟨rfl, hn⟩
    dsimp only at h1
    rw [Real.dist_eq] at h1
    have h2 := abs_farElectric_le hn (hM n hn) i
    have h3 := abs_sub_abs_le_abs_sub (R * electricField F i (vector (u + R) (R • n)))
      (farElectric k u n i)
    rw [abs_sub_comm] at h3
    linarith
  have hBe : ∀ i, ∀ᶠ R in atTop, ∀ n ∈ sphere (0 : E3) 1,
      |R * magneticField F i (vector (u + R) (R • n))| ≤ 2 * M + 1 := by
    intro i
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hB i) 1 one_pos] with R hR n hn
    have h1 := hR (u, n) ⟨rfl, hn⟩
    dsimp only at h1
    rw [Real.dist_eq] at h1
    have h2 := abs_farMagnetic_le hn (hM n hn) i
    have h3 := abs_sub_abs_le_abs_sub (R * magneticField F i (vector (u + R) (R • n)))
      (farMagnetic k u n i)
    rw [abs_sub_comm] at h3
    linarith
  have hflux : (fun R => sphereFlux (poyntingVector F) (u + R) R) = fun R =>
      ∫ n : sphere (0 : E3) 1,
        radialCross (fun i => R * electricField F i (vector (u + R) (R • (n : E3))))
          (fun i => R * magneticField F i (vector (u + R) (R • (n : E3)))) n ∂sphereMeasure := by
    funext R
    rw [sphereFlux, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    dsimp only
    rw [radialCross_eq]
    simp only [poyntingVector, Fin.sum_univ_three]
    simp
    ring
  rw [hflux, radiatedPower]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 6 * ((4 * M + 1) * (2 * M + 1)))
    ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun R => Continuous.aestronglyMeasurable ?_
    have hE' : ∀ i, Continuous fun n : sphere (0 : E3) 1 =>
        R * electricField F i (vector (u + R) (R • (n : E3))) := fun i =>
      continuous_const.mul ((hEc i).comp (hv R))
    have hB' : ∀ i, Continuous fun n : sphere (0 : E3) 1 =>
        R * magneticField F i (vector (u + R) (R • (n : E3))) := fun i =>
      continuous_const.mul ((hBc i).comp (hv R))
    have hN : ∀ i, Continuous fun n : sphere (0 : E3) 1 => (n : E3) i := fun i =>
      (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp continuous_subtype_val
    simp only [radialCross_eq]
    exact (((((hE' 1).mul (hB' 2)).sub ((hE' 2).mul (hB' 1))).mul (hN 0)).add
      ((((hE' 2).mul (hB' 0)).sub ((hE' 0).mul (hB' 2))).mul (hN 1))).add
      ((((hE' 0).mul (hB' 1)).sub ((hE' 1).mul (hB' 0))).mul (hN 2))
  · filter_upwards [eventually_all.mpr hEe, eventually_all.mpr hBe] with R hR1 hR2
    refine Eventually.of_forall fun n => ?_
    rw [Real.norm_eq_abs]
    exact abs_radialCross_le (fun i => hR1 i n n.2) (fun i => hR2 i n n.2)
      (abs_apply_le_one n.2)
  · refine Eventually.of_forall fun n => ?_
    have he : ∀ i, Tendsto (fun R => R * electricField F i (vector (u + R) (R • (n : E3))))
        atTop (𝓝 (farElectric k u n i)) := fun i =>
      (hE i).tendsto_at (x := (u, (n : E3))) ⟨rfl, n.2⟩
    have hb : ∀ i, Tendsto (fun R => R * magneticField F i (vector (u + R) (R • (n : E3))))
        atTop (𝓝 (farMagnetic k u n i)) := fun i =>
      (hB i).tendsto_at (x := (u, (n : E3))) ⟨rfl, n.2⟩
    have h := tendsto_radialCross (farElectric k u n) (farMagnetic k u n) n he hb
    rwa [farPoynting_eq k u (mem_sphere_zero_iff_norm.mp n.2)] at h

/-! ### The transversality of the radiation -/

/-- The rate of `R (∂ⱼaₘ) → −nⱼ ∂ᵤÃₘ` for a localized current of class `C²`. -/
theorem exists_bound_mul_spaceDeriv_splitComponent_add {k : Spacetime → Spacetime}
    (hk : ContDiff ℝ 2 k) {a : ℝ}
    (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p)) {K : Set ℝ}
    (hK : IsCompact K) (j : Fin 3) (μ : Fin 4) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (u + R, R • n) +
        n j * radiationAmplitude (currentRate k) u n μ| ≤ C / R := by
  obtain ⟨C, hC⟩ := Wave.exists_bound_mul_spaceDeriv_retardedIntegral_add
    (contDiff_splitComponent hk μ) (localizedSupport_splitComponent hloc μ) hK j
  refine ⟨C, hC.mono fun R hR u hu n hn => ?_⟩
  have h := hR u hu n hn
  rwa [farAmplitude_timeDeriv_splitComponent (hk.differentiable (by norm_num))] at h

/-- Two remainders `O(1/R)` give a remainder `O(1/R)` of the difference. -/
private theorem abs_sub_le_add_div {x y C₁ C₂ R : ℝ} (hx : |x| ≤ C₁ / R)
    (hy : |y| ≤ C₂ / R) :
    |x - y| ≤ (C₁ + C₂) / R := by
  rw [add_div]
  exact (abs_sub x y).trans (add_le_add hx hy)

/-- **The rate of the electric far field**: for a conserved localized current of class `C²`,
`|R Eᵢ − (n⟨n, ∂ᵤÃ⟩ − ∂ᵤÃ)ᵢ| ≤ C/R` for large `R`, `u` in a compact set and `n` on the unit
sphere. -/
theorem exists_bound_mul_electricField_sub {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {a : ℝ} (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * electricField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
        farElectric k u n i| ≤ C / R := by
  have hd : Differentiable ℝ k := hk.differentiable (by norm_num)
  obtain ⟨C₁, h₁⟩ := exists_bound_mul_spaceDeriv_splitComponent_add hk hloc hK i 0
  obtain ⟨C₂, h₂⟩ := Wave.exists_bound_mul_timeDeriv_retardedIntegral_sub
    (contDiff_splitComponent hk i.succ) (localizedSupport_splitComponent hloc i.succ) hK
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with R hR₁ hR₂ u hu n hn
  have e₁ := hR₁ u hu n hn
  have e₂ := hR₂ u hu n hn
  rw [radiationAmplitude_currentRate_zero hk hloc hdiv] at e₁
  rw [farAmplitude_timeDeriv_splitComponent hd] at e₂
  have key : R * electricField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
      farElectric k u n i =
        -(R * Wave.spaceDeriv i (Wave.retardedIntegral (splitComponent k 0)) (u + R, R • n) +
          n i * ∑ j, n j * amplitudeRate k u n j) -
        (R * Wave.timeDeriv (Wave.retardedIntegral (splitComponent k i.succ)) (u + R, R • n) -
          radiationAmplitude (currentRate k) u n i.succ) := by
    rw [electricField_retardedPotential hk hloc.subluminalSupport, farElectric]
    simp only [amplitudeRate]
    ring
  rw [key]
  exact abs_sub_le_add_div (by rwa [abs_neg]) e₂

/-- **The rate of the magnetic far field**: for a localized current of class `C²`,
`|R Bᵢ − (∂ᵤÃ × n)ᵢ| ≤ C/R` for large `R`, `u` in a compact set and `n` on the unit sphere. -/
theorem exists_bound_mul_magneticField_sub {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {a : ℝ} (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    {K : Set ℝ} (hK : IsCompact K) (i : Fin 3) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * magneticField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
        farMagnetic k u n i| ≤ C / R := by
  have hs := hloc.subluminalSupport
  have hS := exists_bound_mul_spaceDeriv_splitComponent_add hk hloc hK
  have hcurl : ∀ (j l : Fin 3) (μ ν : Fin 4), ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K,
      ∀ n ∈ sphere (0 : E3) 1,
        |R * (Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (u + R, R • n) -
            Wave.spaceDeriv l (Wave.retardedIntegral (splitComponent k ν)) (u + R, R • n)) -
          (n l * radiationAmplitude (currentRate k) u n ν -
            n j * radiationAmplitude (currentRate k) u n μ)| ≤ C / R := by
    intro j l μ ν
    obtain ⟨C₁, h₁⟩ := hS j μ
    obtain ⟨C₂, h₂⟩ := hS l ν
    refine ⟨C₁ + C₂, ?_⟩
    filter_upwards [h₁, h₂] with R hR₁ hR₂ u hu n hn
    have key : R * (Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (u + R, R • n) -
          Wave.spaceDeriv l (Wave.retardedIntegral (splitComponent k ν)) (u + R, R • n)) -
        (n l * radiationAmplitude (currentRate k) u n ν -
          n j * radiationAmplitude (currentRate k) u n μ) =
        (R * Wave.spaceDeriv j (Wave.retardedIntegral (splitComponent k μ)) (u + R, R • n) +
            n j * radiationAmplitude (currentRate k) u n μ) -
          (R * Wave.spaceDeriv l (Wave.retardedIntegral (splitComponent k ν)) (u + R, R • n) +
            n l * radiationAmplitude (currentRate k) u n ν) := by ring
    rw [key]
    exact abs_sub_le_add_div (hR₁ u hu n hn) (hR₂ u hu n hn)
  have c0 : ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * magneticField (fieldTensor (retardedPotential k)) 0 (vector (u + R) (R • n)) -
        farMagnetic k u n 0| ≤ C / R := by
    obtain ⟨C, hC⟩ := hcurl 1 2 3 2
    refine ⟨C, hC.mono fun R hR u hu n hn => ?_⟩
    have h := hR u hu n hn
    rw [(magneticField_retardedPotential hk hs _ _).1]
    simp only [farMagnetic, cross_apply, amplitudeRate]
    convert h using 2
    simp
    ring
  have c1 : ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * magneticField (fieldTensor (retardedPotential k)) 1 (vector (u + R) (R • n)) -
        farMagnetic k u n 1| ≤ C / R := by
    obtain ⟨C, hC⟩ := hcurl 2 0 1 3
    refine ⟨C, hC.mono fun R hR u hu n hn => ?_⟩
    have h := hR u hu n hn
    rw [(magneticField_retardedPotential hk hs _ _).2.1]
    simp only [farMagnetic, cross_apply, amplitudeRate]
    convert h using 2
    simp
    ring
  have c2 : ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1,
      |R * magneticField (fieldTensor (retardedPotential k)) 2 (vector (u + R) (R • n)) -
        farMagnetic k u n 2| ≤ C / R := by
    obtain ⟨C, hC⟩ := hcurl 0 1 2 1
    refine ⟨C, hC.mono fun R hR u hu n hn => ?_⟩
    have h := hR u hu n hn
    rw [(magneticField_retardedPotential hk hs _ _).2.2]
    simp only [farMagnetic, cross_apply, amplitudeRate]
    convert h using 2
    simp
    ring
  fin_cases i
  · exact c0
  · exact c1
  · exact c2

/-- A bound `C/R` for each of the three components gives one for all of them. -/
private theorem exists_bound_forall_fin_three {K : Set ℝ} (G : Fin 3 → ℝ → ℝ → E3 → ℝ)
    (h : ∀ i, ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, |G i R u n| ≤ C / R) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, ∀ i, |G i R u n| ≤ C / R := by
  choose C hC using h
  refine ⟨∑ i, |C i|, ?_⟩
  filter_upwards [eventually_all.mpr hC, eventually_gt_atTop 0] with R hR hR0 u hu n hn i
  exact (hR i u hu n hn).trans (div_le_div_of_nonneg_right ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
    hR0.le)

/-- One component of `E − B × n` from the remainders of `R E` and `R B` and `E∞ = B∞ × n`. -/
private theorem abs_sub_cross_le {R E₀ B₁ B₂ n₁ n₂ E₀' B₁' B₂' C₁ C₂ : ℝ} (hR : 0 < R)
    (hE : |R * E₀ - E₀'| ≤ C₁ / R) (hB₁ : |R * B₁ - B₁'| ≤ C₂ / R)
    (hB₂ : |R * B₂ - B₂'| ≤ C₂ / R) (hn₁ : |n₁| ≤ 1) (hn₂ : |n₂| ≤ 1)
    (hfar : E₀' = B₁' * n₂ - B₂' * n₁) :
    |E₀ - (B₁ * n₂ - B₂ * n₁)| ≤ (C₁ + 2 * C₂) / R ^ 2 := by
  have key : E₀ - (B₁ * n₂ - B₂ * n₁) =
      ((R * E₀ - E₀') - ((R * B₁ - B₁') * n₂ - (R * B₂ - B₂') * n₁)) / R := by
    rw [hfar]
    field_simp
    ring
  have h₁ : |(R * B₁ - B₁') * n₂| ≤ C₂ / R := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hn₂).trans hB₁
  have h₂ : |(R * B₂ - B₂') * n₁| ≤ C₂ / R := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hn₁).trans hB₂
  have hnum : |(R * E₀ - E₀') - ((R * B₁ - B₁') * n₂ - (R * B₂ - B₂') * n₁)| ≤
      (C₁ + 2 * C₂) / R := by
    have := abs_sub_le_add_div hE (abs_sub_le_add_div h₁ h₂)
    rwa [show C₁ + (C₂ + C₂) = C₁ + 2 * C₂ by ring] at this
  rw [key, abs_div, abs_of_pos hR, pow_two, ← div_div]
  exact div_le_div_of_nonneg_right hnum hR.le

/-- **The radiation is transverse**: for a conserved localized current of class `C²`, the field of
the retarded potential at `(u + R, Rn)` has `E − B × n = O(1/R²)`, uniformly for `u` in a compact
set and `n` on the unit sphere; to leading order `E ⊥ n`, `B ⊥ n` and `|E| = |B|`. -/
theorem exists_bound_electricField_sub_cross {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    {a : ℝ} (hloc : Wave.LocalizedSupport a fun p => k (Wave.timeSpaceEquiv.symm p))
    (hdiv : ∀ v, divergence4 k v = 0) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, ∀ i : Fin 3,
      |electricField (fieldTensor (retardedPotential k)) i (vector (u + R) (R • n)) -
        crossProduct (fun j => magneticField (fieldTensor (retardedPotential k)) j
          (vector (u + R) (R • n))) ⇑n i| ≤ C / R ^ 2 := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_forall_fin_three
    (fun i R u n => R * electricField (fieldTensor (retardedPotential k)) i
      (vector (u + R) (R • n)) - farElectric k u n i)
    fun i => exists_bound_mul_electricField_sub hk hloc hdiv hK i
  obtain ⟨C₂, hC₂⟩ := exists_bound_forall_fin_three
    (fun i R u n => R * magneticField (fieldTensor (retardedPotential k)) i
      (vector (u + R) (R • n)) - farMagnetic k u n i)
    fun i => exists_bound_mul_magneticField_sub hk hloc hK i
  refine ⟨C₁ + 2 * C₂, ?_⟩
  filter_upwards [hC₁, hC₂, eventually_gt_atTop 0] with R hE hB hR u hu n hn i
  have hN := abs_apply_le_one hn
  have hfar := congrFun (farElectric_eq_cross k u (mem_sphere_zero_iff_norm.mp hn))
  have hE' := hE u hu n hn
  have hB' := hB u hu n hn
  have t0 : |electricField (fieldTensor (retardedPotential k)) 0 (vector (u + R) (R • n)) -
      crossProduct (fun j => magneticField (fieldTensor (retardedPotential k)) j
        (vector (u + R) (R • n))) ⇑n 0| ≤ (C₁ + 2 * C₂) / R ^ 2 := by
    have h := hfar 0
    simp only [cross_apply] at h ⊢
    simp only [Matrix.cons_val_zero] at h ⊢
    exact abs_sub_cross_le hR (hE' 0) (hB' 1) (hB' 2) (hN 1) (hN 2) h
  have t1 : |electricField (fieldTensor (retardedPotential k)) 1 (vector (u + R) (R • n)) -
      crossProduct (fun j => magneticField (fieldTensor (retardedPotential k)) j
        (vector (u + R) (R • n))) ⇑n 1| ≤ (C₁ + 2 * C₂) / R ^ 2 := by
    have h := hfar 1
    simp only [cross_apply] at h ⊢
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h ⊢
    exact abs_sub_cross_le hR (hE' 1) (hB' 2) (hB' 0) (hN 2) (hN 0) h
  have t2 : |electricField (fieldTensor (retardedPotential k)) 2 (vector (u + R) (R • n)) -
      crossProduct (fun j => magneticField (fieldTensor (retardedPotential k)) j
        (vector (u + R) (R • n))) ⇑n 2| ≤ (C₁ + 2 * C₂) / R ^ 2 := by
    have h := hfar 2
    simp only [cross_apply] at h ⊢
    simp only [Matrix.cons_val] at h ⊢
    exact abs_sub_cross_le hR (hE' 2) (hB' 0) (hB' 1) (hN 0) (hN 1) h
  fin_cases i
  · exact t0
  · exact t1
  · exact t2

/-! ### An instance -/

/-- **An instance**: the circulating current `(∂₁χ, −∂₀χ, 0, 0)` of a bump `χ` on space-time has
localized support. -/
theorem localizedSupport_circulatingCurrent :
    ∃ a, Wave.LocalizedSupport a fun p => circulatingCurrent (Wave.timeSpaceEquiv.symm p) := by
  obtain ⟨a, ha⟩ := exists_subluminalSupport_circulatingCurrent
  exact ⟨a, ha.localizedSupport⟩

/-- **The far field of the circulating current**: `R E → n × (n × ∂ᵤÃ)` and `R B → −n × ∂ᵤÃ`,
uniformly for `u` in a compact set and `n` on the unit sphere. -/
theorem tendstoUniformlyOn_mul_field_circulatingCurrent {K : Set ℝ} (hK : IsCompact K)
    (i : Fin 3) :
    TendstoUniformlyOn
        (fun R (p : ℝ × E3) => R * electricField (fieldTensor
          (retardedPotential circulatingCurrent)) i (vector (p.1 + R) (R • p.2)))
        (fun p => farElectric circulatingCurrent p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) ∧
      TendstoUniformlyOn
        (fun R (p : ℝ × E3) => R * magneticField (fieldTensor
          (retardedPotential circulatingCurrent)) i (vector (p.1 + R) (R • p.2)))
        (fun p => farMagnetic circulatingCurrent p.1 p.2 i) atTop (K ×ˢ sphere (0 : E3) 1) := by
  obtain ⟨a, ha⟩ := localizedSupport_circulatingCurrent
  have hk : ContDiff ℝ 2 circulatingCurrent := contDiff_circulatingCurrent.of_le (by simp)
  exact ⟨tendstoUniformlyOn_mul_electricField hk ha divergence4_circulatingCurrent hK i,
    tendstoUniformlyOn_mul_magneticField hk ha hK i⟩

/-- **The power radiated by the circulating current**: the flux of the vector of Poynting through
the sphere of radius `R` at the time `u + R` tends to `radiatedPower circulatingCurrent u`. -/
theorem tendsto_sphereFlux_poynting_circulatingCurrent (u : ℝ) :
    Tendsto (fun R => sphereFlux (poyntingVector (fieldTensor
      (retardedPotential circulatingCurrent))) (u + R) R) atTop
      (𝓝 (radiatedPower circulatingCurrent u)) := by
  obtain ⟨a, ha⟩ := localizedSupport_circulatingCurrent
  exact tendsto_sphereFlux_poynting (contDiff_circulatingCurrent.of_le (by simp)) ha
    divergence4_circulatingCurrent u

/-- **The radiation of the circulating current is transverse**: `E − B × n = O(1/R²)`. -/
theorem exists_bound_electricField_sub_cross_circulatingCurrent {K : Set ℝ}
    (hK : IsCompact K) :
    ∃ C, ∀ᶠ R in atTop, ∀ u ∈ K, ∀ n ∈ sphere (0 : E3) 1, ∀ i : Fin 3,
      |electricField (fieldTensor (retardedPotential circulatingCurrent)) i
          (vector (u + R) (R • n)) -
        crossProduct (fun j => magneticField (fieldTensor (retardedPotential circulatingCurrent))
          j (vector (u + R) (R • n))) ⇑n i| ≤ C / R ^ 2 := by
  obtain ⟨a, ha⟩ := localizedSupport_circulatingCurrent
  exact exists_bound_electricField_sub_cross (contDiff_circulatingCurrent.of_le (by simp)) ha
    divergence4_circulatingCurrent hK

end ProjectAinos.Electrodynamics.Radiation
