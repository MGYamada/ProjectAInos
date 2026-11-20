/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# The Newton kernel of three-dimensional space

Space is `EuclideanSpace ℝ (Fin 3)`, with the Euclidean norm `‖x‖ = √(x₁² + x₂² + x₃²)` and its
Lebesgue measure. The Newton kernel `newtonKernel x = 1/(4π‖x‖)` is the potential of a unit
point charge in the units with `div E = ρ`.

* `newtonKernel_eq_regularKernel`: the kernel is the case `ε = 0` of the regularized kernel
  `regularKernel ε x = 1/(4π√(‖x‖² + ε²))`; `contDiff_regularKernel`: the regularized kernel is
  smooth for `ε ≠ 0`.
* `laplacian_regularKernel`: `Δ (regularKernel ε) x = −3ε²/(4π(‖x‖² + ε²)^{5/2})`.
* `integral_peakFunction`: the peak function `3/(4π(‖x‖² + 1)^{5/2})` has the integral one, so
  `−Δ (regularKernel ε)` is an approximate identity as `ε → 0`.
* `locallyIntegrable_newtonKernel`, `contDiffAt_newtonKernel`, `analyticAt_newtonKernel`,
  `harmonicAt_newtonKernel`: the kernel is locally integrable, and analytic and harmonic away
  from the origin; `norm_fderiv_newtonKernel`: its derivative has the norm `1/(4π‖x‖²)`.
* `integral_newtonKernel_mul_laplacian`: **the point source in pairing form**,
  `∫ K Δχ = −χ(0)` for every `C²` function `χ` of compact support, which is the identity
  `ΔK = −δ` tested against `χ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real Bornology
open scoped Topology Laplacian ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The kernels -/

/-- The Newton kernel `1/(4π‖x‖)` on three-dimensional space. Its value at the origin is `0`,
because `(0 : ℝ)⁻¹ = 0`. -/
def newtonKernel (x : E3) : ℝ := (4 * π * ‖x‖)⁻¹

/-- The regularized kernel `1/(4π√(‖x‖² + ε²))`. -/
def regularKernel (ε : ℝ) (x : E3) : ℝ := (4 * π * √(‖x‖ ^ 2 + ε ^ 2))⁻¹

/-- The radial profile `s ↦ (4π)⁻¹ (s + e)^{-1/2}` of the kernels, a function of `s = ‖x‖²`. -/
def kernelProfile (e s : ℝ) : ℝ := (4 * π)⁻¹ * (s + e) ^ (-(1 / 2 : ℝ))

/-- The kernel is the regularized kernel at `ε = 0`. -/
theorem newtonKernel_eq_regularKernel : newtonKernel = regularKernel 0 := by
  funext x
  simp [newtonKernel, regularKernel, Real.sqrt_sq (norm_nonneg x)]

/-- The regularized kernel is the profile at `s = ‖x‖²` and `e = ε²`. -/
theorem regularKernel_eq_kernelProfile (ε : ℝ) (x : E3) :
    regularKernel ε x = kernelProfile (ε ^ 2) (‖x‖ ^ 2) := by
  have hu : 0 ≤ ‖x‖ ^ 2 + ε ^ 2 := by positivity
  rw [regularKernel, kernelProfile, Real.sqrt_eq_rpow, Real.rpow_neg hu, mul_inv]

/-- The kernel is even. -/
theorem newtonKernel_neg (x : E3) : newtonKernel (-x) = newtonKernel x := by
  simp [newtonKernel]

/-- The kernel is nonnegative. -/
theorem newtonKernel_nonneg (x : E3) : 0 ≤ newtonKernel x := by
  unfold newtonKernel
  positivity

/-- The regularized kernel is positive for `ε ≠ 0`. -/
theorem regularKernel_pos {ε : ℝ} (hε : ε ≠ 0) (x : E3) : 0 < regularKernel ε x := by
  have : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  unfold regularKernel
  positivity

/-- The regularized kernel lies below the kernel away from the origin. -/
theorem regularKernel_le_newtonKernel (ε : ℝ) {x : E3} (hx : x ≠ 0) :
    regularKernel ε x ≤ newtonKernel x := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  unfold regularKernel newtonKernel
  apply inv_anti₀ (by positivity)
  have : ‖x‖ ≤ √(‖x‖ ^ 2 + ε ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hπ : 0 < 4 * π := by positivity
  nlinarith

/-! ### Derivatives of the profile -/

/-- The derivative of the profile is `−(8π)⁻¹ (s + e)^{-3/2}`. -/
theorem hasDerivAt_kernelProfile {e s : ℝ} (h : 0 < s + e) :
    HasDerivAt (kernelProfile e) (-(8 * π)⁻¹ * (s + e) ^ (-(3 / 2 : ℝ))) s := by
  have h1 := (((hasDerivAt_id s).add_const e).rpow_const (p := -(1 / 2 : ℝ))
    (Or.inl h.ne')).const_mul (4 * π)⁻¹
  refine h1.congr_deriv ?_
  simp only [id]
  rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2) by norm_num]
  field_simp
  ring

/-- The second derivative of the profile is `3 (16π)⁻¹ (s + e)^{-5/2}`. -/
theorem hasDerivAt_kernelProfile_deriv {e s : ℝ} (h : 0 < s + e) :
    HasDerivAt (fun t => -(8 * π)⁻¹ * (t + e) ^ (-(3 / 2 : ℝ)))
      (3 * (16 * π)⁻¹ * (s + e) ^ (-(5 / 2 : ℝ))) s := by
  have h1 := (((hasDerivAt_id s).add_const e).rpow_const (p := -(3 / 2 : ℝ))
    (Or.inl h.ne')).const_mul (-(8 * π)⁻¹)
  refine h1.congr_deriv ?_
  simp only [id]
  rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num]
  field_simp
  ring

/-- The Laplacian of the regularized kernel, where `‖x‖² + ε² > 0`, in powers. -/
theorem coordLaplacian_regularKernel_rpow {ε : ℝ} {x : E3} (h : 0 < ‖x‖ ^ 2 + ε ^ 2) :
    coordLaplacian (regularKernel ε) x =
      -(3 * ε ^ 2 / (4 * π)) * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
  have hfun : regularKernel ε = fun y => kernelProfile (ε ^ 2) (‖y‖ ^ 2) :=
    funext (regularKernel_eq_kernelProfile ε)
  have hev : ∀ᶠ s in 𝓝 (‖x‖ ^ 2), HasDerivAt (kernelProfile (ε ^ 2))
      (-(8 * π)⁻¹ * (s + ε ^ 2) ^ (-(3 / 2 : ℝ))) s := by
    have : ∀ᶠ s in 𝓝 (‖x‖ ^ 2), 0 < s + ε ^ 2 :=
      (continuous_id.add continuous_const).continuousAt.eventually (lt_mem_nhds h)
    filter_upwards [this] with s hs using hasDerivAt_kernelProfile hs
  rw [hfun, coordLaplacian_comp_normSq hev (hasDerivAt_kernelProfile_deriv h)]
  set u := ‖x‖ ^ 2 + ε ^ 2 with hu
  have h32 : u ^ (-(3 / 2 : ℝ)) = u * u ^ (-(5 / 2 : ℝ)) := by
    rw [show -(3 / 2 : ℝ) = 1 + -(5 / 2) by norm_num, Real.rpow_add h, Real.rpow_one]
  rw [h32]
  have hx2 : ‖x‖ ^ 2 = u - ε ^ 2 := by rw [hu]; ring
  rw [hx2]
  push_cast
  field_simp
  ring

/-- **The Laplacian of the regularized kernel**: `Δ K_ε = −3ε²/(4π(‖x‖² + ε²)^{5/2})` where
`‖x‖² + ε² > 0`, in the co-ordinates. -/
theorem coordLaplacian_regularKernel {ε : ℝ} {x : E3} (h : 0 < ‖x‖ ^ 2 + ε ^ 2) :
    coordLaplacian (regularKernel ε) x =
      -3 * ε ^ 2 / (4 * π * (‖x‖ ^ 2 + ε ^ 2) ^ (5 / 2 : ℝ)) := by
  rw [coordLaplacian_regularKernel_rpow h, Real.rpow_neg h.le]
  field_simp

/-! ### Smoothness and harmonicity -/

/-- The regularized kernel is smooth for `ε ≠ 0`. -/
theorem contDiff_regularKernel {ε : ℝ} (hε : ε ≠ 0) {n : WithTop ℕ∞} :
    ContDiff ℝ n (regularKernel ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hu : ‖x‖ ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have h1 : ContDiffAt ℝ n (fun y : E3 => ‖y‖ ^ 2 + ε ^ 2) x :=
    ((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt
  have h2 := (contDiffAt_const (c := 4 * π)).mul (h1.sqrt hu)
  refine h2.inv ?_
  have : 0 < √(‖x‖ ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **The Laplacian of the regularized kernel**: for `ε ≠ 0`,
`Δ K_ε x = −3ε²/(4π(‖x‖² + ε²)^{5/2})` at every point. -/
theorem laplacian_regularKernel {ε : ℝ} (hε : ε ≠ 0) (x : E3) :
    Δ (regularKernel ε) x = -3 * ε ^ 2 / (4 * π * (‖x‖ ^ 2 + ε ^ 2) ^ (5 / 2 : ℝ)) := by
  rw [← coordLaplacian_eq_laplacian (contDiff_regularKernel hε).contDiffAt,
    coordLaplacian_regularKernel (by positivity)]

/-- The kernel is smooth, of every order including `ω`, away from the origin. -/
theorem contDiffAt_newtonKernel {x : E3} (hx : x ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n newtonKernel x := by
  have h2 := (contDiffAt_const (c := 4 * π)).mul (contDiffAt_norm ℝ hx (n := n))
  refine h2.inv ?_
  have : 0 < ‖x‖ := norm_pos_iff.mpr hx
  positivity

/-- The kernel is analytic away from the origin. -/
theorem analyticAt_newtonKernel {x : E3} (hx : x ≠ 0) : AnalyticAt ℝ newtonKernel x :=
  (contDiffAt_newtonKernel hx (n := ω)).analyticAt

/-- The Laplacian of the kernel vanishes away from the origin, in the co-ordinates. -/
theorem coordLaplacian_newtonKernel {x : E3} (hx : x ≠ 0) : coordLaplacian newtonKernel x = 0 := by
  have h : 0 < ‖x‖ ^ 2 + (0 : ℝ) ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  rw [newtonKernel_eq_regularKernel, coordLaplacian_regularKernel h]
  simp

/-- The kernel is harmonic away from the origin. -/
theorem harmonicAt_newtonKernel {x : E3} (hx : x ≠ 0) :
    InnerProductSpace.HarmonicAt newtonKernel x := by
  refine ⟨contDiffAt_newtonKernel hx, ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  rw [Pi.zero_apply, ← coordLaplacian_eq_laplacian (contDiffAt_newtonKernel hy),
    coordLaplacian_newtonKernel hy]

/-- The derivative of the kernel away from the origin, `DK(x) v = −⟨x, v⟩/(4π‖x‖³)`. -/
theorem hasFDerivAt_newtonKernel {x : E3} (hx : x ≠ 0) :
    HasFDerivAt newtonKernel (-(4 * π * ‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h0 : 0 < ‖x‖ ^ 2 + 0 := by positivity
  have hfun : newtonKernel = fun y => kernelProfile 0 (‖y‖ ^ 2) := by
    funext y
    rw [newtonKernel_eq_regularKernel, regularKernel_eq_kernelProfile]
    simp
  rw [hfun]
  refine (hasFDerivAt_comp_normSq (hasDerivAt_kernelProfile h0)).congr_fderiv ?_
  congr 1
  rw [add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x),
    show ((2 : ℕ) : ℝ) * -(3 / 2) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg x),
    Real.rpow_natCast]
  field_simp
  ring

/-- The derivative of the kernel has the norm `1/(4π‖x‖²)` away from the origin. -/
theorem norm_fderiv_newtonKernel {x : E3} (hx : x ≠ 0) :
    ‖fderiv ℝ newtonKernel x‖ = (4 * π * ‖x‖ ^ 2)⁻¹ := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [(hasFDerivAt_newtonKernel hx).fderiv, norm_smul, innerSL_apply_norm, norm_neg,
    Real.norm_of_nonneg (by positivity)]
  field_simp

/-- The kernel is locally integrable. -/
theorem locallyIntegrable_newtonKernel : LocallyIntegrable newtonKernel := by
  refine locallyIntegrable_of_norm_le_rpow (by simp) (α := 1) (C := (4 * π)⁻¹)
    (by simp) (Eventually.of_forall fun x => ?_) ?_
  · rw [Real.rpow_neg_one, Real.norm_of_nonneg (newtonKernel_nonneg x),
      newtonKernel, mul_inv]
  · exact ((measurable_norm.const_mul _).inv).aestronglyMeasurable

/-! ### The peak function -/

/-- The peak function `3/(4π(‖x‖² + 1)^{5/2})`. -/
def peakFunction (x : E3) : ℝ := 3 / (4 * π) * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ))

/-- The peak function is nonnegative. -/
theorem peakFunction_nonneg (x : E3) : 0 ≤ peakFunction x := by
  unfold peakFunction
  positivity

/-- The radial integral `∫₀^∞ 3r²(r² + 1)^{-5/2} dr = 1`, with the primitive
`r³(r² + 1)^{-3/2}`. -/
theorem integral_Ioi_peakProfile :
    ∫ r in Ioi (0 : ℝ), 3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)) = 1 := by
  have hpos (r : ℝ) : 0 < r ^ 2 + 1 := by positivity
  set F : ℝ → ℝ := fun r => r ^ 3 * (r ^ 2 + 1) ^ (-(3 / 2 : ℝ)) with hF
  have hderiv (r : ℝ) : HasDerivAt F (3 * r ^ 2 * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ))) r := by
    have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + 1) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).add_const 1
    have h2 := h1.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (hpos r).ne')
    have h3 := (hasDerivAt_pow 3 r).mul h2
    refine h3.congr_deriv ?_
    have h32 : (r ^ 2 + 1) ^ (-(3 / 2 : ℝ)) =
        (r ^ 2 + 1) * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)) := by
      rw [show -(3 / 2 : ℝ) = 1 + -(5 / 2) by norm_num, Real.rpow_add (hpos r), Real.rpow_one]
    rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2) by norm_num, h32]
    push_cast
    ring
  have hlim : Tendsto F atTop (𝓝 1) := by
    have h1 : Tendsto (fun r : ℝ => r ^ 2 / (r ^ 2 + 1)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun r : ℝ => 1 - (r ^ 2 + 1)⁻¹) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)))
      rw [sub_zero] at h0
      refine h0.congr fun r => ?_
      field_simp
      ring
    have h2 := ((Real.continuousAt_rpow_const 1 (3 / 2 : ℝ) (Or.inl one_ne_zero)).tendsto).comp h1
    rw [Real.one_rpow] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp only [Function.comp_apply, hF]
    rw [Real.div_rpow (by positivity) (hpos r).le, Real.rpow_neg (hpos r).le, ← div_eq_mul_inv,
      ← Real.rpow_natCast r 2, ← Real.rpow_mul hr]
    norm_num
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := F) (a := 0) (l := 1)
    (hderiv 0).continuousAt.continuousWithinAt (fun r _ => hderiv r)
    (fun r _ => by positivity) hlim
  rw [this]
  simp [hF]

/-- The peak function has the integral one. -/
theorem integral_peakFunction : ∫ x, peakFunction x = 1 := by
  have h := integral_fun_norm_addHaar (volume : Measure E3)
    (fun r => 3 / (4 * π) * (r ^ 2 + 1) ^ (-(5 / 2 : ℝ)))
  have hvol : (volume : Measure E3).real (ball 0 1) = π * 4 / 3 := by
    simp [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (3 - 1) • (3 / (4 * π) * (y ^ 2 + 1) ^ (-(5 / 2 : ℝ))) =
      (4 * π)⁻¹ := by
    have hfun : (fun y : ℝ => y ^ (3 - 1) • (3 / (4 * π) * (y ^ 2 + 1) ^ (-(5 / 2 : ℝ)))) =
        fun y => (4 * π)⁻¹ * (3 * y ^ 2 * (y ^ 2 + 1) ^ (-(5 / 2 : ℝ))) := by
      funext y
      simp only [smul_eq_mul]
      ring
    rw [hfun, integral_const_mul, integral_Ioi_peakProfile, mul_one]
  simp only [finrank_euclideanSpace_fin] at h
  unfold peakFunction
  rw [h, hvol, hI]
  simp only [nsmul_eq_mul, smul_eq_mul]
  field_simp
  norm_num

/-- The peak function decays faster than `‖x‖⁻³`. -/
theorem tendsto_norm_pow_mul_peakFunction :
    Tendsto (fun x : E3 => ‖x‖ ^ Module.finrank ℝ E3 * peakFunction x) (cobounded E3)
      (𝓝 0) := by
  rw [finrank_euclideanSpace_fin]
  have hlim : Tendsto (fun x : E3 => 3 / (4 * π) * (‖x‖ ^ 2 + 1)⁻¹) (cobounded E3) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => 3 / (4 * π) * (r ^ 2 + 1)⁻¹) atTop (𝓝 (3 / (4 * π) * 0)) :=
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)))
    rw [mul_zero] at h0
    exact h0.comp tendsto_norm_cobounded_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun x => ?_)
    (fun x => ?_)
  · exact mul_nonneg (by positivity) (peakFunction_nonneg x)
  · have hu : 0 < ‖x‖ ^ 2 + 1 := by positivity
    have h3 : ‖x‖ ^ 3 ≤ (‖x‖ ^ 2 + 1) ^ (3 / 2 : ℝ) := by
      have : ‖x‖ ^ 3 = (‖x‖ ^ 2) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg _)]
        norm_num
      rw [this]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hsplit : (‖x‖ ^ 2 + 1)⁻¹ =
        (‖x‖ ^ 2 + 1) ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_add hu, ← Real.rpow_neg_one]
      norm_num
    have hw : 0 ≤ (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ)) := by positivity
    have hc : 0 ≤ 3 / (4 * π) := by positivity
    unfold peakFunction
    rw [hsplit]
    calc ‖x‖ ^ 3 * (3 / (4 * π) * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ)))
        = 3 / (4 * π) * (‖x‖ ^ 3 * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ 3 / (4 * π) * ((‖x‖ ^ 2 + 1) ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hw) hc

/-- `−Δ K_ε` is the peak function rescaled by `ε`: `−Δ K_ε(y) = ε⁻³ P(y/ε)`. -/
theorem neg_coordLaplacian_regularKernel {ε : ℝ} (hε : 0 < ε) (y : E3) :
    -coordLaplacian (regularKernel ε) y = ε⁻¹ ^ 3 * peakFunction (ε⁻¹ • y) := by
  have hu : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity
  rw [coordLaplacian_regularKernel_rpow hu, neg_mul, neg_neg]
  unfold peakFunction
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le), mul_pow]
  have hsc : ε⁻¹ ^ 2 * ‖y‖ ^ 2 + 1 = (ε ^ 2)⁻¹ * (‖y‖ ^ 2 + ε ^ 2) := by
    field_simp
  have h5 : (ε ^ 2) ^ (5 / 2 : ℝ) = ε ^ 5 := by
    rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    norm_num
  rw [hsc, Real.mul_rpow (by positivity) hu.le, Real.inv_rpow (sq_nonneg ε),
    Real.rpow_neg (sq_nonneg ε), inv_inv, h5]
  field_simp

/-! ### The point source -/

/-- The integrals of the regularized kernel against `Δχ` converge to the integral of the kernel
against `Δχ` as `ε → 0⁺`. -/
theorem tendsto_integral_regularKernel_mul {L : E3 → ℝ} (hL : Continuous L)
    (hcL : HasCompactSupport L) :
    Tendsto (fun ε => ∫ y, regularKernel ε y * L y) (𝓝[>] 0)
      (𝓝 (∫ y, newtonKernel y * L y)) := by
  have hae : ∀ᵐ y : E3, y ≠ 0 := by
    rw [ae_iff]
    simp
  refine tendsto_integral_filter_of_dominated_convergence (fun y => newtonKernel y * |L y|)
    ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact ((contDiff_regularKernel hε.ne' (n := 0)).continuous.mul hL).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    filter_upwards [hae] with y hy
    rw [norm_mul, Real.norm_of_nonneg (regularKernel_pos hε.ne' y).le, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (regularKernel_le_newtonKernel ε hy) (abs_nonneg _)
  · simpa [smul_eq_mul] using
      locallyIntegrable_newtonKernel.integrable_smul_right_of_hasCompactSupport hL.abs hcL.abs
  · filter_upwards [hae] with y hy
    have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hc : ContinuousAt (fun ε : ℝ => regularKernel ε y) 0 := by
      unfold regularKernel
      refine ContinuousAt.inv₀ (by fun_prop) ?_
      have : 0 < √(‖y‖ ^ 2 + (0 : ℝ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
      positivity
    have h0 : Tendsto (fun ε => regularKernel ε y) (𝓝[>] 0) (𝓝 (newtonKernel y)) := by
      rw [newtonKernel_eq_regularKernel]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    exact h0.mul_const _

/-- **The point source in pairing form**: for every `C²` function `χ` of compact support,
`∫ K Δχ = −χ(0)`, with the Laplacian in the co-ordinates. -/
theorem integral_newtonKernel_mul_coordLaplacian {χ : E3 → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) :
    ∫ y, newtonKernel y * coordLaplacian χ y = -χ 0 := by
  have hlim1 := tendsto_integral_regularKernel_mul (continuous_coordLaplacian hχ)
    (hasCompactSupport_coordLaplacian hcχ)
  have hpk := tendsto_integral_comp_smul_smul_of_integrable (μ := (volume : Measure E3))
    peakFunction_nonneg integral_peakFunction tendsto_norm_pow_mul_peakFunction
    (hχ.continuous.integrable_of_hasCompactSupport hcχ) hχ.continuous.continuousAt
  have hlim2 : Tendsto (fun ε => ∫ y, regularKernel ε y * coordLaplacian χ y) (𝓝[>] 0)
      (𝓝 (-χ 0)) := by
    refine Tendsto.congr' ?_ (hpk.comp tendsto_inv_nhdsGT_zero).neg
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [integral_mul_coordLaplacian (contDiff_regularKernel hε.ne') hχ hcχ, Function.comp_apply,
      ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [finrank_euclideanSpace_fin, smul_eq_mul]
    rw [← neg_coordLaplacian_regularKernel hε]
    ring
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The point source in pairing form**, `ΔK = −δ` tested against a `C²` function `χ` of compact
support: `∫ K Δχ = −χ(0)`. -/
theorem integral_newtonKernel_mul_laplacian {χ : E3 → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hcχ : HasCompactSupport χ) : ∫ y, newtonKernel y * Δ χ y = -χ 0 := by
  rw [laplacian_eq_coordLaplacian hχ]
  exact integral_newtonKernel_mul_coordLaplacian hχ hcχ

end ProjectAinos.SmoothGeometry.Potential
