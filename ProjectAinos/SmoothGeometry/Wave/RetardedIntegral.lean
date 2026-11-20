/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.NewtonKernel
public import ProjectAinos.SmoothGeometry.Minkowski.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# The retarded integral

Space-time is `ℝ × ℝ³` with `ℝ³ = EuclideanSpace ℝ (Fin 3)`, and `□ = ∂ₜ² − Δ` is the wave
operator `waveOperator`, with the partial derivatives `timeDeriv` and `spaceDeriv i`; it is
`−box` for the operator `box = −∂₀² + Δ` of the electrodynamics. The **retarded integral** of a
function `f` is

  `retardedIntegral f (t, x) = ∫ f(t − ‖y‖, x − y)/(4π‖y‖) dy`

(Landau–Lifshitz, *The Classical Theory of Fields*, §62). It is defined for functions with values
in a normed space, so that the derivatives of `f` are retarded in the same way.

* `integral_wave_div_norm`: **the retarded identity**
  `∫ □f(t − ‖y‖, x − y)/(4π‖y‖) dy = f(t, x)` for a `C²` function `f` whose support meets the past
  cone of `(t, x)` in a bounded set. Away from the origin `□f(t − ‖y‖, x − y)/‖y‖ = div V(y)` for
  the field `Vᵢ = ∂ᵢf/‖y‖ − ∂ₜf yᵢ/‖y‖² − f yᵢ/‖y‖³` at the retarded point
  (`retardedField`, `sum_fderiv_retardedField`). With the smooth cutoff `χ_ε(y) = ψ(‖y‖/ε − 1)`
  the integral of `div V χ_ε` is `−∫ V · ∇χ_ε = 4π ∫ ε⁻³ k(y/ε) q(y) dy`
  (`integral_wave_mul_cutoff`), where `k` is the normalized shell kernel `shellKernel` and
  `q = f + ‖y‖ ∂ₜf − y · ∇f` (`fluxDensity`) has `q(0) = f(t, x)`; as `ε → 0⁺` the left side
  tends to the retarded integral of `□f` and the right side to `4π f(t, x)`, which is the flux of
  `V` through a small sphere.
* `SubluminalSupport R v₀ f`: the support lies in `‖x‖ ≤ R + v₀|t|` with `0 ≤ v₀ < 1`. A function
  of compact support has one (`exists_subluminalSupport_of_hasCompactSupport`), and so has a
  profile carried with a velocity of speed below `1` (`subluminalSupport_moving`; with a bump
  and the speed `1/2`, `subluminalSupport_movingBump`). Beyond the
  radius `pastRadius R v₀ p₀` the past cones of the points near `p₀` miss the support
  (`SubluminalSupport.notMem_tsupport`), so the integrand has compact support locally uniformly.
* `contDiff_retardedIntegral`: the retarded integral of a `Cⁿ` function with subluminal support is
  `Cⁿ` for `n ≤ ∞`, and `fderiv_retardedIntegral`, `timeDeriv_retardedIntegral`,
  `spaceDeriv_retardedIntegral`: the derivatives commute with the integral.
* `wave_retardedIntegral`: **the retarded integral solves the wave equation**,
  `□(retardedIntegral f) = f`, for a `C²` function with subluminal support.
* Causal support: `retardedIntegral_eq_zero_of_support`, the retarded integral vanishes at a point
  whose past cone `pastCone` misses the support; `retardedIntegral_eq_zero_of_le`, a source that
  vanishes up to a time gives a potential that vanishes up to that time;
  `retardedIntegral_eq_zero_of_far`, a source switched on at the time `T` in the ball `‖x‖ ≤ ρ`
  gives zero for `‖x‖ > ρ + (t − T)`; `norm_le_of_retardedIntegral_ne_zero`, for a source that
  vanishes in the past the spatial support is bounded on every finite interval of time.
* Space-time: `timeSpaceEquiv` is the splitting `v ↦ (v⁰, 𝐯)` of `MinkowskiModel 3`, with the
  inverse `Minkowski.vector`; `fderiv_comp_timeSpaceEquiv_zero` and
  `fderiv_comp_timeSpaceEquiv_succ` carry the derivatives along the axes `e₀` and `eᵢ₊₁` to
  `timeDeriv` and `spaceDeriv i`, and `retardedIntegral_comp_symm` writes the retarded integral of
  a function on space-time as `∫ k(v − (‖y‖, y))/(4π‖y‖) dy`.

Uniqueness among the solutions that vanish in the past is proved in
`ProjectAinos.Electrodynamics.RetardedPotential` with the energy identity of the electrodynamics.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The derivatives on `ℝ × ℝ³` -/

/-- The time derivative `∂ₜf` of a function on `ℝ × ℝ³`. -/
def timeDeriv (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ := fderiv ℝ f p (1, 0)

/-- The spatial derivative `∂ᵢf` of a function on `ℝ × ℝ³`. -/
def spaceDeriv (i : Fin 3) (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  fderiv ℝ f p (0, EuclideanSpace.single i 1)

/-- The wave operator `□f = ∂ₜ²f − Δf` on `ℝ × ℝ³`. -/
def waveOperator (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  timeDeriv (timeDeriv f) p - ∑ i, spaceDeriv i (spaceDeriv i f) p

/-- The derivative of the norm away from the origin, `D‖·‖(y) = ⟨y, ·⟩/‖y‖`. -/
theorem hasFDerivAt_norm_of_ne_zero {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fun z : E3 => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.sqrt (by positivity)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, two_smul, add_apply]
  field_simp
  ring

/-- The derivative `v ↦ (−⟨y, v⟩/‖y‖, −v)` of the retarded point `y ↦ (t − ‖y‖, x − y)`. -/
def retardedDeriv (y : E3) : E3 →L[ℝ] ℝ × E3 :=
  (-(‖y‖⁻¹ • innerSL ℝ y)).prod (-ContinuousLinearMap.id ℝ E3)

/-- The retarded point `y ↦ (t − ‖y‖, x − y)` has the derivative `retardedDeriv y` away from the
origin. -/
theorem hasFDerivAt_retarded (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fun z : E3 => (t - ‖z‖, x - z)) (retardedDeriv y) y :=
  ((hasFDerivAt_norm_of_ne_zero hy).const_sub t).prodMk ((hasFDerivAt_id y).const_sub x)

/-- The derivative of a function along the retarded point, in the direction `eᵢ`:
`∂ᵢ [b(t − ‖y‖, x − y)] = −(yᵢ/‖y‖) ∂ₜb − ∂ᵢb`. -/
theorem fderiv_retardedDeriv_single (b : ℝ × E3 → ℝ) (q : ℝ × E3) (y : E3) (i : Fin 3) :
    (fderiv ℝ b q).comp (retardedDeriv y) (EuclideanSpace.single i 1) =
      -(y i / ‖y‖) * timeDeriv b q - spaceDeriv i b q := by
  have hv : retardedDeriv y (EuclideanSpace.single i 1) =
      (-(y i / ‖y‖)) • ((1 : ℝ), (0 : E3)) - ((0 : ℝ), EuclideanSpace.single i 1) := by
    simp only [retardedDeriv, ContinuousLinearMap.prod_apply, neg_apply,
      smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      ContinuousLinearMap.id_apply]
    ext <;> simp [div_eq_inv_mul]
  rw [ContinuousLinearMap.comp_apply, hv, map_sub, map_smul, smul_eq_mul]
  rfl

/-- A function along the retarded point has the derivative `Db ∘ retardedDeriv y` away from the
origin. -/
theorem hasFDerivAt_comp_retarded {b : ℝ × E3 → ℝ} (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0)
    (hb : DifferentiableAt ℝ b (t - ‖y‖, x - y)) :
    HasFDerivAt (fun z : E3 => b (t - ‖z‖, x - z))
      ((fderiv ℝ b (t - ‖y‖, x - y)).comp (retardedDeriv y)) y :=
  hb.hasFDerivAt.comp y (hasFDerivAt_retarded t x hy)

/-- For a function that is `C²` at `q`, the derivative along `v` of the derivative along `w` is
the second derivative on `(v, w)`. -/
theorem fderiv_fderiv_apply_eq {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hf : ContDiffAt ℝ 2 f q)
    (v w : ℝ × E3) :
    fderiv ℝ (fun p => fderiv ℝ f p w) q v = fderiv ℝ (fderiv ℝ f) q v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- The mixed derivatives of a `C²` function commute: `∂ₜ∂ᵢf = ∂ᵢ∂ₜf`. -/
theorem timeDeriv_spaceDeriv {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hf : ContDiffAt ℝ 2 f q)
    (i : Fin 3) : timeDeriv (spaceDeriv i f) q = spaceDeriv i (timeDeriv f) q := by
  have hs := hf.isSymmSndFDerivAt (by simp)
  change fderiv ℝ (fun p => fderiv ℝ f p (0, EuclideanSpace.single i 1)) q (1, 0) =
    fderiv ℝ (fun p => fderiv ℝ f p (1, 0)) q (0, EuclideanSpace.single i 1)
  rw [fderiv_fderiv_apply_eq hf, fderiv_fderiv_apply_eq hf]
  exact hs _ _

/-! ### The field whose divergence is the retarded wave operator -/

/-- The field `V` with `div V = □f(t − ‖y‖, x − y)/‖y‖` away from the origin,
`Vᵢ(y) = ∂ᵢf/‖y‖ − ∂ₜf yᵢ/‖y‖² − f yᵢ/‖y‖³`, the function and its derivatives taken at the
retarded point `(t − ‖y‖, x − y)`. -/
def retardedField (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) (i : Fin 3) (y : E3) : ℝ :=
  spaceDeriv i f (t - ‖y‖, x - y) * ‖y‖⁻¹ -
    timeDeriv f (t - ‖y‖, x - y) * (y i * (‖y‖ ^ 2)⁻¹) -
    f (t - ‖y‖, x - y) * (y i * (‖y‖ ^ 3)⁻¹)

/-- The first derivatives of a `C²` function are `C¹`. -/
theorem contDiff_timeDeriv {n : ℕ∞ω} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (timeDeriv f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

/-- The first derivatives of a `C²` function are `C¹`. -/
theorem contDiff_spaceDeriv {n : ℕ∞ω} {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ (n + 1) f)
    (i : Fin 3) : ContDiff ℝ n (spaceDeriv i f) :=
  (hf.fderiv_right le_rfl).clm_apply contDiff_const

/-- The derivative `∂ᵢVᵢ` of a component of the field away from the origin. -/
theorem fderiv_retardedField_single {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3)
    {y : E3} (hy : y ≠ 0) (i : Fin 3) :
    fderiv ℝ (retardedField f t x i) y (EuclideanSpace.single i 1) =
      (-(y i / ‖y‖) * timeDeriv (spaceDeriv i f) (t - ‖y‖, x - y) -
          spaceDeriv i (spaceDeriv i f) (t - ‖y‖, x - y)) * ‖y‖⁻¹ -
        spaceDeriv i f (t - ‖y‖, x - y) * (y i / ‖y‖ ^ 3) -
        ((-(y i / ‖y‖) * timeDeriv (timeDeriv f) (t - ‖y‖, x - y) -
          spaceDeriv i (timeDeriv f) (t - ‖y‖, x - y)) * (y i / ‖y‖ ^ 2) +
          timeDeriv f (t - ‖y‖, x - y) * (1 / ‖y‖ ^ 2 - 2 * y i ^ 2 / ‖y‖ ^ 4)) -
        ((-(y i / ‖y‖) * timeDeriv f (t - ‖y‖, x - y) - spaceDeriv i f (t - ‖y‖, x - y)) *
            (y i / ‖y‖ ^ 3) +
          f (t - ‖y‖, x - y) * (1 / ‖y‖ ^ 3 - 3 * y i ^ 2 / ‖y‖ ^ 5)) := by
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hN := hasFDerivAt_norm_of_ne_zero hy
  have hNinv := (hasDerivAt_inv hr.ne').comp_hasFDerivAt y hN
  have hN2 := ((hasDerivAt_pow 2 ‖y‖).inv (by positivity)).comp_hasFDerivAt y hN
  have hN3 := ((hasDerivAt_pow 3 ‖y‖).inv (by positivity)).comp_hasFDerivAt y hN
  have hP : HasFDerivAt (fun z : E3 => z i) (EuclideanSpace.proj i : E3 →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt
  have h1 := hasFDerivAt_comp_retarded t x hy
    (((contDiff_spaceDeriv (n := 1) hf i).differentiable (by norm_num)) (t - ‖y‖, x - y))
  have h2 := hasFDerivAt_comp_retarded t x hy
    (((contDiff_timeDeriv (n := 1) hf).differentiable (by norm_num)) (t - ‖y‖, x - y))
  have h3 := hasFDerivAt_comp_retarded t x hy ((hf.differentiable (by norm_num)) (t - ‖y‖, x - y))
  have H := ((h1.mul hNinv).sub (h2.mul (hP.mul hN2))).sub (h3.mul (hP.mul hN3))
  have H' : HasFDerivAt (retardedField f t x i) _ y :=
    H.congr_of_eventuallyEq (Eventually.of_forall fun z => rfl)
  rw [H'.fderiv]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, fderiv_retardedDeriv_single,
    innerSL_apply_apply, EuclideanSpace.inner_single_right]
  simp
  field_simp
  ring

/-- **The divergence of the field**: away from the origin, `div V(y) = □f(t − ‖y‖, x − y)/‖y‖`
for a `C²` function `f`. -/
theorem sum_fderiv_retardedField {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3)
    {y : E3} (hy : y ≠ 0) :
    ∑ i, fderiv ℝ (retardedField f t x i) y (EuclideanSpace.single i 1) =
      waveOperator f (t - ‖y‖, x - y) / ‖y‖ := by
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hS : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - ‖y‖ ^ 2 = 0 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    ring
  simp only [fderiv_retardedField_single hf t x hy, timeDeriv_spaceDeriv hf.contDiffAt]
  rw [Fin.sum_univ_three, waveOperator, Fin.sum_univ_three]
  generalize timeDeriv (timeDeriv f) (t - ‖y‖, x - y) = A
  generalize timeDeriv f (t - ‖y‖, x - y) = a
  generalize f (t - ‖y‖, x - y) = c
  have key : ∀ (B C b : Fin 3 → ℝ), ∑ i : Fin 3, ((-(y i / ‖y‖) * B i - C i) * ‖y‖⁻¹ -
        b i * (y i / ‖y‖ ^ 3) - ((-(y i / ‖y‖) * A - B i) * (y i / ‖y‖ ^ 2) +
          a * (1 / ‖y‖ ^ 2 - 2 * y i ^ 2 / ‖y‖ ^ 4)) -
        ((-(y i / ‖y‖) * a - b i) * (y i / ‖y‖ ^ 3) +
          c * (1 / ‖y‖ ^ 3 - 3 * y i ^ 2 / ‖y‖ ^ 5))) =
      (A - ∑ i, C i) / ‖y‖ + (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - ‖y‖ ^ 2) *
        (A / ‖y‖ ^ 3 + 3 * a / ‖y‖ ^ 4 + 3 * c / ‖y‖ ^ 5) := by
    intro B C b
    simp only [Fin.sum_univ_three]
    field_simp
    ring
  have := key (fun i => spaceDeriv i (timeDeriv f) (t - ‖y‖, x - y))
    (fun i => spaceDeriv i (spaceDeriv i f) (t - ‖y‖, x - y))
    (fun i => spaceDeriv i f (t - ‖y‖, x - y))
  simp only [Fin.sum_univ_three, hS, zero_mul, add_zero] at this
  exact this

/-! ### Supports -/

/-- The time derivative is supported in the support of the function. -/
theorem tsupport_timeDeriv_subset (f : ℝ × E3 → ℝ) : tsupport (timeDeriv f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (1, 0)

/-- The spatial derivatives are supported in the support of the function. -/
theorem tsupport_spaceDeriv_subset (i : Fin 3) (f : ℝ × E3 → ℝ) :
    tsupport (spaceDeriv i f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (0, EuclideanSpace.single i 1)

/-- The time derivative vanishes outside the support. -/
theorem timeDeriv_eq_zero_of_notMem {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hq : q ∉ tsupport f) :
    timeDeriv f q = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hq (tsupport_timeDeriv_subset f h)

/-- The spatial derivatives vanish outside the support. -/
theorem spaceDeriv_eq_zero_of_notMem {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hq : q ∉ tsupport f)
    (i : Fin 3) : spaceDeriv i f q = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hq (tsupport_spaceDeriv_subset i f h)

/-- The wave operator vanishes outside the support. -/
theorem waveOperator_eq_zero_of_notMem {f : ℝ × E3 → ℝ} {q : ℝ × E3} (hq : q ∉ tsupport f) :
    waveOperator f q = 0 := by
  have ht : q ∉ tsupport (timeDeriv f) := fun h => hq (tsupport_timeDeriv_subset f h)
  have hs : ∀ i, q ∉ tsupport (spaceDeriv i f) := fun i h => hq (tsupport_spaceDeriv_subset i f h)
  simp [waveOperator, timeDeriv_eq_zero_of_notMem ht, spaceDeriv_eq_zero_of_notMem (hs _)]

/-! ### The cutoff and the shell kernel -/

/-- The derivative of the smooth transition. -/
theorem hasDerivAt_smoothTransition (s : ℝ) :
    HasDerivAt smoothTransition (deriv smoothTransition s) s :=
  ((smoothTransition.contDiff (n := 1)).differentiable (by norm_num) s).hasDerivAt

/-- The smooth transition is nondecreasing. -/
theorem deriv_smoothTransition_nonneg (s : ℝ) : 0 ≤ deriv smoothTransition s :=
  smoothTransition.monotone.deriv_nonneg

/-- The derivative of the smooth transition vanishes on `s < 0`. -/
theorem deriv_smoothTransition_of_neg {s : ℝ} (hs : s < 0) : deriv smoothTransition s = 0 := by
  have h : smoothTransition =ᶠ[𝓝 s] fun _ => 0 :=
    eventually_of_mem (Iio_mem_nhds hs) fun r hr => smoothTransition.zero_of_nonpos (le_of_lt hr)
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the smooth transition vanishes on `s > 1`. -/
theorem deriv_smoothTransition_of_one_lt {s : ℝ} (hs : 1 < s) : deriv smoothTransition s = 0 := by
  have h : smoothTransition =ᶠ[𝓝 s] fun _ => 1 :=
    eventually_of_mem (Ioi_mem_nhds hs) fun r hr => smoothTransition.one_of_one_le (le_of_lt hr)
  rw [h.deriv_eq, deriv_const]

/-- `∫₀^∞ ψ'(r − 1) dr = 1` for the smooth transition `ψ`. -/
theorem integral_Ioi_deriv_smoothTransition :
    ∫ r in Ioi (0 : ℝ), deriv smoothTransition (r - 1) = 1 := by
  have hd (r : ℝ) : HasDerivAt (fun r => smoothTransition (r - 1))
      (deriv smoothTransition (r - 1)) r := by
    exact HasDerivAt.comp_sub_const r 1 (hasDerivAt_smoothTransition (r - 1))
  have hlim : Tendsto (fun r => smoothTransition (r - 1)) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with r hr
    rw [smoothTransition.one_of_one_le (by linarith)]
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (hd 0).continuousAt.continuousWithinAt
    (fun r _ => hd r) (fun r _ => deriv_smoothTransition_nonneg _) hlim]
  simp

/-- The shell kernel `ψ'(‖z‖ − 1)/(4π‖z‖²)`, supported in the shell `1 ≤ ‖z‖ ≤ 2`. -/
def shellKernel (z : E3) : ℝ := deriv smoothTransition (‖z‖ - 1) / (4 * π * ‖z‖ ^ 2)

/-- The shell kernel is nonnegative. -/
theorem shellKernel_nonneg (z : E3) : 0 ≤ shellKernel z :=
  div_nonneg (deriv_smoothTransition_nonneg _) (by positivity)

/-- The shell kernel has the integral one. -/
theorem integral_shellKernel : ∫ z, shellKernel z = 1 := by
  have h := integral_fun_norm_addHaar (volume : Measure E3)
    (fun r => deriv smoothTransition (r - 1) / (4 * π * r ^ 2))
  have hvol : (volume : Measure E3).real (ball 0 1) = π * 4 / 3 := by
    simp [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  have hI : ∫ r in Ioi (0 : ℝ), r ^ (3 - 1) • (deriv smoothTransition (r - 1) / (4 * π * r ^ 2)) =
      (4 * π)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun r => (4 * π)⁻¹ *
      deriv smoothTransition (r - 1)) fun r (hr : 0 < r) => by
        simp only [smul_eq_mul]
        field_simp, integral_const_mul, integral_Ioi_deriv_smoothTransition, mul_one]
  simp only [finrank_euclideanSpace_fin] at h
  unfold shellKernel
  rw [h, hvol, hI]
  simp only [nsmul_eq_mul, smul_eq_mul]
  field_simp
  norm_num

/-- The shell kernel vanishes outside the ball of radius `2`. -/
theorem shellKernel_eq_zero_of_two_lt {z : E3} (hz : 2 < ‖z‖) : shellKernel z = 0 := by
  rw [shellKernel, deriv_smoothTransition_of_one_lt (by linarith), zero_div]

/-- The shell kernel decays faster than `‖z‖⁻³`. -/
theorem tendsto_norm_pow_mul_shellKernel :
    Tendsto (fun z : E3 => ‖z‖ ^ Module.finrank ℝ E3 * shellKernel z) (Bornology.cobounded E3)
      (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_norm_cobounded_atTop (E := E3)).eventually (eventually_gt_atTop 2)]
    with z hz
  rw [shellKernel_eq_zero_of_two_lt hz, mul_zero]

/-- The cutoff `χ_ε(y) = ψ(‖y‖/ε − 1)` with the smooth transition `ψ`: it vanishes for
`‖y‖ ≤ ε` and is `1` for `‖y‖ ≥ 2ε`. -/
def cutoff (ε : ℝ) (y : E3) : ℝ := smoothTransition (‖y‖ / ε - 1)

/-- The cutoff vanishes on the ball of radius `ε`. -/
theorem cutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {y : E3} (hy : ‖y‖ ≤ ε) : cutoff ε y = 0 := by
  refine smoothTransition.zero_of_nonpos ?_
  rw [sub_nonpos, div_le_one hε]
  exact hy

/-- The cutoff is `1` outside the ball of radius `2ε`. -/
theorem cutoff_eq_one {ε : ℝ} (hε : 0 < ε) {y : E3} (hy : 2 * ε ≤ ‖y‖) : cutoff ε y = 1 := by
  refine smoothTransition.one_of_one_le ?_
  rw [le_sub_iff_add_le, le_div_iff₀ hε]
  linarith

/-- The cutoff vanishes near the origin. -/
theorem cutoff_eventuallyEq_zero {ε : ℝ} (hε : 0 < ε) : cutoff ε =ᶠ[𝓝 0] fun _ => 0 :=
  eventually_of_mem (ball_mem_nhds 0 hε) fun y hy =>
    cutoff_eq_zero hε (by rw [mem_ball_zero_iff] at hy; exact hy.le)

/-- The derivative of the cutoff away from the origin. -/
theorem hasFDerivAt_cutoff (ε : ℝ) {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (cutoff ε)
      (deriv smoothTransition (‖y‖ / ε - 1) • (ε⁻¹ • (‖y‖⁻¹ • innerSL ℝ y))) y := by
  have h := (hasDerivAt_smoothTransition (‖y‖ / ε - 1)).comp_hasFDerivAt y
    (((hasFDerivAt_norm_of_ne_zero hy).mul_const ε⁻¹).sub_const 1)
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun z => by
    simp [cutoff, Function.comp, div_eq_mul_inv])

/-- The cutoff is smooth. -/
theorem contDiff_cutoff {ε : ℝ} (hε : 0 < ε) {n : ℕ∞} : ContDiff ℝ n (cutoff ε) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    exact contDiffAt_const.congr_of_eventuallyEq (cutoff_eventuallyEq_zero hε)
  · exact smoothTransition.contDiffAt.comp y
      (((contDiffAt_norm ℝ hy).div_const ε).sub contDiffAt_const)

/-- The cutoff takes values in `[0, 1]`. -/
theorem cutoff_mem_Icc (ε : ℝ) (y : E3) : cutoff ε y ∈ Icc (0 : ℝ) 1 :=
  ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩

/-! ### The flux through a small sphere -/

/-- The density `q(y) = f + ‖y‖ ∂ₜf − Σᵢ yᵢ ∂ᵢf` at the retarded point `(t − ‖y‖, x − y)`, with
`q(0) = f(t, x)`: the radial component of the field is `V(y) · y/‖y‖ = −q(y)/‖y‖²`. -/
def fluxDensity (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) (y : E3) : ℝ :=
  f (t - ‖y‖, x - y) + ‖y‖ * timeDeriv f (t - ‖y‖, x - y) -
    ∑ i, spaceDeriv i f (t - ‖y‖, x - y) * y i

/-- The radial component of the field: `Σᵢ Vᵢ(y) yᵢ = −q(y)/‖y‖` away from the origin. -/
theorem sum_retardedField_mul {f : ℝ × E3 → ℝ} (t : ℝ) (x : E3) {y : E3} (hy : y ≠ 0) :
    ∑ i, retardedField f t x i y * y i = -fluxDensity f t x y / ‖y‖ := by
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hS : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - ‖y‖ ^ 2 = 0 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    ring
  have key : ∑ i, retardedField f t x i y * y i = -fluxDensity f t x y / ‖y‖ +
      (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - ‖y‖ ^ 2) *
        (-timeDeriv f (t - ‖y‖, x - y) / ‖y‖ ^ 2 - f (t - ‖y‖, x - y) / ‖y‖ ^ 3) := by
    simp only [retardedField, fluxDensity, Fin.sum_univ_three]
    field_simp
    ring
  rw [key, hS, zero_mul, add_zero]

/-- The field is `C¹` away from the origin. -/
theorem contDiffAt_retardedField {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3)
    {y : E3} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ 1 (retardedField f t x i) y := by
  have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hn : ContDiffAt ℝ 1 (fun z : E3 => ‖z‖) y := contDiffAt_norm ℝ hy
  have hΦ : ContDiffAt ℝ 1 (fun z : E3 => (t - ‖z‖, x - z)) y :=
    (contDiffAt_const.sub hn).prodMk (contDiffAt_const.sub contDiffAt_id)
  have h1 := (contDiff_spaceDeriv (n := 1) hf i).contDiffAt.comp y hΦ
  have h2 := (contDiff_timeDeriv (n := 1) hf).contDiffAt.comp y hΦ
  have h3 := (hf.of_le (by norm_num)).contDiffAt.comp y hΦ
  have hP : ContDiffAt ℝ 1 (fun z : E3 => z i) y :=
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.contDiffAt
  exact ((h1.mul (hn.inv hr)).sub (h2.mul (hP.mul ((hn.pow 2).inv (pow_ne_zero 2 hr))))).sub
    (h3.mul (hP.mul ((hn.pow 3).inv (pow_ne_zero 3 hr))))

/-- The field vanishes where the retarded point is outside the support of `f`. -/
theorem retardedField_eq_zero {f : ℝ × E3 → ℝ} {t : ℝ} {x y : E3}
    (hy : (t - ‖y‖, x - y) ∉ tsupport f) (i : Fin 3) : retardedField f t x i y = 0 := by
  simp [retardedField, spaceDeriv_eq_zero_of_notMem hy, timeDeriv_eq_zero_of_notMem hy,
    image_eq_zero_of_notMem_tsupport hy]

/-- The density `q` vanishes where the retarded point is outside the support of `f`. -/
theorem fluxDensity_eq_zero {f : ℝ × E3 → ℝ} {t : ℝ} {x y : E3}
    (hy : (t - ‖y‖, x - y) ∉ tsupport f) : fluxDensity f t x y = 0 := by
  simp [fluxDensity, spaceDeriv_eq_zero_of_notMem hy, timeDeriv_eq_zero_of_notMem hy,
    image_eq_zero_of_notMem_tsupport hy]

/-- The density `q` is continuous for a `C¹` function. -/
theorem continuous_fluxDensity {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) (t : ℝ) (x : E3) :
    Continuous (fluxDensity f t x) := by
  have hΦ : Continuous fun z : E3 => (t - ‖z‖, x - z) := by fun_prop
  have h1 : ∀ i, Continuous (spaceDeriv i f) := fun i =>
    (contDiff_spaceDeriv (n := 0) (by simpa using hf) i).continuous
  have h2 : Continuous (timeDeriv f) := (contDiff_timeDeriv (n := 0) (by simpa using hf)).continuous
  unfold fluxDensity
  refine ((hf.continuous.comp hΦ).add (continuous_norm.mul (h2.comp hΦ))).sub
    (continuous_finsetSum _ fun i _ => ((h1 i).comp hΦ).mul ?_)
  exact (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous

/-- The density at the origin is `q(0) = f(t, x)`. -/
theorem fluxDensity_zero (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) : fluxDensity f t x 0 = f (t, x) := by
  simp [fluxDensity]

/-- The wave operator of a `C²` function is continuous. -/
theorem continuous_waveOperator {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (waveOperator f) := by
  have ht : Continuous (timeDeriv (timeDeriv f)) :=
    (contDiff_timeDeriv (n := 0) (contDiff_timeDeriv (n := 1) hf)).continuous
  have hs : ∀ i, Continuous (spaceDeriv i (spaceDeriv i f)) := fun i =>
    (contDiff_spaceDeriv (n := 0) (contDiff_spaceDeriv (n := 1) hf i) i).continuous
  exact ht.sub (continuous_finsetSum _ fun i _ => hs i)

/-- The integral of a derivative of a `C¹` function of compact support vanishes. -/
theorem integral_fderiv_eq_zero {W : E3 → ℝ} (hW : ContDiff ℝ 1 W) (hc : HasCompactSupport W)
    (v : E3) : ∫ y, fderiv ℝ W y v = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure E3))
    (f := fun _ => (1 : ℝ)) (g := W) (v := v) (by simp) (by
      simpa using ((hW.continuous_fderiv (by norm_num)).clm_apply
        continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) v))
    (by simpa using hW.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _)
    (fun y _ => (hW.differentiable (by norm_num)) y)
  simpa using h

/-- Where the retarded point leaves the support beyond the radius `L`, the retarded wave operator
`□f(t − ‖y‖, x − y)` has compact support in `y`. -/
theorem hasCompactSupport_waveOperator_retarded {f : ℝ × E3 → ℝ} {t : ℝ} {x : E3} {L : ℝ}
    (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    HasCompactSupport fun y : E3 => waveOperator f (t - ‖y‖, x - y) :=
  HasCompactSupport.intro (isCompact_closedBall 0 L) fun y hy =>
    waveOperator_eq_zero_of_notMem (hL y (le_of_lt (show L < ‖y‖ by simpa using hy)))

/-- The retarded wave operator divided by `‖y‖` is integrable. -/
theorem integrable_wave_div_norm {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) {t : ℝ} {x : E3}
    {L : ℝ} (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    Integrable fun y : E3 => waveOperator f (t - ‖y‖, x - y) / ‖y‖ := by
  have hg : Continuous fun y : E3 => waveOperator f (t - ‖y‖, x - y) :=
    (continuous_waveOperator hf).comp (by fun_prop)
  have h := (Potential.locallyIntegrable_newtonKernel.integrable_smul_right_of_hasCompactSupport
    hg (hasCompactSupport_waveOperator_retarded hL)).const_mul (4 * π)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, Potential.newtonKernel, mul_inv, div_eq_mul_inv]
  field_simp

/-- The rescaled shell kernel, `4π ε⁻³ k(y/ε) = ψ'(‖y‖/ε − 1)/(ε‖y‖²)`. -/
theorem shellKernel_smul {ε : ℝ} (hε : 0 < ε) (y : E3) :
    4 * π * (ε⁻¹ ^ 3 * shellKernel (ε⁻¹ • y)) =
      deriv smoothTransition (‖y‖ / ε - 1) * (ε⁻¹ * ‖y‖⁻¹) * ‖y‖⁻¹ := by
  rw [shellKernel, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le), inv_mul_eq_div]
  rcases eq_or_ne ‖y‖ 0 with h | h
  · simp [h]
  · field_simp

/-- **Integration by parts with the cutoff**: for `ε > 0`,
`∫ □f(t − ‖y‖, x − y) χ_ε(y)/‖y‖ dy = 4π ∫ ε⁻³ k(y/ε) q(y) dy`, since the left side is
`∫ div V χ_ε = −∫ V · ∇χ_ε`. -/
theorem integral_wave_mul_cutoff {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3)
    {L : ℝ} (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y =
      4 * π * ∫ y, ε⁻¹ ^ 3 * shellKernel (ε⁻¹ • y) * fluxDensity f t x y := by
  set W : Fin 3 → E3 → ℝ := fun i y => retardedField f t x i y * cutoff ε y with hW
  have hWc : ∀ i, ContDiff ℝ 1 (W i) := by
    intro i
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y = 0
    · subst hy
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [cutoff_eventuallyEq_zero hε] with z hz
      simp [hW, hz]
    · exact (contDiffAt_retardedField hf t x hy i).mul (contDiff_cutoff hε).contDiffAt
  have hWs : ∀ i, HasCompactSupport (W i) := fun i =>
    HasCompactSupport.intro (isCompact_closedBall 0 L) fun y hy => by
      simp [hW, retardedField_eq_zero (hL y (le_of_lt (show L < ‖y‖ by simpa using hy)))]
  have hcont : ∀ i, Continuous fun y => fderiv ℝ (W i) y (EuclideanSpace.single i 1) :=
    fun i => ((hWc i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hint2 : Integrable fun y => ∑ i, fderiv ℝ (W i) y (EuclideanSpace.single i 1) :=
    integrable_finsetSum _ fun i _ => (hcont i).integrable_of_hasCompactSupport
      ((hWs i).fderiv_apply (𝕜 := ℝ) _)
  have hzero : ∫ y, ∑ i, fderiv ℝ (W i) y (EuclideanSpace.single i 1) = 0 := by
    rw [integral_finsetSum]
    · simp [integral_fderiv_eq_zero (hWc _) (hWs _)]
    · exact fun i _ => (hcont i).integrable_of_hasCompactSupport
        ((hWs i).fderiv_apply (𝕜 := ℝ) _)
  have hpt : ∀ y : E3, y ≠ 0 → ∑ i, fderiv ℝ (W i) y (EuclideanSpace.single i 1) =
      waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y -
        4 * π * (ε⁻¹ ^ 3 * shellKernel (ε⁻¹ • y)) * fluxDensity f t x y := by
    intro y hy
    have hprod : ∀ i, fderiv ℝ (W i) y (EuclideanSpace.single i 1) =
        fderiv ℝ (retardedField f t x i) y (EuclideanSpace.single i 1) * cutoff ε y +
          deriv smoothTransition (‖y‖ / ε - 1) * (ε⁻¹ * ‖y‖⁻¹) *
            (retardedField f t x i y * y i) := by
      intro i
      have hV := ((contDiffAt_retardedField hf t x hy i).differentiableAt
        (by norm_num)).hasFDerivAt
      have H : HasFDerivAt (W i) _ y :=
        (hV.mul (hasFDerivAt_cutoff ε hy)).congr_of_eventuallyEq (Eventually.of_forall fun z => rfl)
      rw [H.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
        EuclideanSpace.inner_single_right]
      simp
      ring
    simp only [hprod, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_fderiv_retardedField hf t x hy, sum_retardedField_mul t x hy, shellKernel_smul hε]
    ring
  have hint1 : Integrable fun y => waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y := by
    refine (integrable_wave_div_norm hf hL).mul_bdd (c := 1)
      (contDiff_cutoff hε (n := 0)).continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (cutoff_mem_Icc ε y).1]
    exact (cutoff_mem_Icc ε y).2
  have hae : (fun y => 4 * π * (ε⁻¹ ^ 3 * shellKernel (ε⁻¹ • y) * fluxDensity f t x y)) =ᵐ[volume]
      fun y => waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y -
        ∑ i, fderiv ℝ (W i) y (EuclideanSpace.single i 1) := by
    have h0 : ∀ᵐ y : E3, y ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with y hy
    rw [hpt y hy]
    ring
  rw [← integral_const_mul, integral_congr_ae hae, integral_sub hint1 hint2, hzero, sub_zero]

/-- **The retarded identity at a point**: for a `C²` function `f` whose support meets the past
cone of `(t, x)` in a bounded set, `∫ □f(t − ‖y‖, x − y)/‖y‖ dy = 4π f(t, x)`. The two sides of
`integral_wave_mul_cutoff` converge as `ε → 0⁺`: the left by dominated convergence, the right
since `ε⁻³ k(y/ε)` is an approximate identity and `q(0) = f(t, x)`. -/
theorem integral_wave_div_norm_eq_mul {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3)
    {L : ℝ} (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖ = 4 * π * f (t, x) := by
  have hint := integrable_wave_div_norm hf hL
  have hlim1 : Tendsto (fun ε => ∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y)
      (𝓝[>] 0) (𝓝 (∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖waveOperator f (t - ‖y‖, x - y) / ‖y‖‖) ?_ ?_ hint.norm ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact hint.aestronglyMeasurable.mul
        (contDiff_cutoff hε (n := 0)).continuous.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul, Real.norm_of_nonneg (cutoff_mem_Icc ε y).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (cutoff_mem_Icc ε y).2
    · have h0 : ∀ᵐ y : E3, y ≠ 0 := by
        rw [ae_iff]
        simp
      filter_upwards [h0] with y hy
      have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
        (show (0 : ℝ) < ‖y‖ / 2 by positivity))] with ε (hε : 0 < ε) (hε' : ε < ‖y‖ / 2)
      rw [cutoff_eq_one hε (by linarith), mul_one]
  have hq : Continuous (fluxDensity f t x) := continuous_fluxDensity (hf.of_le (by norm_num)) t x
  have hqc : HasCompactSupport (fluxDensity f t x) :=
    HasCompactSupport.intro (isCompact_closedBall 0 L) fun y hy =>
      fluxDensity_eq_zero (hL y (le_of_lt (show L < ‖y‖ by simpa using hy)))
  have hpk := tendsto_integral_comp_smul_smul_of_integrable (μ := (volume : Measure E3))
    shellKernel_nonneg integral_shellKernel tendsto_norm_pow_mul_shellKernel
    (hq.integrable_of_hasCompactSupport hqc) hq.continuousAt
  rw [fluxDensity_zero, finrank_euclideanSpace_fin] at hpk
  have hlim2 : Tendsto (fun ε => ∫ y, waveOperator f (t - ‖y‖, x - y) / ‖y‖ * cutoff ε y)
      (𝓝[>] 0) (𝓝 (4 * π * f (t, x))) := by
    refine Tendsto.congr' ?_ ((hpk.comp tendsto_inv_nhdsGT_zero).const_mul (4 * π))
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [integral_wave_mul_cutoff hf t x hL hε]
    simp [smul_eq_mul]
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The retarded identity**: `∫ □f(t − ‖y‖, x − y)/(4π‖y‖) dy = f(t, x)` for a `C²` function
`f` whose support meets the past cone of `(t, x)` in a bounded set. -/
theorem integral_wave_div_norm {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) (x : E3)
    {L : ℝ} (hL : ∀ y : E3, L ≤ ‖y‖ → (t - ‖y‖, x - y) ∉ tsupport f) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / (4 * π * ‖y‖) = f (t, x) := by
  have h := integral_wave_div_norm_eq_mul hf t x hL
  have hfun : (fun y : E3 => waveOperator f (t - ‖y‖, x - y) / (4 * π * ‖y‖)) =
      fun y => (4 * π)⁻¹ * (waveOperator f (t - ‖y‖, x - y) / ‖y‖) := by
    funext y
    rw [mul_comm (4 * π), ← div_div, div_eq_inv_mul]
  rw [hfun, integral_const_mul, h]
  field_simp

/-! ### The retarded integral and subluminal supports -/

section RetardedIntegral

variable {G : Type*} [NormedAddCommGroup G]

/-- A function has **subluminal support** with the radius `R` and the speed `v₀ < 1` if its
support lies in `{(t, x) | ‖x‖ ≤ R + v₀|t|}`. -/
structure SubluminalSupport (R v₀ : ℝ) (f : ℝ × E3 → G) : Prop where
  /-- The speed is nonnegative. -/
  nonneg : 0 ≤ v₀
  /-- The speed is less than the speed of light. -/
  lt_one : v₀ < 1
  /-- The support lies in the region `‖x‖ ≤ R + v₀|t|`. -/
  subset : tsupport f ⊆ {p | ‖p.2‖ ≤ R + v₀ * |p.1|}

/-- A function supported in the support of a function with subluminal support has subluminal
support. -/
theorem SubluminalSupport.mono {G' : Type*} [NormedAddCommGroup G'] {R v₀ : ℝ}
    {f : ℝ × E3 → G} {g : ℝ × E3 → G'} (hf : SubluminalSupport R v₀ f)
    (hg : tsupport g ⊆ tsupport f) : SubluminalSupport R v₀ g :=
  ⟨hf.nonneg, hf.lt_one, hg.trans hf.subset⟩

/-- A function of compact support has subluminal support, with the speed `0`. -/
theorem exists_subluminalSupport_of_hasCompactSupport {f : ℝ × E3 → G}
    (hf : HasCompactSupport f) : ∃ R, SubluminalSupport R 0 f := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, le_rfl, by norm_num, fun p hp => ?_⟩
  have h := hR hp
  rw [mem_closedBall_zero_iff] at h
  simp only [mem_ofPred_eq, zero_mul, add_zero]
  exact (norm_snd_le p).trans h

/-- The radius `(R + v₀(|t₀| + 1) + ‖x₀‖ + 2)/(1 − v₀)` beyond which the past cones of the
points within the distance `1` of `p₀ = (t₀, x₀)` miss a subluminal support. -/
def pastRadius (R v₀ : ℝ) (p₀ : ℝ × E3) : ℝ := (R + v₀ * (|p₀.1| + 1) + ‖p₀.2‖ + 2) / (1 - v₀)

/-- The past cone of a point near `p₀` leaves a subluminal support beyond the radius
`pastRadius R v₀ p₀`. -/
theorem SubluminalSupport.notMem_tsupport {R v₀ : ℝ} {f : ℝ × E3 → G}
    (hf : SubluminalSupport R v₀ f) {p₀ p : ℝ × E3} (hp : dist p p₀ < 1) {y : E3}
    (hy : pastRadius R v₀ p₀ ≤ ‖y‖) : p - (‖y‖, y) ∉ tsupport f := by
  intro hmem
  have h := hf.subset hmem
  simp only [mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub] at h
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm] at hp
  obtain ⟨h1, h2⟩ := hp
  have hv := hf.nonneg
  have hv1 : 0 < 1 - v₀ := by linarith [hf.lt_one]
  have ht : |p.1| ≤ |p₀.1| + 1 := by
    have := abs_sub_abs_le_abs_sub p.1 p₀.1
    linarith
  have hx : ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
    have := norm_sub_norm_le p.2 p₀.2
    linarith
  have h3 : ‖y‖ - ‖p.2‖ ≤ ‖p.2 - y‖ := by
    have := norm_sub_norm_le y p.2
    rw [norm_sub_rev] at this
    linarith
  have h4 : |p.1 - ‖y‖| ≤ |p.1| + ‖y‖ := by
    have := abs_sub (p.1) ‖y‖
    rwa [abs_of_nonneg (norm_nonneg y)] at this
  have hy' : R + v₀ * (|p₀.1| + 1) + ‖p₀.2‖ + 2 ≤ (1 - v₀) * ‖y‖ := by
    rw [pastRadius, div_le_iff₀ hv1] at hy
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hv, mul_le_mul_of_nonneg_left ht hv]

/-- The integrand of the retarded integral of a continuous function with subluminal support has
compact support. -/
theorem SubluminalSupport.hasCompactSupport_comp {R v₀ : ℝ} {f : ℝ × E3 → G}
    (hf : SubluminalSupport R v₀ f) (p : ℝ × E3) :
    HasCompactSupport fun y : E3 => f (p - (‖y‖, y)) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (pastRadius R v₀ p)) fun y hy =>
    image_eq_zero_of_notMem_tsupport (hf.notMem_tsupport (by simp)
      (le_of_lt (show pastRadius R v₀ p < ‖y‖ by simpa using hy)))

variable [NormedSpace ℝ G]

/-- The derivative of a function with subluminal support has subluminal support. -/
theorem SubluminalSupport.fderiv {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) :
    SubluminalSupport R v₀ (fderiv ℝ f) :=
  hf.mono (tsupport_fderiv_subset ℝ)

/-- The **retarded integral** `∫ f(t − ‖y‖, x − y)/(4π‖y‖) dy` of a function on `ℝ × ℝ³`, at the
point `p = (t, x)`. -/
def retardedIntegral (f : ℝ × E3 → G) (p : ℝ × E3) : G :=
  ∫ y, (4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y))

/-- The retarded integral of a real function is `∫ f(t − ‖y‖, x − y)/(4π‖y‖) dy`. -/
theorem retardedIntegral_apply (f : ℝ × E3 → ℝ) (t : ℝ) (x : E3) :
    retardedIntegral f (t, x) = ∫ y, f (t - ‖y‖, x - y) / (4 * π * ‖y‖) := by
  simp only [retardedIntegral, smul_eq_mul, div_eq_inv_mul]
  rfl

/-- The integrand of the retarded integral of a continuous function with subluminal support is
integrable. -/
theorem SubluminalSupport.integrable {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f)
    (hc : Continuous f) (p : ℝ × E3) :
    Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y)) :=
  Potential.locallyIntegrable_newtonKernel.integrable_smul_right_of_hasCompactSupport
    (hc.comp (by fun_prop)) (hf.hasCompactSupport_comp p)

/-- A local bound for the integrand: near `p₀` it is at most `C/(4π‖y‖)` on the ball of radius
`pastRadius R v₀ p₀` and vanishes outside. -/
theorem SubluminalSupport.exists_bound {R v₀ : ℝ} {f : ℝ × E3 → G}
    (hf : SubluminalSupport R v₀ f) (hc : Continuous f) (p₀ : ℝ × E3) :
    ∃ C, ∀ p ∈ ball p₀ 1, ∀ y : E3, ‖(4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y))‖ ≤
      (closedBall (0 : E3) (pastRadius R v₀ p₀)).indicator
        (fun y => C * Potential.newtonKernel y) y := by
  set ρ := pastRadius R v₀ p₀
  have hK : IsCompact ((fun q : (ℝ × E3) × E3 => q.1 - (‖q.2‖, q.2)) ''
      (closedBall p₀ 1 ×ˢ closedBall (0 : E3) ρ)) :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (by fun_prop)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun p hp y => ?_⟩
  by_cases hy : ‖y‖ ≤ ρ
  · rw [indicator_of_mem (by simpa using hy), norm_smul, Real.norm_of_nonneg (by positivity),
      mul_comm, Potential.newtonKernel]
    exact mul_le_mul_of_nonneg_right (hC _ ⟨(p, y), ⟨ball_subset_closedBall hp,
      by simpa using hy⟩, rfl⟩) (by positivity)
  · rw [indicator_of_notMem (by simpa using hy),
      image_eq_zero_of_notMem_tsupport (hf.notMem_tsupport (mem_ball.mp hp) (not_le.mp hy).le),
      smul_zero, norm_zero]

/-- The local bound is integrable. -/
theorem integrable_indicator_newtonKernel (C ρ : ℝ) :
    Integrable ((closedBall (0 : E3) ρ).indicator fun y => C * Potential.newtonKernel y) :=
  IntegrableOn.integrable_indicator
    ((Potential.locallyIntegrable_newtonKernel.integrableOn_isCompact
      (isCompact_closedBall 0 ρ)).const_mul C) measurableSet_closedBall

/-- The retarded integral of a continuous function with subluminal support is continuous. -/
theorem continuous_retardedIntegral {R v₀ : ℝ} {f : ℝ × E3 → G} (hc : Continuous f)
    (hf : SubluminalSupport R v₀ f) : Continuous (retardedIntegral f) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨C, hC⟩ := hf.exists_bound hc p₀
  refine continuousAt_of_dominated (Eventually.of_forall fun p =>
    (hf.integrable hc p).aestronglyMeasurable) ?_
    (integrable_indicator_newtonKernel C (pastRadius R v₀ p₀)) ?_
  · filter_upwards [ball_mem_nhds p₀ one_pos] with p hp
    exact Eventually.of_forall (hC p hp)
  · exact Eventually.of_forall fun y => (continuous_const.smul (hc.comp (by fun_prop))).continuousAt

/-- **The derivative of the retarded integral** is the retarded integral of the derivative, for a
`C¹` function with subluminal support. -/
theorem hasFDerivAt_retardedIntegral [CompleteSpace G] {R v₀ : ℝ} {f : ℝ × E3 → G}
    (hc : ContDiff ℝ 1 f) (hf : SubluminalSupport R v₀ f) (p₀ : ℝ × E3) :
    HasFDerivAt (retardedIntegral f) (retardedIntegral (fderiv ℝ f) p₀) p₀ := by
  have hc' : Continuous (fderiv ℝ f) := hc.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := hf.fderiv.exists_bound hc' p₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds p₀ one_pos)
    (Eventually.of_forall fun p => (hf.integrable hc.continuous p).aestronglyMeasurable)
    (hf.integrable hc.continuous p₀) (hf.fderiv.integrable hc' p₀).aestronglyMeasurable
    (Eventually.of_forall fun y p hp => hC p hp y)
    (integrable_indicator_newtonKernel C (pastRadius R v₀ p₀))
    (Eventually.of_forall fun y p _ => ?_)
  exact ((hasFDerivAt_comp_sub (‖y‖, y)).mpr
    ((hc.differentiable (by norm_num)) (p - (‖y‖, y))).hasFDerivAt).const_smul _

/-- The derivative of the retarded integral of a `C¹` function with subluminal support. -/
theorem fderiv_retardedIntegral [CompleteSpace G] {R v₀ : ℝ} {f : ℝ × E3 → G}
    (hc : ContDiff ℝ 1 f) (hf : SubluminalSupport R v₀ f) :
    fderiv ℝ (retardedIntegral f) = retardedIntegral (fderiv ℝ f) :=
  funext fun p => (hasFDerivAt_retardedIntegral hc hf p).fderiv

/-- The retarded integral commutes with the evaluation of linear maps. -/
theorem retardedIntegral_apply_clm [CompleteSpace G] {R v₀ : ℝ}
    {F : ℝ × E3 → ℝ × E3 →L[ℝ] G} (hc : Continuous F) (hF : SubluminalSupport R v₀ F)
    (p : ℝ × E3) (v : ℝ × E3) :
    retardedIntegral F p v = retardedIntegral (fun q => F q v) p := by
  rw [retardedIntegral, ContinuousLinearMap.integral_apply (hF.integrable hc p)]
  rfl

/-- **Smoothness of the retarded integral**: the retarded integral of a `Cⁿ` function with
subluminal support is `Cⁿ`. -/
theorem contDiff_retardedIntegral_nat [CompleteSpace G] {R v₀ : ℝ} (n : ℕ) {f : ℝ × E3 → G}
    (hc : ContDiff ℝ n f) (hf : SubluminalSupport R v₀ f) :
    ContDiff ℝ n (retardedIntegral f) := by
  induction n generalizing G with
  | zero =>
    exact contDiff_zero.mpr (continuous_retardedIntegral (contDiff_zero.mp hc) hf)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one] at hc ⊢
    rw [contDiff_succ_iff_hasFDerivAt]
    exact ⟨retardedIntegral (fderiv ℝ f), ih (hc.fderiv_right le_rfl) hf.fderiv,
      hasFDerivAt_retardedIntegral (hc.of_le (by simp)) hf⟩

/-- **Smoothness of the retarded integral**: the retarded integral of a `Cⁿ` function with
subluminal support is `Cⁿ`, for `n ≤ ∞`. -/
theorem contDiff_retardedIntegral [CompleteSpace G] {R v₀ : ℝ} {n : ℕ∞} {f : ℝ × E3 → G}
    (hc : ContDiff ℝ n f) (hf : SubluminalSupport R v₀ f) :
    ContDiff ℝ n (retardedIntegral f) := by
  induction n with
  | top =>
    exact contDiff_infty.mpr fun m =>
      contDiff_retardedIntegral_nat m (hc.of_le (by exact_mod_cast le_top)) hf
  | coe m => exact contDiff_retardedIntegral_nat m hc hf

/-- The retarded integral is additive on integrable integrands. -/
theorem retardedIntegral_add {f g : ℝ × E3 → G} {p : ℝ × E3}
    (hf : Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • f (p - (‖y‖, y)))
    (hg : Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • g (p - (‖y‖, y))) :
    retardedIntegral (fun q => f q + g q) p = retardedIntegral f p + retardedIntegral g p := by
  simp only [retardedIntegral, smul_add]
  exact integral_add hf hg

/-- The retarded integral commutes with finite sums of integrable integrands. -/
theorem retardedIntegral_finsetSum {ι : Type*} (s : Finset ι) {f : ι → ℝ × E3 → G}
    {p : ℝ × E3} (hf : ∀ i ∈ s, Integrable fun y : E3 => (4 * π * ‖y‖)⁻¹ • f i (p - (‖y‖, y))) :
    retardedIntegral (fun q => ∑ i ∈ s, f i q) p = ∑ i ∈ s, retardedIntegral (f i) p := by
  simp only [retardedIntegral, Finset.smul_sum]
  exact integral_finsetSum s hf

/-- The retarded integral of the zero function vanishes. -/
@[simp] theorem retardedIntegral_zero (p : ℝ × E3) :
    retardedIntegral (fun _ => (0 : G)) p = 0 := by
  simp [retardedIntegral]

omit [NormedSpace ℝ G] in
/-- **A moving source**: a profile `χ` supported in the ball of radius `R`, carried with the
velocity `w` of speed `‖w‖ < 1`, has subluminal support with the radius `R` and the speed
`‖w‖`. -/
theorem subluminalSupport_moving {χ : E3 → G} {R : ℝ} (hχ : tsupport χ ⊆ closedBall 0 R)
    {w : E3} (hw : ‖w‖ < 1) : SubluminalSupport R ‖w‖ fun p : ℝ × E3 => χ (p.2 - p.1 • w) := by
  refine ⟨norm_nonneg w, hw, fun q hq => ?_⟩
  have h := hχ (tsupport_comp_subset_preimage χ (f := fun p : ℝ × E3 => p.2 - p.1 • w)
    (by fun_prop) hq)
  rw [mem_closedBall_zero_iff] at h
  have h2 := norm_le_norm_add_norm_sub' q.2 (q.1 • w)
  rw [norm_smul, Real.norm_eq_abs] at h2
  simp only [mem_ofPred_eq]
  linarith [mul_comm |q.1| ‖w‖]

/-- A smooth bump on space, `1` on the unit ball and supported in the ball of radius `2`. -/
def spaceBump : ContDiffBump (0 : E3) := ⟨1, 2, by norm_num, by norm_num⟩

/-- **An instance with a positive speed**: the bump `spaceBump` carried with the velocity
`(1/2) e₀` has subluminal support with the radius `2` and the speed `1/2`. -/
theorem subluminalSupport_movingBump :
    SubluminalSupport 2 (1 / 2) fun p : ℝ × E3 =>
      spaceBump (p.2 - p.1 • ((1 / 2 : ℝ) • EuclideanSpace.single 0 1)) := by
  have hw : ‖(1 / 2 : ℝ) • (EuclideanSpace.single 0 1 : E3)‖ = 1 / 2 := by
    rw [norm_smul, PiLp.norm_single]
    norm_num
  have h := subluminalSupport_moving (χ := (spaceBump : E3 → ℝ)) (R := 2)
    (by rw [spaceBump.tsupport_eq]; rfl) (w := (1 / 2 : ℝ) • EuclideanSpace.single 0 1)
    (by rw [hw]; norm_num)
  rwa [hw] at h

end RetardedIntegral

/-! ### The wave equation -/

/-- **The retarded identity for a subluminal support**:
`∫ □f(t − ‖y‖, x − y)/(4π‖y‖) dy = f(t, x)` for a `C²` function `f` with subluminal support. -/
theorem integral_wave_div_norm_of_subluminalSupport {R v₀ : ℝ} {f : ℝ × E3 → ℝ}
    (hc : ContDiff ℝ 2 f) (hf : SubluminalSupport R v₀ f) (t : ℝ) (x : E3) :
    ∫ y, waveOperator f (t - ‖y‖, x - y) / (4 * π * ‖y‖) = f (t, x) :=
  integral_wave_div_norm hc t x (L := pastRadius R v₀ (t, x))
    fun y hy => hf.notMem_tsupport (p₀ := (t, x)) (p := (t, x)) (by simp) hy

/-- The time derivative of a function with subluminal support has subluminal support. -/
theorem SubluminalSupport.timeDeriv {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hf : SubluminalSupport R v₀ f) :
    SubluminalSupport R v₀ (timeDeriv f) :=
  hf.mono (tsupport_timeDeriv_subset f)

/-- The spatial derivatives of a function with subluminal support have subluminal support. -/
theorem SubluminalSupport.spaceDeriv {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hf : SubluminalSupport R v₀ f)
    (i : Fin 3) : SubluminalSupport R v₀ (spaceDeriv i f) :=
  hf.mono (tsupport_spaceDeriv_subset i f)

/-- The wave operator of a function with subluminal support has subluminal support. -/
theorem SubluminalSupport.waveOperator {R v₀ : ℝ} {f : ℝ × E3 → ℝ}
    (hf : SubluminalSupport R v₀ f) : SubluminalSupport R v₀ (waveOperator f) :=
  hf.mono (closure_minimal (fun q hq => by
    by_contra h
    exact hq (waveOperator_eq_zero_of_notMem h)) (isClosed_tsupport f))

/-- The time derivative commutes with the retarded integral. -/
theorem timeDeriv_retardedIntegral {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f)
    (hf : SubluminalSupport R v₀ f) :
    timeDeriv (retardedIntegral f) = retardedIntegral (timeDeriv f) := by
  funext p
  rw [timeDeriv, fderiv_retardedIntegral hc hf,
    retardedIntegral_apply_clm (hc.continuous_fderiv (by norm_num)) hf.fderiv]
  rfl

/-- The spatial derivatives commute with the retarded integral. -/
theorem spaceDeriv_retardedIntegral {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 1 f)
    (hf : SubluminalSupport R v₀ f) (i : Fin 3) :
    spaceDeriv i (retardedIntegral f) = retardedIntegral (spaceDeriv i f) := by
  funext p
  rw [spaceDeriv, fderiv_retardedIntegral hc hf,
    retardedIntegral_apply_clm (hc.continuous_fderiv (by norm_num)) hf.fderiv]
  rfl

/-- The wave operator commutes with the retarded integral, for a `C²` function with subluminal
support. -/
theorem waveOperator_retardedIntegral {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f)
    (hf : SubluminalSupport R v₀ f) :
    waveOperator (retardedIntegral f) = retardedIntegral (waveOperator f) := by
  funext p
  have hc1 : ContDiff ℝ 1 f := hc.of_le (by norm_num)
  have ht := contDiff_timeDeriv (n := 1) hc
  have hs := fun i => contDiff_spaceDeriv (n := 1) hc i
  have htt : Continuous (timeDeriv (timeDeriv f)) := (contDiff_timeDeriv (n := 0) ht).continuous
  have hss : ∀ i, Continuous (spaceDeriv i (spaceDeriv i f)) := fun i =>
    (contDiff_spaceDeriv (n := 0) (hs i) i).continuous
  simp only [waveOperator]
  rw [timeDeriv_retardedIntegral hc1 hf, timeDeriv_retardedIntegral ht hf.timeDeriv]
  simp only [spaceDeriv_retardedIntegral hc1 hf, fun i => spaceDeriv_retardedIntegral (hs i)
    (hf.spaceDeriv i) i]
  simp only [retardedIntegral]
  rw [← integral_finsetSum _ fun i _ => (hf.spaceDeriv i).spaceDeriv i |>.integrable (hss i) p,
    ← integral_sub (hf.timeDeriv.timeDeriv.integrable htt p)
      (integrable_finsetSum _ fun i _ => (hf.spaceDeriv i).spaceDeriv i |>.integrable (hss i) p)]
  simp only [waveOperator, smul_sub, Finset.smul_sum]

/-- **The retarded integral solves the wave equation**: `□(Rf) = (∂ₜ² − Δ)(Rf) = f` for a `C²`
function `f` with subluminal support. -/
theorem wave_retardedIntegral {R v₀ : ℝ} {f : ℝ × E3 → ℝ} (hc : ContDiff ℝ 2 f)
    (hf : SubluminalSupport R v₀ f) (p : ℝ × E3) :
    waveOperator (retardedIntegral f) p = f p := by
  rw [waveOperator_retardedIntegral hc hf]
  have h := integral_wave_div_norm hc p.1 p.2 (L := pastRadius R v₀ p)
    fun y hy => hf.notMem_tsupport (by simp) hy
  rw [← h, retardedIntegral]
  simp only [smul_eq_mul, div_eq_inv_mul]
  rfl

/-! ### Causal support -/

/-- The past light cone `{q | ‖x − q₂‖ = t − q₁}` of the point `p = (t, x)`. -/
def pastCone (p : ℝ × E3) : Set (ℝ × E3) := {q | ‖p.2 - q.2‖ = p.1 - q.1}

/-- The retarded points `p − (‖y‖, y)` lie on the past light cone of `p`. -/
theorem sub_mem_pastCone (p : ℝ × E3) (y : E3) : p - (‖y‖, y) ∈ pastCone p := by
  simp [pastCone]

/-- **Causal support**: the retarded integral vanishes at a point whose past light cone misses
the support of `f`. -/
theorem retardedIntegral_eq_zero_of_support {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ × E3 → G} {p : ℝ × E3} (h : Disjoint (pastCone p) (Function.support f)) :
    retardedIntegral f p = 0 := by
  have hz : ∀ y : E3, f (p - (‖y‖, y)) = 0 := fun y =>
    Function.notMem_support.mp (h.notMem_of_mem_left (sub_mem_pastCone p y))
  simp [retardedIntegral, hz]

/-- The retarded integral of a source that vanishes up to the time `T` vanishes up to `T`. -/
theorem retardedIntegral_eq_zero_of_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ × E3 → G} {T : ℝ} (hT : ∀ q : ℝ × E3, q.1 ≤ T → f q = 0) {p : ℝ × E3}
    (hp : p.1 ≤ T) : retardedIntegral f p = 0 := by
  refine retardedIntegral_eq_zero_of_support (Set.disjoint_left.mpr fun q hq hfq => hfq ?_)
  have : q.1 ≤ p.1 := by
    have h0 := norm_nonneg (p.2 - q.2)
    rw [hq] at h0
    linarith
  exact hT q (this.trans hp)

/-- **Finite speed of propagation**: if the source is switched on at the time `T` inside the
ball `‖x‖ ≤ ρ`, the retarded integral vanishes at `(t, x)` with `‖x‖ > ρ + (t − T)`. -/
theorem retardedIntegral_eq_zero_of_far {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ × E3 → G} {T ρ : ℝ} (hsupp : ∀ q : ℝ × E3, f q ≠ 0 → T ≤ q.1 ∧ ‖q.2‖ ≤ ρ)
    {p : ℝ × E3} (hp : ρ + (p.1 - T) < ‖p.2‖) : retardedIntegral f p = 0 := by
  refine retardedIntegral_eq_zero_of_support (Set.disjoint_left.mpr fun q hq hfq => ?_)
  obtain ⟨h1, h2⟩ := hsupp q hfq
  have h3 := norm_sub_norm_le p.2 q.2
  rw [hq] at h3
  linarith

/-- The retarded integral of a source with subluminal support that vanishes before the time `T₀`
is supported, for times `t ≤ T`, in the ball `‖x‖ ≤ R + v₀(|T₀| + |T|) + (T − T₀)`. -/
theorem norm_le_of_retardedIntegral_ne_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {R v₀ : ℝ} {f : ℝ × E3 → G} (hf : SubluminalSupport R v₀ f) {T₀ T : ℝ}
    (hpast : ∀ q : ℝ × E3, f q ≠ 0 → T₀ ≤ q.1) {p : ℝ × E3} (hpT : p.1 ≤ T)
    (hne : retardedIntegral f p ≠ 0) : ‖p.2‖ ≤ R + v₀ * (|T₀| + |T|) + (T - T₀) := by
  by_contra hlt
  refine hne (retardedIntegral_eq_zero_of_support (Set.disjoint_left.mpr fun q hq hfq => hlt ?_))
  have hq1 := hpast q hfq
  have hq2 : ‖q.2‖ ≤ R + v₀ * |q.1| := hf.subset (subset_tsupport f hfq)
  have hq0 : q.1 ≤ p.1 := by
    have h0 := norm_nonneg (p.2 - q.2)
    rw [hq] at h0
    linarith
  have habs : |q.1| ≤ |T₀| + |T| := by
    rw [abs_le]
    constructor <;> cases abs_cases T₀ <;> cases abs_cases T <;> linarith
  have h3 := norm_le_norm_add_norm_sub' p.2 q.2
  rw [hq] at h3
  nlinarith [mul_le_mul_of_nonneg_left habs hf.nonneg]

/-! ### Space-time -/

/-- The splitting `v ↦ (v⁰, 𝐯)` of `MinkowskiModel 3` into time and space, a continuous linear
equivalence with the inverse `(t, x) ↦ Minkowski.vector t x`. -/
def timeSpaceEquiv : MinkowskiModel 3 ≃L[ℝ] ℝ × E3 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => (v 0, Minkowski.space v)
      map_add' := fun v w => by ext <;> simp
      map_smul' := fun c v => by ext <;> simp
      invFun := fun p => Minkowski.vector p.1 p.2
      left_inv := fun v => Minkowski.vector_time_space v
      right_inv := fun p => by simp }

/-- The splitting of a vector into time and space. -/
@[simp] theorem timeSpaceEquiv_apply (v : MinkowskiModel 3) :
    timeSpaceEquiv v = (v 0, Minkowski.space v) := rfl

/-- The inverse of the splitting assembles a vector from its time and its space part. -/
@[simp] theorem timeSpaceEquiv_symm_apply (p : ℝ × E3) :
    timeSpaceEquiv.symm p = Minkowski.vector p.1 p.2 := rfl

/-- The axis of the time is `(1, 0)`. -/
theorem timeSpaceEquiv_single_zero : timeSpaceEquiv (Pi.single 0 1) = ((1 : ℝ), (0 : E3)) := by
  ext i
  · simp
  · simp [Minkowski.space_apply, Fin.succ_ne_zero]

/-- The axis `i + 1` of space-time is `(0, eᵢ)`. -/
theorem timeSpaceEquiv_single_succ (i : Fin 3) :
    timeSpaceEquiv (Pi.single i.succ 1) = ((0 : ℝ), EuclideanSpace.single i 1) := by
  ext j
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Minkowski.space_apply, Pi.single_apply, Fin.succ_inj, eq_comm]

/-- The derivative of a function of `ℝ × ℝ³` pulled back to space-time. -/
theorem fderiv_comp_timeSpaceEquiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {u : ℝ × E3 → G} {v : MinkowskiModel 3} (hu : DifferentiableAt ℝ u (timeSpaceEquiv v))
    (w : MinkowskiModel 3) :
    fderiv ℝ (fun z => u (timeSpaceEquiv z)) v w =
      fderiv ℝ u (timeSpaceEquiv v) (timeSpaceEquiv w) := by
  have h := hu.hasFDerivAt.comp v timeSpaceEquiv.hasFDerivAt
  rw [show (fun z => u (timeSpaceEquiv z)) = u ∘ timeSpaceEquiv from rfl, h.fderiv]
  rfl

/-- The derivative along the axis of the time of a pulled-back function is its time derivative. -/
theorem fderiv_comp_timeSpaceEquiv_zero {u : ℝ × E3 → ℝ} (hu : Differentiable ℝ u) :
    (fun v => fderiv ℝ (fun z => u (timeSpaceEquiv z)) v (Pi.single 0 1)) =
      fun v => timeDeriv u (timeSpaceEquiv v) := by
  funext v
  rw [fderiv_comp_timeSpaceEquiv (hu _), timeSpaceEquiv_single_zero]
  rfl

/-- The derivative along the axis `i + 1` of a pulled-back function is its spatial derivative
`∂ᵢ`. -/
theorem fderiv_comp_timeSpaceEquiv_succ {u : ℝ × E3 → ℝ} (hu : Differentiable ℝ u) (i : Fin 3) :
    (fun v => fderiv ℝ (fun z => u (timeSpaceEquiv z)) v (Pi.single i.succ 1)) =
      fun v => spaceDeriv i u (timeSpaceEquiv v) := by
  funext v
  rw [fderiv_comp_timeSpaceEquiv (hu _), timeSpaceEquiv_single_succ]
  rfl

/-- **Transport to space-time**: the retarded integral of a function `k` on space-time, written in
`ℝ × ℝ³`, is `∫ k(v − (‖y‖, y))/(4π‖y‖) dy`. -/
theorem retardedIntegral_comp_symm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : MinkowskiModel 3 → G) (v : MinkowskiModel 3) :
    retardedIntegral (fun p => k (timeSpaceEquiv.symm p)) (timeSpaceEquiv v) =
      ∫ y, (4 * π * ‖y‖)⁻¹ • k (v - Minkowski.vector ‖y‖ y) := by
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  congr 2
  rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end ProjectAinos.SmoothGeometry.Wave
