/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Wave.FarField
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The energy estimate of the wave equation

Space-time is `ℝ × ℝ³` with `ℝ³ = EuclideanSpace ℝ (Fin 3)` and the wave operator
`□ = ∂ₜ² − Δ` (`waveOperator`). The **energy** of a function `w` at the time `t` is

  `energy w t = ½ ∫ ((∂ₜw)² + |∇w|²)(t, x) dx`,

with the density `gradNormSq w = (∂ₜw)² + Σᵢ (∂ᵢw)²` (the pairing `gradInner f g` of two
gradients is `∂ₜf ∂ₜg + Σᵢ ∂ᵢf ∂ᵢg`), and `spatialL2Norm f t` is the norm
`(∫ f(t, x)² dx)^{1/2}` of `f(t, ·)` in `L²(ℝ³)`. A function has **support in a ball on a time
interval**, `BallSupportOn T R f`, if `f(s, y) = 0` for `s ∈ [0, T]` and `‖y‖ > R`; a localized
support (`LocalizedSupport.ballSupportOn`) and a profile carried with the speed of light over a
finite time are examples.

* `hasDerivAt_energy`: for a `C²` function with support in a ball on `[0, T]`, the energy has the
  derivative `E′(t) = ∫ ∂ₜw □w (t, x) dx` for `0 < t < T`; the term `∫ ∇w · ∇∂ₜw` is integrated by
  parts (`integral_mul_spaceDeriv_eq_neg`).
* `abs_integral_mul_le_sqrt`: the inequality of Cauchy and Schwarz `|∫ fg| ≤ ‖f‖ ‖g‖` for
  integrals, from the discriminant of `∫ (r g + f)²`, so that `|E′| ≤ √(2E) ‖□w‖`.
* `sqrt_two_mul_energy_le`: **the energy estimate**
  `√(2E(t)) ≤ √(2E(0)) + ∫₀ᵗ ‖□w(s, ·)‖_{L²} ds` for `t ∈ [0, T]`; the comparison is made for
  `√(2E + δ) − ∫₀ᵗ ‖□w‖`, which is antitone for every `δ > 0`, and `δ → 0` removes the points
  where `E = 0`. `sqrt_energy_le`: the weaker form `√E(t) ≤ √E(0) + ∫₀ᵗ ‖□w(s, ·)‖_{L²} ds`.
* `sqrt_energy_le_bump`: an instance, `w(t, x) = cos t · χ(x)` for the bump `χ = spaceBump`.

The estimate measures the error of an approximate solution of the wave equation in
`ProjectAinos.Electrodynamics.Optics.Error` (Landau–Lifshitz, *The Classical Theory of Fields*,
§58).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology

namespace ProjectAinos.SmoothGeometry.Wave

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The energy -/

/-- The Euclidean square `(∂ₜf)² + Σᵢ (∂ᵢf)²` of the gradient of a function on `ℝ × ℝ³`. -/
def gradNormSq (f : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  timeDeriv f p ^ 2 + ∑ i, spaceDeriv i f p ^ 2

/-- The Euclidean pairing `∂ₜf ∂ₜg + Σᵢ ∂ᵢf ∂ᵢg` of the gradients of two functions on `ℝ × ℝ³`. -/
def gradInner (f g : ℝ × E3 → ℝ) (p : ℝ × E3) : ℝ :=
  timeDeriv f p * timeDeriv g p + ∑ i, spaceDeriv i f p * spaceDeriv i g p

/-- The square of the gradient is the pairing of the gradient with itself. -/
theorem gradNormSq_eq_gradInner (f : ℝ × E3 → ℝ) (p : ℝ × E3) :
    gradNormSq f p = gradInner f f p := by
  simp only [gradNormSq, gradInner, sq]

/-- The **energy** `½ ∫ ((∂ₜw)² + |∇w|²)(t, x) dx` of `w` at the time `t`. -/
def energy (w : ℝ × E3 → ℝ) (t : ℝ) : ℝ := (1 / 2) * ∫ x, gradNormSq w (t, x)

/-- The norm `(∫ f(t, x)² dx)^{1/2}` of `f(t, ·)` in `L²(ℝ³)`. -/
def spatialL2Norm (f : ℝ × E3 → ℝ) (t : ℝ) : ℝ := √(∫ x, f (t, x) ^ 2)

/-- The square of the gradient is nonnegative. -/
theorem gradNormSq_nonneg (f : ℝ × E3 → ℝ) (p : ℝ × E3) : 0 ≤ gradNormSq f p :=
  add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The energy is nonnegative. -/
theorem energy_nonneg (w : ℝ × E3 → ℝ) (t : ℝ) : 0 ≤ energy w t :=
  mul_nonneg (by norm_num) (integral_nonneg fun _ => gradNormSq_nonneg w _)

/-- The norm in `L²(ℝ³)` is nonnegative. -/
theorem spatialL2Norm_nonneg (f : ℝ × E3 → ℝ) (t : ℝ) : 0 ≤ spatialL2Norm f t := sqrt_nonneg _

/-! ### Slices in time and in space -/

/-- The derivative of the space slice `y ↦ f(s, y)` is the derivative of `f` along `0 × ℝ³`. -/
theorem hasFDerivAt_spaceSlice {f : ℝ × E3 → ℝ} {s : ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f (s, x)) :
    HasFDerivAt (fun y => f (s, y))
      ((fderiv ℝ f (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E3)) x :=
  hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)

/-- The spatial derivative `∂ᵢf` is the derivative of the space slice along `eᵢ`. -/
theorem fderiv_spaceSlice {f : ℝ × E3 → ℝ} {s : ℝ} {x : E3}
    (hf : DifferentiableAt ℝ f (s, x)) (i : Fin 3) :
    fderiv ℝ (fun y => f (s, y)) x (EuclideanSpace.single i 1) = spaceDeriv i f (s, x) := by
  rw [(hasFDerivAt_spaceSlice hf).fderiv]
  rfl

/-! ### Support in a ball on a time interval -/

/-- A function on `ℝ × ℝ³` has **support in the ball** of radius `R` on the times of `[0, T]` if
`f(s, y) = 0` for `s ∈ [0, T]` and `‖y‖ > R`. -/
def BallSupportOn (T R : ℝ) (f : ℝ × E3 → ℝ) : Prop :=
  ∀ s ∈ Icc 0 T, ∀ y : E3, R < ‖y‖ → f (s, y) = 0

/-- A localized support is a support in the ball on every time interval. -/
theorem LocalizedSupport.ballSupportOn {a : ℝ} {f : ℝ × E3 → ℝ} (hf : LocalizedSupport a f)
    (T : ℝ) : BallSupportOn T a f :=
  fun s _ y hy => hf s y hy

/-- A support in a ball on `[0, T]` is a support in a larger ball on a shorter interval. -/
theorem BallSupportOn.mono {T T' R R' : ℝ} {f : ℝ × E3 → ℝ} (hf : BallSupportOn T R f)
    (hT : T' ≤ T) (hR : R ≤ R') : BallSupportOn T' R' f :=
  fun s hs y hy => hf s ⟨hs.1, hs.2.trans hT⟩ y (hR.trans_lt hy)

/-- A product with a function with support in a ball has support in the ball. -/
theorem BallSupportOn.mul_left {T R : ℝ} {g : ℝ × E3 → ℝ} (hg : BallSupportOn T R g)
    (f : ℝ × E3 → ℝ) : BallSupportOn T R fun p => f p * g p :=
  fun s hs y hy => by simp only [hg s hs y hy, mul_zero]

/-- A product with a function with support in a ball has support in the ball. -/
theorem BallSupportOn.mul_right {T R : ℝ} {g : ℝ × E3 → ℝ} (hg : BallSupportOn T R g)
    (f : ℝ × E3 → ℝ) : BallSupportOn T R fun p => g p * f p :=
  fun s hs y hy => by simp only [hg s hs y hy, zero_mul]

/-- A sum of functions with support in a ball has support in the ball. -/
theorem BallSupportOn.add {T R : ℝ} {f g : ℝ × E3 → ℝ} (hf : BallSupportOn T R f)
    (hg : BallSupportOn T R g) : BallSupportOn T R fun p => f p + g p :=
  fun s hs y hy => by simp only [hf s hs y hy, hg s hs y hy, add_zero]

/-- A difference of functions with support in a ball has support in the ball. -/
theorem BallSupportOn.sub {T R : ℝ} {f g : ℝ × E3 → ℝ} (hf : BallSupportOn T R f)
    (hg : BallSupportOn T R g) : BallSupportOn T R fun p => f p - g p :=
  fun s hs y hy => by simp only [hf s hs y hy, hg s hs y hy, sub_zero]

/-- A power of a function with support in a ball has support in the ball. -/
theorem BallSupportOn.pow {T R : ℝ} {f : ℝ × E3 → ℝ} (hf : BallSupportOn T R f) {n : ℕ}
    (hn : n ≠ 0) : BallSupportOn T R fun p => f p ^ n :=
  fun s hs y hy => by simp only [hf s hs y hy, zero_pow hn]

private theorem isOpen_slab (T R : ℝ) :
    IsOpen ((Prod.fst ⁻¹' Ioo 0 T) ∩ {p : ℝ × E3 | R < ‖p.2‖}) :=
  (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt continuous_const (continuous_norm.comp continuous_snd))

/-- The derivative vanishes outside the ball at the inner times. -/
theorem BallSupportOn.fderiv_eq_zero {T R : ℝ} {f : ℝ × E3 → ℝ} (hf : BallSupportOn T R f)
    {s : ℝ} (hs : s ∈ Ioo 0 T) {y : E3} (hy : R < ‖y‖) : fderiv ℝ f (s, y) = 0 := by
  have h : f =ᶠ[𝓝 (s, y)] fun _ => 0 := by
    filter_upwards [(isOpen_slab T R).mem_nhds ⟨hs, hy⟩] with p hp
    exact hf p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2
  rw [h.fderiv_eq, fderiv_const_apply]

/-- A continuous function that vanishes outside the ball at the inner times of `[0, T]` vanishes
there at the end points too. -/
theorem BallSupportOn.of_Ioo {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hc : Continuous f)
    (h : ∀ s ∈ Ioo 0 T, ∀ y : E3, R < ‖y‖ → f (s, y) = 0) : BallSupportOn T R f := by
  intro s hs y hy
  have hcl : IsClosed {r : ℝ | f (r, y) = 0} :=
    isClosed_eq (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  have hsub : closure (Ioo 0 T) ⊆ {r : ℝ | f (r, y) = 0} :=
    hcl.closure_subset_iff.mpr fun r hr => h r hr y hy
  rw [closure_Ioo hT.ne] at hsub
  exact hsub hs

/-- The time derivative of a `C¹` function with support in a ball has support in the ball. -/
theorem BallSupportOn.timeDeriv {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 1 f)
    (h : BallSupportOn T R f) : BallSupportOn T R (timeDeriv f) :=
  BallSupportOn.of_Ioo hT (contDiff_timeDeriv (n := 0) hf).continuous fun s hs y hy => by
    rw [Wave.timeDeriv, h.fderiv_eq_zero hs hy]
    rfl

/-- The spatial derivatives of a differentiable function with support in a ball have support in
the ball. -/
theorem BallSupportOn.spaceDeriv {T R : ℝ} {f : ℝ × E3 → ℝ} (hf : Differentiable ℝ f)
    (h : BallSupportOn T R f) (i : Fin 3) : BallSupportOn T R (spaceDeriv i f) := by
  intro s hs y hy
  have hev : (fun z => f (s, z)) =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact h s hs z hz
  rw [← fderiv_spaceSlice (hf _) i, hev.fderiv_eq, fderiv_const_apply]
  rfl

/-- The wave operator of a `C²` function with support in a ball has support in the ball. -/
theorem BallSupportOn.waveOperator {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T) (hf : ContDiff ℝ 2 f)
    (h : BallSupportOn T R f) : BallSupportOn T R (waveOperator f) := by
  have h1 : ContDiff ℝ 1 (Wave.timeDeriv f) := contDiff_timeDeriv (n := 1) hf
  have h2 := (h.timeDeriv hT (hf.of_le (by norm_num))).timeDeriv hT h1
  have h3 : ∀ i, BallSupportOn T R (Wave.spaceDeriv i (Wave.spaceDeriv i f)) := fun i =>
    (h.spaceDeriv (hf.differentiable (by norm_num)) i).spaceDeriv
      ((contDiff_spaceDeriv (n := 1) hf i).differentiable (by norm_num)) i
  intro s hs y hy
  simp only [Wave.waveOperator, h2 s hs y hy, h3 _ s hs y hy, Finset.sum_const_zero, sub_zero]

/-- The Euclidean pairing of the gradients of two `C¹` functions is continuous. -/
theorem continuous_gradInner {f g : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Continuous (gradInner f g) :=
  ((contDiff_timeDeriv (n := 0) hf).continuous.fun_mul
    (contDiff_timeDeriv (n := 0) hg).continuous).fun_add
    (continuous_finsetSum _ fun i _ => (contDiff_spaceDeriv (n := 0) hf i).continuous.fun_mul
      (contDiff_spaceDeriv (n := 0) hg i).continuous)

/-- The square of the gradient of a `C¹` function is continuous. -/
theorem continuous_gradNormSq {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gradNormSq f) := by
  rw [show gradNormSq f = gradInner f f from funext (gradNormSq_eq_gradInner f)]
  exact continuous_gradInner hf hf

/-- The pairing of the gradient of a `C¹` function with support in a ball has support in the
ball. -/
theorem BallSupportOn.gradInner_left {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T)
    (hf : ContDiff ℝ 1 f) (h : BallSupportOn T R f) (g : ℝ × E3 → ℝ) :
    BallSupportOn T R (gradInner f g) := fun s hs y hy => by
  have hi : ∀ i, Wave.spaceDeriv i f (s, y) = 0 := fun i =>
    h.spaceDeriv (hf.differentiable one_ne_zero) i s hs y hy
  simp only [gradInner, h.timeDeriv hT hf s hs y hy, hi, zero_mul, Finset.sum_const_zero,
    add_zero]

/-- The square of the gradient of a `C¹` function with support in a ball has support in the
ball. -/
theorem BallSupportOn.gradNormSq {T R : ℝ} {f : ℝ × E3 → ℝ} (hT : 0 < T)
    (hf : ContDiff ℝ 1 f) (h : BallSupportOn T R f) : BallSupportOn T R (gradNormSq f) := by
  rw [show Wave.gradNormSq f = gradInner f f from funext (gradNormSq_eq_gradInner f)]
  exact h.gradInner_left hT hf f

/-- A continuous function with support in a ball is integrable on the space slices. -/
theorem BallSupportOn.integrable {T R : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (h : BallSupportOn T R f) {s : ℝ} (hs : s ∈ Icc 0 T) : Integrable fun x : E3 => f (s, x) :=
  (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall 0 R) fun y hy =>
      h s hs y (by rwa [mem_closedBall_zero_iff, not_le] at hy))

private theorem integrable_indicator_closedBall (R C : ℝ) :
    Integrable ((closedBall (0 : E3) R).indicator fun _ => C) :=
  (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)

private theorem BallSupportOn.exists_bound {T R : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (h : BallSupportOn T R f) :
    ∃ C, ∀ s ∈ Icc 0 T, ∀ x : E3,
      ‖f (s, x)‖ ≤ (closedBall (0 : E3) R).indicator (fun _ => C) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod
    (isCompact_closedBall (0 : E3) R)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun s hs x => ?_⟩
  by_cases hx : x ∈ closedBall (0 : E3) R
  · rw [indicator_of_mem hx]
    exact hC (s, x) ⟨hs, hx⟩
  · rw [indicator_of_notMem hx, h s hs x (by rwa [mem_closedBall_zero_iff, not_le] at hx),
      norm_zero]

/-- The integral over space of a continuous function with support in a ball is continuous on
`[0, T]`. -/
theorem BallSupportOn.continuousOn_integral {T R : ℝ} {f : ℝ × E3 → ℝ} (hc : Continuous f)
    (h : BallSupportOn T R f) : ContinuousOn (fun s => ∫ x, f (s, x)) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := h.exists_bound hc
  exact continuousOn_of_dominated
    (fun s _ => (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun s hs => Eventually.of_forall (hC s hs)) (integrable_indicator_closedBall R C)
    (Eventually.of_forall fun x => (hc.comp (continuous_id.prodMk continuous_const)).continuousOn)

/-- **Differentiation under the integral** over space at the inner times of `[0, T]`. -/
theorem BallSupportOn.hasDerivAt_integral {T R : ℝ} {f f' : ℝ × E3 → ℝ} (hc : Continuous f)
    (hc' : Continuous f') (hd : ∀ (s : ℝ) (x : E3), HasDerivAt (fun r => f (r, x)) (f' (s, x)) s)
    (h : BallSupportOn T R f) (h' : BallSupportOn T R f') {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => ∫ x, f (s, x)) (∫ x, f' (t, x)) t := by
  obtain ⟨C, hC⟩ := h'.exists_bound hc'
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun s x => f (s, x))
    (F' := fun s x => f' (s, x)) (Icc_mem_nhds ht.1 ht.2)
    (Eventually.of_forall fun s =>
      (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (h.integrable hc (Ioo_subset_Icc_self ht))
    (hc'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun x s hs => hC s hs x) (integrable_indicator_closedBall R C)
    (Eventually.of_forall fun x s _ => hd s x)).2

/-- **Integration by parts in space**: `∫ f ∂ᵢg = −∫ ∂ᵢf g` on a time slice, for `C¹` functions
of which `f` has support in a ball. -/
theorem integral_mul_spaceDeriv_eq_neg {f g : ℝ × E3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) {T R : ℝ} (h : BallSupportOn T R f) {s : ℝ} (hs : s ∈ Icc 0 T)
    (i : Fin 3) :
    ∫ x, f (s, x) * spaceDeriv i g (s, x) = -∫ x, spaceDeriv i f (s, x) * g (s, x) := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hfi : ∀ y : E3, fderiv ℝ (fun z => f (s, z)) y (EuclideanSpace.single i 1) =
      spaceDeriv i f (s, y) := fun y => fderiv_spaceSlice (hfd _) i
  have hgi : ∀ y : E3, fderiv ℝ (fun z => g (s, z)) y (EuclideanSpace.single i 1) =
      spaceDeriv i g (s, y) := fun y => fderiv_spaceSlice (hgd _) i
  have hfc : Continuous (Wave.spaceDeriv i f) := (contDiff_spaceDeriv (n := 0) hf i).continuous
  have hgc : Continuous (Wave.spaceDeriv i g) := (contDiff_spaceDeriv (n := 0) hg i).continuous
  have i1 : Integrable fun x => spaceDeriv i f (s, x) * g (s, x) :=
    ((h.spaceDeriv hfd i).mul_right g).integrable (hfc.fun_mul hg.continuous) hs
  have i2 : Integrable fun x => f (s, x) * spaceDeriv i g (s, x) :=
    (h.mul_right _).integrable (hf.continuous.fun_mul hgc) hs
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z => f (s, z)) (g := fun z => g (s, z)) (v := EuclideanSpace.single i 1)
    (by simp only [hfi]; exact i1) (by simp only [hgi]; exact i2)
    ((h.mul_right g).integrable (hf.continuous.fun_mul hg.continuous) hs)
    (fun y _ => (hfd.comp (differentiable_const s |>.prodMk differentiable_id)) y)
    (fun y _ => (hgd.comp (differentiable_const s |>.prodMk differentiable_id)) y)
  simpa only [hfi, hgi] using key

/-- **The derivative of the energy**: `E′(t) = ∫ ∂ₜw □w (t, x) dx` at the inner times of `[0, T]`
for a `C²` function with support in a ball on `[0, T]`. -/
theorem hasDerivAt_energy {w : ℝ × E3 → ℝ} (hw : ContDiff ℝ 2 w) {T R : ℝ} (hT : 0 < T)
    (h : BallSupportOn T R w) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (energy w) (∫ x, timeDeriv w (t, x) * waveOperator w (t, x)) t := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have ht1 : ContDiff ℝ 1 (Wave.timeDeriv w) := contDiff_timeDeriv (n := 1) hw
  have hs1 : ∀ i, ContDiff ℝ 1 (Wave.spaceDeriv i w) := fun i => contDiff_spaceDeriv (n := 1) hw i
  have h0 : BallSupportOn T R (Wave.timeDeriv w) := h.timeDeriv hT hw1
  have hi : ∀ i, BallSupportOn T R (Wave.spaceDeriv i w) := fun i =>
    h.spaceDeriv (hw.differentiable (by norm_num)) i
  set f' : ℝ × E3 → ℝ := fun p => 2 * (Wave.timeDeriv w p * Wave.timeDeriv (Wave.timeDeriv w) p) +
    ∑ i, 2 * (Wave.spaceDeriv i w p * Wave.spaceDeriv i (Wave.timeDeriv w) p) with hf'
  have hd : ∀ (s : ℝ) (x : E3), HasDerivAt (fun r => gradNormSq w (r, x)) (f' (s, x)) s := by
    intro s x
    have h0d := (hasDerivAt_timeSlice (ht1.differentiable one_ne_zero) s x).fun_pow 2
    have hid : ∀ i ∈ (Finset.univ : Finset (Fin 3)), HasDerivAt
        (fun r => Wave.spaceDeriv i w (r, x) ^ 2)
        (2 * (Wave.spaceDeriv i w (s, x) * Wave.spaceDeriv i (Wave.timeDeriv w) (s, x))) s := by
      intro i _
      have h' := (hasDerivAt_timeSlice ((hs1 i).differentiable one_ne_zero) s x).fun_pow 2
      rw [timeDeriv_spaceDeriv (hw.contDiffAt) i] at h'
      convert h' using 1
      norm_num
      ring
    convert h0d.fun_add (HasDerivAt.fun_sum hid) using 1
    · rfl
    · simp only [hf']
      norm_num
      ring
  have hgc : Continuous (gradNormSq w) := continuous_gradNormSq hw1
  have htt : Continuous (Wave.timeDeriv (Wave.timeDeriv w)) :=
    (contDiff_timeDeriv (n := 0) ht1).continuous
  have hst : ∀ i, Continuous (Wave.spaceDeriv i (Wave.timeDeriv w)) := fun i =>
    (contDiff_spaceDeriv (n := 0) ht1 i).continuous
  have hss : ∀ i, Continuous (Wave.spaceDeriv i (Wave.spaceDeriv i w)) := fun i =>
    (contDiff_spaceDeriv (n := 0) (hs1 i) i).continuous
  have hf'c : Continuous f' :=
    (continuous_const.fun_mul (ht1.continuous.fun_mul htt)).fun_add
      (continuous_finsetSum _ fun i _ =>
        continuous_const.fun_mul ((hs1 i).continuous.fun_mul (hst i)))
  have hgs : BallSupportOn T R (gradNormSq w) := fun s hs y hy => by
    simp only [gradNormSq, h0 s hs y hy, hi _ s hs y hy]
    norm_num
  have hf's : BallSupportOn T R f' := fun s hs y hy => by
    simp only [hf', h0 s hs y hy, hi _ s hs y hy]
    norm_num
  have hD := (hgs.hasDerivAt_integral hgc hf'c hd hf's ht).const_mul (1 / 2 : ℝ)
  have hts : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hibp : ∀ i, ∫ x, Wave.spaceDeriv i w (t, x) * Wave.spaceDeriv i (Wave.timeDeriv w) (t, x) =
      -∫ x, Wave.timeDeriv w (t, x) * Wave.spaceDeriv i (Wave.spaceDeriv i w) (t, x) := fun i => by
    rw [integral_mul_spaceDeriv_eq_neg (hs1 i) ht1 (hi i) hts i]
    simp only [mul_comm]
  have hint1 : Integrable fun x =>
      Wave.timeDeriv w (t, x) * Wave.timeDeriv (Wave.timeDeriv w) (t, x) :=
    (h0.mul_right _).integrable (ht1.continuous.fun_mul htt) hts
  have hint2 : ∀ i, Integrable fun x =>
      Wave.spaceDeriv i w (t, x) * Wave.spaceDeriv i (Wave.timeDeriv w) (t, x) := fun i =>
    ((hi i).mul_right _).integrable ((hs1 i).continuous.fun_mul (hst i)) hts
  have hint3 : ∀ i, Integrable fun x =>
      Wave.timeDeriv w (t, x) * Wave.spaceDeriv i (Wave.spaceDeriv i w) (t, x) := fun i =>
    (h0.mul_right _).integrable (ht1.continuous.fun_mul (hss i)) hts
  have e1 : ∫ x, f' (t, x) = 2 * (∫ x, Wave.timeDeriv w (t, x) *
      Wave.timeDeriv (Wave.timeDeriv w) (t, x)) - ∑ i, 2 * ∫ x,
        Wave.timeDeriv w (t, x) * Wave.spaceDeriv i (Wave.spaceDeriv i w) (t, x) := by
    simp only [hf']
    rw [integral_add (hint1.const_mul 2) (integrable_finsetSum _ fun i _ => (hint2 i).const_mul 2),
      integral_const_mul, integral_finsetSum _ fun i _ => (hint2 i).const_mul 2]
    simp only [integral_const_mul, hibp, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  have e2 : ∫ x, Wave.timeDeriv w (t, x) * Wave.waveOperator w (t, x) =
      (∫ x, Wave.timeDeriv w (t, x) * Wave.timeDeriv (Wave.timeDeriv w) (t, x)) - ∑ i, ∫ x,
        Wave.timeDeriv w (t, x) * Wave.spaceDeriv i (Wave.spaceDeriv i w) (t, x) := by
    simp only [Wave.waveOperator, mul_sub, Finset.mul_sum]
    rw [integral_sub hint1 (integrable_finsetSum _ fun i _ => hint3 i),
      integral_finsetSum _ fun i _ => hint3 i]
  rw [show energy w = fun y => 1 / 2 * ∫ x, gradNormSq w (y, x) from rfl]
  convert hD using 1
  rw [e2, e1, ← Finset.mul_sum]
  ring

/-! ### The inequality of Cauchy and Schwarz -/

/-- **The inequality of Cauchy and Schwarz** for integrals, `|∫ fg| ≤ (∫ f²)^{1/2} (∫ g²)^{1/2}`,
from the discriminant of the quadratic polynomial `r ↦ ∫ (r g + f)² ≥ 0`. -/
theorem abs_integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  have hq : ∀ r : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂μ) * (r * r) + (2 * ∫ x, f x * g x ∂μ) * r +
      ∫ x, f x ^ 2 ∂μ := by
    intro r
    have e : ∀ x, (r * g x + f x) ^ 2 = (r * r) * g x ^ 2 + (2 * r) * (f x * g x) + f x ^ 2 :=
      fun x => by ring
    have hI : ∫ x, (r * g x + f x) ^ 2 ∂μ = (∫ x, g x ^ 2 ∂μ) * (r * r) +
        (2 * ∫ x, f x * g x ∂μ) * r + ∫ x, f x ^ 2 ∂μ := by
      simp_rw [e]
      rw [integral_add ((hg.const_mul _).fun_add (hfg.const_mul _)) hf,
        integral_add (hg.const_mul _) (hfg.const_mul _), integral_const_mul, integral_const_mul]
      ring
    rw [← hI]
    exact integral_nonneg fun x => sq_nonneg _
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  rw [← sqrt_mul (integral_nonneg fun x => sq_nonneg _), ← sqrt_sq_eq_abs]
  apply sqrt_le_sqrt
  nlinarith

/-! ### The energy estimate -/

private theorem sqrt_add_sq_le {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε) : √(a + ε ^ 2) ≤ √a + ε := by
  rw [sqrt_le_left (by positivity)]
  have h := sq_sqrt ha
  nlinarith [sqrt_nonneg a]

/-- **The energy estimate**: for a `C²` function `w` with support in a ball on `[0, T]`,
`√(2E(t)) ≤ √(2E(0)) + ∫₀ᵗ ‖□w(s, ·)‖_{L²} ds` for `t ∈ [0, T]`. -/
theorem sqrt_two_mul_energy_le {w : ℝ × E3 → ℝ} (hw : ContDiff ℝ 2 w) {T R : ℝ}
    (h : BallSupportOn T R w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(2 * energy w t) ≤ √(2 * energy w 0) + ∫ s in 0..t, spatialL2Norm (waveOperator w) s := by
  rcases ht.1.eq_or_lt with rfl | ht0
  · simp
  have h' : BallSupportOn t R w := h.mono ht.2 le_rfl
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have ht1 : ContDiff ℝ 1 (Wave.timeDeriv w) := contDiff_timeDeriv (n := 1) hw
  have hs1 : ∀ i, ContDiff ℝ 1 (Wave.spaceDeriv i w) := fun i => contDiff_spaceDeriv (n := 1) hw i
  have h0 : BallSupportOn t R (Wave.timeDeriv w) := h'.timeDeriv ht0 hw1
  have hi : ∀ i, BallSupportOn t R (Wave.spaceDeriv i w) := fun i =>
    h'.spaceDeriv (hw.differentiable (by norm_num)) i
  have hwave : BallSupportOn t R (Wave.waveOperator w) := h'.waveOperator ht0 hw
  have hwc : Continuous (Wave.waveOperator w) := continuous_waveOperator hw
  set N := spatialL2Norm (Wave.waveOperator w) with hN
  set F : ℝ → ℝ := fun s => ∫ x, gradNormSq w (s, x) with hF
  have hFE : ∀ s, 2 * energy w s = F s := fun s => by simp only [energy, hF]; ring
  simp only [hFE]
  have hgc : Continuous (gradNormSq w) := continuous_gradNormSq hw1
  have hgs : BallSupportOn t R (gradNormSq w) := fun s hs y hy => by
    simp only [gradNormSq, h0 s hs y hy, hi _ s hs y hy]
    norm_num
  have hFc : ContinuousOn F (Icc 0 t) := hgs.continuousOn_integral hgc
  have hF0 : ∀ s, 0 ≤ F s := fun s => integral_nonneg fun _ => gradNormSq_nonneg w _
  have hNc : ContinuousOn N (Icc 0 t) :=
    ((hwave.pow two_ne_zero).continuousOn_integral (hwc.fun_pow 2)).sqrt
  have hFd : ∀ s ∈ Ioo 0 t, HasDerivAt F
      (2 * ∫ x, Wave.timeDeriv w (s, x) * Wave.waveOperator w (s, x)) s := fun s hs => by
    have := (hasDerivAt_energy hw ht0 h' hs).const_mul 2
    simpa only [hFE] using this
  have hFle : ∀ s ∈ Ioo 0 t,
      2 * ∫ x, Wave.timeDeriv w (s, x) * Wave.waveOperator w (s, x) ≤ 2 * √(F s) * N s := by
    intro s hs
    have hs' : s ∈ Icc 0 t := Ioo_subset_Icc_self hs
    have hcs := abs_integral_mul_le_sqrt (μ := volume)
      ((h0.pow two_ne_zero).integrable (ht1.continuous.fun_pow 2) hs')
      ((hwave.pow two_ne_zero).integrable (hwc.fun_pow 2) hs')
      ((h0.mul_right _).integrable (ht1.continuous.fun_mul hwc) hs')
    have hle : ∫ x, Wave.timeDeriv w (s, x) ^ 2 ≤ F s :=
      integral_mono ((h0.pow two_ne_zero).integrable (ht1.continuous.fun_pow 2) hs')
        (hgs.integrable hgc hs') fun x =>
          le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [show √(∫ x, Wave.waveOperator w (s, x) ^ 2) = N s from rfl] at hcs
    have h1 := le_abs_self (∫ x, Wave.timeDeriv w (s, x) * Wave.waveOperator w (s, x))
    have h2 : √(∫ x, Wave.timeDeriv w (s, x) ^ 2) * N s ≤ √(F s) * N s :=
      mul_le_mul_of_nonneg_right (sqrt_le_sqrt hle) (sqrt_nonneg _)
    nlinarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set G : ℝ → ℝ := fun s => √(F s + ε ^ 2) - ∫ r in 0..s, N r with hG
  have hNi : ∀ s ∈ Icc 0 t, IntervalIntegrable N volume 0 s := fun s hs =>
    (hNc.mono (by rw [uIcc_of_le hs.1]; exact Icc_subset_Icc le_rfl hs.2)).intervalIntegrable
  have hGd : ∀ s ∈ Ioo 0 t, HasDerivAt G
      ((2 * ∫ x, Wave.timeDeriv w (s, x) * Wave.waveOperator w (s, x)) /
        (2 * √(F s + ε ^ 2)) - N s) s := by
    intro s hs
    have hpos : F s + ε ^ 2 ≠ 0 := by have := hF0 s; positivity
    exact (((hFd s hs).add_const (ε ^ 2)).sqrt hpos).sub
      (intervalIntegral.integral_hasDerivAt_right (hNi s (Ioo_subset_Icc_self hs))
        ((hNc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
        (hNc.continuousAt (Icc_mem_nhds hs.1 hs.2)))
  have hGc : ContinuousOn G (Icc 0 t) := by
    refine ((hFc.add continuousOn_const).sqrt).sub ?_
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := t)
      (f := N) (by rw [uIcc_of_le ht0.le]; exact hNc.integrableOn_Icc)
    rwa [uIcc_of_le ht0.le] at this
  have hanti : AntitoneOn G (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hGc ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hGd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hGd s hs).deriv, sub_nonpos]
      have hpos : 0 < √(F s + ε ^ 2) := sqrt_pos.mpr (by have := hF0 s; positivity)
      rw [div_le_iff₀ (by positivity)]
      have h3 : √(F s) ≤ √(F s + ε ^ 2) := sqrt_le_sqrt (by nlinarith)
      have := hFle s hs
      nlinarith [spatialL2Norm_nonneg (Wave.waveOperator w) s]
  have hGt := hanti ⟨le_rfl, ht0.le⟩ ⟨ht0.le, le_rfl⟩ ht0.le
  simp only [hG, intervalIntegral.integral_same, sub_zero] at hGt
  have h4 : √(F t) ≤ √(F t + ε ^ 2) := sqrt_le_sqrt (by nlinarith)
  have h5 := sqrt_add_sq_le (hF0 0) hε.le
  linarith

/-- **The energy estimate** `√E(t) ≤ √E(0) + ∫₀ᵗ ‖□w(s, ·)‖_{L²} ds` for `t ∈ [0, T]`, for a `C²`
function `w` with support in a ball on `[0, T]`. -/
theorem sqrt_energy_le {w : ℝ × E3 → ℝ} (hw : ContDiff ℝ 2 w) {T R : ℝ}
    (h : BallSupportOn T R w) {t : ℝ} (ht : t ∈ Icc 0 T) :
    √(energy w t) ≤ √(energy w 0) + ∫ s in 0..t, spatialL2Norm (waveOperator w) s := by
  have h2 := sqrt_two_mul_energy_le hw h ht
  rw [sqrt_mul (by norm_num), sqrt_mul (by norm_num)] at h2
  have hI : 0 ≤ ∫ s in 0..t, spatialL2Norm (waveOperator w) s :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => spatialL2Norm_nonneg _ _
  have hs2 : 1 ≤ √2 := by rw [show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by norm_num)
  nlinarith [sqrt_nonneg (energy w t), sqrt_nonneg (energy w 0)]

/-- **An instance** of the energy estimate: `w(t, x) = cos t · χ(x)` for the bump
`χ = spaceBump`, which is smooth with support in the ball of radius `2` at all times. -/
theorem sqrt_energy_le_bump {T t : ℝ} (ht : t ∈ Icc 0 T) :
    √(energy (fun p : ℝ × E3 => cos p.1 * spaceBump p.2) t) ≤
      √(energy (fun p : ℝ × E3 => cos p.1 * spaceBump p.2) 0) +
        ∫ s in 0..t, spatialL2Norm (waveOperator fun p : ℝ × E3 => cos p.1 * spaceBump p.2) s := by
  have hw : ContDiff ℝ 2 fun p : ℝ × E3 => cos p.1 * spaceBump p.2 :=
    (contDiff_cos.comp contDiff_fst).mul (spaceBump.contDiff.comp contDiff_snd)
  have hl : LocalizedSupport 2 fun p : ℝ × E3 => cos p.1 * spaceBump p.2 := fun s y hy => by
    simp only [localizedSupport_spaceBump s y hy, mul_zero]
  exact sqrt_energy_le hw (hl.ballSupportOn T) ht

end ProjectAinos.SmoothGeometry.Wave
