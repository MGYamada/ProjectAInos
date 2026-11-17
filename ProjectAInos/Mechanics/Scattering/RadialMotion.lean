/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.ScalarFlow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import ProjectAInos.SmoothAlgebra.DividedDifference

/-!
# The radial motion of scattering

Let the square of the radial velocity be `F(r) = (r − r₀) W(r)` for `r ≥ r₀`,
with `W` positive and bounded: `r₀` is a simple turning point, the distance of
closest approach, and the motion is unbounded. With `r = r₀ + s²` the equation
`ṙ² = F(r)` becomes `ṡ = ½ √W(r₀ + s²)`, a smooth positive bounded field on the
line, so that the motion exists for all times, the incoming branch being
`s < 0`.

* `parameter W r₀` is the solution `s(t)` with `s(0) = 0`, and
  `radius W r₀ t = r₀ + s(t)²`.
* `radialVelocity_sq`: `ṙ² = F(r)`. `radialVelocity_pos`: `ṙ > 0` after the
  closest approach. `radius_neg`: `r(−t) = r(t)`.
* `tendsto_radius_atTop`: `r(t) → ∞` as `t → ∞`.
* `IsFactor.hasDerivAt_radialVelocity`: `r̈ = F′(r)/2`.
* `exists_isFactor_dividedDifference`: a smooth function with a simple zero at
  `r₀` that is positive and bounded after it has such a factor, its divided
  difference at `r₀`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace ProjectAInos.Mechanics.Scattering

open SmoothGeometry.NonlinearODE

/-- The field of the parameter `s` of `r = r₀ + s²`: `ṡ = ½ √W(r₀ + s²)`. -/
def parameterField (W : ℝ → ℝ) (r₀ s : ℝ) : ℝ := √(W (r₀ + s ^ 2)) / 2

/-- The parameter `s(t)` of the radial motion, with `s(0) = 0`. -/
def parameter (W : ℝ → ℝ) (r₀ t : ℝ) : ℝ := flow (parameterField W r₀) (t, 0)

/-- The radius `r(t) = r₀ + s(t)²` of the motion with the closest approach `r₀`
at the time zero. -/
def radius (W : ℝ → ℝ) (r₀ t : ℝ) : ℝ := r₀ + parameter W r₀ t ^ 2

/-- The radial velocity `ṙ = 2 s ṡ`. -/
def radialVelocity (W : ℝ → ℝ) (r₀ t : ℝ) : ℝ :=
  2 * parameter W r₀ t * parameterField W r₀ (parameter W r₀ t)

/-- The factor `W` of the square of the radial velocity is smooth, positive and
bounded along `r = r₀ + s²`. -/
structure IsFactor (W : ℝ → ℝ) (r₀ C : ℝ) : Prop where
  /-- The factor is smooth in the parameter. -/
  contDiff : ContDiff ℝ ∞ fun s : ℝ => W (r₀ + s ^ 2)
  /-- The factor is positive. -/
  pos : ∀ s : ℝ, 0 < W (r₀ + s ^ 2)
  /-- The factor is bounded. -/
  le : ∀ s : ℝ, W (r₀ + s ^ 2) ≤ C

variable {W : ℝ → ℝ} {r₀ C : ℝ}

namespace IsFactor

theorem contDiff_parameterField (h : IsFactor W r₀ C) :
    ContDiff ℝ ∞ (parameterField W r₀) :=
  (h.contDiff.sqrt fun s => (h.pos s).ne').div_const 2

theorem parameterField_pos (h : IsFactor W r₀ C) (s : ℝ) : 0 < parameterField W r₀ s :=
  div_pos (Real.sqrt_pos.mpr (h.pos s)) two_pos

theorem abs_parameterField_le (h : IsFactor W r₀ C) (s : ℝ) :
    |parameterField W r₀ s| ≤ √C / 2 := by
  rw [abs_of_pos (h.parameterField_pos s), parameterField]
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (h.le s)) two_pos.le

theorem parameterField_neg (W : ℝ → ℝ) (r₀ s : ℝ) :
    parameterField W r₀ (-s) = parameterField W r₀ s := by
  rw [parameterField, parameterField, neg_sq]

theorem hasDerivAt_parameter (h : IsFactor W r₀ C) (t : ℝ) :
    HasDerivAt (parameter W r₀) (parameterField W r₀ (parameter W r₀ t)) t :=
  hasDerivAt_flow_zero h.contDiff_parameterField h.abs_parameterField_le t

theorem strictMono_parameter (h : IsFactor W r₀ C) : StrictMono (parameter W r₀) :=
  strictMono_flow_zero h.contDiff_parameterField h.parameterField_pos h.abs_parameterField_le

end IsFactor

@[simp] theorem parameter_zero (W : ℝ → ℝ) (r₀ : ℝ) : parameter W r₀ 0 = 0 :=
  flow_zero _ _

@[simp] theorem radius_zero (W : ℝ → ℝ) (r₀ : ℝ) : radius W r₀ 0 = r₀ := by
  simp [radius]

theorem le_radius (W : ℝ → ℝ) (r₀ t : ℝ) : r₀ ≤ radius W r₀ t :=
  le_add_of_nonneg_right (sq_nonneg _)

namespace IsFactor

theorem parameter_pos (h : IsFactor W r₀ C) {t : ℝ} (ht : 0 < t) : 0 < parameter W r₀ t := by
  have := h.strictMono_parameter ht
  rwa [parameter_zero] at this

/-- The parameter is an odd function of the time. -/
theorem parameter_neg (h : IsFactor W r₀ C) (t : ℝ) :
    parameter W r₀ (-t) = -parameter W r₀ t := by
  have hX : ContDiff ℝ 1 (parameterField W r₀) := h.contDiff_parameterField.of_le (by simp)
  have hf : ∀ r ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => -parameter W r₀ (-s))
      (parameterField W r₀ (-parameter W r₀ (-r))) r := by
    intro r _
    have h1 : HasDerivAt (fun s => parameter W r₀ (-s))
        (parameterField W r₀ (parameter W r₀ (-r)) * -1) r :=
      HasDerivAt.comp r (h.hasDerivAt_parameter (-r)) (hasDerivAt_neg r)
    have h2 : HasDerivAt (fun s => -parameter W r₀ (-s))
        (-(parameterField W r₀ (parameter W r₀ (-r)) * -1)) r := h1.neg
    rw [parameterField_neg]
    refine h2.congr_deriv ?_
    ring
  have hg : ∀ r ∈ uIcc (0 : ℝ) t, HasDerivAt (parameter W r₀)
      (parameterField W r₀ (parameter W r₀ r)) r := fun r _ => h.hasDerivAt_parameter r
  have heq := eq_of_hasDerivAt_of_eq hX (f := fun s => -parameter W r₀ (-s))
    (g := parameter W r₀) (s := 0) (t := t) hf hg (by simp)
  simpa [neg_eq_iff_eq_neg] using heq

theorem radius_neg (h : IsFactor W r₀ C) (t : ℝ) : radius W r₀ (-t) = radius W r₀ t := by
  rw [radius, radius, h.parameter_neg, neg_sq]

theorem hasDerivAt_radius (h : IsFactor W r₀ C) (t : ℝ) :
    HasDerivAt (radius W r₀) (radialVelocity W r₀ t) t := by
  have h1 := ((h.hasDerivAt_parameter t).pow 2).const_add r₀
  refine h1.congr_deriv ?_
  rw [radialVelocity]
  simp

/-- `ṙ² = (r − r₀) W(r)`. -/
theorem radialVelocity_sq (h : IsFactor W r₀ C) (t : ℝ) :
    radialVelocity W r₀ t ^ 2 = (radius W r₀ t - r₀) * W (radius W r₀ t) := by
  rw [radialVelocity, parameterField, radius, add_sub_cancel_left, mul_pow, mul_pow, div_pow,
    Real.sq_sqrt (h.pos _).le]
  ring

theorem radialVelocity_pos (h : IsFactor W r₀ C) {t : ℝ} (ht : 0 < t) :
    0 < radialVelocity W r₀ t :=
  mul_pos (mul_pos two_pos (h.parameter_pos ht)) (h.parameterField_pos _)

theorem tendsto_parameter_atTop (h : IsFactor W r₀ C) : Tendsto (parameter W r₀) atTop atTop :=
  h.strictMono_parameter.monotone.tendsto_atTop_atTop fun b =>
    ⟨scalarTime (parameterField W r₀) b,
      (flow_scalarTime h.contDiff_parameterField h.parameterField_pos
        h.abs_parameterField_le b).ge⟩

/-- The radius tends to infinity. -/
theorem tendsto_radius_atTop (h : IsFactor W r₀ C) : Tendsto (radius W r₀) atTop atTop := by
  have h1 : Tendsto (fun t => parameter W r₀ t ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp h.tendsto_parameter_atTop
  exact tendsto_atTop_add_const_left _ r₀ h1

theorem strictMonoOn_radius (h : IsFactor W r₀ C) : StrictMonoOn (radius W r₀) (Ici 0) := by
  intro a ha b _ hab
  have h0 : 0 ≤ parameter W r₀ a := by
    rcases eq_or_lt_of_le (mem_Ici.mp ha) with rfl | hpos
    · simp
    · exact (h.parameter_pos hpos).le
  have h1 := h.strictMono_parameter hab
  rw [radius, radius]
  nlinarith

theorem contDiff_parameter (h : IsFactor W r₀ C) : ContDiff ℝ ∞ (parameter W r₀) := by
  have hdom : ∀ t : ℝ, ((t, (0 : ℝ)) : ℝ × ℝ) ∈ flowDomain (parameterField W r₀) := fun t => by
    rw [flowDomain_eq_univ_of_abs_le h.contDiff_parameterField h.abs_parameterField_le]
    exact mem_univ _
  exact contDiff_iff_contDiffAt.mpr fun t =>
    (contDiffAt_flow h.contDiff_parameterField (hdom t)).comp t
      (contDiffAt_id.prodMk contDiffAt_const)

theorem contDiff_radius (h : IsFactor W r₀ C) : ContDiff ℝ ∞ (radius W r₀) :=
  contDiff_const.add (h.contDiff_parameter.pow 2)

theorem contDiff_radialVelocity (h : IsFactor W r₀ C) : ContDiff ℝ ∞ (radialVelocity W r₀) :=
  (contDiff_const.mul h.contDiff_parameter).mul
    (h.contDiff_parameterField.comp h.contDiff_parameter)

theorem radialVelocity_neg (h : IsFactor W r₀ C) (t : ℝ) :
    radialVelocity W r₀ (-t) = -radialVelocity W r₀ t := by
  rw [radialVelocity, radialVelocity, h.parameter_neg, parameterField_neg]
  ring

/-- The equation of the radial motion: `r̈ = F′(r)/2` for `F(r) = (r − r₀) W(r)`. -/
theorem hasDerivAt_radialVelocity (h : IsFactor W r₀ C) {F F' : ℝ → ℝ}
    (hF : ∀ r, r₀ ≤ r → F r = (r - r₀) * W r) (hF' : ∀ r, r₀ ≤ r → HasDerivAt F (F' r) r)
    (t : ℝ) : HasDerivAt (radialVelocity W r₀) (F' (radius W r₀ t) / 2) t := by
  have hvd : HasDerivAt (radialVelocity W r₀) (deriv (radialVelocity W r₀) t) t :=
    (h.contDiff_radialVelocity.differentiable (by simp) t).hasDerivAt
  have hsq : ∀ s : ℝ, radialVelocity W r₀ s ^ 2 = F (radius W r₀ s) := fun s => by
    rw [h.radialVelocity_sq, hF _ (le_radius W r₀ s)]
  have h1 : HasDerivAt (fun s => radialVelocity W r₀ s ^ 2)
      (2 * radialVelocity W r₀ t * deriv (radialVelocity W r₀) t) t := by
    refine (hvd.pow 2).congr_deriv ?_
    simp
  have h2 : HasDerivAt (fun s => F (radius W r₀ s))
      (F' (radius W r₀ t) * radialVelocity W r₀ t) t :=
    HasDerivAt.comp t (hF' _ (le_radius W r₀ t)) (h.hasDerivAt_radius t)
  have hfun : (fun s => radialVelocity W r₀ s ^ 2) = fun s => F (radius W r₀ s) := funext hsq
  rw [hfun] at h1
  have hval := h1.unique h2
  by_cases ht : radialVelocity W r₀ t = 0
  · -- the closest approach: `F′(r₀) = W(r₀)` and `v̇ = W(r₀)/2`
    have hs0 : parameter W r₀ t = 0 := by
      rcases mul_eq_zero.mp ht with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_left two_ne_zero
      · exact absurd h3 (h.parameterField_pos _).ne'
    have hr : radius W r₀ t = r₀ := by rw [radius, hs0]; simp
    have hW0 : F' r₀ = W r₀ := by
      have hslope := hasDerivAt_iff_tendsto_slope.mp (hF' r₀ le_rfl)
      have hmap : Tendsto (fun s : ℝ => r₀ + s ^ 2) (𝓝[≠] 0) (𝓝[≠] r₀) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc : Continuous fun s : ℝ => r₀ + s ^ 2 := by fun_prop
          have := hc.tendsto 0
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          have : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
          simpa using this
      have h3 := hslope.comp hmap
      have h4 : Tendsto (fun s : ℝ => W (r₀ + s ^ 2)) (𝓝[≠] 0) (𝓝 (W r₀)) := by
        have := (h.contDiff.continuous.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
        simpa using this
      refine tendsto_nhds_unique (h3.congr' ?_) h4
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s ≠ 0 := hs
      rw [Function.comp_apply, slope, vsub_eq_sub, smul_eq_mul, hF _ (le_add_of_nonneg_right
        (sq_nonneg s)), hF r₀ le_rfl, sub_self, zero_mul, sub_zero, add_sub_cancel_left]
      field_simp
    have hvd0 : HasDerivAt (radialVelocity W r₀)
        (2 * parameterField W r₀ (parameter W r₀ t) * parameterField W r₀ (parameter W r₀ t) +
          2 * parameter W r₀ t * deriv (fun s => parameterField W r₀ (parameter W r₀ s)) t) t := by
      have hg : HasDerivAt (fun s => parameterField W r₀ (parameter W r₀ s))
          (deriv (fun s => parameterField W r₀ (parameter W r₀ s)) t) t :=
        ((h.contDiff_parameterField.comp h.contDiff_parameter).differentiable (by simp)
          t).hasDerivAt
      exact ((h.hasDerivAt_parameter t).const_mul 2).mul hg
    rw [hs0] at hvd0
    refine hvd0.congr_deriv ?_
    rw [hr, hW0, parameterField]
    have hpos := h.pos 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_zero,
      zero_mul] at hpos ⊢
    have hsq' : √(W r₀) * √(W r₀) = W r₀ := Real.mul_self_sqrt hpos.le
    linear_combination (1 / 2 : ℝ) * hsq'
  · have hd : deriv (radialVelocity W r₀) t = F' (radius W r₀ t) / 2 := by
      have h3 : 2 * deriv (radialVelocity W r₀) t = F' (radius W r₀ t) :=
        mul_right_cancel₀ ht (by linear_combination hval)
      linarith
    rw [← hd]
    exact hvd

end IsFactor

/-- A smooth function with a simple zero at `r₀`, positive and bounded after
it, is `(r − r₀) W(r)` with a factor `W` of the kind required. -/
theorem exists_isFactor_dividedDifference {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {r₀ B : ℝ}
    (h0 : G r₀ = 0) (hd : 0 < deriv G r₀) (hpos : ∀ r, r₀ < r → 0 < G r)
    (hB : ∀ r, r₀ ≤ r → G r ≤ B) :
    (∀ r, G r = (r - r₀) * SmoothAlgebra.dividedDifference G (r, r₀)) ∧
      ∃ C : ℝ, IsFactor (fun r => SmoothAlgebra.dividedDifference G (r, r₀)) r₀ C := by
  have hfac : ∀ r, G r = (r - r₀) * SmoothAlgebra.dividedDifference G (r, r₀) := fun r => by
    have h := SmoothAlgebra.sub_eq_mul_dividedDifference (hG.of_le (by simp)) r r₀
    rwa [h0, sub_zero] at h
  have hsm : ContDiff ℝ ∞ fun s : ℝ => SmoothAlgebra.dividedDifference G (r₀ + s ^ 2, r₀) :=
    (SmoothAlgebra.contDiff_dividedDifference hG).comp
      ((contDiff_const.add (contDiff_id.pow 2)).prodMk contDiff_const)
  have hval : ∀ s : ℝ, s ≠ 0 →
      SmoothAlgebra.dividedDifference G (r₀ + s ^ 2, r₀) = G (r₀ + s ^ 2) / s ^ 2 := by
    intro s hs
    have h := hfac (r₀ + s ^ 2)
    rw [add_sub_cancel_left] at h
    rw [h]
    field_simp
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-1 : ℝ) 1)
    hsm.continuous.continuousOn
  refine ⟨hfac, max C₁ |B|, hsm, fun s => ?_, fun s => ?_⟩
  · rcases eq_or_ne s 0 with rfl | hs
    · simpa [SmoothAlgebra.dividedDifference_self] using hd
    · rw [hval s hs]
      have hs2 : 0 < s ^ 2 := by positivity
      exact div_pos (hpos _ (by linarith)) hs2
  · by_cases hs : s ∈ Icc (-1 : ℝ) 1
    · exact (le_abs_self _).trans ((hC₁ s hs).trans (le_max_left _ _))
    · have hs1 : 1 < s ^ 2 := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hs
        rcases hs with h | h <;> nlinarith
      have hs0 : s ≠ 0 := fun h => by rw [h] at hs1; norm_num at hs1
      rw [hval s hs0]
      have hGle : G (r₀ + s ^ 2) ≤ |B| :=
        (hB _ (le_add_of_nonneg_right (sq_nonneg s))).trans (le_abs_self B)
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg B]

/-! ### The angle -/

/-- The polar angle `φ(t) = ∫₀ᵗ ℓ/r²`, for the angular momentum `m ℓ`. -/
def angle (W : ℝ → ℝ) (r₀ ℓ t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, ℓ / radius W r₀ τ ^ 2

@[simp] theorem angle_zero (W : ℝ → ℝ) (r₀ ℓ : ℝ) : angle W r₀ ℓ 0 = 0 := by
  simp [angle]

namespace IsFactor

theorem continuous_angleRate (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) (ℓ : ℝ) :
    Continuous fun τ => ℓ / radius W r₀ τ ^ 2 :=
  continuous_const.div (h.contDiff_radius.continuous.pow 2) fun τ =>
    pow_ne_zero 2 (hr₀.trans_le (le_radius W r₀ τ)).ne'

theorem hasDerivAt_angle (h : IsFactor W r₀ C) (hr₀ : 0 < r₀) (ℓ t : ℝ) :
    HasDerivAt (angle W r₀ ℓ) (ℓ / radius W r₀ t ^ 2) t :=
  ((h.continuous_angleRate hr₀ ℓ).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The angle is an odd function of the time. -/
theorem angle_neg (h : IsFactor W r₀ C) (ℓ t : ℝ) : angle W r₀ ℓ (-t) = -angle W r₀ ℓ t := by
  have h1 := intervalIntegral.integral_comp_neg (a := 0) (b := t)
    (fun τ => ℓ / radius W r₀ τ ^ 2)
  simp only [h.radius_neg, neg_zero] at h1
  rw [angle, angle, intervalIntegral.integral_symm, ← h1]

end IsFactor

end ProjectAInos.Mechanics.Scattering
