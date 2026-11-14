/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Quadrature
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quadrature up to simple turning points

Between two turning points `u₁ < u₂` of a motion with `ẋ² = F(x)`, the time
is `∫ du / √F(u)`. The integrand is unbounded at the turning points, but for
simple turning points, `F(u) = (u − u₁)(u₂ − u) G(u)` with `G > 0`, it is
integrable, and the substitution `u = (u₁ + u₂)/2 + (u₂ − u₁)/2 · cos θ`
removes the singularity:

`∫ w(u) du / √((u − u₁)(u₂ − u) G(u)) = ∫₀^π w(u(θ)) dθ / √G(u(θ))`.

* `integral_div_sqrt_turning`: this identity, for all functions `w` and `G`.
* `integrableOn_div_sqrt_turning`: the integrand is integrable when `w` and
  `G` are continuous and `G > 0`.
* `integral_comp_eq_integral_div_sqrt_turning`: for a motion with `ẋ > 0`
  between the turning points, `∫ w(x(t)) dt = ∫ w(u) du / √F(u)`.
* `sub_eq_sqrt_mul_integral_of_energy_turning`: Landau–Lifshitz (11.5), the
  time between two turning points is `√(m/2) ∫ dx / √(E − U(x))`.

The integrals are Lebesgue integrals, so no limit at the turning points is
taken. The parameter `θ` is the eccentric anomaly in Kepler's problem.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open Set MeasureTheory
open scoped Real

/-- The point `(u₁ + u₂)/2 + (u₂ − u₁)/2 · cos θ` of the interval `[u₁, u₂]`:
`u₂` at `θ = 0` and `u₁` at `θ = π`. -/
def turningParam (u₁ u₂ θ : ℝ) : ℝ := (u₁ + u₂) / 2 + (u₂ - u₁) / 2 * Real.cos θ

theorem hasDerivAt_turningParam (u₁ u₂ θ : ℝ) :
    HasDerivAt (turningParam u₁ u₂) (-((u₂ - u₁) / 2 * Real.sin θ)) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul ((u₂ - u₁) / 2)).const_add ((u₁ + u₂) / 2)
  have e : (u₂ - u₁) / 2 * -Real.sin θ = -((u₂ - u₁) / 2 * Real.sin θ) := by ring
  rw [e] at h
  exact h

theorem continuous_turningParam (u₁ u₂ : ℝ) : Continuous (turningParam u₁ u₂) :=
  continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_turningParam u₁ u₂ θ).continuousAt

theorem turningParam_image {u₁ u₂ : ℝ} (h : u₁ < u₂) :
    turningParam u₁ u₂ '' Icc 0 π = Icc u₁ u₂ := by
  have hh : 0 < (u₂ - u₁) / 2 := by linarith
  have hcomp : turningParam u₁ u₂ =
      (fun y => (u₂ - u₁) / 2 * y + (u₁ + u₂) / 2) ∘ Real.cos := by
    funext θ
    simp only [turningParam, Function.comp_apply]
    ring
  rw [hcomp, Set.image_comp, Real.bijOn_cos.image_eq, Set.image_affine_Icc' hh]
  congr 1 <;> ring

theorem turningParam_mem_Icc {u₁ u₂ : ℝ} (h : u₁ < u₂) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    turningParam u₁ u₂ θ ∈ Icc u₁ u₂ := by
  rw [← turningParam_image h]
  exact mem_image_of_mem _ hθ

/-- The mean of the parametrization over `[0, π]` is the midpoint. -/
theorem integral_turningParam (u₁ u₂ : ℝ) :
    ∫ θ in (0 : ℝ)..π, turningParam u₁ u₂ θ = π * ((u₁ + u₂) / 2) := by
  have h : ∫ θ in (0 : ℝ)..π, turningParam u₁ u₂ θ =
      (∫ _ in (0 : ℝ)..π, (u₁ + u₂) / 2) + ∫ θ in (0 : ℝ)..π, (u₂ - u₁) / 2 * Real.cos θ :=
    intervalIntegral.integral_add intervalIntegrable_const
      ((Real.continuous_cos.const_mul _).intervalIntegrable _ _)
  rw [h, intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos,
    Real.sin_pi, Real.sin_zero, sub_zero, sub_zero, mul_zero, add_zero, smul_eq_mul]

theorem injOn_turningParam {u₁ u₂ : ℝ} (h : u₁ < u₂) :
    InjOn (turningParam u₁ u₂) (Icc 0 π) := by
  intro a ha b hb hab
  have hh : (u₂ - u₁) / 2 ≠ 0 := by
    have : 0 < (u₂ - u₁) / 2 := by linarith
    exact this.ne'
  simp only [turningParam] at hab
  exact Real.injOn_cos ha hb (mul_left_cancel₀ hh (add_left_cancel hab))

/-- `(u − u₁)(u₂ − u) = ((u₂ − u₁)/2 · sin θ)²` on the parametrized interval. -/
theorem turningParam_sub_mul_sub (u₁ u₂ θ : ℝ) :
    (turningParam u₁ u₂ θ - u₁) * (u₂ - turningParam u₁ u₂ θ) =
      ((u₂ - u₁) / 2 * Real.sin θ) ^ 2 := by
  simp only [turningParam]
  linear_combination (-(((u₂ - u₁) / 2) ^ 2)) * Real.sin_sq_add_cos_sq θ

/-- The Jacobian of the parametrization cancels the square root of
`(u − u₁)(u₂ − u)`. -/
theorem abs_deriv_smul_div_sqrt_turning {u₁ u₂ : ℝ} (h : u₁ < u₂) (w G : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    |-((u₂ - u₁) / 2 * Real.sin θ)| •
        (w (turningParam u₁ u₂ θ) / √((turningParam u₁ u₂ θ - u₁) *
          (u₂ - turningParam u₁ u₂ θ) * G (turningParam u₁ u₂ θ))) =
      w (turningParam u₁ u₂ θ) / √(G (turningParam u₁ u₂ θ)) := by
  have hs : 0 < (u₂ - u₁) / 2 * Real.sin θ :=
    mul_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
  rw [turningParam_sub_mul_sub, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs.le, abs_neg,
    abs_of_pos hs, smul_eq_mul, ← mul_div_assoc, mul_div_mul_left _ _ hs.ne']

/-- The regularization of the integral between two simple turning points:
`∫ w(u) du / √((u − u₁)(u₂ − u) G(u)) = ∫₀^π w(u(θ)) dθ / √G(u(θ))`. -/
theorem integral_div_sqrt_turning {u₁ u₂ : ℝ} (h : u₁ < u₂) (w G : ℝ → ℝ) :
    ∫ u in u₁..u₂, w u / √((u - u₁) * (u₂ - u) * G u) =
      ∫ θ in (0 : ℝ)..π, w (turningParam u₁ u₂ θ) / √(G (turningParam u₁ u₂ θ)) := by
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun θ _ => (hasDerivAt_turningParam u₁ u₂ θ).hasDerivWithinAt) (injOn_turningParam h)
    (fun u => w u / √((u - u₁) * (u₂ - u) * G u))
  rw [turningParam_image h] at key
  rw [intervalIntegral.integral_of_le h.le, intervalIntegral.integral_of_le Real.pi_pos.le,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, key,
    integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun θ hθ =>
    abs_deriv_smul_div_sqrt_turning h w G hθ

/-- Between two simple turning points the integrand `w / √F` is integrable. -/
theorem integrableOn_div_sqrt_turning {u₁ u₂ : ℝ} (h : u₁ < u₂) {w G : ℝ → ℝ}
    (hw : ContinuousOn w (Icc u₁ u₂)) (hG : ContinuousOn G (Icc u₁ u₂))
    (hGpos : ∀ u ∈ Icc u₁ u₂, 0 < G u) :
    IntegrableOn (fun u => w u / √((u - u₁) * (u₂ - u) * G u)) (Icc u₁ u₂) := by
  have hmaps : MapsTo (turningParam u₁ u₂) (Icc 0 π) (Icc u₁ u₂) := by
    rw [← turningParam_image h]
    exact mapsTo_image _ _
  have hp : ContinuousOn (turningParam u₁ u₂) (Icc 0 π) :=
    (continuous_turningParam u₁ u₂).continuousOn
  have hcont : ContinuousOn
      (fun θ => w (turningParam u₁ u₂ θ) / √(G (turningParam u₁ u₂ θ))) (Icc 0 π) :=
    (hw.comp hp hmaps).div (Real.continuous_sqrt.comp_continuousOn (hG.comp hp hmaps))
      fun θ hθ => (Real.sqrt_pos.mpr (hGpos _ (hmaps hθ))).ne'
  rw [← turningParam_image h]
  refine (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (fun θ _ => (hasDerivAt_turningParam u₁ u₂ θ).hasDerivWithinAt) (injOn_turningParam h)
    _).mpr ((integrableOn_Icc_iff_integrableOn_Ioo).mpr ?_)
  exact (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
    (fun θ hθ => (abs_deriv_smul_div_sqrt_turning h w G hθ).symm) measurableSet_Ioo

/-- Quadrature up to the turning points: if `x` increases from the turning
point `u₁` to the turning point `u₂` and `ẋ² = (x − u₁)(u₂ − x) G(x)` with
`G > 0`, then `∫ w(x(t)) dt = ∫ w(u) du / √((u − u₁)(u₂ − u) G(u))`. The
velocity may vanish at both ends. -/
theorem integral_comp_eq_integral_div_sqrt_turning {x x' w G : ℝ → ℝ} {t₁ t₂ u₁ u₂ : ℝ}
    (ht : t₁ < t₂) (hu : u₁ < u₂) (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t)
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < x' t) (h₁ : x t₁ = u₁) (h₂ : x t₂ = u₂)
    (hF : ∀ t ∈ Ioo t₁ t₂, x' t ^ 2 = (x t - u₁) * (u₂ - x t) * G (x t))
    (hw : ContinuousOn w (Icc u₁ u₂)) (hG : ContinuousOn G (Icc u₁ u₂))
    (hGpos : ∀ u ∈ Icc u₁ u₂, 0 < G u) :
    ∫ t in t₁..t₂, w (x t) = ∫ u in u₁..u₂, w u / √((u - u₁) * (u₂ - u) * G u) := by
  have hcont : ContinuousOn x (Icc t₁ t₂) := fun t ht' =>
    (hx t ht').continuousAt.continuousWithinAt
  have hmono : StrictMonoOn x (Icc t₁ t₂) :=
    strictMonoOn_of_deriv_pos (convex_Icc t₁ t₂) hcont fun t ht' => by
      rw [interior_Icc] at ht'
      rw [(hx t (Ioo_subset_Icc_self ht')).deriv]
      exact hpos t ht'
  have hmapsIcc : MapsTo x (Icc t₁ t₂) (Icc u₁ u₂) := fun t ht' =>
    ⟨h₁ ▸ hmono.monotoneOn (left_mem_Icc.mpr ht.le) ht' ht'.1,
      h₂ ▸ hmono.monotoneOn ht' (right_mem_Icc.mpr ht.le) ht'.2⟩
  have hmapsIoo : MapsTo x (Ioo t₁ t₂) (Ioo u₁ u₂) := fun t ht' =>
    ⟨h₁ ▸ hmono (left_mem_Icc.mpr ht.le) (Ioo_subset_Icc_self ht') ht'.1,
      h₂ ▸ hmono (Ioo_subset_Icc_self ht') (right_mem_Icc.mpr ht.le) ht'.2⟩
  have hgcont : ContinuousOn (fun u => w u / √((u - u₁) * (u₂ - u) * G u)) (Ioo u₁ u₂) := by
    refine (hw.mono Ioo_subset_Icc_self).div (Real.continuous_sqrt.comp_continuousOn
      (((continuous_id.sub continuous_const).mul
        (continuous_const.sub continuous_id)).continuousOn.mul
          (hG.mono Ioo_subset_Icc_self))) fun u hu' => ?_
    exact (Real.sqrt_pos.mpr (mul_pos (mul_pos (sub_pos.mpr hu'.1) (sub_pos.mpr hu'.2))
      (hGpos u (Ioo_subset_Icc_self hu')))).ne'
  have hpoint : ∀ t ∈ Ioo t₁ t₂,
      ((fun u => w u / √((u - u₁) * (u₂ - u) * G u)) ∘ x) t * x' t = w (x t) := fun t ht' => by
    simp only [Function.comp_apply]
    rw [← hF t ht', Real.sqrt_sq (hpos t ht').le, div_mul_cancel₀ _ (hpos t ht').ne']
  have hwx : IntegrableOn (fun t => w (x t)) (Icc t₁ t₂) :=
    (hw.comp hcont hmapsIcc).integrableOn_Icc
  have key := intervalIntegral.integral_comp_mul_deriv''' (a := t₁) (b := t₂) (f := x)
    (f' := x') (g := fun u => w u / √((u - u₁) * (u₂ - u) * G u))
    (by rwa [uIcc_of_le ht.le])
    (fun t ht' => by
      rw [min_eq_left ht.le, max_eq_right ht.le] at ht'
      exact (hx t (Ioo_subset_Icc_self ht')).hasDerivWithinAt)
    (by
      rw [min_eq_left ht.le, max_eq_right ht.le]
      exact hgcont.mono (image_subset_iff.mpr hmapsIoo))
    (by
      rw [uIcc_of_le ht.le]
      exact (integrableOn_div_sqrt_turning hu hw hG hGpos).mono_set
        (image_subset_iff.mpr hmapsIcc))
    (by
      rw [uIcc_of_le ht.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr
        ((hwx.mono_set Ioo_subset_Icc_self).congr_fun
          (fun t ht' => (hpoint t ht').symm) measurableSet_Ioo))
  rw [h₁, h₂] at key
  rw [← key, intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht' => (hpoint t ht').symm

/-- A function with a positive derivative in the interior of an interval takes
a smaller value at the left end than at the right end. -/
theorem lt_of_hasDerivAt_pos {x x' : ℝ → ℝ} {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < x' t) :
    x t₁ < x t₂ :=
  strictMonoOn_of_deriv_pos (convex_Icc t₁ t₂)
    (fun t ht' => (hx t ht').continuousAt.continuousWithinAt)
    (fun t ht' => by
      rw [interior_Icc] at ht'
      rw [(hx t (Ioo_subset_Icc_self ht')).deriv]
      exact hpos t ht')
    (left_mem_Icc.mpr ht.le) (right_mem_Icc.mpr ht.le) ht

/-- A function with a negative derivative in the interior of an interval takes
a larger value at the left end than at the right end. -/
theorem lt_of_hasDerivAt_neg {x x' : ℝ → ℝ} {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t) (hneg : ∀ t ∈ Ioo t₁ t₂, x' t < 0) :
    x t₂ < x t₁ :=
  strictAntiOn_of_deriv_neg (convex_Icc t₁ t₂)
    (fun t ht' => (hx t ht').continuousAt.continuousWithinAt)
    (fun t ht' => by
      rw [interior_Icc] at ht'
      rw [(hx t (Ioo_subset_Icc_self ht')).deriv]
      exact hneg t ht')
    (left_mem_Icc.mpr ht.le) (right_mem_Icc.mpr ht.le) ht

/-- Quadrature up to the turning points for a decreasing motion: if `x`
decreases from the turning point `u₂` to the turning point `u₁`, the integral
over the time is the same integral over `[u₁, u₂]`. -/
theorem integral_comp_eq_integral_div_sqrt_turning_of_neg {x x' w G : ℝ → ℝ}
    {t₁ t₂ u₁ u₂ : ℝ} (ht : t₁ < t₂) (hu : u₁ < u₂)
    (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t) (hneg : ∀ t ∈ Ioo t₁ t₂, x' t < 0)
    (h₁ : x t₁ = u₂) (h₂ : x t₂ = u₁)
    (hF : ∀ t ∈ Ioo t₁ t₂, x' t ^ 2 = (x t - u₁) * (u₂ - x t) * G (x t))
    (hw : ContinuousOn w (Icc u₁ u₂)) (hG : ContinuousOn G (Icc u₁ u₂))
    (hGpos : ∀ u ∈ Icc u₁ u₂, 0 < G u) :
    ∫ t in t₁..t₂, w (x t) = ∫ u in u₁..u₂, w u / √((u - u₁) * (u₂ - u) * G u) := by
  have hIcc : ∀ s ∈ Icc t₁ t₂, t₁ + t₂ - s ∈ Icc t₁ t₂ := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hIoo : ∀ s ∈ Ioo t₁ t₂, t₁ + t₂ - s ∈ Ioo t₁ t₂ := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have key := integral_comp_eq_integral_div_sqrt_turning (x := fun s => x (t₁ + t₂ - s))
    (x' := fun s => -x' (t₁ + t₂ - s)) (w := w) (G := G) ht hu
    (fun s hs => by
      have h := (hx _ (hIcc s hs)).comp s ((hasDerivAt_id s).const_sub (t₁ + t₂))
      rw [mul_neg_one] at h
      exact h)
    (fun s hs => neg_pos.mpr (hneg _ (hIoo s hs)))
    (by rw [add_sub_cancel_left, h₂]) (by rw [add_sub_cancel_right, h₁])
    (fun s hs => by rw [neg_sq]; exact hF _ (hIoo s hs)) hw hG hGpos
  rw [← key, intervalIntegral.integral_comp_sub_left (fun t => w (x t)) (t₁ + t₂),
    add_sub_cancel_right, add_sub_cancel_left]

/-- The time between two simple turning points as a regular integral:
`t₂ − t₁ = ∫₀^π dθ / √G(u(θ))`. -/
theorem sub_eq_integral_turningParam {x x' G : ℝ → ℝ} {t₁ t₂ u₁ u₂ : ℝ}
    (ht : t₁ < t₂) (hu : u₁ < u₂) (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t)
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < x' t) (h₁ : x t₁ = u₁) (h₂ : x t₂ = u₂)
    (hF : ∀ t ∈ Ioo t₁ t₂, x' t ^ 2 = (x t - u₁) * (u₂ - x t) * G (x t))
    (hG : ContinuousOn G (Icc u₁ u₂)) (hGpos : ∀ u ∈ Icc u₁ u₂, 0 < G u) :
    t₂ - t₁ = ∫ θ in (0 : ℝ)..π, 1 / √(G (turningParam u₁ u₂ θ)) := by
  rw [← integral_div_sqrt_turning hu (fun _ => 1) G,
    ← integral_comp_eq_integral_div_sqrt_turning (w := fun _ => 1) ht hu hx hpos h₁ h₂ hF
      continuousOn_const hG hGpos, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- Motion in one dimension (Landau–Lifshitz (11.5)): if `x` goes from the
turning point `u₁` to the turning point `u₂` with `m ẋ²/2 + U(x) = E`, and the
turning points are simple, `E − U(u) = (u − u₁)(u₂ − u) W(u)` with `W > 0`,
then `t₂ − t₁ = √(m/2) ∫ dx / √(E − U(x))`. For a periodic motion this is
half the period. -/
theorem sub_eq_sqrt_mul_integral_of_energy_turning {x x' U W : ℝ → ℝ}
    {m E t₁ t₂ u₁ u₂ : ℝ} (hm : 0 < m) (ht : t₁ < t₂) (hu : u₁ < u₂)
    (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < x' t)
    (h₁ : x t₁ = u₁) (h₂ : x t₂ = u₂)
    (hE : ∀ t ∈ Ioo t₁ t₂, m / 2 * x' t ^ 2 + U (x t) = E)
    (hU : ∀ u ∈ Icc u₁ u₂, E - U u = (u - u₁) * (u₂ - u) * W u)
    (hW : ContinuousOn W (Icc u₁ u₂)) (hWpos : ∀ u ∈ Icc u₁ u₂, 0 < W u) :
    t₂ - t₁ = √(m / 2) * ∫ u in u₁..u₂, 1 / √(E - U u) := by
  have hm2 : 0 < m / 2 := by positivity
  have hcont : ContinuousOn x (Icc t₁ t₂) := fun t ht' =>
    (hx t ht').continuousAt.continuousWithinAt
  have hmono : StrictMonoOn x (Icc t₁ t₂) :=
    strictMonoOn_of_deriv_pos (convex_Icc t₁ t₂) hcont fun t ht' => by
      rw [interior_Icc] at ht'
      rw [(hx t (Ioo_subset_Icc_self ht')).deriv]
      exact hpos t ht'
  have hmapsIcc : MapsTo x (Icc t₁ t₂) (Icc u₁ u₂) := fun t ht' =>
    ⟨h₁ ▸ hmono.monotoneOn (left_mem_Icc.mpr ht.le) ht' ht'.1,
      h₂ ▸ hmono.monotoneOn ht' (right_mem_Icc.mpr ht.le) ht'.2⟩
  have hF : ∀ t ∈ Ioo t₁ t₂,
      x' t ^ 2 = (x t - u₁) * (u₂ - x t) * (W (x t) / (m / 2)) := fun t ht' => by
    rw [← mul_div_assoc, ← hU _ (hmapsIcc (Ioo_subset_Icc_self ht')), eq_div_iff hm2.ne',
      ← hE t ht']
    ring
  have h := integral_comp_eq_integral_div_sqrt_turning (w := fun _ => 1)
    (G := fun u => W u / (m / 2)) ht hu hx hpos h₁ h₂ hF continuousOn_const
    (hW.div_const _) fun u hu' => div_pos (hWpos u hu') hm2
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h
  rw [h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu' => ?_
  rw [uIcc_of_le hu.le] at hu'
  change 1 / √((u - u₁) * (u₂ - u) * (W u / (m / 2))) = √(m / 2) * (1 / √(E - U u))
  rw [← mul_div_assoc, ← hU u hu', Real.sqrt_div' _ hm2.le, one_div_div, mul_one_div]

/-! ### The oscillator -/

/-- The formula gives the half period of the oscillator: for
`U = m ω² x²/2` and `E = m ω² a²/2`,
`√(m/2) ∫ dx / √(E − U(x)) = π/ω` between the turning points `∓a`. -/
theorem sqrt_mul_integral_oscillator {m ω a : ℝ} (hm : 0 < m) (hω : 0 < ω) (ha : 0 < a) :
    √(m / 2) * ∫ u in -a..a, 1 / √(m * ω ^ 2 / 2 * a ^ 2 - m * ω ^ 2 / 2 * u ^ 2) = π / ω := by
  have hc : 0 < m * ω ^ 2 / 2 := by positivity
  have hint : ∫ u in -a..a, 1 / √(m * ω ^ 2 / 2 * a ^ 2 - m * ω ^ 2 / 2 * u ^ 2) =
      ∫ u in -a..a, 1 / √((u - -a) * (a - u) * (m * ω ^ 2 / 2)) :=
    intervalIntegral.integral_congr fun u _ => by
      congr 2
      ring
  rw [hint, integral_div_sqrt_turning (by linarith) (fun _ => 1) fun _ => m * ω ^ 2 / 2,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hs : √(m * ω ^ 2 / 2) = √(m / 2) * ω := by
    rw [show m * ω ^ 2 / 2 = m / 2 * ω ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hω.le]
  have hm2 : √(m / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [hs]
  field_simp

/-- The motion `x = −a cos ωt` of the oscillator goes from the turning point
`−a` at `t = 0` to the turning point `a` at `t = π/ω`, and this time is the
integral of Landau–Lifshitz (11.5). The hypotheses of
`sub_eq_sqrt_mul_integral_of_energy_turning` hold for it. -/
theorem sub_eq_sqrt_mul_integral_oscillator {m ω a : ℝ} (hm : 0 < m) (hω : 0 < ω)
    (ha : 0 < a) :
    π / ω - 0 =
      √(m / 2) * ∫ u in -a..a, 1 / √(m * ω ^ 2 / 2 * a ^ 2 - m * ω ^ 2 / 2 * u ^ 2) := by
  have hπ : 0 < π / ω := div_pos Real.pi_pos hω
  refine sub_eq_sqrt_mul_integral_of_energy_turning (x := fun t => -(a * Real.cos (ω * t)))
    (x' := fun t => a * (ω * Real.sin (ω * t))) (U := fun u => m * ω ^ 2 / 2 * u ^ 2)
    (W := fun _ => m * ω ^ 2 / 2) hm hπ (by linarith) (fun t _ => ?_) (fun t ht => ?_) ?_ ?_
    (fun t _ => ?_) (fun u _ => ?_) continuousOn_const fun _ _ => by positivity
  · have h := (((hasDerivAt_id t).const_mul ω).cos.const_mul a).neg
    have e : -(a * (-Real.sin (ω * id t) * (ω * 1))) = a * (ω * Real.sin (ω * t)) := by
      simp only [id]
      ring
    rw [e] at h
    exact h
  · have h1 : 0 < ω * t := mul_pos hω ht.1
    have h2 : ω * t < π := by
      have := mul_lt_mul_of_pos_left ht.2 hω
      rwa [mul_div_cancel₀ _ hω.ne'] at this
    exact mul_pos ha (mul_pos hω (Real.sin_pos_of_pos_of_lt_pi h1 h2))
  · simp
  · simp only [mul_div_cancel₀ _ hω.ne', Real.cos_pi]
    ring
  · linear_combination (m * ω ^ 2 / 2 * a ^ 2) * Real.sin_sq_add_cos_sq (ω * t)
  · ring

end ProjectAInos.Mechanics
