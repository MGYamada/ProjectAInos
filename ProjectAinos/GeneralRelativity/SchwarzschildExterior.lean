/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Killing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp

/-!
# The gravitational red shift in the exterior Schwarzschild field

In the co-ordinates `(t, r, θ, φ)` on the domain `r > 2M`, `0 < θ < π`, the exterior field of a
mass `M ≥ 0` has the metric
`ds² = −(1 − 2M/r) dt² + dr²/(1 − 2M/r) + r² dθ² + r² sin²θ dφ²`, a Lorentz metric there
(`metric`). The angle `φ` is read on the real line, so the domain is the universal cover of the
exterior with the axis removed.

* `isKillingField_time`, `isKillingField_angle`: `∂_t` and `∂_φ` are Killing fields, since the
  metric depends on neither `t` nor `φ`.
* `killingNorm_time`: the norm of `∂_t` is `√(1 − 2M/r)`.
* `killingNorm_mul_observedFrequency_eq`: **the gravitational red shift** (Landau–Lifshitz, §88).
  Along every geodesic of the domain, given on a convex set of parameters, the frequency `ω` that
  the static observers measure satisfies `√(1 − 2M/r) ω = const`. A ray sent radially from
  `r₁` to `r₂` is one of these geodesics.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace
open scoped ContDiff

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski
open LorentzMetric (chartField)
open CoordinateMetric (physicalChart)

variable {M : ℝ}

/-- The exterior domain `r > 2M`, `0 < θ < π`. -/
def domain (M : ℝ) : Opens (MinkowskiModel 3) :=
  ⟨{x | 2 * M < x 1 ∧ 0 < x 2 ∧ x 2 < Real.pi},
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))⟩

/-- The Schwarzschild form `diag(−(1 − 2M/r), 1/(1 − 2M/r), r², r² sin²θ)` at the point `x`. -/
def form (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  (-((x 1 - 2 * M) / x 1)) •
      (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (x 1 / (x 1 - 2 * M)) •
      (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (x 1 ^ 2) •
      (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (x 1 ^ 2 * Real.sin (x 2) ^ 2) •
      (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ)

theorem form_apply (x v w : MinkowskiModel 3) :
    form M x v w = -((x 1 - 2 * M) / x 1) * (v 0 * w 0) + x 1 / (x 1 - 2 * M) * (v 1 * w 1) +
      x 1 ^ 2 * (v 2 * w 2) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3) := by
  simp only [form, add_apply, smul_apply, smulRight_apply, proj_apply, smul_eq_mul]

theorem contDiffOn_form (hM : 0 ≤ M) : ContDiffOn ℝ ∞ (form M) (domain M) := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
  have h1 : ∀ x ∈ (domain M : Set (MinkowskiModel 3)), x 1 ≠ 0 := fun x hx => by
    have : 2 * M < x 1 := hx.1
    linarith
  have h2 : ∀ x ∈ (domain M : Set (MinkowskiModel 3)), x 1 - 2 * M ≠ 0 := fun x hx => by
    have : 2 * M < x 1 := hx.1
    linarith
  have hr : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 1 := contDiff_apply ℝ (fun _ => ℝ) 1
  have hθ : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 2 := contDiff_apply ℝ (fun _ => ℝ) 2
  have hA : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => (x 1 - 2 * M) / x 1) (domain M) :=
    (hr.sub contDiff_const).contDiffOn.div hr.contDiffOn h1
  have hB : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => x 1 / (x 1 - 2 * M)) (domain M) :=
    hr.contDiffOn.div (hr.sub contDiff_const).contDiffOn h2
  simp only [form_apply]
  have hv (i : Fin 4) : ContDiff ℝ ∞ fun _ : MinkowskiModel 3 => v i * w i := contDiff_const
  exact (((hA.neg.mul (hv 0).contDiffOn).add (hB.mul (hv 1).contDiffOn)).add
    ((hr.pow 2).contDiffOn.mul (hv 2).contDiffOn)).add
    (((hr.pow 2).mul (hθ.sin.pow 2)).contDiffOn.mul (hv 3).contDiffOn)

/-- The exterior Schwarzschild metric on the domain `r > 2M`, `0 < θ < π`. -/
def metric (hM : 0 ≤ M) : CoordinateMetric .timeNegative 3 (domain M) :=
  CoordinateMetric.ofCriterion (form M) (contDiffOn_form hM)
    (fun x _ v w => by rw [form_apply, form_apply]; ring)
    (fun x hx => by
      have hr : 2 * M < x 1 := hx.1
      have h0 : 0 < x 1 := by linarith
      rw [form_apply]
      simp only [LorentzConvention.timeSign, Fin.cons_zero, Fin.cons_one]
      have h : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 2 = 0 := rfl
      have h' : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 3 = 0 := rfl
      rw [h, h']
      simp only [Pi.zero_apply, mul_zero, add_zero, mul_one, neg_neg, one_mul]
      exact neg_neg_of_pos (div_pos (by linarith) h0))
    (fun x hx v hv => by
      have hr : 2 * M < x 1 := hx.1
      have h0 : 0 < x 1 := by linarith
      have hs : 0 < Real.sin (x 2) := Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
      rw [form_apply]
      have e1 : (Fin.cons 0 v : MinkowskiModel 3) 1 = v 0 := rfl
      have e2 : (Fin.cons 0 v : MinkowskiModel 3) 2 = v 1 := rfl
      have e3 : (Fin.cons 0 v : MinkowskiModel 3) 3 = v 2 := rfl
      simp only [LorentzConvention.timeSign, Fin.cons_zero, e1, e2, e3, mul_zero, zero_add,
        neg_neg, one_mul]
      have hB : 0 < x 1 / (x 1 - 2 * M) := div_pos h0 (by linarith)
      by_contra hle
      apply hv
      have hq : 0 ≤ x 1 / (x 1 - 2 * M) * (v 0 * v 0) := mul_nonneg hB.le (mul_self_nonneg _)
      have hq2 : 0 ≤ x 1 ^ 2 * (v 1 * v 1) := mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
      have hq3 : 0 ≤ x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 2 * v 2) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_self_nonneg _)
      have z0 : v 0 * v 0 = 0 := by
        have := (mul_eq_zero.mp (le_antisymm (by linarith) hq)).resolve_left hB.ne'
        exact this
      have z1 : v 1 * v 1 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by linarith) hq2)).resolve_left (pow_pos h0 2).ne'
      have z2 : v 2 * v 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by linarith) hq3)).resolve_left
          (mul_pos (pow_pos h0 2) (pow_pos hs 2)).ne'
      funext i
      fin_cases i
      · exact mul_self_eq_zero.mp z0
      · exact mul_self_eq_zero.mp z1
      · exact mul_self_eq_zero.mp z2)

theorem metric_form (hM : 0 ≤ M) (x : MinkowskiModel 3) : (metric hM).form x = form M x := rfl

/-- The metric depends on neither `t` nor `φ`. -/
theorem form_add (k : Fin 4) (hk : k = 0 ∨ k = 3) (y : MinkowskiModel 3) (t : ℝ) :
    form M (y + t • Pi.single k 1) = form M y := by
  have h1 : (y + t • Pi.single k 1 : MinkowskiModel 3) 1 = y 1 := by
    rcases hk with rfl | rfl <;> simp
  have h2 : (y + t • Pi.single k 1 : MinkowskiModel 3) 2 = y 2 := by
    rcases hk with rfl | rfl <;> simp
  simp only [form, h1, h2]

/-- `∂_t` is a Killing field. -/
theorem isKillingField_time (hM : 0 ≤ M) (x₀ : domain M) :
    (metric hM).toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single 0 1)) :=
  CoordinateMetric.isKillingField_of_invariant (metric hM) x₀ 0 (form_add 0 (Or.inl rfl))

/-- `∂_φ` is a Killing field. -/
theorem isKillingField_angle (hM : 0 ≤ M) (x₀ : domain M) :
    (metric hM).toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single 3 1)) :=
  CoordinateMetric.isKillingField_of_invariant (metric hM) x₀ 3 (form_add 3 (Or.inr rfl))

theorem form_time {y : MinkowskiModel 3} (hy : y 1 ≠ 0) :
    form M y (Pi.single 0 1) (Pi.single 0 1) = -(1 - 2 * M / y 1) := by
  rw [form_apply]
  simp
  field_simp
  ring

/-- The norm of `∂_t` at `y` is `√(1 − 2M/r)`. -/
theorem killingNorm_time (hM : 0 ≤ M) (x₀ y : domain M) :
    (metric hM).toLorentzMetric.killingNorm (chartField (physicalChart x₀) (Pi.single 0 1)) y =
      Real.sqrt (1 - 2 * M / (y : MinkowskiModel 3) 1) := by
  have h0 : 0 < (y : MinkowskiModel 3) 1 := by
    have := y.property.1
    linarith
  rw [LorentzMetric.killingNorm, CoordinateMetric.toLorentzMetric_form,
    CoordinateMetric.physicalChart_chartField, metric_form, form_time h0.ne', neg_neg]

theorem form_time_neg (hM : 0 ≤ M) (x₀ y : domain M) :
    (metric hM).toLorentzMetric.form y (chartField (physicalChart x₀) (Pi.single 0 1) y)
      (chartField (physicalChart x₀) (Pi.single 0 1) y) < 0 := by
  have hr : 2 * M < (y : MinkowskiModel 3) 1 := y.property.1
  have h0 : 0 < (y : MinkowskiModel 3) 1 := by linarith
  rw [CoordinateMetric.toLorentzMetric_form, CoordinateMetric.physicalChart_chartField,
    metric_form, form_time h0.ne']
  have : 2 * M / (y : MinkowskiModel 3) 1 < 1 := (div_lt_one h0).mpr hr
  linarith

/-- **The gravitational red shift** (Landau–Lifshitz, §88). Along every geodesic of the domain,
given on a convex set of parameters, the frequency `ω` that the static observers measure satisfies
`√(1 − 2M/r) ω = const`: a ray sent from the radius `r₁` is received at `r₂` with the frequency
multiplied by `√(1 − 2M/r₁)/√(1 − 2M/r₂)`. -/
theorem killingNorm_mul_observedFrequency_eq (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    Real.sqrt (1 - 2 * M / (γ a : MinkowskiModel 3) 1) *
        (metric hM).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) γ a =
      Real.sqrt (1 - 2 * M / (γ b : MinkowskiModel 3) 1) *
        (metric hM).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) γ b := by
  rw [← killingNorm_time hM x₀ (γ a), ← killingNorm_time hM x₀ (γ b)]
  exact LorentzMetric.killingNorm_mul_observedFrequency_eq (isKillingField_time hM x₀)
    (fun y => CoordinateMetric.chartField_mdifferentiableAt x₀ y _) hγ hs ha hb
    (form_time_neg hM x₀ (γ a)) (form_time_neg hM x₀ (γ b))

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
