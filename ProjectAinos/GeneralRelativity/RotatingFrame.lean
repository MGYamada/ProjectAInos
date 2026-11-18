/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.ObserverMeasurement
public import ProjectAinos.SmoothGeometry.Lorentzian.Killing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Rotating co-ordinates in Minkowski space

In the co-ordinates `(t, x, y, z)` that rotate with the angular velocity `Ω` about the `z` axis,
the Minkowski interval is
`ds² = −(1 − Ω²(x² + y²)) dt² + 2Ω (x dy − y dx) dt + dx² + dy² + dz²`
(Landau–Lifshitz, §89, with `c = 1` and the signature `(−+++)`).

* `form_eq_pullback`, `hasDerivAt_toInertial`: the rotating form is the pullback of the
  Minkowski form by the map `toInertial` to the inertial co-ordinates
  `(t, x cos Ωt − y sin Ωt, x sin Ωt + y cos Ωt, z)`: its values are the Minkowski products of
  the inertial velocities of the lines of the rotating co-ordinates.
* `metric`: on the domain `Ω²(x² + y²) < 1`, where the rotating time axis is timelike, it is a
  Lorentz metric. Beyond the light cylinder `Ω²(x² + y²) = 1` no observer is at rest.
* `properTime_static`: a clock at rest at the distance `ρ` from the axis runs at the rate
  `√(1 − Ω²ρ²)`.
* `spatialForm_radial`, `spatialForm_tangential`, `circumference_circle`: the observers at rest
  measure radial displacements with their Euclidean length, and the circle of radius `ρ` about
  the axis with the length `2πρ/√(1 − Ω²ρ²)`.
* `synchronization_circle`: synchronizing each clock on the circle of radius `ρ` with its
  neighbour, going round in the sense of increasing `φ` (the sense of the rotation for `Ω > 0`),
  gives a co-ordinate time `2πΩρ²/(1 − Ω²ρ²)` over one turn; a clock on the circle reads
  `√(1 − Ω²ρ²)` times this gap. This is the synchronization gap of §89, and twice it is the
  Sagnac delay of two signals sent round in opposite senses.
* `isKillingField_time`, `killingNorm_mul_observedFrequency_eq`: `∂_t` is a Killing field, and
  along every geodesic segment inside the light cylinder the frequency `ω` that the observers at
  rest measure satisfies `√(1 − Ω²ρ²) ω = const`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace MeasureTheory
open scoped ContDiff

namespace ProjectAinos.GeneralRelativity.RotatingFrame

open SmoothGeometry Minkowski
open LorentzMetric (chartField)
open CoordinateMetric (physicalChart)

variable (Ω : ℝ)

/-- The squared distance `x² + y²` from the axis of rotation. -/
def axisDistSq (x : MinkowskiModel 3) : ℝ := x 1 ^ 2 + x 2 ^ 2

theorem continuous_axisDistSq : Continuous axisDistSq := by
  unfold axisDistSq
  fun_prop

/-- The domain `Ω²(x² + y²) < 1` inside the light cylinder. -/
def domain : Opens (MinkowskiModel 3) :=
  ⟨{x | Ω ^ 2 * axisDistSq x < 1}, isOpen_lt (continuous_const.mul continuous_axisDistSq)
    continuous_const⟩

/-- The rotating form at the point `x`. -/
def form (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  minkowskiForm .timeNegative 3 +
    (Ω ^ 2 * axisDistSq x) •
      (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (-(Ω * x 2)) •
      ((proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
        (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ)) +
    (Ω * x 1) •
      ((proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ) +
        (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ))

theorem form_apply (x v w : MinkowskiModel 3) :
    form Ω x v w = -(1 - Ω ^ 2 * axisDistSq x) * (v 0 * w 0) -
      Ω * x 2 * (v 0 * w 1 + v 1 * w 0) + Ω * x 1 * (v 0 * w 2 + v 2 * w 0) +
      v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  simp only [form, add_apply, smul_apply, smulRight_apply, proj_apply, smul_eq_mul,
    minkowskiForm_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, lorentzSign,
    LorentzConvention.timeSign]
  simp
  ring

theorem contDiff_form : ContDiff ℝ ∞ (form Ω) := by
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  simp only [form_apply, axisDistSq]
  fun_prop

/-- The rotating time axis is timelike inside the light cylinder. -/
theorem form_timeAxis (x : MinkowskiModel 3) :
    form Ω x (Pi.single 0 1) (Pi.single 0 1) = -(1 - Ω ^ 2 * axisDistSq x) := by
  rw [form_apply]
  simp

theorem form_space (x : MinkowskiModel 3) (v : Fin 3 → ℝ) :
    form Ω x (Fin.cons 0 v) (Fin.cons 0 v) = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [form_apply]
  change _ + v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = _
  simp
  ring

/-- The rotating co-ordinates of the domain inside the light cylinder, as a Lorentz metric. -/
def metric : CoordinateMetric .timeNegative 3 (domain Ω) :=
  CoordinateMetric.ofCriterion (form Ω) (contDiff_form Ω).contDiffOn
    (fun x _ v w => by rw [form_apply, form_apply]; ring)
    (fun x hx => by
      have hx' : Ω ^ 2 * axisDistSq x < 1 := hx
      rw [show (Fin.cons 1 0 : MinkowskiModel 3) = Pi.single 0 1 by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp, form_timeAxis]
      simp only [LorentzConvention.timeSign]
      linarith)
    (fun x _ v hv => by
      rw [form_space]
      simp only [LorentzConvention.timeSign, neg_neg, one_mul]
      by_contra h
      apply hv
      funext i
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)])

theorem metric_form (x : MinkowskiModel 3) : (metric Ω).form x = form Ω x := rfl

/-! ### The rotating co-ordinates in Minkowski space -/

/-- The inertial co-ordinates `(t, x cos Ωt − y sin Ωt, x sin Ωt + y cos Ωt, z)` of a point
given in the rotating co-ordinates. -/
def toInertial (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![x 0, x 1 * Real.cos (Ω * x 0) - x 2 * Real.sin (Ω * x 0),
    x 1 * Real.sin (Ω * x 0) + x 2 * Real.cos (Ω * x 0), x 3]

/-- The inertial velocity of the line through `x` with the rotating velocity `v`. -/
def inertialVelocity (x v : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![v 0, Real.cos (Ω * x 0) * v 1 - Real.sin (Ω * x 0) * v 2 -
      Ω * (x 1 * Real.sin (Ω * x 0) + x 2 * Real.cos (Ω * x 0)) * v 0,
    Real.sin (Ω * x 0) * v 1 + Real.cos (Ω * x 0) * v 2 +
      Ω * (x 1 * Real.cos (Ω * x 0) - x 2 * Real.sin (Ω * x 0)) * v 0, v 3]

/-- `inertialVelocity x v` is the velocity of the image of the line `τ ↦ x + τ v`. -/
theorem hasDerivAt_toInertial (x v : MinkowskiModel 3) :
    HasDerivAt (fun τ : ℝ => toInertial Ω (x + τ • v)) (inertialVelocity Ω x v) 0 := by
  have hl (i : Fin 4) : HasDerivAt (fun τ : ℝ => (x + τ • v) i) (v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (x i)
  have ha : HasDerivAt (fun τ : ℝ => Ω * (x + τ • v) 0) (Ω * v 0) 0 := (hl 0).const_mul Ω
  have h0 : (x + (0 : ℝ) • v) = x := by simp
  have c0 : HasDerivAt (fun τ : ℝ => toInertial Ω (x + τ • v) 0) (inertialVelocity Ω x v 0) 0 :=
    hl 0
  have c1 : HasDerivAt (fun τ : ℝ => toInertial Ω (x + τ • v) 1) (inertialVelocity Ω x v 1) 0 := by
    have h := ((hl 1).mul ha.cos).sub ((hl 2).mul ha.sin)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => rfl)
    simp only [h0, inertialVelocity, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  have c2 : HasDerivAt (fun τ : ℝ => toInertial Ω (x + τ • v) 2) (inertialVelocity Ω x v 2) 0 := by
    have h := ((hl 1).mul ha.sin).add ((hl 2).mul ha.cos)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => rfl)
    simp only [h0, inertialVelocity]
    simp
    ring
  have c3 : HasDerivAt (fun τ : ℝ => toInertial Ω (x + τ • v) 3) (inertialVelocity Ω x v 3) 0 :=
    hl 3
  refine hasDerivAt_pi.mpr fun i => ?_
  fin_cases i
  exacts [c0, c1, c2, c3]

/-- **The rotating form is the Minkowski form in rotating co-ordinates.** -/
theorem form_eq_pullback (x v w : MinkowskiModel 3) :
    form Ω x v w =
      minkowskiForm .timeNegative 3 (inertialVelocity Ω x v) (inertialVelocity Ω x w) := by
  rw [form_apply, minkowskiForm_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, lorentzSign, LorentzConvention.timeSign,
    inertialVelocity, axisDistSq]
  simp
  linear_combination (-(v 1 * w 1 + v 2 * w 2 + Ω ^ 2 * (x 1 ^ 2 + x 2 ^ 2) * (v 0 * w 0) -
    Ω * x 2 * (v 0 * w 1 + v 1 * w 0) + Ω * x 1 * (v 0 * w 2 + v 2 * w 0))) *
      Real.sin_sq_add_cos_sq (Ω * x 0)

/-! ### Clocks and distances of the observers at rest -/

/-- A clock at rest at the point `x₀` of the domain. -/
def staticWorldline {x₀ : MinkowskiModel 3} (hx₀ : x₀ ∈ domain Ω) (t : ℝ) : domain Ω :=
  ⟨x₀ + t • Pi.single 0 1, by
    have h : axisDistSq (x₀ + t • Pi.single 0 1) = axisDistSq x₀ := by
      simp [axisDistSq]
    change Ω ^ 2 * axisDistSq (x₀ + t • Pi.single 0 1) < 1
    rw [h]
    exact hx₀⟩

/-- **Time dilation on a rotating disc.** A clock at rest at the distance `ρ` from the axis
runs at the rate `√(1 − Ω²ρ²)`. -/
theorem properTime_static {x₀ : MinkowskiModel 3} (hx₀ : x₀ ∈ domain Ω) (a b : ℝ) :
    properTime (metric Ω).toLorentzMetric (staticWorldline Ω hx₀) a b =
      (b - a) * Real.sqrt (1 - Ω ^ 2 * axisDistSq x₀) := by
  have hc : ContDiff ℝ ∞ fun t => ((staticWorldline Ω hx₀ t : domain Ω) : MinkowskiModel 3) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  rw [properTime_atRest (metric Ω) hc (x₀ := x₀) (fun t _ => rfl)]
  have h (t : ℝ) : (metric Ω).form (staticWorldline Ω hx₀ t) (Pi.single 0 1) (Pi.single 0 1) =
      -(1 - Ω ^ 2 * axisDistSq x₀) := by
    rw [metric_form, form_timeAxis]
    simp [staticWorldline, axisDistSq]
  simp only [h, neg_neg, intervalIntegral.integral_const, smul_eq_mul]

/-- The spatial form of the observers at rest gives a radial displacement `(0, x, y, 0)` at `x`
its Euclidean length. Observers at rest exist inside the light cylinder. -/
theorem spatialForm_radial (x : MinkowskiModel 3) :
    spatialForm (form Ω x) (Pi.single 0 1) ![0, x 1, x 2, 0] ![0, x 1, x 2, 0] = axisDistSq x := by
  have h0v : form Ω x (Pi.single 0 1) ![0, x 1, x 2, 0] = 0 := by
    rw [form_apply]
    simp
    ring
  have hvv : form Ω x ![0, x 1, x 2, 0] ![0, x 1, x 2, 0] = axisDistSq x := by
    rw [form_apply]
    simp [axisDistSq]
    ring
  rw [spatialForm_apply, h0v, hvv]
  simp

/-- The spatial form of the observers at rest gives the tangent `(0, −y, x, 0)` of the circle
about the axis through `x`, the velocity per unit angle, the squared length
`ρ²/(1 − Ω²ρ²)`. -/
theorem spatialForm_tangential (x : MinkowskiModel 3) (hx : Ω ^ 2 * axisDistSq x < 1) :
    spatialForm (form Ω x) (Pi.single 0 1) ![0, -x 2, x 1, 0] ![0, -x 2, x 1, 0] =
      axisDistSq x / (1 - Ω ^ 2 * axisDistSq x) := by
  have h1 : 1 - Ω ^ 2 * axisDistSq x ≠ 0 := by linarith
  have h1' : 1 - axisDistSq x * Ω ^ 2 ≠ 0 := by rw [mul_comm]; exact h1
  have h0v : form Ω x (Pi.single 0 1) ![0, -x 2, x 1, 0] = Ω * axisDistSq x := by
    rw [form_apply]
    simp [axisDistSq]
    ring
  have hvv : form Ω x ![0, -x 2, x 1, 0] ![0, -x 2, x 1, 0] = axisDistSq x := by
    rw [form_apply]
    simp [axisDistSq]
    ring
  rw [spatialForm_apply, h0v, hvv, form_timeAxis]
  field_simp
  ring

/-- The point at the angle `φ` of the circle of radius `ρ` in the plane `z = 0` at `t = 0`. -/
def circle (ρ φ : ℝ) : MinkowskiModel 3 := ![0, ρ * Real.cos φ, ρ * Real.sin φ, 0]

theorem axisDistSq_circle (ρ φ : ℝ) : axisDistSq (circle ρ φ) = ρ ^ 2 := by
  simp only [axisDistSq, circle]
  simp
  linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq φ

/-- **The synchronization gap** (the Sagnac effect). Along the circle of radius `ρ` inside the
light cylinder, traversed in the sense of increasing `φ` (the sense of the rotation for `Ω > 0`),
the co-ordinate time
`dt = −g_{0i} dx^i / g_{00}` by which each clock is synchronized with its neighbour adds up to
`2πΩρ²/(1 − Ω²ρ²)` over one turn. -/
theorem synchronization_circle {ρ : ℝ} (hρ : Ω ^ 2 * ρ ^ 2 < 1) :
    ∫ φ in (0 : ℝ)..2 * Real.pi,
        -(∑ i, form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single i.succ 1) *
            ![-(ρ * Real.sin φ), ρ * Real.cos φ, 0] i) /
          form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single 0 1) =
      2 * Real.pi * (Ω * ρ ^ 2 / (1 - Ω ^ 2 * ρ ^ 2)) := by
  have h1 : 1 - Ω ^ 2 * ρ ^ 2 ≠ 0 := by linarith
  have h (φ : ℝ) :
      -(∑ i, form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single i.succ 1) *
          ![-(ρ * Real.sin φ), ρ * Real.cos φ, 0] i) /
        form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single 0 1) = Ω * ρ ^ 2 / (1 - Ω ^ 2 * ρ ^ 2) := by
    have hsum : ∑ i, form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single i.succ 1) *
        ![-(ρ * Real.sin φ), ρ * Real.cos φ, 0] i = Ω * ρ ^ 2 := by
      rw [Fin.sum_univ_three]
      simp only [form_apply]
      simp [circle]
      linear_combination Ω * ρ ^ 2 * Real.sin_sq_add_cos_sq φ
    rw [hsum, form_timeAxis, axisDistSq_circle, neg_div_neg_eq]
  simp only [h, intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- **The circumference of a rotating circle.** The observers at rest give the circle of radius
`ρ` about the axis the length `2πρ/√(1 − Ω²ρ²)`: the integral of the line element `√(γ(ċ, ċ)) dφ`
of the spatial metric along it. The metric does not depend on `t`, so this length does not depend
on the slice. -/
theorem circumference_circle {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : Ω ^ 2 * ρ ^ 2 < 1) :
    ∫ φ in (0 : ℝ)..2 * Real.pi, Real.sqrt (spatialForm (form Ω (circle ρ φ)) (Pi.single 0 1)
        ![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0] ![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0]) =
      2 * Real.pi * (ρ / Real.sqrt (1 - Ω ^ 2 * ρ ^ 2)) := by
  have h (φ : ℝ) : Real.sqrt (spatialForm (form Ω (circle ρ φ)) (Pi.single 0 1)
      ![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0] ![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0]) =
      ρ / Real.sqrt (1 - Ω ^ 2 * ρ ^ 2) := by
    have hv : (![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0] : MinkowskiModel 3) =
        ![0, -(circle ρ φ 2), circle ρ φ 1, 0] := by
      simp [circle]
    rw [hv, spatialForm_tangential Ω (circle ρ φ) (by rw [axisDistSq_circle]; exact hρ),
      axisDistSq_circle, Real.sqrt_div' _ (by linarith), Real.sqrt_sq hρ0]
  simp only [h, intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-! ### The Killing field `∂_t` and the frequency shift on the disc -/

/-- The rotating form does not depend on `t`. -/
theorem form_add_time (y : MinkowskiModel 3) (t : ℝ) :
    form Ω (y + t • Pi.single 0 1) = form Ω y := by
  have h1 : (y + t • Pi.single 0 1 : MinkowskiModel 3) 1 = y 1 := by simp
  have h2 : (y + t • Pi.single 0 1 : MinkowskiModel 3) 2 = y 2 := by simp
  simp only [form, axisDistSq, h1, h2]

/-- `∂_t` is a Killing field of the rotating metric. -/
theorem isKillingField_time (x₀ : domain Ω) :
    (metric Ω).toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single 0 1)) :=
  CoordinateMetric.isKillingField_of_invariant (metric Ω) x₀ 0 (form_add_time Ω)

/-- The norm of `∂_t` at `y` is `√(1 − Ω²ρ²)`. -/
theorem killingNorm_time (x₀ y : domain Ω) :
    (metric Ω).toLorentzMetric.killingNorm (chartField (physicalChart x₀) (Pi.single 0 1)) y =
      Real.sqrt (1 - Ω ^ 2 * axisDistSq y) := by
  rw [LorentzMetric.killingNorm, CoordinateMetric.toLorentzMetric_form,
    CoordinateMetric.physicalChart_chartField, metric_form, form_timeAxis, neg_neg]

theorem form_time_neg (x₀ y : domain Ω) :
    (metric Ω).toLorentzMetric.form y (chartField (physicalChart x₀) (Pi.single 0 1) y)
      (chartField (physicalChart x₀) (Pi.single 0 1) y) < 0 := by
  rw [CoordinateMetric.toLorentzMetric_form, CoordinateMetric.physicalChart_chartField,
    metric_form, form_timeAxis]
  have hy : Ω ^ 2 * axisDistSq y < 1 := y.property
  linarith

/-- **The frequency shift on a rotating disc.** Along every geodesic of the domain, given on a
convex set of parameters, the frequency `ω` that the observers at rest measure satisfies
`√(1 − Ω²ρ²) ω = const`. A ray sent from the axis to the rim at the radius `R` arrives with its
frequency multiplied by `1/√(1 − Ω²R²)`. -/
theorem killingNorm_mul_observedFrequency_eq (x₀ : domain Ω) {γ : ℝ → domain Ω} {s : Set ℝ}
    (hγ : (metric Ω).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) :
    Real.sqrt (1 - Ω ^ 2 * axisDistSq (γ a)) *
        (metric Ω).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
          γ a =
      Real.sqrt (1 - Ω ^ 2 * axisDistSq (γ b)) *
        (metric Ω).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
          γ b := by
  rw [← killingNorm_time Ω x₀ (γ a), ← killingNorm_time Ω x₀ (γ b)]
  exact LorentzMetric.killingNorm_mul_observedFrequency_eq (isKillingField_time Ω x₀)
    (fun y => CoordinateMetric.chartField_mdifferentiableAt x₀ y _) hγ hs ha hb
    (form_time_neg Ω x₀ (γ a)) (form_time_neg Ω x₀ (γ b))

end ProjectAinos.GeneralRelativity.RotatingFrame
