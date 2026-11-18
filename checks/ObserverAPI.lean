/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.RotatingFrame
import ProjectAinos.GeneralRelativity.SchwarzschildExterior

/-! Public consumers of the measurements of observers: the proper time of a curve in the
co-ordinates of an open set and the clock of an observer at rest, the rotating co-ordinates of
Minkowski space with the time dilation, the lengths, the synchronization gap and the frequency
shift on the disc, and the gravitational red shift in the exterior Schwarzschild field.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Bundle MeasureTheory Set TopologicalSpace
open scoped Manifold ContDiff Topology
namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

example (g : CoordinateMetric .timeNegative d U) {γ : ℝ → U}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : MinkowskiModel d)) (a b : ℝ) :
    properTime g.toLorentzMetric γ a b =
      ∫ t in a..b, Real.sqrt (-g.form (γ t) (deriv (fun s => (γ s : MinkowskiModel d)) t)
        (deriv (fun s => (γ s : MinkowskiModel d)) t)) :=
  properTime_coordinate g hγ a b

example (g : CoordinateMetric .timeNegative d U) {γ : ℝ → U}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : MinkowskiModel d)) {x₀ : MinkowskiModel d} {a b : ℝ}
    (hrest : ∀ t ∈ uIcc a b, (γ t : MinkowskiModel d) = x₀ + t • Pi.single 0 1) :
    properTime g.toLorentzMetric γ a b =
      ∫ t in a..b, Real.sqrt (-g.form (γ t) (Pi.single 0 1) (Pi.single 0 1)) :=
  properTime_atRest g hγ hrest

end ProjectAinos.GeneralRelativity

open ContinuousLinearMap Set TopologicalSpace MeasureTheory
open scoped ContDiff
namespace ProjectAinos.GeneralRelativity.RotatingFrame

open SmoothGeometry Minkowski

open LorentzMetric (chartField)

open CoordinateMetric (physicalChart)

variable (Ω : ℝ)

example : Continuous axisDistSq :=
  continuous_axisDistSq

example (x v w : MinkowskiModel 3) :
    form Ω x v w = -(1 - Ω ^ 2 * axisDistSq x) * (v 0 * w 0) -
      Ω * x 2 * (v 0 * w 1 + v 1 * w 0) + Ω * x 1 * (v 0 * w 2 + v 2 * w 0) +
      v 1 * w 1 + v 2 * w 2 + v 3 * w 3 :=
  form_apply Ω x v w

example : ContDiff ℝ ∞ (form Ω) :=
  contDiff_form Ω

example (x : MinkowskiModel 3) :
    form Ω x (Pi.single 0 1) (Pi.single 0 1) = -(1 - Ω ^ 2 * axisDistSq x) :=
  form_timeAxis Ω x

example (x : MinkowskiModel 3) (v : Fin 3 → ℝ) :
    form Ω x (Fin.cons 0 v) (Fin.cons 0 v) = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 :=
  form_space Ω x v

example (x : MinkowskiModel 3) : (metric Ω).form x = form Ω x :=
  metric_form Ω x

example (x v : MinkowskiModel 3) :
    HasDerivAt (fun τ : ℝ => toInertial Ω (x + τ • v)) (inertialVelocity Ω x v) 0 :=
  hasDerivAt_toInertial Ω x v

example (x v w : MinkowskiModel 3) :
    form Ω x v w =
      minkowskiForm .timeNegative 3 (inertialVelocity Ω x v) (inertialVelocity Ω x w) :=
  form_eq_pullback Ω x v w

example {x₀ : MinkowskiModel 3} (hx₀ : x₀ ∈ domain Ω) (a b : ℝ) :
    properTime (metric Ω).toLorentzMetric (staticWorldline Ω hx₀) a b =
      (b - a) * Real.sqrt (1 - Ω ^ 2 * axisDistSq x₀) :=
  properTime_static Ω hx₀ a b

example (x : MinkowskiModel 3) :
    spatialForm (form Ω x) (Pi.single 0 1) ![0, x 1, x 2, 0] ![0, x 1, x 2, 0] = axisDistSq x :=
  spatialForm_radial Ω x

example (x : MinkowskiModel 3) (hx : Ω ^ 2 * axisDistSq x < 1) :
    spatialForm (form Ω x) (Pi.single 0 1) ![0, -x 2, x 1, 0] ![0, -x 2, x 1, 0] =
      axisDistSq x / (1 - Ω ^ 2 * axisDistSq x) :=
  spatialForm_tangential Ω x hx

example (ρ φ : ℝ) : axisDistSq (circle ρ φ) = ρ ^ 2 :=
  axisDistSq_circle ρ φ

example {ρ : ℝ} (hρ : Ω ^ 2 * ρ ^ 2 < 1) :
    ∫ φ in (0 : ℝ)..2 * Real.pi,
        -(∑ i, form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single i.succ 1) *
            ![-(ρ * Real.sin φ), ρ * Real.cos φ, 0] i) /
          form Ω (circle ρ φ) (Pi.single 0 1) (Pi.single 0 1) =
      2 * Real.pi * (Ω * ρ ^ 2 / (1 - Ω ^ 2 * ρ ^ 2)) :=
  synchronization_circle Ω hρ

example {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : Ω ^ 2 * ρ ^ 2 < 1) :
    ∫ φ in (0 : ℝ)..2 * Real.pi, Real.sqrt (spatialForm (form Ω (circle ρ φ)) (Pi.single 0 1)
        ![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0] ![0, -(ρ * Real.sin φ), ρ * Real.cos φ, 0]) =
      2 * Real.pi * (ρ / Real.sqrt (1 - Ω ^ 2 * ρ ^ 2)) :=
  circumference_circle Ω hρ0 hρ

example (y : MinkowskiModel 3) (t : ℝ) :
    form Ω (y + t • Pi.single 0 1) = form Ω y :=
  form_add_time Ω y t

example (x₀ : domain Ω) :
    (metric Ω).toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single 0 1)) :=
  isKillingField_time Ω x₀

example (x₀ y : domain Ω) :
    (metric Ω).toLorentzMetric.killingNorm (chartField (physicalChart x₀) (Pi.single 0 1)) y =
      Real.sqrt (1 - Ω ^ 2 * axisDistSq y) :=
  killingNorm_time Ω x₀ y

example (x₀ y : domain Ω) :
    (metric Ω).toLorentzMetric.form y (chartField (physicalChart x₀) (Pi.single 0 1) y)
      (chartField (physicalChart x₀) (Pi.single 0 1) y) < 0 :=
  form_time_neg Ω x₀ y

example (x₀ : domain Ω) {γ : ℝ → domain Ω} {s : Set ℝ}
    (hγ : (metric Ω).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) :
    Real.sqrt (1 - Ω ^ 2 * axisDistSq (γ a)) *
        (metric Ω).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
          γ a =
      Real.sqrt (1 - Ω ^ 2 * axisDistSq (γ b)) *
        (metric Ω).toLorentzMetric.observedFrequency (chartField (physicalChart x₀) (Pi.single 0 1))
          γ b :=
  killingNorm_mul_observedFrequency_eq Ω x₀ hγ hs ha hb

end ProjectAinos.GeneralRelativity.RotatingFrame

open ContinuousLinearMap Set TopologicalSpace
open scoped ContDiff
namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

open LorentzMetric (chartField)

open CoordinateMetric (physicalChart)

variable {M : ℝ}

example (x v w : MinkowskiModel 3) :
    form M x v w = -((x 1 - 2 * M) / x 1) * (v 0 * w 0) + x 1 / (x 1 - 2 * M) * (v 1 * w 1) +
      x 1 ^ 2 * (v 2 * w 2) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3) :=
  form_apply x v w

example (hM : 0 ≤ M) : ContDiffOn ℝ ∞ (form M) (domain M) :=
  contDiffOn_form hM

example (hM : 0 ≤ M) (x : MinkowskiModel 3) : (metric hM).form x = form M x :=
  metric_form hM x

example (k : Fin 4) (hk : k = 0 ∨ k = 3) (y : MinkowskiModel 3) (t : ℝ) :
    form M (y + t • Pi.single k 1) = form M y :=
  form_add k hk y t

example (hM : 0 ≤ M) (x₀ : domain M) :
    (metric hM).toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single 0 1)) :=
  isKillingField_time hM x₀

example (hM : 0 ≤ M) (x₀ : domain M) :
    (metric hM).toLorentzMetric.IsKillingField (chartField (physicalChart x₀) (Pi.single 3 1)) :=
  isKillingField_angle hM x₀

example {y : MinkowskiModel 3} (hy : y 1 ≠ 0) :
    form M y (Pi.single 0 1) (Pi.single 0 1) = -(1 - 2 * M / y 1) :=
  form_time hy

example (hM : 0 ≤ M) (x₀ y : domain M) :
    (metric hM).toLorentzMetric.killingNorm (chartField (physicalChart x₀) (Pi.single 0 1)) y =
      Real.sqrt (1 - 2 * M / (y : MinkowskiModel 3) 1) :=
  killingNorm_time hM x₀ y

example (hM : 0 ≤ M) (x₀ y : domain M) :
    (metric hM).toLorentzMetric.form y (chartField (physicalChart x₀) (Pi.single 0 1) y)
      (chartField (physicalChart x₀) (Pi.single 0 1) y) < 0 :=
  form_time_neg hM x₀ y

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M}
    {s : Set ℝ} (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    Real.sqrt (1 - 2 * M / (γ a : MinkowskiModel 3) 1) *
        (metric hM).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) γ a =
      Real.sqrt (1 - 2 * M / (γ b : MinkowskiModel 3) 1) *
        (metric hM).toLorentzMetric.observedFrequency
          (chartField (physicalChart x₀) (Pi.single 0 1)) γ b :=
  killingNorm_mul_observedFrequency_eq hM x₀ hγ hs ha hb

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
