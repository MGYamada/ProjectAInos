/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Propagator
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module

/-!
# The motion with a linear equation for the velocity

For a bounded operator `A` of a Banach space, `linearVelocity A u₀` is the solution of
`u′ = A u` with `u(0) = u₀`, and `linearMotion A x₀ u₀` is the curve with this velocity that
starts at `x₀`. Both are smooth and are defined for all values of the parameter.

* `eq_linearVelocity_of_hasDerivAt`: the solution is unique.
* `linearVelocity_eq_of_cube`, `linearMotion_eq_of_cube`: if `A³ = κ A`, and `s`, `c`, `C` are
  functions with `s′ = 1 + κ c`, `c′ = s`, `C′ = c` that vanish at `0`, then
  `u = u₀ + s A u₀ + c A² u₀` and `x = x₀ + τ u₀ + c A u₀ + C A² u₀`.
* `linearVelocity_add`: for two operators with `A₁ A₂ = A₂ A₁ = 0`, the solution of the sum
  is the sum of the solutions minus the initial value.
* `linearVelocity_eq_of_projection`: for a projection `P` that commutes with `A`, with
  `A² = κ₁` on its range and `A² = κ₂` on its kernel, the solution is the sum of the two
  solutions of the kind `A³ = κ A`.
* `linearVelocity_eq_of_quartic`: if `(A² − a²)(A² + b²) = 0` with `a² + b² ≠ 0`, then
  `hyperbolicProjection A a b = (A² + b²)/(a² + b²)` is such a projection, with `κ₁ = a²` and
  `κ₂ = −b²`.

The functions are `sinh`, `cosh` for `κ > 0`, `sin`, `cos` for `κ < 0` and powers for `κ = 0`.
A constant electromagnetic field gives an equation of this kind for the four-velocity of a
charge in the proper time.
-/

@[expose] public section
noncomputable section

open Set
open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The solution of `u′ = A u` with `u(0) = u₀`. -/
def linearVelocity (A : E →L[ℝ] E) (u₀ : E) (τ : ℝ) : E :=
  propagator (ContinuousMap.const ℝ A) τ 0 u₀

@[simp] theorem linearVelocity_zero (A : E →L[ℝ] E) (u₀ : E) : linearVelocity A u₀ 0 = u₀ := by
  rw [linearVelocity, propagator_self]
  rfl

theorem hasDerivAt_linearVelocity (A : E →L[ℝ] E) (u₀ : E) (τ : ℝ) :
    HasDerivAt (linearVelocity A u₀) (A (linearVelocity A u₀ τ)) τ :=
  hasDerivAt_propagator_apply (ContinuousMap.const ℝ A) τ 0 u₀

theorem contDiff_linearVelocity (A : E →L[ℝ] E) (u₀ : E) :
    ContDiff ℝ ∞ (linearVelocity A u₀) := by
  have hA : ContDiff ℝ ∞ (ContinuousMap.const ℝ A : C(ℝ, E →L[ℝ] E)) :=
    contDiff_const (c := A)
  have h := propagator_contDiff_of_contDiff hA
  exact (h.comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

/-- A solution of `u′ = A u` is determined by its value at `0`. -/
theorem eq_linearVelocity_of_hasDerivAt (A : E →L[ℝ] E) {f : ℝ → E}
    (hf : ∀ r, HasDerivAt f (A (f r)) r) (τ : ℝ) : f τ = linearVelocity A (f 0) τ :=
  eq_propagator_apply_of_hasDerivAt (ContinuousMap.const ℝ A) (s := 0) (t := τ)
    (fun r _ => (hf r).continuousAt.continuousWithinAt) (fun r _ => hf r)

/-- The curve with the velocity `linearVelocity A u₀` that starts at `x₀`. -/
def linearMotion (A : E →L[ℝ] E) (x₀ u₀ : E) (τ : ℝ) : E :=
  x₀ + ∫ s in (0 : ℝ)..τ, linearVelocity A u₀ s

@[simp] theorem linearMotion_zero (A : E →L[ℝ] E) (x₀ u₀ : E) : linearMotion A x₀ u₀ 0 = x₀ := by
  rw [linearMotion, intervalIntegral.integral_same, add_zero]

theorem hasDerivAt_linearMotion (A : E →L[ℝ] E) (x₀ u₀ : E) (τ : ℝ) :
    HasDerivAt (linearMotion A x₀ u₀) (linearVelocity A u₀ τ) τ := by
  have hc : Continuous (linearVelocity A u₀) := (contDiff_linearVelocity A u₀).continuous
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add x₀

theorem deriv_linearMotion (A : E →L[ℝ] E) (x₀ u₀ : E) :
    deriv (linearMotion A x₀ u₀) = linearVelocity A u₀ :=
  funext fun τ => (hasDerivAt_linearMotion A x₀ u₀ τ).deriv

theorem contDiff_linearMotion (A : E →L[ℝ] E) (x₀ u₀ : E) :
    ContDiff ℝ ∞ (linearMotion A x₀ u₀) := by
  refine contDiff_infty_iff_deriv.mpr
    ⟨fun τ => (hasDerivAt_linearMotion A x₀ u₀ τ).differentiableAt, ?_⟩
  rw [deriv_linearMotion]
  exact contDiff_linearVelocity A u₀

/-! ### An operator with `A³ = κ A` -/

section Cube

variable {A : E →L[ℝ] E} {κ : ℝ} {s c C : ℝ → ℝ}

/-- If `A³ = κ A`, `s′ = 1 + κ c`, `c′ = s` and `s(0) = c(0) = 0`, the solution of `u′ = A u`
is `u₀ + s A u₀ + c A² u₀`. -/
theorem linearVelocity_eq_of_cube (hA : ∀ v, A (A (A v)) = κ • A v)
    (hs : ∀ τ, HasDerivAt s (1 + κ * c τ) τ) (hc : ∀ τ, HasDerivAt c (s τ) τ)
    (hs0 : s 0 = 0) (hc0 : c 0 = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity A u₀ τ = u₀ + s τ • A u₀ + c τ • A (A u₀) := by
  have hf : ∀ r, HasDerivAt (fun r => u₀ + (s r • A u₀ + c r • A (A u₀)))
      (A (u₀ + (s r • A u₀ + c r • A (A u₀)))) r := by
    intro r
    have h := (((hs r).smul_const (A u₀)).add ((hc r).smul_const (A (A u₀)))).const_add u₀
    have hval : A (u₀ + (s r • A u₀ + c r • A (A u₀))) =
        (1 + κ * c r) • A u₀ + s r • A (A u₀) := by
      rw [map_add, map_add, map_smul, map_smul, hA]
      module
    rw [hval]
    exact h
  have h := eq_linearVelocity_of_hasDerivAt A hf τ
  simp only [hs0, hc0, zero_smul, add_zero] at h
  rw [add_assoc]
  exact h.symm

/-- With `C′ = c` and `C(0) = 0` in addition, the motion is
`x₀ + τ u₀ + c A u₀ + C A² u₀`. -/
theorem linearMotion_eq_of_cube (hA : ∀ v, A (A (A v)) = κ • A v)
    (hs : ∀ τ, HasDerivAt s (1 + κ * c τ) τ) (hc : ∀ τ, HasDerivAt c (s τ) τ)
    (hs0 : s 0 = 0) (hc0 : c 0 = 0) (hC : ∀ τ, HasDerivAt C (c τ) τ) (hC0 : C 0 = 0)
    (x₀ u₀ : E) (τ : ℝ) :
    linearMotion A x₀ u₀ τ = x₀ + τ • u₀ + c τ • A u₀ + C τ • A (A u₀) := by
  have hd : ∀ r ∈ uIcc 0 τ, HasDerivAt (fun r => r • u₀ + c r • A u₀ + C r • A (A u₀))
      (linearVelocity A u₀ r) r := by
    intro r _
    rw [linearVelocity_eq_of_cube hA hs hc hs0 hc0]
    have h : HasDerivAt (fun r => r • u₀ + c r • A u₀ + C r • A (A u₀))
        ((1 : ℝ) • u₀ + s r • A u₀ + c r • A (A u₀)) r :=
      (((hasDerivAt_id r).smul_const u₀).add ((hc r).smul_const (A u₀))).add
        ((hC r).smul_const (A (A u₀)))
    rwa [one_smul] at h
  rw [linearMotion, intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((contDiff_linearVelocity A u₀).continuous.intervalIntegrable _ _)]
  simp only [hc0, hC0, zero_smul, add_zero, sub_zero]
  abel

end Cube

/-! ### Two operators with zero products -/

/-- For two operators with `A₁ A₂ = A₂ A₁ = 0`, the solution of `u′ = (A₁ + A₂) u` is the sum
of the two solutions minus the initial value. -/
theorem linearVelocity_add {A₁ A₂ : E →L[ℝ] E} (h12 : ∀ v, A₁ (A₂ v) = 0)
    (h21 : ∀ v, A₂ (A₁ v) = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity (A₁ + A₂) u₀ τ =
      linearVelocity A₁ u₀ τ + linearVelocity A₂ u₀ τ - u₀ := by
  -- `A₁` annihilates the change of the second solution, and conversely
  have hconst (A B : E →L[ℝ] E) (hAB : ∀ v, A (B v) = 0) (r : ℝ) :
      A (linearVelocity B u₀ r) = A u₀ := by
    have hd : ∀ t, HasDerivAt (fun t => A (linearVelocity B u₀ t)) 0 t := fun t => by
      have h := A.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_linearVelocity B u₀ t)
      rwa [hAB] at h
    have h := is_const_of_deriv_eq_zero (f := fun t => A (linearVelocity B u₀ t))
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) r 0
    simpa using h
  have hf : ∀ r, HasDerivAt (fun r => linearVelocity A₁ u₀ r + linearVelocity A₂ u₀ r - u₀)
      ((A₁ + A₂) (linearVelocity A₁ u₀ r + linearVelocity A₂ u₀ r - u₀)) r := by
    intro r
    have h := ((hasDerivAt_linearVelocity A₁ u₀ r).add
      (hasDerivAt_linearVelocity A₂ u₀ r)).sub_const u₀
    have hval : (A₁ + A₂) (linearVelocity A₁ u₀ r + linearVelocity A₂ u₀ r - u₀) =
        A₁ (linearVelocity A₁ u₀ r) + A₂ (linearVelocity A₂ u₀ r) := by
      simp only [add_apply, map_sub, map_add, hconst A₁ A₂ h12 r,
        hconst A₂ A₁ h21 r]
      abel
    rw [hval]
    exact h
  have h := eq_linearVelocity_of_hasDerivAt (A₁ + A₂) hf τ
  simp only [linearVelocity_zero, add_sub_cancel_right] at h
  exact h.symm

/-! ### A projection that commutes with the operator -/

section Projection

variable {A P : E →L[ℝ] E} {κ κ₁ κ₂ : ℝ}

omit [CompleteSpace E] in
/-- If a projection `P` commutes with `A` and `A² = κ` on its range, the cube of `A P` is
`κ A P`. -/
theorem comp_projection_cube (hc : ∀ w, P (A w) = A (P w)) (hi : ∀ w, P (P w) = P w)
    (hκ : ∀ w, A (A (P w)) = κ • P w) (w : E) :
    (A ∘L P) ((A ∘L P) ((A ∘L P) w)) = κ • (A ∘L P) w := by
  simp only [ContinuousLinearMap.comp_apply, hc, hi]
  rw [hκ, map_smul]

/-- If a projection `P` commutes with `A`, `A² = κ₁` on its range and `A² = κ₂` on its kernel,
the solution of `u′ = A u` is the sum of the two solutions of the kind `A³ = κ A`. -/
theorem linearVelocity_eq_of_projection (hc : ∀ w, P (A w) = A (P w))
    (hi : ∀ w, P (P w) = P w) (h₁ : ∀ w, A (A (P w)) = κ₁ • P w)
    (h₂ : ∀ w, A (A (w - P w)) = κ₂ • (w - P w)) {s₁ c₁ s₂ c₂ : ℝ → ℝ}
    (hs₁ : ∀ τ, HasDerivAt s₁ (1 + κ₁ * c₁ τ) τ) (hc₁ : ∀ τ, HasDerivAt c₁ (s₁ τ) τ)
    (hs₁0 : s₁ 0 = 0) (hc₁0 : c₁ 0 = 0)
    (hs₂ : ∀ τ, HasDerivAt s₂ (1 + κ₂ * c₂ τ) τ) (hc₂ : ∀ τ, HasDerivAt c₂ (s₂ τ) τ)
    (hs₂0 : s₂ 0 = 0) (hc₂0 : c₂ 0 = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity A u₀ τ = u₀ + s₁ τ • A (P u₀) + c₁ τ • A (A (P u₀)) +
      s₂ τ • A (u₀ - P u₀) + c₂ τ • A (A (u₀ - P u₀)) := by
  have hc' : ∀ w, (1 - P) (A w) = A ((1 - P) w) := fun w => by
    simp only [sub_apply, one_apply_eq_self, hc, map_sub]
  have hi' : ∀ w, (1 - P) ((1 - P) w) = (1 - P) w := fun w => by
    simp only [sub_apply, one_apply_eq_self, map_sub, hi, sub_self, sub_zero]
  have h₂' : ∀ w, A (A ((1 - P) w)) = κ₂ • (1 - P) w := fun w => h₂ w
  have hsum : A = A ∘L P + A ∘L (1 - P) := by
    ext w
    simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub,
      add_sub_cancel]
  have h12 : ∀ v, (A ∘L P) ((A ∘L (1 - P)) v) = 0 := fun v => by
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub, hc, hi,
      sub_self]
  have h21 : ∀ v, (A ∘L (1 - P)) ((A ∘L P) v) = 0 := fun v => by
    simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, hc, hi, sub_self,
      map_zero]
  have hadd := linearVelocity_add h12 h21 u₀ τ
  rw [← hsum] at hadd
  rw [hadd, linearVelocity_eq_of_cube (comp_projection_cube hc hi h₁) hs₁ hc₁ hs₁0 hc₁0,
    linearVelocity_eq_of_cube (comp_projection_cube hc' hi' h₂') hs₂ hc₂ hs₂0 hc₂0]
  simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub, hc, hi,
    sub_self, sub_zero, map_zero]
  abel

end Projection

/-! ### An operator with `(A² − a²)(A² + b²) = 0` -/

section Quartic

variable {A : E →L[ℝ] E} {a b : ℝ}

/-- The projection `(A² + b²)/(a² + b²)` on the part of the space where `A² = a²`. -/
def hyperbolicProjection (A : E →L[ℝ] E) (a b : ℝ) : E →L[ℝ] E :=
  (a ^ 2 + b ^ 2)⁻¹ • (A ∘L A + b ^ 2 • (1 : E →L[ℝ] E))

omit [CompleteSpace E] in
theorem hyperbolicProjection_apply (A : E →L[ℝ] E) (a b : ℝ) (w : E) :
    hyperbolicProjection A a b w = (a ^ 2 + b ^ 2)⁻¹ • (A (A w) + b ^ 2 • w) := rfl

omit [CompleteSpace E] in
theorem hyperbolicProjection_comm (A : E →L[ℝ] E) (a b : ℝ) (w : E) :
    hyperbolicProjection A a b (A w) = A (hyperbolicProjection A a b w) := by
  simp only [hyperbolicProjection_apply, map_smul, map_add]

variable (hA : ∀ v, A (A (A (A v))) = (a ^ 2 - b ^ 2) • A (A v) + (a ^ 2 * b ^ 2) • v)

include hA in
omit [CompleteSpace E] in
theorem sq_apply_add (w : E) :
    A (A (A (A w) + b ^ 2 • w)) = a ^ 2 • (A (A w) + b ^ 2 • w) := by
  rw [map_add, map_add, map_smul, map_smul, hA]
  module

include hA in
omit [CompleteSpace E] in
/-- On the range of the projection, `A² = a²`. -/
theorem sq_hyperbolicProjection (w : E) :
    A (A (hyperbolicProjection A a b w)) = a ^ 2 • hyperbolicProjection A a b w := by
  rw [hyperbolicProjection_apply, map_smul, map_smul, sq_apply_add hA, smul_comm]

include hA in
omit [CompleteSpace E] in
theorem hyperbolicProjection_idem (hN : a ^ 2 + b ^ 2 ≠ 0) (w : E) :
    hyperbolicProjection A a b (hyperbolicProjection A a b w) = hyperbolicProjection A a b w := by
  rw [hyperbolicProjection_apply A a b (hyperbolicProjection A a b w),
    sq_hyperbolicProjection hA, ← add_smul, smul_smul, inv_mul_cancel₀ hN, one_smul]

include hA in
omit [CompleteSpace E] in
/-- On the kernel of the projection, `A² = −b²`. -/
theorem sq_sub_hyperbolicProjection (hN : a ^ 2 + b ^ 2 ≠ 0) (w : E) :
    A (A (w - hyperbolicProjection A a b w)) = -b ^ 2 • (w - hyperbolicProjection A a b w) := by
  have hNP : (a ^ 2 + b ^ 2) • hyperbolicProjection A a b w = A (A w) + b ^ 2 • w := by
    rw [hyperbolicProjection_apply, smul_smul, mul_inv_cancel₀ hN, one_smul]
  have hAA : A (A w) = (a ^ 2 + b ^ 2) • hyperbolicProjection A a b w - b ^ 2 • w := by
    rw [hNP]
    module
  rw [map_sub, map_sub, sq_hyperbolicProjection hA, hAA]
  module

include hA in
/-- If `(A² − a²)(A² + b²) = 0`, the solution of `u′ = A u` is the sum of a hyperbolic motion
on the range of the projection `P = (A² + b²)/(a² + b²)` and a circular motion on its
kernel. -/
theorem linearVelocity_eq_of_quartic (hN : a ^ 2 + b ^ 2 ≠ 0) {s₁ c₁ s₂ c₂ : ℝ → ℝ}
    (hs₁ : ∀ τ, HasDerivAt s₁ (1 + a ^ 2 * c₁ τ) τ) (hc₁ : ∀ τ, HasDerivAt c₁ (s₁ τ) τ)
    (hs₁0 : s₁ 0 = 0) (hc₁0 : c₁ 0 = 0)
    (hs₂ : ∀ τ, HasDerivAt s₂ (1 + -b ^ 2 * c₂ τ) τ) (hc₂ : ∀ τ, HasDerivAt c₂ (s₂ τ) τ)
    (hs₂0 : s₂ 0 = 0) (hc₂0 : c₂ 0 = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity A u₀ τ = u₀ + s₁ τ • A (hyperbolicProjection A a b u₀) +
      c₁ τ • A (A (hyperbolicProjection A a b u₀)) +
      s₂ τ • A (u₀ - hyperbolicProjection A a b u₀) +
      c₂ τ • A (A (u₀ - hyperbolicProjection A a b u₀)) :=
  linearVelocity_eq_of_projection (hyperbolicProjection_comm A a b)
    (hyperbolicProjection_idem hA hN) (sq_hyperbolicProjection hA)
    (sq_sub_hyperbolicProjection hA hN) hs₁ hc₁ hs₁0 hc₁0 hs₂ hc₂ hs₂0 hc₂0 u₀ τ

end Quartic

end ProjectAinos.SmoothGeometry.LinearODE
