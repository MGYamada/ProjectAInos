/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.Propagator
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The propagator for a small coefficient

Let `‖A(r)‖ ≤ g` between the times `s ≤ t`. The propagator `Φ(t, s)` satisfies
`‖Φ(t, s) y‖ ≤ e^{g (t − s)} ‖y‖`, and it is approximated by the first terms of
its series in the coefficient,

`Φ(t, s) y = y + ∫ A(r) y dr + ∫ A(r) (∫ A(x) y dx) dr + R`,

with `‖R‖ ≤ e^{g (t − s)} (g (t − s))³ / 6 · ‖y‖`. In finite dimension the trace
of the term of second order is half the trace of the square of `∫ A`, so the
trace of the propagator is known to this order from the integral of the
coefficient alone.
-/

@[expose] public section
noncomputable section

open Set ContinuousLinearMap
open scoped Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Growth of a solution: `‖Φ(t, s) y‖ ≤ e^{g (t − s)} ‖y‖`. -/
theorem norm_propagator_apply_le (A : C(ℝ, E →L[ℝ] E)) {s t g : ℝ} (hst : s ≤ t)
    (hg : ∀ r ∈ Icc s t, ‖A r‖ ≤ g) (y : E) :
    ‖propagator A t s y‖ ≤ ‖y‖ * Real.exp (g * (t - s)) := by
  have hd : ∀ r : ℝ, HasDerivAt (fun u => propagator A u s y) (A r (propagator A r s y)) r :=
    fun r => hasDerivAt_propagator_apply A r s y
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun u => propagator A u s y)
    (f' := fun r => A r (propagator A r s y)) (δ := ‖y‖) (K := g) (ε := 0) (a := s) (b := t)
    (continuous_iff_continuousAt.mpr fun r => (hd r).continuousAt).continuousOn
    (fun r _ => (hd r).hasDerivWithinAt) (by simp)
    (fun r hr => by
      rw [add_zero]
      exact ((A r).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hg r ⟨hr.1, hr.2.le⟩) (norm_nonneg _)))
    t ⟨hst, le_rfl⟩
  rwa [gronwallBound_ε0] at h

omit [CompleteSpace E] in
/-- One step of the series: a bound `c (r − s)ᵏ` on `u` gives the bound
`g c (τ − s)ᵏ⁺¹ / (k + 1)` on `∫ A(r) u(r) dr`. -/
theorem norm_integral_apply_le (A : C(ℝ, E →L[ℝ] E)) {s t g c : ℝ} {k : ℕ}
    (hg : ∀ r ∈ Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g) {u : ℝ → E}
    (hu : ∀ r ∈ Icc s t, ‖u r‖ ≤ c * (r - s) ^ k) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    ‖∫ r in s..τ, A r (u r)‖ ≤ g * c * (τ - s) ^ (k + 1) / (k + 1) := by
  have hbound : ∀ r ∈ Ioc s τ, ‖A r (u r)‖ ≤ g * c * (r - s) ^ k := by
    intro r hr
    have hr' : r ∈ Icc s t := ⟨hr.1.le, hr.2.trans hτ.2⟩
    calc ‖A r (u r)‖ ≤ ‖A r‖ * ‖u r‖ := (A r).le_opNorm _
      _ ≤ g * (c * (r - s) ^ k) :=
        mul_le_mul (hg r hr') (hu r hr') (norm_nonneg _) hg0
      _ = g * c * (r - s) ^ k := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hτ.1
    (Filter.Eventually.of_forall hbound)
    ((continuous_const.mul ((continuous_id.sub continuous_const).pow k)).intervalIntegrable s τ)
  refine h.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_sub_right (a := s) (b := τ)
    (fun x : ℝ => x ^ k) s
  rw [hsub, sub_self, integral_pow]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

variable (A : C(ℝ, E →L[ℝ] E)) {s t g : ℝ}

/-- The term of first order in the coefficient. -/
def firstOrder (s : ℝ) (y : E) (r : ℝ) : E := ∫ x in s..r, A x y

/-- The term of second order in the coefficient. -/
def secondOrder (s : ℝ) (y : E) (r : ℝ) : E := ∫ x in s..r, A x (firstOrder A s y x)

omit [CompleteSpace E] in
theorem continuous_apply_const (y : E) : Continuous fun r : ℝ => A r y :=
  A.continuous.clm_apply continuous_const

theorem hasDerivAt_firstOrder (s : ℝ) (y : E) (r : ℝ) :
    HasDerivAt (firstOrder A s y) (A r y) r :=
  ((continuous_apply_const A y).integral_hasStrictDerivAt s r).hasDerivAt

theorem continuous_firstOrder (s : ℝ) (y : E) : Continuous (firstOrder A s y) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_firstOrder A s y r).continuousAt

variable {A}

/-- `‖Φ(τ, s) y − y‖ ≤ e^{g (t − s)} g (τ − s) ‖y‖`. -/
theorem norm_propagator_apply_sub_le (hg : ∀ r ∈ Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g) (y : E)
    {τ : ℝ} (hτ : τ ∈ Icc s t) :
    ‖propagator A τ s y - y‖ ≤ ‖y‖ * Real.exp (g * (t - s)) * g * (τ - s) := by
  have heq : propagator A τ s y - y = ∫ r in s..τ, A r (propagator A r s y) := by
    rw [propagator_apply_eq_add_integral A τ s y]
    abel
  have hu : ∀ r ∈ Icc s t, ‖propagator A r s y‖ ≤ ‖y‖ * Real.exp (g * (t - s)) * (r - s) ^ 0 := by
    intro r hr
    rw [pow_zero, mul_one]
    refine (norm_propagator_apply_le A hr.1 (fun x hx => hg x ⟨hx.1, hx.2.trans hr.2⟩) y).trans ?_
    gcongr
    exact hr.2
  have h := norm_integral_apply_le A hg hg0 hu hτ
  rw [heq]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- `‖Φ(τ, s) y − y − ∫ A y‖ ≤ e^{g (t − s)} g² (τ − s)² / 2 · ‖y‖`. -/
theorem norm_propagator_apply_sub_firstOrder_le (hg : ∀ r ∈ Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g)
    (y : E) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    ‖propagator A τ s y - y - firstOrder A s y τ‖ ≤
      ‖y‖ * Real.exp (g * (t - s)) * g ^ 2 * (τ - s) ^ 2 / 2 := by
  have hA : Continuous fun r : ℝ => A r := A.continuous
  have hc1 : Continuous fun r : ℝ => A r (propagator A r s y) :=
    hA.clm_apply ((continuous_propagator_left A s).clm_apply continuous_const)
  have heq : propagator A τ s y - y - firstOrder A s y τ =
      ∫ r in s..τ, A r (propagator A r s y - y) := by
    have h1 : propagator A τ s y - y = ∫ r in s..τ, A r (propagator A r s y) := by
      rw [propagator_apply_eq_add_integral A τ s y]
      abel
    rw [h1, firstOrder, ← intervalIntegral.integral_sub (hc1.intervalIntegrable s τ)
      ((continuous_apply_const A y).intervalIntegrable s τ)]
    simp only [map_sub]
  have hu : ∀ r ∈ Icc s t,
      ‖propagator A r s y - y‖ ≤ ‖y‖ * Real.exp (g * (t - s)) * g * (r - s) ^ 1 := by
    intro r hr
    rw [pow_one]
    exact norm_propagator_apply_sub_le hg hg0 y hr
  have h := norm_integral_apply_le A hg hg0 hu hτ
  rw [heq]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- The expansion to second order with its remainder:
`‖Φ(t, s) y − y − ∫ A y − ∫ A ∫ A y‖ ≤ e^{g (t − s)} (g (t − s))³ / 6 · ‖y‖`. -/
theorem norm_propagator_apply_sub_secondOrder_le (hst : s ≤ t)
    (hg : ∀ r ∈ Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g) (y : E) :
    ‖propagator A t s y - y - firstOrder A s y t - secondOrder A s y t‖ ≤
      ‖y‖ * Real.exp (g * (t - s)) * (g * (t - s)) ^ 3 / 6 := by
  have hA : Continuous fun r : ℝ => A r := A.continuous
  have hc1 : Continuous fun r : ℝ => A r (propagator A r s y - y) :=
    hA.clm_apply (((continuous_propagator_left A s).clm_apply continuous_const).sub
      continuous_const)
  have hc2 : Continuous fun r : ℝ => A r (firstOrder A s y r) :=
    hA.clm_apply (continuous_firstOrder A s y)
  have heq : propagator A t s y - y - firstOrder A s y t - secondOrder A s y t =
      ∫ r in s..t, A r (propagator A r s y - y - firstOrder A s y r) := by
    have h1 : propagator A t s y - y - firstOrder A s y t =
        ∫ r in s..t, A r (propagator A r s y - y) := by
      have h0 : propagator A t s y - y = ∫ r in s..t, A r (propagator A r s y) := by
        rw [propagator_apply_eq_add_integral A t s y]
        abel
      have hc0 : Continuous fun r : ℝ => A r (propagator A r s y) :=
        hA.clm_apply ((continuous_propagator_left A s).clm_apply continuous_const)
      rw [h0, firstOrder, ← intervalIntegral.integral_sub (hc0.intervalIntegrable s t)
        ((continuous_apply_const A y).intervalIntegrable s t)]
      simp only [map_sub]
    rw [h1, secondOrder, ← intervalIntegral.integral_sub (hc1.intervalIntegrable s t)
      (hc2.intervalIntegrable s t)]
    simp only [map_sub]
  have hu : ∀ r ∈ Icc s t, ‖propagator A r s y - y - firstOrder A s y r‖ ≤
      ‖y‖ * Real.exp (g * (t - s)) * g ^ 2 / 2 * (r - s) ^ 2 := by
    intro r hr
    refine (norm_propagator_apply_sub_firstOrder_le hg hg0 y hr).trans (le_of_eq ?_)
    ring
  have h := norm_integral_apply_le A hg hg0 hu ⟨hst, le_rfl⟩
  rw [heq]
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-! ### The trace of the term of second order -/

variable (A)

/-- The integral of the coefficient, as an operator. -/
def integralCoefficient (s r : ℝ) : E →L[ℝ] E := ∫ x in s..r, A x

theorem hasDerivAt_integralCoefficient (s r : ℝ) :
    HasDerivAt (integralCoefficient A s) (A r) r :=
  (A.continuous.integral_hasStrictDerivAt s r).hasDerivAt

theorem continuous_integralCoefficient (s : ℝ) : Continuous (integralCoefficient A s) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_integralCoefficient A s r).continuousAt

omit [CompleteSpace E] in
@[simp] theorem integralCoefficient_self (s : ℝ) : integralCoefficient A s s = 0 := by
  simp [integralCoefficient]

omit [CompleteSpace E] in
theorem firstOrder_eq (s : ℝ) (y : E) (r : ℝ) :
    firstOrder A s y r = integralCoefficient A s r y :=
  (ContinuousLinearMap.intervalIntegral_apply (A.continuous.intervalIntegrable s r) y).symm

/-- The term of second order, as an operator. -/
def secondOrderOperator (s r : ℝ) : E →L[ℝ] E :=
  ∫ x in s..r, A x ∘L integralCoefficient A s x

theorem continuous_comp_integralCoefficient (s : ℝ) :
    Continuous fun x : ℝ => A x ∘L integralCoefficient A s x := by
  have hA : Continuous fun r : ℝ => A r := A.continuous
  exact hA.clm_comp (continuous_integralCoefficient A s)

theorem hasDerivAt_secondOrderOperator (s r : ℝ) :
    HasDerivAt (secondOrderOperator A s) (A r ∘L integralCoefficient A s r) r :=
  ((continuous_comp_integralCoefficient A s).integral_hasStrictDerivAt s r).hasDerivAt

omit [CompleteSpace E] in
@[simp] theorem secondOrderOperator_self (s : ℝ) : secondOrderOperator A s s = 0 := by
  simp [secondOrderOperator]

theorem secondOrder_eq (s : ℝ) (y : E) (r : ℝ) :
    secondOrder A s y r = secondOrderOperator A s r y := by
  rw [secondOrderOperator, ContinuousLinearMap.intervalIntegral_apply
    ((continuous_comp_integralCoefficient A s).intervalIntegrable s r) y]
  apply intervalIntegral.integral_congr
  intro x _
  change A x (firstOrder A s y x) = A x (integralCoefficient A s x y)
  rw [firstOrder_eq]

variable [FiniteDimensional ℝ E]

/-- The trace, as a continuous linear functional on the operators of a
finite-dimensional space. -/
def traceCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))

omit [CompleteSpace E] in
theorem traceCLM_apply (L : E →L[ℝ] E) : traceCLM L = LinearMap.trace ℝ E (L : E →ₗ[ℝ] E) :=
  rfl

omit [CompleteSpace E] in
theorem traceCLM_comp_comm (L L' : E →L[ℝ] E) : traceCLM (L ∘L L') = traceCLM (L' ∘L L) := by
  rw [traceCLM_apply, traceCLM_apply]
  exact LinearMap.trace_mul_comm ℝ (L : E →ₗ[ℝ] E) (L' : E →ₗ[ℝ] E)

/-- The trace of the term of second order is half the trace of the square of
the integral of the coefficient. -/
theorem traceCLM_secondOrderOperator (s t : ℝ) :
    traceCLM (secondOrderOperator A s t) =
      1 / 2 * traceCLM (integralCoefficient A s t ∘L integralCoefficient A s t) := by
  let φ : ℝ → ℝ := fun r => traceCLM (secondOrderOperator A s r) -
    1 / 2 * traceCLM (integralCoefficient A s r ∘L integralCoefficient A s r)
  have hφ : ∀ r, HasDerivAt φ 0 r := by
    intro r
    have h1 := (traceCLM (E := E)).hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_secondOrderOperator A s r)
    have hP := hasDerivAt_integralCoefficient A s r
    have h2 := (traceCLM (E := E)).hasFDerivAt.comp_hasDerivAt r (hP.clm_comp hP)
    have h := h1.sub (h2.const_mul (1 / 2 : ℝ))
    have hz : traceCLM (A r ∘L integralCoefficient A s r) -
        1 / 2 * traceCLM (A r ∘L integralCoefficient A s r +
          integralCoefficient A s r ∘L A r) = 0 := by
      rw [map_add, traceCLM_comp_comm (integralCoefficient A s r) (A r)]
      ring
    rw [← hz]
    exact h
  have hconst := is_const_of_deriv_eq_zero (fun r => (hφ r).differentiableAt)
    (fun r => (hφ r).deriv) t s
  have hs : φ s = 0 := by
    change traceCLM (secondOrderOperator A s s) -
      1 / 2 * traceCLM (integralCoefficient A s s ∘L integralCoefficient A s s) = 0
    simp
  have ht : φ t = 0 := hconst.trans hs
  exact sub_eq_zero.mp ht

end ProjectAInos.SmoothGeometry.LinearODE
