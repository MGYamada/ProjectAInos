/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.PropagatorExpansion
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The determinant of the propagator

The derivative of the determinant at the identity is the trace. Hence the
determinant of the propagator of `y' = A(t) y` on a finite-dimensional space
satisfies `δ' = tr A · δ`, and

`det Φ(t, s) = exp (∫ tr A)`

(Liouville's formula). A family of operators that solves `M' = A(t) M` between
two times is the propagator applied to its initial value, so its determinant is
multiplied by the same factor. In particular a coefficient of trace zero has a
propagator of determinant one.
-/

@[expose] public section
noncomputable section

open Set ContinuousLinearMap
open scoped Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

/-! ### The derivative of the determinant at the identity -/

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem differentiable_det :
    Differentiable ℝ (fun M : n → n → ℝ => Matrix.det (Matrix.of M)) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

/-- Jacobi's formula at the identity: if `M(t₀) = 1`, the derivative of
`det M(t)` at `t₀` is the trace of the derivative of `M`. -/
theorem hasDerivAt_det_of_eq_one {M : ℝ → n → n → ℝ} {B : n → n → ℝ} {t₀ : ℝ}
    (h0 : Matrix.of (M t₀) = 1) (hM : HasDerivAt M B t₀) :
    HasDerivAt (fun t => Matrix.det (Matrix.of (M t))) (Matrix.trace (Matrix.of B)) t₀ := by
  let g : (n → n → ℝ) → ℝ := fun N => Matrix.det (Matrix.of N)
  have hg := (differentiable_det (n := n) (M t₀)).hasFDerivAt
  have h1 := hg.comp_hasDerivAt t₀ hM
  have hline : HasDerivAt (fun s : ℝ => M t₀ + s • B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add (M t₀)
  have hg0 : HasFDerivAt g (fderiv ℝ g (M t₀)) (M t₀ + (0 : ℝ) • B) := by
    rw [zero_smul, add_zero]
    exact hg
  have h2 := hg0.comp_hasDerivAt 0 hline
  let P := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) •
    (Matrix.of B).map Polynomial.C)).divX.divX
  have hexp : (g ∘ fun s : ℝ => M t₀ + s • B) =
      fun s : ℝ => 1 + Matrix.trace (Matrix.of B) * s + P.eval s * s ^ 2 := by
    funext s
    change Matrix.det (Matrix.of (M t₀) + s • Matrix.of B) = _
    rw [h0]
    exact Matrix.det_one_add_smul s (Matrix.of B)
  have h3 : HasDerivAt (fun s : ℝ => 1 + Matrix.trace (Matrix.of B) * s + P.eval s * s ^ 2)
      (Matrix.trace (Matrix.of B)) 0 := by
    have ha := ((hasDerivAt_id (0 : ℝ)).const_mul (Matrix.trace (Matrix.of B))).const_add 1
    have hb := (P.hasDerivAt 0).mul ((hasDerivAt_id (0 : ℝ)).pow 2)
    have h := ha.add hb
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => rfl)
    simp
  rw [hexp] at h2
  have hu := h2.unique h3
  change HasDerivAt (g ∘ M) _ t₀
  rw [← hu]
  exact h1

end Matrix

/-! ### Liouville's formula -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem continuous_traceCLM_apply (A : C(ℝ, E →L[ℝ] E)) :
    Continuous fun r : ℝ => traceCLM (A r) :=
  (traceCLM (E := E)).continuous.comp A.continuous

/-- The determinant of the propagator satisfies `δ' = tr A · δ`. -/
theorem hasDerivAt_det_propagator (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) :
    HasDerivAt (fun r => LinearMap.det (propagator A r s : E →ₗ[ℝ] E))
      (traceCLM (A t) * LinearMap.det (propagator A t s : E →ₗ[ℝ] E)) t := by
  let b := Module.finBasis ℝ E
  have hsplit : ∀ r : ℝ, LinearMap.det (propagator A r s : E →ₗ[ℝ] E) =
      LinearMap.det (propagator A r t : E →ₗ[ℝ] E) *
        LinearMap.det (propagator A t s : E →ₗ[ℝ] E) := by
    intro r
    rw [← LinearMap.det_comp, ← ContinuousLinearMap.toLinearMap_comp, propagator_comp]
  let M : ℝ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun r i j => b.repr (propagator A r t (b j)) i
  have hMeq : ∀ r : ℝ, Matrix.of (M r) =
      LinearMap.toMatrix b b (propagator A r t : E →ₗ[ℝ] E) := by
    intro r
    ext i j
    simp [M, LinearMap.toMatrix_apply]
  have hMdet : ∀ r : ℝ, Matrix.det (Matrix.of (M r)) =
      LinearMap.det (propagator A r t : E →ₗ[ℝ] E) := by
    intro r
    rw [hMeq, LinearMap.det_toMatrix]
  have hM0 : Matrix.of (M t) = 1 := by
    rw [hMeq, propagator_self]
    exact LinearMap.toMatrix_id b
  have hMd : HasDerivAt M (fun i j => b.repr (A t (b j)) i) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    have hc := (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_propagator_apply A t t (b j))
    rw [propagator_self] at hc
    exact hc
  have hd := hasDerivAt_det_of_eq_one hM0 hMd
  have htrace : Matrix.trace (Matrix.of fun i j => b.repr (A t (b j)) i) = traceCLM (A t) := by
    rw [traceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ b]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [htrace] at hd
  have hfun : (fun r => LinearMap.det (propagator A r s : E →ₗ[ℝ] E)) =
      fun r => Matrix.det (Matrix.of (M r)) *
        LinearMap.det (propagator A t s : E →ₗ[ℝ] E) := by
    funext r
    rw [hMdet, hsplit r]
  rw [hfun]
  exact hd.mul_const _

/-- Liouville's formula: `det Φ(t, s) = exp (∫ tr A)`. -/
theorem det_propagator (A : C(ℝ, E →L[ℝ] E)) (t s : ℝ) :
    LinearMap.det (propagator A t s : E →ₗ[ℝ] E) =
      Real.exp (∫ r in s..t, traceCLM (A r)) := by
  let I : ℝ → ℝ := fun r => ∫ x in s..r, traceCLM (A x)
  have hI : ∀ r, HasDerivAt I (traceCLM (A r)) r := fun r =>
    ((continuous_traceCLM_apply A).integral_hasStrictDerivAt s r).hasDerivAt
  let φ : ℝ → ℝ := fun r =>
    LinearMap.det (propagator A r s : E →ₗ[ℝ] E) * Real.exp (-I r)
  have hφ : ∀ r, HasDerivAt φ 0 r := by
    intro r
    have h1 := hasDerivAt_det_propagator A r s
    have h2 := ((hI r).neg).exp
    have h := h1.mul h2
    have hz : traceCLM (A r) * LinearMap.det (propagator A r s : E →ₗ[ℝ] E) *
        Real.exp (-I r) + LinearMap.det (propagator A r s : E →ₗ[ℝ] E) *
          (Real.exp (-I r) * -traceCLM (A r)) = 0 := by ring
    rw [← hz]
    exact h
  have hconst := is_const_of_deriv_eq_zero (fun r => (hφ r).differentiableAt)
    (fun r => (hφ r).deriv) t s
  have hs : φ s = 1 := by
    change LinearMap.det (propagator A s s : E →ₗ[ℝ] E) * Real.exp (-I s) = 1
    have hIs : I s = 0 := intervalIntegral.integral_same
    rw [propagator_self, hIs, neg_zero, Real.exp_zero, mul_one]
    exact LinearMap.det_id
  have ht : φ t = 1 := hconst.trans hs
  change LinearMap.det (propagator A t s : E →ₗ[ℝ] E) * Real.exp (-I t) = 1 at ht
  rw [Real.exp_neg] at ht
  have hpos : Real.exp (I t) ≠ 0 := (Real.exp_pos _).ne'
  field_simp at ht
  exact ht

/-- A coefficient of trace zero has a propagator of determinant one. -/
theorem det_propagator_of_trace_eq_zero (A : C(ℝ, E →L[ℝ] E))
    (hA : ∀ r, traceCLM (A r) = 0) (t s : ℝ) :
    LinearMap.det (propagator A t s : E →ₗ[ℝ] E) = 1 := by
  rw [det_propagator]
  simp [hA]

omit [FiniteDimensional ℝ E] in
/-- A family of operators that solves `M' = A(t) M` between two times is the
propagator applied to its initial value. -/
theorem eq_propagator_comp_of_hasDerivAt (A : C(ℝ, E →L[ℝ] E)) {M : ℝ → E →L[ℝ] E}
    {s t : ℝ} (hc : ContinuousOn M (uIcc s t))
    (hM : ∀ r ∈ Ioo (min s t) (max s t), HasDerivAt M (A r ∘L M r) r) :
    M t = propagator A t s ∘L M s := by
  ext y
  have h := eq_propagator_apply_of_hasDerivAt A (f := fun r => M r y) (s := s) (t := t)
    (fun r hr => ((hc r hr).clm_apply continuousWithinAt_const))
    (fun r hr => (hM r hr).clm_apply (hasDerivAt_const r y) |>.congr_deriv (by simp))
  exact h

/-- The determinant of a family of operators that solves `M' = A(t) M`. -/
theorem det_eq_det_mul_exp_integral_trace (A : C(ℝ, E →L[ℝ] E)) {M : ℝ → E →L[ℝ] E}
    {s t : ℝ} (hc : ContinuousOn M (uIcc s t))
    (hM : ∀ r ∈ Ioo (min s t) (max s t), HasDerivAt M (A r ∘L M r) r) :
    LinearMap.det (M t : E →ₗ[ℝ] E) =
      Real.exp (∫ r in s..t, traceCLM (A r)) * LinearMap.det (M s : E →ₗ[ℝ] E) := by
  rw [eq_propagator_comp_of_hasDerivAt A hc hM, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, det_propagator]

end ProjectAInos.SmoothGeometry.LinearODE
