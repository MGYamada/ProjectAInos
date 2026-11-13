/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UnitInterval
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # The Volterra operator for linear equations on the unit interval

Continuous coefficient curves act on a Banach space of continuous vector
curves. Integration gives a bounded linear Volterra operator. For coefficients
of norm less than one, its resolvent constructs the solution and supplies
smooth dependence on the whole coefficient curve and initial value.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set ContinuousLinearMap
open scoped unitInterval ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous vector curves on the fixed unit interval. -/
abbrev Curve (E : Type) [TopologicalSpace E] := C(unitInterval, E)

/-- Extend a continuous curve by its endpoint values outside the interval. -/
def extend (f : Curve E) (t : ℝ) : E := f (projIcc 0 1 zero_le_one t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem extend_continuous (f : Curve E) : Continuous (extend f) :=
  f.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extend_coe (f : Curve E) (t : unitInterval) : extend f t = f t := by
  simp [extend]

/-- The indefinite integral, retained as a continuous curve. -/
def primitive (f : Curve E) : Curve E where
  toFun t := ∫ s in 0..(t : ℝ), extend f s
  continuous_toFun :=
    (continuous_iff_continuousAt.mpr fun t =>
      ((extend_continuous f).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt).comp
      continuous_subtype_val

theorem primitive_norm_le (f : Curve E) : ‖primitive f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := ‖f‖)
    (fun s _ => f.norm_coe_le_norm (projIcc 0 1 zero_le_one s))
  change ‖∫ s in 0..(t : ℝ), extend f s‖ ≤ ‖f‖
  apply h.trans
  simpa only [sub_zero, abs_of_nonneg t.property.1] using
    mul_le_of_le_one_right (norm_nonneg f) t.property.2

/-- Indefinite integration is a bounded linear operator of norm at most one. -/
def primitiveCLM : Curve E →L[ℝ] Curve E :=
  LinearMap.mkContinuous
    ({ toFun := primitive
       map_add' := by
        intro f g
        ext t
        exact intervalIntegral.integral_add ((extend_continuous f).intervalIntegrable _ _)
          ((extend_continuous g).intervalIntegrable _ _)
       map_smul' := by
        intro a f
        ext t
        exact intervalIntegral.integral_smul a (extend f) } : Curve E →ₗ[ℝ] Curve E) 1
    (fun f => by change ‖primitive f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using primitive_norm_le f)

@[simp] theorem primitiveCLM_apply (f : Curve E) : primitiveCLM f = primitive f := rfl

/-- Pointwise action of a continuous coefficient curve on a vector curve. -/
def pointwiseApply (A : Curve (E →L[ℝ] E)) (f : Curve E) : Curve E :=
  ⟨fun t => A t (f t), A.continuous.clm_apply f.continuous⟩

omit [CompleteSpace E] in
theorem pointwiseApply_norm_le (A : Curve (E →L[ℝ] E)) (f : Curve E) :
    ‖pointwiseApply A f‖ ≤ ‖A‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg f))).mpr
  intro t
  exact ((A t).le_opNorm (f t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (f.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- Coefficients determine a continuous linear action on vector curves. -/
def coefficientAction (A : Curve (E →L[ℝ] E)) : Curve E →L[ℝ] Curve E :=
  LinearMap.mkContinuous
    { toFun := pointwiseApply A
      map_add' := by intro f g; ext t; exact (A t).map_add _ _
      map_smul' := by intro a f; ext t; exact (A t).map_smul a (f t) }
    ‖A‖ (pointwiseApply_norm_le A)

omit [CompleteSpace E] in
theorem coefficientAction_norm_le (A : Curve (E →L[ℝ] E)) : ‖coefficientAction A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Pointwise action also depends continuously and linearly on the coefficient
curve itself, in the operator norm on the space of continuous curves. -/
def coefficientActionCLM : Curve (E →L[ℝ] E) →L[ℝ] (Curve E →L[ℝ] Curve E) := by
  let L : Curve (E →L[ℝ] E) →ₗ[ℝ] (Curve E →L[ℝ] Curve E) :=
    { toFun := coefficientAction
      map_add' := by intro A B; ext f t; rfl
      map_smul' := by intro a A; ext f t; rfl }
  have hL : ∀ A, ‖L A‖ ≤ 1 * ‖A‖ := by
    intro A
    change ‖coefficientAction A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using coefficientAction_norm_le A
  let result := LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Curve (E →L[ℝ] E)) (F := Curve E →L[ℝ] Curve E) («σ» := RingHom.id ℝ) L 1 hL
  exact result

/-- The coefficient-dependent Volterra operator `f ↦ ∫₀ᵗ A(s) f(s) ds`. -/
def volterra : Curve (E →L[ℝ] E) →L[ℝ] (Curve E →L[ℝ] Curve E) :=
  (compL ℝ (Curve E) (Curve E) (Curve E) primitiveCLM).comp coefficientActionCLM

@[simp] theorem volterra_apply (A : Curve (E →L[ℝ] E)) (f : Curve E) (t : unitInterval) :
    volterra A f t = ∫ s in 0..(t : ℝ), extend A s (extend f s) := rfl

theorem volterra_norm_le (A : Curve (E →L[ℝ] E)) : ‖volterra A‖ ≤ ‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg A)
  intro f
  exact (primitive_norm_le (pointwiseApply A f)).trans (pointwiseApply_norm_le A f)

/-- The integral equation operator `id - V_A`. -/
def equationOperator (A : Curve (E →L[ℝ] E)) : Curve E →L[ℝ] Curve E :=
  ContinuousLinearMap.id ℝ (Curve E) - volterra A

/-- A small coefficient curve gives an invertible integral equation operator. -/
theorem equationOperator_isInvertible {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1) :
    (equationOperator A).IsInvertible := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one (x := volterra A) ((volterra_norm_le A).trans_lt hA)
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

/-- The solution as a continuous linear function of its initial value. The
ODE specifications below require `‖A‖ < 1`; no invertibility is assumed. -/
def solutionOperator (A : Curve (E →L[ℝ] E)) : E →L[ℝ] Curve E :=
  (equationOperator A).inverse.comp (ContinuousLinearMap.const ℝ unitInterval)

/-- The unique curve solving the Volterra integral equation. -/
theorem solution_integral_eq {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1)
    (y : E) (t : unitInterval) :
    solutionOperator A y t = y +
      ∫ s in 0..(t : ℝ), extend A s (extend (solutionOperator A y) s) := by
  have h := congrArg (fun f : Curve E => f t)
    ((equationOperator_isInvertible hA).self_apply_inverse (ContinuousMap.const _ y))
  change solutionOperator A y t - volterra A (solutionOperator A y) t = y at h
  rw [volterra_apply] at h
  exact sub_eq_iff_eq_add.mp h

@[simp] theorem solution_initial {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1) (y : E) :
    solutionOperator A y 0 = y := by
  simpa using solution_integral_eq hA y 0

/-- Uniqueness among continuous curves satisfying the integral equation. -/
theorem eq_solution_of_integral_eq {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1)
    (y : E) (f : Curve E)
    (hf : ∀ t : unitInterval, f t = y + ∫ s in 0..(t : ℝ), extend A s (extend f s)) :
    f = solutionOperator A y := by
  apply (equationOperator_isInvertible hA).injective
  rw [show equationOperator A (solutionOperator A y) = ContinuousMap.const _ y from
    (equationOperator_isInvertible hA).self_apply_inverse _]
  ext t
  change f t - volterra A f t = y
  rw [volterra_apply, hf t]
  abel

/-- The constructed curve satisfies the differential equation, including
one-sided derivatives at both endpoints of the unit interval. -/
theorem solution_hasDerivWithinAt {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1)
    (y : E) (t : unitInterval) :
    HasDerivWithinAt (extend (solutionOperator A y)) (A t (solutionOperator A y t))
      (Icc (0 : ℝ) 1) t := by
  have hd := ((extend_continuous (pointwiseApply A (solutionOperator A y))).integral_hasStrictDerivAt 0 (t : ℝ)).hasDerivAt.const_add y
  have heq : ∀ s ∈ Icc (0 : ℝ) 1, extend (solutionOperator A y) s =
      y + ∫ u in 0..s, extend (pointwiseApply A (solutionOperator A y)) u := by
    intro s hs
    change extend (solutionOperator A y) (⟨s, hs⟩ : unitInterval) = _
    rw [extend_coe]
    exact solution_integral_eq hA y ⟨s, hs⟩
  simpa only [extend_coe, pointwiseApply, ContinuousMap.coe_mk] using
    hd.hasDerivWithinAt.congr_of_mem heq t.property

/-- Differential-equation uniqueness. No derivative at the endpoints is
required: continuity there and the equation on the interior suffice. -/
theorem eq_solution_of_hasDerivAt {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1)
    (y : E) (f : Curve E) (h0 : f 0 = y)
    (hf : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (extend f) (extend A t (extend f t)) t) :
    f = solutionOperator A y := by
  apply eq_solution_of_integral_eq hA y f
  intro t
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    (extend_continuous f).continuousOn
    (fun s hs => hf s ⟨hs.1, hs.2.trans_le t.property.2⟩)
    ((extend_continuous (pointwiseApply A f)).intervalIntegrable 0 (t : ℝ))
  have hzero : extend f 0 = y := by
    change extend f ((0 : unitInterval) : ℝ) = y
    rw [extend_coe, h0]
  rw [extend_coe, hzero] at h
  change f t = y + ∫ s in 0..(t : ℝ), extend A s (extend f s)
  rw [h]
  abel

/-- A priori supremum-norm estimate for the constructed solution. -/
theorem solution_norm_le {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1) (y : E) :
    ‖solutionOperator A y‖ ≤ ‖y‖ / (1 - ‖A‖) := by
  have heq : solutionOperator A y = ContinuousMap.const _ y +
      volterra A (solutionOperator A y) := by
    ext t
    exact solution_integral_eq hA y t
  have hbound := norm_add_le (ContinuousMap.const unitInterval y)
    (volterra A (solutionOperator A y))
  rw [← heq] at hbound
  have hc : ‖ContinuousMap.const unitInterval y‖ ≤ ‖y‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg y)).mpr (fun _ => le_rfl)
  have hv := (volterra A).le_opNorm (solutionOperator A y)
  have hn := mul_le_mul_of_nonneg_right (volterra_norm_le A) (norm_nonneg (solutionOperator A y))
  apply (le_div_iff₀ (sub_pos.mpr hA)).mpr
  nlinarith

/-- Smooth dependence on the whole coefficient curve in the supremum norm.
The initial-value map is linear and the inverse is smooth on invertible maps. -/
theorem solutionOperator_contDiffAt {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1) :
    ContDiffAt ℝ ∞ (solutionOperator (E := E)) A := by
  have hv := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := Curve (E →L[ℝ] E)) (F := Curve E →L[ℝ] Curve E) (volterra (E := E))
  have he : ContDiff ℝ ∞ (equationOperator (E := E)) := contDiff_const.sub hv
  exact ((equationOperator_isInvertible hA).contDiffAt_map_inverse.comp A he.contDiffAt).clm_comp contDiffAt_const

/-- Joint smooth dependence on the coefficient curve and initial value. -/
theorem solution_contDiffAt {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1) (y : E) :
    ContDiffAt ℝ ∞ (fun p : Curve (E →L[ℝ] E) × E => solutionOperator p.1 p.2) (A, y) := by
  exact ((solutionOperator_contDiffAt hA).comp (A, y) contDiffAt_fst).clm_apply contDiffAt_snd

/-- Fixed-time evaluation preserves smooth dependence. -/
theorem solution_eval_contDiffAt {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1)
    (y : E) (t : unitInterval) :
    ContDiffAt ℝ ∞ (fun p : Curve (E →L[ℝ] E) × E => solutionOperator p.1 p.2 t) (A, y) :=
  (ContinuousMap.evalCLM ℝ (M := E) t).contDiff.contDiffAt.comp _ (solution_contDiffAt hA y)

/-- Smooth parameter families of coefficient curves and initial values give
smooth families of entire solutions, with the same fixed time interval. -/
theorem solution_family_contDiffAt {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {A : P → Curve (E →L[ℝ] E)} {y : P → E} {p : P}
    (hA : ContDiffAt ℝ ∞ A p) (hy : ContDiffAt ℝ ∞ y p) (hsmall : ‖A p‖ < 1) :
    ContDiffAt ℝ ∞ (fun q => solutionOperator (A q) (y q)) p := by
  have hs := solutionOperator_contDiffAt (E := E) (A := A p) hsmall
  exact (hs.comp p hA).clm_apply hy

@[simp] theorem solution_zero_coefficient (y : E) :
    solutionOperator (0 : Curve (E →L[ℝ] E)) y = ContinuousMap.const _ y := by
  symm
  have hsmall : ‖(0 : Curve (E →L[ℝ] E))‖ < 1 := by
    rw [@norm_zero (Curve (E →L[ℝ] E)) _]
    exact zero_lt_one
  have hz := eq_solution_of_integral_eq hsmall y (ContinuousMap.const _ y)
  apply hz
  intro t
  simp [extend]

end ProjectAInos.SmoothGeometry.LinearODE
