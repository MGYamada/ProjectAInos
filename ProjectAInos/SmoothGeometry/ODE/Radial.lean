/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.ContinuousFamily
public import ProjectAInos.SmoothGeometry.ODE.Volterra

/-! # Smooth radial transport from coordinate connection coefficients

A smooth coefficient field determines a smooth family of linear ODEs along
radial segments. Near the zero displacement the coefficients are small, and
the endpoint maps and their inverses form smooth invertible families. This
construction alone does not assert that they are parallel in all directions;
that conclusion requires the curvature compatibility argument.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Filter Metric ContinuousLinearMap
open scoped ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The vector-transport coefficient along `t ↦ p + t • x`. -/
def radialCoefficient (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ)
    (p x : E) : Curve (E →L[ℝ] E) :=
  ContinuousFamily.slices (fun q : E × ℝ => -(Γ (p + q.2 • q.1) q.1))
    ((hΓ.continuous.comp (continuous_const.add
      (continuous_snd.smul continuous_fst))).clm_apply continuous_fst).neg
    ⟨Subtype.val, continuous_subtype_val⟩ x

@[simp] theorem radialCoefficient_apply (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p x : E) (t : unitInterval) :
    radialCoefficient Γ hΓ p x t = -(Γ (p + (t : ℝ) • x) x) := rfl

@[simp] theorem radialCoefficient_zero (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) : radialCoefficient Γ hΓ p 0 = 0 := by
  ext t v
  simp

/-- The radial coefficients depend smoothly on displacement in supremum norm. -/
theorem radialCoefficient_contDiff (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) : ContDiff ℝ ∞ (radialCoefficient Γ hΓ p) := by
  have h : ContDiff ℝ ∞ (fun q : E × ℝ => -(Γ (p + q.2 • q.1) q.1)) :=
    ((hΓ.comp (contDiff_const.add (contDiff_snd.smul contDiff_fst))).clm_apply contDiff_fst).neg
  exact ContinuousFamily.slices_contDiff h ⟨Subtype.val, continuous_subtype_val⟩

/-- Short displacements give small coefficients on the entire unit interval. -/
theorem eventually_radialCoefficient_small (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) :
    ∀ᶠ x in 𝓝 (0 : E), ‖radialCoefficient Γ hΓ p x‖ < 1 := by
  have hc : Continuous (fun x => ‖radialCoefficient Γ hΓ p x‖) :=
    (@continuous_norm (Curve (E →L[ℝ] E)) _).comp
      (radialCoefficient_contDiff Γ hΓ p).continuous
  have ho : IsOpen {x : E | ‖radialCoefficient Γ hΓ p x‖ < 1} := isOpen_lt hc continuous_const
  apply ho.mem_nhds
  change ‖radialCoefficient Γ hΓ p 0‖ < 1
  rw [radialCoefficient_zero, @norm_zero (Curve (E →L[ℝ] E)) _]
  exact zero_lt_one

variable [CompleteSpace E]

/-- Endpoint of the radial solution, linear in the initial vector. Its ODE
and smoothness specifications below apply to small displacements. -/
def radialEndpoint (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ)
    (p x : E) : E →L[ℝ] E :=
  (ContinuousMap.evalCLM ℝ (M := E) (1 : unitInterval)).comp
    (solutionOperator (radialCoefficient Γ hΓ p x))

@[simp] theorem radialEndpoint_zero (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) : radialEndpoint Γ hΓ p 0 = ContinuousLinearMap.id ℝ E := by
  ext v
  change solutionOperator (radialCoefficient Γ hΓ p 0) v 1 = v
  rw [radialCoefficient_zero, solution_zero_coefficient]
  rfl

theorem radialEndpoint_contDiffAt (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) {x : E}
    (hx : ‖radialCoefficient Γ hΓ p x‖ < 1) :
    ContDiffAt ℝ ∞ (radialEndpoint Γ hΓ p) x := by
  have hs := (solutionOperator_contDiffAt hx).comp x
    (radialCoefficient_contDiff Γ hΓ p).contDiffAt
  exact contDiffAt_const.clm_comp hs

/-- The radial frame is invertible near its identity initial value. -/
theorem eventually_radialEndpoint_isInvertible (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) :
    ∀ᶠ x in 𝓝 (0 : E), (radialEndpoint Γ hΓ p x).IsInvertible := by
  have hsmall : ‖radialCoefficient Γ hΓ p 0‖ < 1 :=
    (eventually_radialCoefficient_small Γ hΓ p).self_of_nhds
  have hi : (radialEndpoint Γ hΓ p 0).IsInvertible := by
    rw [radialEndpoint_zero]
    exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
  exact (radialEndpoint_contDiffAt Γ hΓ p hsmall).continuousAt hi.eventually_nhds

/-- Inverse radial frame; parallelness in transverse directions is not yet
claimed by this definition or its smoothness theorem. -/
def radialCoframe (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ)
    (p x : E) : E →L[ℝ] E := (radialEndpoint Γ hΓ p x).inverse

/-- A common ball carries smooth radial frames and coframes with identity
value at the center. No flatness assumption is needed for this construction. -/
theorem exists_radial_ball (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) :
    ∃ r : ℝ, 0 < r ∧
      (∀ x ∈ ball (0 : E) r, ‖radialCoefficient Γ hΓ p x‖ < 1) ∧
      (∀ x ∈ ball (0 : E) r, (radialEndpoint Γ hΓ p x).IsInvertible) ∧
      ContDiffOn ℝ ∞ (radialEndpoint Γ hΓ p) (ball 0 r) ∧
      ContDiffOn ℝ ∞ (radialCoframe Γ hΓ p) (ball 0 r) ∧
      radialCoframe Γ hΓ p 0 = ContinuousLinearMap.id ℝ E := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((eventually_radialCoefficient_small Γ hΓ p).and
      (eventually_radialEndpoint_isInvertible Γ hΓ p))
  refine ⟨r, hr, fun x hx => (hball hx).1, fun x hx => (hball hx).2, ?_, ?_, ?_⟩
  · exact fun x hx => (radialEndpoint_contDiffAt Γ hΓ p (hball hx).1).contDiffWithinAt
  · intro x hx
    exact ((hball hx).2.contDiffAt_map_inverse.comp x
      (radialEndpoint_contDiffAt Γ hΓ p (hball hx).1)).contDiffWithinAt
  · simp [radialCoframe]

/-- Each member of the smooth family solves the radial vector-transport ODE. -/
theorem radialSolution_hasDerivWithinAt (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p x v : E) (hx : ‖radialCoefficient Γ hΓ p x‖ < 1)
    (t : unitInterval) :
    HasDerivWithinAt (extend (solutionOperator (radialCoefficient Γ hΓ p x) v))
      (-(Γ (p + (t : ℝ) • x) x (solutionOperator (radialCoefficient Γ hΓ p x) v t)))
      (Icc (0 : ℝ) 1) t := by
  simpa only [radialCoefficient_apply, neg_apply] using
    solution_hasDerivWithinAt hx v t

end ProjectAInos.SmoothGeometry.LinearODE
