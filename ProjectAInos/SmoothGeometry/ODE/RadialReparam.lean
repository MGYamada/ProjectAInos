/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.Radial

/-! # Radial endpoint maps along their defining rays

Rescaling a radial segment rescales its ODE coefficient. Uniqueness identifies
the endpoint at a shorter displacement with the intermediate point of the
original solution. This relates the smooth endpoint family to its radial
transport differential equation.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Filter Metric ContinuousLinearMap
open scoped ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A shorter prefix of a continuous curve, reparametrized onto `[0,1]`. -/
def rescaledCurve (f : Curve E) (s : unitInterval) : Curve E :=
  ⟨fun t => f (s * t), f.continuous.comp (continuous_const.mul continuous_id)⟩

omit [CompleteSpace E] in
theorem radialCoefficient_rescale (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p x : E) (s t : unitInterval) :
    radialCoefficient Γ hΓ p ((s : ℝ) • x) t =
      (s : ℝ) • radialCoefficient Γ hΓ p x (s * t) := by
  simp [radialCoefficient_apply, smul_smul, mul_comm]

/-- The smooth radial endpoint at `s • x` equals the solution at time `s`
along `x`, whenever both coefficient curves satisfy the smallness bound. -/
theorem radialEndpoint_on_ray (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p x v : E) (s : unitInterval)
    (hx : ‖radialCoefficient Γ hΓ p x‖ < 1)
    (hsx : ‖radialCoefficient Γ hΓ p ((s : ℝ) • x)‖ < 1) :
    radialEndpoint Γ hΓ p ((s : ℝ) • x) v =
      solutionOperator (radialCoefficient Γ hΓ p x) v s := by
  by_cases hs : s = 0
  · subst s
    simpa using (solution_initial hx v).symm
  have hspos : (0 : ℝ) < s := by
    apply lt_of_le_of_ne s.property.1
    intro h
    apply hs
    apply Subtype.ext
    exact h.symm
  let f := solutionOperator (radialCoefficient Γ hΓ p x) v
  have hinit : rescaledCurve f s 0 = v := by
    simpa [rescaledCurve, f] using solution_initial hx v
  have hsol : rescaledCurve f s =
      solutionOperator (radialCoefficient Γ hΓ p ((s : ℝ) • x)) v := by
    apply eq_solution_of_hasDerivAt hsx v _ hinit
    intro u hu
    let t : unitInterval := ⟨u, mem_Icc_of_Ioo hu⟩
    have hst : (s : ℝ) * u ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨mul_pos hspos hu.1, ?_⟩
      have hle := mul_le_mul_of_nonneg_right s.property.2 hu.1.le
      exact hle.trans_lt (by simpa using hu.2)
    have hd := (solution_hasDerivWithinAt hx v (s * t)).hasDerivAt
      (Icc_mem_nhds hst.1 hst.2)
    change HasDerivAt _ _ ((s : ℝ) * u) at hd
    have hm : HasDerivAt (fun z : ℝ => (s : ℝ) * z) (s : ℝ) u := by
      simpa using (hasDerivAt_id u).const_mul (s : ℝ)
    have hd' : HasDerivAt (fun z => extend f ((s : ℝ) * z))
        ((s : ℝ) • (radialCoefficient Γ hΓ p x (s * t) (f (s * t)))) u :=
      hd.scomp u hm
    have heq : extend (rescaledCurve f s) =ᶠ[𝓝 u] fun z => extend f ((s : ℝ) * z) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with z hz
      have hsz : (s : ℝ) * z ∈ Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg s.property.1 hz.1.le, ?_⟩
        exact (mul_le_mul_of_nonneg_right s.property.2 hz.1.le).trans (by simpa using hz.2.le)
      simp [extend, projIcc_of_mem zero_le_one (mem_Icc_of_Ioo hz),
        projIcc_of_mem zero_le_one hsz, rescaledCurve]
      congr 1
    have hc : extend (radialCoefficient Γ hΓ p ((s : ℝ) • x)) u =
        (s : ℝ) • radialCoefficient Γ hΓ p x (s * t) := by
      change extend (radialCoefficient Γ hΓ p ((s : ℝ) • x)) (t : ℝ) = _
      rw [extend_coe, radialCoefficient_rescale]
    rw [hc]
    have hv : extend (rescaledCurve f s) u = f (s * t) := by
      change extend (rescaledCurve f s) (t : ℝ) = _
      rw [extend_coe]
      rfl
    rw [hv]
    simpa only [mul_one, smul_apply] using hd'.congr_of_eventuallyEq heq
  have h := congrArg (fun c : Curve E => c 1) hsol
  simpa [rescaledCurve, radialEndpoint, f] using h.symm

/-- The derivative of the smooth endpoint family in the radial direction is
exactly the coordinate transport equation. Transverse parallelness is a
separate flat-curvature consequence. -/
theorem radialEndpoint_fderiv_radial (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hΓ : ContDiff ℝ ∞ Γ) (p : E) {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x ∈ ball (0 : E) r, ‖radialCoefficient Γ hΓ p x‖ < 1)
    {x : E} (hx : x ∈ ball (0 : E) r) (v : E) :
    fderiv ℝ (radialEndpoint Γ hΓ p) x x v =
      -(Γ (p + x) x (radialEndpoint Γ hΓ p x v)) := by
  have hxs (s : unitInterval) : (s : ℝ) • x ∈ ball (0 : E) r :=
    (convex_ball (0 : E) r).smul_mem_of_zero_mem (mem_ball_self hr) hx
      s.property
  have heq : ∀ s ∈ Icc (0 : ℝ) 1,
      radialEndpoint Γ hΓ p (s • x) v =
        extend (solutionOperator (radialCoefficient Γ hΓ p x) v) s := by
    intro s hs
    have h := radialEndpoint_on_ray Γ hΓ p x v ⟨s, hs⟩
      (hsmall x hx) (hsmall _ (hxs ⟨s, hs⟩))
    change _ = extend (solutionOperator (radialCoefficient Γ hΓ p x) v)
      ((⟨s, hs⟩ : unitInterval) : ℝ)
    rw [extend_coe]
    exact h
  have hd₂ : HasDerivWithinAt (fun s : ℝ => radialEndpoint Γ hΓ p (s • x) v)
      (-(Γ (p + x) x (radialEndpoint Γ hΓ p x v))) (Icc (0 : ℝ) 1) 1 := by
    have hd := radialSolution_hasDerivWithinAt Γ hΓ p x v (hsmall x hx) 1
    simpa [radialEndpoint] using
      hd.congr_of_mem heq (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hP := (radialEndpoint_contDiffAt Γ hΓ p (hsmall x hx)).differentiableAt (by simp)
  have hPv := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp x hP.hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => s • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hPv' : HasFDerivAt (fun z => radialEndpoint Γ hΓ p z v)
      ((ContinuousLinearMap.apply ℝ E v).comp (fderiv ℝ (radialEndpoint Γ hΓ p) x))
      ((1 : ℝ) • x) := by
    simpa only [one_smul, Function.comp_def, ContinuousLinearMap.apply_apply] using hPv
  have hd₁ : HasDerivAt (fun s : ℝ => radialEndpoint Γ hΓ p (s • x) v)
      (fderiv ℝ (radialEndpoint Γ hΓ p) x x v) 1 := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply] using hPv'.comp_hasDerivAt 1 hline
  have hu := uniqueDiffOn_Icc_zero_one 1 (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  exact (hd₁.hasDerivWithinAt.derivWithin hu).symm.trans (hd₂.derivWithin hu)

end ProjectAInos.SmoothGeometry.LinearODE
