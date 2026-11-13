/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ParticleAction
public import ProjectAInos.GeneralRelativity.QuadraticLagrangian
public import ProjectAInos.SmoothGeometry.Lorentzian.MotionExamples

/-! # Quadratic variation and the native geodesic equation in model coordinates

The metric and connection are native tangent-bundle objects. This module
identifies the coordinate Euler–Lagrange covector with lowered covariant
acceleration, so null initial data do not require constrained variations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle ContinuousLinearMap Set
open scoped Manifold ContDiff

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ}
local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The native metric in the canonical coordinates of the model manifold. -/
def modelMetric (g : LorentzMetric .timeNegative d E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap).comp
    ((g.form x).comp (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap)

@[simp] theorem modelMetric_apply (g : LorentzMetric .timeNegative d E) (x v w : E) :
    modelMetric g x v w = g.form x (modelField v x) (modelField w x) := rfl

theorem modelMetric_symmetric (g : LorentzMetric .timeNegative d E) (x v w : E) :
    modelMetric g x v w = modelMetric g x w v := g.symmetric x _ _

theorem modelMetric_contDiff (g : LorentzMetric .timeNegative d E) :
    ContDiff ℝ ∞ (modelMetric g) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have h : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (modelMetric g) x := by
    apply Tensor.contMDiffAt_clm_iff.mpr
    intro v
    apply Tensor.contMDiffAt_clm_iff.mpr
    intro w
    exact g.contMDiffAt_pairing (modelField_contMDiff v x) (modelField_contMDiff w x)
  exact h.contDiffAt

/-- Evaluating the derivative of the metric coefficients gives the derivative
of its native pairing with constant coordinate fields. -/
theorem modelMetric_fderiv_apply (g : LorentzMetric .timeNegative d E) (x u v w : E) :
    (fderiv ℝ (modelMetric g) x u) v w =
      fderiv ℝ (fun y => g.form y (modelField v y) (modelField w y)) x u := by
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)
  have h := (ev.hasFDerivAt.comp x
    ((modelMetric_contDiff g).differentiable (by simp) x).hasFDerivAt).fderiv
  exact (congrArg (fun L => L u) h).symm

/-- The coordinate action is exactly the intrinsic quadratic action. -/
theorem quadraticAction_eq_mechanics (g : LorentzMetric .timeNegative d E)
    (γ : ℝ → E) (a b : ℝ) :
    quadraticAction g γ a b = Mechanics.action a b (quadraticLagrangian (modelMetric g)) γ := by
  unfold quadraticAction Mechanics.action quadraticLagrangian
  simp_rw [curveVelocity_model, modelMetric_apply]

/-- The Euler–Lagrange covector is minus the metric dual of native acceleration. -/
theorem quadratic_eulerLagrange_native (g : LorentzMetric .timeNegative d E)
    {γ : ℝ → E} {t : ℝ} (hγ : ContDiffAt ℝ 2 γ t) (w : E) :
    Mechanics.eulerLagrange (quadraticLagrangian (modelMetric g)) γ t w =
      -g.form (γ t) (g.covariantAlong (curveVelocity γ) t) (modelField w (γ t)) := by
  rw [quadratic_eulerLagrange (modelMetric g)
    ((modelMetric_contDiff g).of_le (by simp)).contDiffAt hγ (modelMetric_symmetric g)]
  simp only [modelMetric_fderiv_apply, modelMetric_apply]
  have hv : curveVelocity γ = fun s => modelField (deriv γ s) (γ s) := by
    funext s
    exact curveVelocity_model γ s
  have ha : g.covariantAlong (curveVelocity γ) t =
      modelField (deriv (deriv γ) t) (γ t) +
        g.leviCivita (modelField (deriv γ t)) (γ t) (modelField (deriv γ t) (γ t)) := by
    rw [hv]
    exact g.covariantAlong_model γ (deriv γ) t
  have hs : (fun y => g.form y (modelField w y) (modelField (deriv γ t) y)) =
      (fun y => g.form y (modelField (deriv γ t) y) (modelField w y)) := by
    funext y
    exact g.symmetric y _ _
  rw [ha, map_add, add_apply, g.modelField_leviCivita_pairing, hs]
  ring

/-- The actual quadratic action has the native first-variation formula,
including the endpoint pairing for variations that need not vanish there. -/
theorem quadraticAction_hasDerivAt (g : LorentzMetric .timeNegative d E)
    {γ η : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiff ℝ 2 γ) (hη : ContDiff ℝ 2 η) :
    HasDerivAt (fun ε => quadraticAction g (Variational.perturb γ η ε) a b)
      ((g.form (γ b) (curveVelocity γ b) (modelField (η b) (γ b)) -
        g.form (γ a) (curveVelocity γ a) (modelField (η a) (γ a))) +
        ∫ t in a..b, -g.form (γ t) (g.covariantAlong (curveVelocity γ) t)
          (modelField (η t) (γ t))) 0 := by
  have hB : ContDiff ℝ 2 (modelMetric g) := (modelMetric_contDiff g).of_le (by simp)
  have hL : ContDiff ℝ 2 (Function.uncurry (quadraticLagrangian (modelMetric g))) := by
    rw [← contDiffOn_univ]
    simpa using quadraticLagrangian_contDiffOn _ (U := Set.univ) hB.contDiffOn
  simp_rw [quadraticAction_eq_mechanics]
  have hd := Mechanics.hasDerivAt_action_firstVariation (L := quadraticLagrangian (modelMetric g))
    hab hL hγ hη
  rw [Mechanics.firstVariation_eq_boundary_add_integral hL hγ hη] at hd
  simp_rw [quadratic_momentum (modelMetric g) γ _ (hB.differentiable (by norm_num) _)
    (modelMetric_symmetric g _), quadratic_eulerLagrange_native g hγ.contDiffAt] at hd
  simpa only [modelMetric_apply, curveVelocity_model] using hd

/-- In model coordinates, stationarity of the actual action is equivalent to
the native affine geodesic equation, with no causal constraint on variations. -/
theorem quadraticAction_stationary_iff_geodesic (g : LorentzMetric .timeNegative d E)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ) :
    (∀ η : ℝ → E, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => quadraticAction g (Variational.perturb γ η ε) a b) 0 0) ↔
      g.IsGeodesicOn (Ioo a b) γ := by
  simp_rw [quadraticAction_eq_mechanics]
  change Mechanics.Stationary a b (quadraticLagrangian (modelMetric g)) γ ↔ _
  rw [quadratic_stationary_iff (modelMetric g) isOpen_univ
    ((modelMetric_contDiff g).of_le (by simp)).contDiffOn hab hγ (fun _ _ => mem_univ _)]
  constructor
  · intro hel t ht
    refine ⟨(hγ.of_le (by simp)).contMDiff.contMDiffAt, ?_⟩
    apply g.nondegenerate (γ t)
    intro v
    have hw := congrArg (fun L : E →L[ℝ] ℝ => L (NormedSpace.fromTangentSpace (γ t) v))
      (hel t ht)
    rw [quadratic_eulerLagrange_native g hγ.contDiffAt] at hw
    simpa only [modelField, ContinuousLinearEquiv.symm_apply_apply, zero_apply, neg_eq_zero] using hw
  · intro hg t ht
    ext w
    rw [quadratic_eulerLagrange_native g hγ.contDiffAt, (hg t ht).2]
    simp

end ProjectAInos.GeneralRelativity
