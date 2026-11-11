module
public import ProjectAInos.Electrodynamics.ParticleAction
public import ProjectAInos.Electrodynamics.LorentzForce
public import ProjectAInos.Mechanics.TotalTimeDerivative

/-! # Gauge transformations of the particle action

The action changes by a genuine endpoint term. C¹ gauge functions suffice
for that identity; C³ regularity supplies a C² transformed Lagrangian.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.DifferentialForm SpecialRelativity Mechanics

theorem continuous_chargedLagrangian (m e : ℝ) {A : Potential} (hA : Continuous A) :
    Continuous (Function.uncurry (chargedLagrangian m e A)) :=
  (continuous_const.mul (properSpeed_continuous.comp (continuous_snd.comp continuous_snd))).add
    (continuous_const.mul (((oneCovector.continuous.comp hA).comp
      (continuous_fst.comp continuous_snd)).clm_apply (continuous_snd.comp continuous_snd)))

theorem chargedLagrangian_gauge (m e : ℝ) (A : Potential) {χ : Spacetime → ℝ}
    (hχ : Differentiable ℝ χ) :
    chargedLagrangian m e (gaugeShift A χ) = chargedLagrangian m e A +
      totalTimeDerivative (fun z : ℝ × Spacetime => e * χ z.2) := by
  funext t z
  have hs : HasFDerivAt (Prod.snd : ℝ × Spacetime → Spacetime)
      (ContinuousLinearMap.snd ℝ ℝ Spacetime) (t, z.1) := hasFDerivAt_snd
  have hd := ((hχ z.1).hasFDerivAt.comp (t, z.1) hs).const_mul e
  have hdf : fderiv ℝ (fun z : ℝ × Spacetime => e * χ z.2) (t, z.1) =
      e • (fderiv ℝ χ z.1).comp (ContinuousLinearMap.snd ℝ ℝ Spacetime) := by
    have he : (fun z : ℝ × Spacetime => e * χ z.2) =
        (fun y : ℝ × Spacetime => e * (χ ∘ Prod.snd) y) := by funext y; rfl
    rw [he]
    exact hd.fderiv
  simp only [chargedLagrangian, potentialCovector, gaugeShift, Pi.add_apply, map_add,
    scalar_derivative, add_apply, totalTimeDerivative, hdf,
    smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change freeLagrangian m t z + e * (oneCovector (A z.1) z.2 + fderiv ℝ χ z.1 z.2) =
    freeLagrangian m t z + e * oneCovector (A z.1) z.2 + e * fderiv ℝ χ z.1 z.2
  ring

theorem chargedAction_gauge (m e : ℝ) {A : Potential} (hA : Continuous A)
    {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 1 χ) {γ : ℝ → Spacetime}
    (hγ : ContDiff ℝ 1 γ) (a b : ℝ) :
    chargedAction m e (gaugeShift A χ) γ a b = chargedAction m e A γ a b +
      e * (χ (γ b) - χ (γ a)) := by
  have hF : ContDiff ℝ 1 (fun z : ℝ × Spacetime => e * χ z.2) :=
    contDiff_const.mul (hχ.comp contDiff_snd)
  rw [chargedAction, chargedLagrangian_gauge m e A (hχ.differentiable one_ne_zero),
    action_add_totalTimeDerivative (continuous_chargedLagrangian m e hA) hF hγ]
  simp only [chargedAction, mul_sub]

theorem stationary_gauge_iff (m e : ℝ) {A : Potential} (hA : Continuous A)
    {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 1 χ) {γ : ℝ → Spacetime}
    (hγ : ContDiff ℝ 1 γ) (a b : ℝ) :
    Stationary a b (chargedLagrangian m e (gaugeShift A χ)) γ ↔
      Stationary a b (chargedLagrangian m e A) γ := by
  rw [chargedLagrangian_gauge m e A (hχ.differentiable one_ne_zero)]
  exact stationary_add_totalTimeDerivative_iff (continuous_chargedLagrangian m e hA)
    (contDiff_const.mul (hχ.comp contDiff_snd)) hγ

/-- A C³ gauge function is required here because its differential is part of
the C² potential entering the action theorem. -/
theorem gaugeShift_contDiffOn {A : Potential} {χ : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (hχ : ContDiffOn ℝ 3 χ U) : ContDiffOn ℝ 2 (gaugeShift A χ) U := by
  intro x hx
  have hχx := scalarForm_contDiffAt ((hχ x hx).contDiffAt (hU.mem_nhds hx))
  have hd := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ).contDiff.contDiffAt.comp x
    (hχx.fderiv_right (m := 2) (by norm_num))
  exact (((hA x hx).contDiffAt (hU.mem_nhds hx)).add hd).contDiffWithinAt

/-- Gauge stationarity on an arbitrary open potential domain. Neither A nor χ
has to be smooth outside that domain. -/
theorem stationary_gauge_iff_on (m e : ℝ) {A : Potential} {χ : Spacetime → ℝ}
    {U : Set Spacetime} {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ) (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) (hχ : ContDiffOn ℝ 3 χ U)
    (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hv : ∀ t ∈ Icc a b, Minkowski.Timelike (deriv γ t)) :
    Stationary a b (chargedLagrangian m e (gaugeShift A χ)) γ ↔
      Stationary a b (chargedLagrangian m e A) γ := by
  rw [stationary_iff_lorentzForce m e hab hγ hU (gaugeShift_contDiffOn hU hA hχ) hγU hv,
    stationary_iff_lorentzForce m e hab hγ hU hA hγU hv]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  rw [fieldTensor_gauge_on A χ hU (hA.of_le (by norm_num)) (hχ.of_le (by norm_num))
    (hγU t ⟨ht.1.le, ht.2.le⟩)]

/-- The endpoint formula also holds when the potential is only continuous on
the path image and the gauge function is C¹ on its open domain. -/
theorem chargedAction_gauge_on (m e : ℝ) {A : Potential} {χ : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContinuousOn A U)
    (hχ : ContDiffOn ℝ 1 χ U) {γ : ℝ → Spacetime} (hγ : ContDiff ℝ 2 γ)
    (a b : ℝ) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) :
    chargedAction m e (gaugeShift A χ) γ a b = chargedAction m e A γ a b +
      e * (χ (γ b) - χ (γ a)) := by
  have hχAt (t : ℝ) (ht : t ∈ uIcc a b) : ContDiffAt ℝ 1 χ (γ t) :=
    (hχ _ (hγU t ht)).contDiffAt (hU.mem_nhds (hγU t ht))
  have hD : ContinuousOn (fun t => fderiv ℝ χ (γ t) (deriv γ t)) (uIcc a b) := by
    intro t ht
    exact ((((hχAt t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.comp
      hγ.continuous.continuousAt).clm_apply
      (contDiff_positionVelocity hγ).continuous.snd.continuousAt).continuousWithinAt
  have hftc : (∫ t in a..b, fderiv ℝ χ (γ t) (deriv γ t)) = χ (γ b) - χ (γ a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => ((hχAt t ht).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t
        (hγ.differentiable (by norm_num) t).hasDerivAt) hD.intervalIntegrable
  have hAline : ContinuousOn (fun t => potentialCovector A (γ t) (deriv γ t)) (uIcc a b) :=
    (oneCovector.continuous.comp_continuousOn (hA.comp hγ.continuous.continuousOn hγU)).clm_apply
      (contDiff_positionVelocity hγ).continuous.snd.continuousOn
  have hfree := properTime_integrable γ a b (fun t _ => hγ.contDiffAt.of_le (by norm_num))
  have hL := (hfree.const_mul (-m)).add (hAline.intervalIntegrable.const_mul e)
  change IntervalIntegrable (fun t => chargedLagrangian m e A t (γ t, deriv γ t))
    MeasureTheory.volume a b at hL
  have he (t : ℝ) : chargedLagrangian m e (gaugeShift A χ) t (γ t, deriv γ t) =
      chargedLagrangian m e A t (γ t, deriv γ t) + e * fderiv ℝ χ (γ t) (deriv γ t) := by
    simp only [chargedLagrangian, potentialCovector, gaugeShift, Pi.add_apply, map_add,
      scalar_derivative, add_apply]
    ring
  unfold chargedAction action
  simp_rw [he]
  rw [intervalIntegral.integral_add hL (hD.intervalIntegrable.const_mul e),
    intervalIntegral.integral_const_mul, hftc]

end ProjectAInos.Electrodynamics
