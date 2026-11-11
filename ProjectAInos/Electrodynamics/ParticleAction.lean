module
public import ProjectAInos.Electrodynamics.Field
public import ProjectAInos.SpecialRelativity.ParticleAction

/-! # Charged worldline action on its timelike domain -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity Mechanics

def potentialCovector (A : Potential) (x : Spacetime) : FourCovector := oneCovector (A x)
def potentialDifferential (A : Potential) (x : Spacetime) : Spacetime →L[ℝ] FourCovector :=
  oneCovector.toContinuousLinearMap.comp (fderiv ℝ A x)

theorem hasFDerivAt_potentialCovector {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) :
    HasFDerivAt (potentialCovector A) (potentialDifferential A x) x :=
  oneCovector.toContinuousLinearMap.hasFDerivAt.comp x hA.hasFDerivAt

def chargedLagrangian (m e : ℝ) (A : Potential) : Lagrangian Spacetime :=
  fun t z => freeLagrangian m t z + e * potentialCovector A z.1 z.2

def chargedAction (m e : ℝ) (A : Potential) (γ : ℝ → Spacetime) (a b : ℝ) : ℝ :=
  action a b (chargedLagrangian m e A) γ

def admissibleJets (U : Set Spacetime) : Set (ℝ × (Spacetime × Spacetime)) :=
  {z | z.2.1 ∈ U ∧ Timelike z.2.2}

theorem isOpen_admissibleJets {U : Set Spacetime} (hU : IsOpen U) :
    IsOpen (admissibleJets U) :=
  (hU.preimage (continuous_fst.comp continuous_snd)).inter isOpen_timelikeJets

theorem chargedLagrangian_contDiffOn (m e : ℝ) {A : Potential}
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U) :
    ContDiffOn ℝ 2 (Function.uncurry (chargedLagrangian m e A)) (admissibleJets U) := by
  intro z hz
  have hAx := (hA z.2.1 hz.1).contDiffAt (hU.mem_nhds hz.1)
  have hAbar := oneCovector.contDiff.contDiffAt.comp z.2.1 hAx
  have hfree := (freeLagrangian_contDiffOn m z hz.2).contDiffAt
    (isOpen_timelikeJets.mem_nhds hz.2)
  exact (hfree.add (contDiffAt_const.mul
    ((hAbar.comp z (contDiff_fst.comp contDiff_snd).contDiffAt).clm_apply
      (contDiff_snd.comp contDiff_snd).contDiffAt))).contDiffWithinAt

theorem chargedAction_eq (m e : ℝ) {A : Potential} {γ : ℝ → Spacetime} (a b : ℝ)
    (hγ : ContDiff ℝ 2 γ) (hA : ContinuousOn A (γ '' uIcc a b)) :
    chargedAction m e A γ a b = freeAction m γ a b +
      e * ∫ t in a..b, potentialCovector A (γ t) (deriv γ t) := by
  have hk := properTime_integrable γ a b (fun t _ => hγ.contDiffAt.of_le (by norm_num))
  have hc : ContinuousOn (fun t => potentialCovector A (γ t) (deriv γ t)) (uIcc a b) :=
    (oneCovector.continuous.comp_continuousOn
      (hA.comp hγ.continuous.continuousOn (mapsTo_image _ _))).clm_apply
        (contDiff_positionVelocity hγ).continuous.snd.continuousOn
  rw [chargedAction, action]
  change (∫ t in a..b, -m * properSpeed (deriv γ t) +
    e * potentialCovector A (γ t) (deriv γ t)) = _
  rw [intervalIntegral.integral_add (hk.const_mul (-m))
    (hc.intervalIntegrable.const_mul e), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

theorem hasFDerivAt_chargedLagrangian (m e : ℝ) {A : Potential}
    {z : Spacetime × Spacetime} (hA : DifferentiableAt ℝ A z.1)
    (hv : Timelike z.2) (t : ℝ) :
    HasFDerivAt (chargedLagrangian m e A t)
      ((kineticMomentum m z.2).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime) +
        e • ((potentialCovector A z.1).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime) +
          ((potentialDifferential A z.1).comp (ContinuousLinearMap.fst ℝ Spacetime Spacetime)).flip z.2)) z := by
  exact (hasFDerivAt_freeLagrangian m hv t).add
    ((((hasFDerivAt_potentialCovector hA).comp z hasFDerivAt_fst).clm_apply
      hasFDerivAt_snd).const_mul e)

theorem charged_force (m e : ℝ) {A : Potential} {γ : ℝ → Spacetime} {t : ℝ}
    (hA : DifferentiableAt ℝ A (γ t)) (hv : Timelike (deriv γ t)) :
    force (chargedLagrangian m e A) γ t = e • (potentialDifferential A (γ t)).flip (deriv γ t) := by
  rw [force, (hasFDerivAt_chargedLagrangian m e (z := (γ t, deriv γ t)) hA hv t).fderiv]
  ext w
  simp

theorem charged_momentum (m e : ℝ) {A : Potential} {γ : ℝ → Spacetime} {t : ℝ}
    (hA : DifferentiableAt ℝ A (γ t)) (hv : Timelike (deriv γ t)) :
    momentum (chargedLagrangian m e A) γ t =
      kineticMomentum m (deriv γ t) + e • potentialCovector A (γ t) := by
  rw [momentum, (hasFDerivAt_chargedLagrangian m e (z := (γ t, deriv γ t)) hA hv t).fderiv]
  ext w
  simp

theorem charged_stationary_iff (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (chargedLagrangian m e A) γ ↔
      ∀ t ∈ Ioo a b, eulerLagrange (chargedLagrangian m e A) γ t = 0 :=
  stationary_iff_eulerLagrange_on hab hγ (isOpen_admissibleJets hU)
    (chargedLagrangian_contDiffOn m e hU hA) (fun t ht => ⟨hγU t ht, hv t ht⟩)

end ProjectAInos.Electrodynamics
