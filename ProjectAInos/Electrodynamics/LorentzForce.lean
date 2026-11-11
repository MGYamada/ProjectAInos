module
public import ProjectAInos.Electrodynamics.ParticleAction
public import ProjectAInos.Electrodynamics.Invariants

/-! # Lorentz force from the charged-particle action

For an arbitrary timelike parameter the equation reads m dU/ds = e F♯(γ̇).
In proper time γ̇ = U, giving m dU/dτ = e F♯(U). The minus sign in the
interior-product expression comes from raising the *first* index of F.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity Mechanics

def lorentzForce (e : ℝ) (F : TwoForm) (v : Spacetime) : Spacetime :=
  sharp .timeNegative (-e • oneCovector (F.curryLeft v))

theorem lorentzForce_lowered (e : ℝ) (F : TwoForm) (v w : Spacetime) :
    minkowskiForm .timeNegative 3 (lorentzForce e F v) w = -e * F ![v, w] := by
  change flat .timeNegative (sharp .timeNegative (-e • oneCovector (F.curryLeft v))) w = _
  rw [show flat .timeNegative (sharp .timeNegative (-e • oneCovector (F.curryLeft v))) =
    -e • oneCovector (F.curryLeft v) from (flat .timeNegative).apply_symm_apply _]
  change -e * oneCovector (F.curryLeft v) w = _
  rw [oneCovector_curryLeft]

theorem lorentzForce_orthogonal (e : ℝ) (F : TwoForm) (v : Spacetime) :
    minkowskiForm .timeNegative 3 (lorentzForce e F v) v = 0 := by
  rw [lorentzForce_lowered]
  have h := twoForm_swap F v v
  have hz : F ![v, v] = 0 := by linarith
  rw [hz, mul_zero]

@[simp] theorem lorentzForce_zero_charge (F : TwoForm) (v : Spacetime) :
    lorentzForce 0 F v = 0 := by simp [lorentzForce]

/-- Unit four-velocity lies on the mass shell, independently of the force law. -/
theorem mass_shell (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    minkowskiForm .timeNegative 3 (m • fourVelocity v) (m • fourVelocity v) = -(m ^ 2) := by
  simp [fourVelocity_metric hv, pow_two]

theorem hasDerivAt_kineticMomentum (m : ℝ) {γ : ℝ → Spacetime} {t : ℝ}
    (hγ : ContDiff ℝ 2 γ) (hv : Timelike (deriv γ t)) :
    HasDerivAt (fun s => kineticMomentum m (deriv γ s))
      (m • flat .timeNegative (deriv (fun s => fourVelocity (deriv γ s)) t)) t := by
  have hd : DifferentiableAt ℝ (fun s => fourVelocity (deriv γ s)) t :=
    ((contDiffAt_fourVelocity hv (n := 1)).comp t
      ((contDiff_positionVelocity hγ).snd.contDiffAt)).differentiableAt one_ne_zero
  exact ((flat .timeNegative).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    hd.hasDerivAt).const_smul m

theorem eulerLagrange_charged (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {t : ℝ} (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U) (ht : γ t ∈ U)
    (hv : Timelike (deriv γ t)) :
    eulerLagrange (chargedLagrangian m e A) γ t =
      flat .timeNegative (lorentzForce e (fieldTensor A (γ t)) (deriv γ t) -
        m • deriv (fun s => fourVelocity (deriv γ s)) t) := by
  have hAt : DifferentiableAt ℝ A (γ t) :=
    ((hA _ ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hem : momentum (chargedLagrangian m e A) γ =ᶠ[𝓝 t]
      fun s => kineticMomentum m (deriv γ s) + e • potentialCovector A (γ s) := by
    filter_upwards [(continuous_pathJet hγ).continuousAt.preimage_mem_nhds
      ((isOpen_admissibleJets hU).mem_nhds (show pathJet γ t ∈ admissibleJets U from ⟨ht, hv⟩))]
      with s hs
    exact charged_momentum m e
      (((hA _ hs.1).contDiffAt (hU.mem_nhds hs.1)).differentiableAt (by norm_num)) hs.2
  have hdA := (hasFDerivAt_potentialCovector hAt).comp_hasDerivAt t
    (hγ.differentiable (by norm_num) t).hasDerivAt
  have hdm : deriv (fun s => kineticMomentum m (deriv γ s) + e • potentialCovector A (γ s)) t =
      m • flat .timeNegative (deriv (fun s => fourVelocity (deriv γ s)) t) +
        e • potentialDifferential A (γ t) (deriv γ t) := by
    have he : (fun s => kineticMomentum m (deriv γ s) + e • potentialCovector A (γ s)) =
        (fun s => kineticMomentum m (deriv γ s)) + e • (potentialCovector A ∘ γ) := by
      funext s
      rfl
    rw [he]
    exact ((hasDerivAt_kineticMomentum m hγ hv).add (hdA.const_smul e)).deriv
  rw [eulerLagrange, charged_force m e hAt hv, hem.deriv_eq, hdm]
  ext w
  simp only [sub_apply, smul_apply, ContinuousLinearMap.flip_apply, add_apply,
    smul_eq_mul, map_sub, map_smul]
  simp only [flat_apply]
  rw [lorentzForce_lowered, fieldTensor_apply]
  simp only [potentialDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  ring

/-- The equation is derived from the derivative of the actual action. No
comparison principle or equation of motion is included in `Stationary`. -/
theorem stationary_iff_lorentzForce (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (chargedLagrangian m e A) γ ↔
      ∀ t ∈ Ioo a b, m • deriv (fun s => fourVelocity (deriv γ s)) t =
        lorentzForce e (fieldTensor A (γ t)) (deriv γ t) := by
  rw [charged_stationary_iff m e hab hγ hU hA hγU hv]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro ht
  rw [eulerLagrange_charged m e hγ hU hA (hγU t ⟨ht.1.le, ht.2.le⟩)
    (hv t ⟨ht.1.le, ht.2.le⟩), map_eq_zero_iff, sub_eq_zero, eq_comm]
  exact (flat .timeNegative).injective

/-- Positive mass turns the zero-charge equation into constant four-velocity. -/
theorem zero_charge_acceleration {m : ℝ} (hm : 0 < m) {F : TwoForm}
    {v a : Spacetime} (h : m • a = lorentzForce 0 F v) : a = 0 := by
  rw [lorentzForce_zero_charge] at h
  exact (smul_eq_zero.mp h).resolve_left (ne_of_gt hm)

/-- Component form, with the first index of F raised and the velocity lowered. -/
theorem lorentzForce_component (e : ℝ) (F : TwoForm) (v : Spacetime) (μ : Fin 4) :
    lorentzForce e F v μ = e * ∑ ν : Fin 4,
      raisedComponent F μ ν * flat .timeNegative v (Pi.single ν 1) := by
  rw [twoForm_expansion F]
  simp only [lorentzForce, sharp_apply, smul_apply, smul_eq_mul, oneCovector_curryLeft]
  fin_cases μ <;>
    simp [raisedComponent, component, twoFormExpansion, DifferentialForm.coordinateForm_apply,
      Matrix.det_fin_two, Pi.single_apply, Fin.sum_univ_succ, lorentzSign, flat_apply,
      minkowskiForm_apply]
  all_goals ring_nf
  all_goals simp

/-- Proper-time form: U = γ̇ and m dU/dτ = e F^{μν} U_ν. -/
theorem stationary_properTime (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U) (hγU : ∀ t ∈ Icc a b, γ t ∈ U)
    (hunit : ∀ t ∈ Icc a b, intervalQuadratic (deriv γ t) = 1)
    (hs : Stationary a b (chargedLagrangian m e A) γ) {t : ℝ} (ht : t ∈ Ioo a b) :
    m • deriv (deriv γ) t = lorentzForce e (fieldTensor A (γ t)) (deriv γ t) := by
  have hv : ∀ s ∈ Icc a b, Timelike (deriv γ s) := by
    intro s hs
    change 0 < intervalQuadratic (deriv γ s)
    rw [hunit s hs]
    norm_num
  have h := (stationary_iff_lorentzForce m e hab hγ hU hA hγU hv).mp hs t ht
  have he : (fun s => fourVelocity (deriv γ s)) =ᶠ[𝓝 t] deriv γ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    simp [fourVelocity, properSpeed, hunit s ⟨hs.1.le, hs.2.le⟩]
  rw [he.deriv_eq] at h
  exact h

end ProjectAInos.Electrodynamics
