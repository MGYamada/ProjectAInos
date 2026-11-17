/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.VacuumAction
public import ProjectAinos.SmoothGeometry.DifferentialForm.InteriorDerivative

/-!
# The action of the field with a prescribed current

For a current three-form `J` on flat space-time the Lagrangian of the field is the vacuum
Lagrangian minus the coefficient of `A ∧ J` (Landau–Lifshitz, *The Classical Theory of
Fields*, §§27–30).

* `hasDerivAt_action`: the derivative of the action along a variation `η` with compact
  support is `−∫ (dη ∧ ⋆F + η ∧ J)`.
* `stationary_iff`: for a `C²` potential and a `C²` current, the action is stationary on an
  open set `U` if and only if `d⋆F + J = 0` on `U`.
* `stationary_iff_excitation`: equivalently `dH = J` with the excitation `H = −⋆F`.
* `lagrangian_zero`: without a current this is the vacuum Lagrangian.

Stationarity is the vanishing of the derivative of the action for all smooth variations with
compact support in `U`. The current is given; it is not varied.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace ProjectAinos.Electrodynamics.SourcedAction

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm
open SpecialRelativity VacuumAction ContinuousLinearMap

/-- The pairing `(a, R) ↦ coefficient (a ∧ R)` of a one-form and a three-form. -/
def sourcePairing : OneForm →L[ℝ] ThreeForm →L[ℝ] ℝ :=
  (postcomp ThreeForm coefficient).comp (wedgeCLM (n := 4) (k := 1) (l := 3))

theorem sourcePairing_apply (a : OneForm) (R : ThreeForm) :
    sourcePairing a R = coefficient (wedgeFiber a R) := rfl

/-- The Lagrangian of the field with the current three-form `J`: the vacuum Lagrangian minus
the coefficient of `A ∧ J`. -/
def lagrangian (J : Form Spacetime 3) : Variational.Lagrangian Spacetime OneForm := fun x z =>
  VacuumAction.lagrangian x z - sourcePairing z.1 (J x)

/-- Without a current the Lagrangian is the vacuum Lagrangian. -/
theorem lagrangian_zero : lagrangian 0 = VacuumAction.lagrangian := by
  funext x z
  simp [lagrangian]

theorem density_eq (J : Form Spacetime 3) (A : Potential) (x : Spacetime) :
    Variational.density (lagrangian J) A x =
      Variational.density VacuumAction.lagrangian A x - sourcePairing (A x) (J x) := rfl

theorem lagrangian_contDiff {J : Form Spacetime 3} (hJ : ContDiff ℝ 2 J) :
    ContDiff ℝ 2 (Function.uncurry (lagrangian J)) := by
  have hW : ContDiff ℝ 2 (fun p : Spacetime × Variational.JetFiber Spacetime OneForm =>
      sourcePairing p.2.1 (J p.1)) :=
    (sourcePairing.contDiff.comp (contDiff_fst.comp contDiff_snd)).clm_apply
      (hJ.comp contDiff_fst)
  exact VacuumAction.lagrangian_contDiff.sub hW

/-- The first variation: that of the vacuum Lagrangian minus the coefficient of `η ∧ J`. -/
theorem firstVariationDensity_eq {J : Form Spacetime 3} (hJ : ContDiff ℝ 2 J) {A η : Potential}
    {x : Spacetime} (hA : DifferentiableAt ℝ A x) (hη : DifferentiableAt ℝ η x) :
    Variational.firstVariationDensity (lagrangian J) A η x =
      -coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) -
        sourcePairing (η x) (J x) := by
  have hd := Variational.hasDerivAt_density (L := lagrangian J) hA hη
    (Variational.differentiable_lagrangian_fiber (lagrangian_contDiff hJ) x _)
  have hv := Variational.hasDerivAt_density (L := VacuumAction.lagrangian) hA hη
    (Variational.differentiable_lagrangian_fiber VacuumAction.lagrangian_contDiff x _)
  rw [VacuumAction.firstVariationDensity_eq hA hη] at hv
  have hs : HasDerivAt (fun ε : ℝ => sourcePairing (Variational.perturb A η ε x) (J x))
      (sourcePairing (η x) (J x)) 0 := by
    have hfun : (fun ε : ℝ => sourcePairing (Variational.perturb A η ε x) (J x)) =
        fun ε => sourcePairing (A x) (J x) + ε * sourcePairing (η x) (J x) := by
      funext ε
      change sourcePairing (A x + ε • η x) (J x) = _
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [hfun]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (sourcePairing (η x) (J x))).const_add
      (sourcePairing (A x) (J x))
  exact hd.unique (hv.sub hs)

/-- The derivative of the action along a variation with compact support. -/
theorem hasDerivAt_action {U : Set Spacetime} {A η : Potential} {J : Form Spacetime 3}
    (hJ : ContDiff ℝ 2 J) (hA : ContDiff ℝ 2 A) (hη : Variational.InteriorVariation U η)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    HasDerivAt (fun ε => Variational.action (volume.restrict U) (lagrangian J)
      (Variational.perturb A η ε))
      (-∫ x in U, (coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) +
        sourcePairing (η x) (J x))) 0 := by
  have h := (Variational.hasDerivAt_action_of_compactSupport (lagrangian_contDiff hJ) hA
    (hη.smooth.of_le (by norm_num)) hη.compact hfin).2
  have hfv : Variational.firstVariation (volume.restrict U) (lagrangian J) A η =
      -∫ x in U, (coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) +
        sourcePairing (η x) (J x)) := by
    rw [Variational.firstVariation, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [firstVariationDensity_eq hJ (hA.differentiable (by norm_num) x)
      (hη.smooth.differentiable (by simp) x)]
    ring
  rwa [hfv] at h

/-- A continuous function that vanishes outside the support of a variation is integrable. -/
theorem integrable_of_eq_zero_off {U : Set Spacetime} {η : Potential}
    (hη : Variational.InteriorVariation U η) {f : Spacetime → ℝ} (hf : Continuous f)
    (h0 : ∀ x, x ∉ tsupport η → f x = 0) : Integrable f volume :=
  hf.integrable_of_hasCompactSupport
    (hη.compact.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (fun x hx => by
        by_contra hn
        exact hx (h0 x hn)) (isClosed_tsupport _)))

/-- The integration by parts: compact support removes the boundary term. -/
theorem weak_form {U : Set Spacetime} {A η : Potential} {J : Form Spacetime 3}
    (hJ : ContDiff ℝ 2 J) (hA : ContDiff ℝ 2 A) (hη : Variational.InteriorVariation U η) :
    (∫ x in U, (coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) +
        sourcePairing (η x) (J x))) =
      ∫ x in U, sourcePairing (η x) (residual A x + J x) := by
  have hG : ContDiff ℝ 1 (fun x => star (fieldTensor A x)) :=
    star.contDiff.comp (exteriorDerivative_contDiff (r := 1) hA)
  have hη1 := hη.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hLc : Continuous fun x =>
      coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) :=
    coefficient.continuous.comp
      (wedge_contDiff (fieldTensor η) _ (exteriorDerivative_contDiff (r := 1) hη1) hG).continuous
  have hRc : Continuous fun x => sourcePairing (η x) (residual A x) :=
    coefficient.continuous.comp
      (wedge_contDiff η (residual A) (hη.smooth.of_le (by simp))
        (exteriorDerivative_contDiff (r := 0) hG)).continuous
  have hSc : Continuous fun x => sourcePairing (η x) (J x) :=
    coefficient.continuous.comp
      (wedge_contDiff η J (hη.smooth.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
        (hJ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num))).continuous
  have hzero (x : Spacetime) (hx : x ∉ tsupport η) : fieldTensor η x = 0 := by
    have hj := Variational.jet_eq_zero_of_notMem_tsupport hx
    change ContinuousAlternatingMap.alternatizeUncurryFin (Variational.jet η x).2 = 0
    rw [hj]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ)
  have hL := integrable_of_eq_zero_off hη hLc fun x hx => by simp [hzero x hx]
  have hR := integrable_of_eq_zero_off hη hRc fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hS := integrable_of_eq_zero_off hη hSc fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [integral_add hL.integrableOn hS.integrableOn, VacuumAction.weak_integrationByParts hA hη,
    ← integral_add (f := fun x => coefficient (wedgeFiber (η x) (VacuumAction.residual A x)))
      hR.integrableOn hS.integrableOn]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [sourcePairing_apply, map_add]

/-- The equation of the field with a current follows from the vanishing of the derivative of
the action against every smooth one-form with compact support in the open region, and
conversely. -/
theorem stationary_iff {U : Set Spacetime} {A : Potential} {J : Form Spacetime 3}
    (hU : IsOpen U) (hA : ContDiff ℝ 2 A) (hJ : ContDiff ℝ 2 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian J) A ↔ ∀ x ∈ U, residual A x + J x = 0 := by
  constructor
  · intro hs x hx
    apply residual_eq_zero_of_pairings
    intro a
    let R : Spacetime → ℝ := fun y => sourcePairing a (residual A y + J y)
    have hG : ContDiff ℝ 1 (fun y => star (fieldTensor A y)) :=
      star.contDiff.comp (exteriorDerivative_contDiff (r := 1) hA)
    have hRc : Continuous R := (sourcePairing a).continuous.comp
      ((exteriorDerivative_contDiff (r := 0) hG).continuous.add hJ.continuous)
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hRc.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet)
      (fun g hg hgK hgU => by
        let η : Potential := fun y => g y • a
        have hsub : tsupport η ⊆ tsupport g :=
          tsupport_comp_subset (g := fun t : ℝ => t • a) (zero_smul ℝ a) g
        have hη : Variational.InteriorVariation U η :=
          ⟨hg.smul contDiff_const, hgK.of_isClosed_subset (isClosed_tsupport _) hsub,
            hsub.trans hgU⟩
        have hv := (hasDerivAt_action hJ hA hη hfin).unique (hs η hη)
        rw [neg_eq_zero, weak_form hJ hA hη] at hv
        have heq : (∫ y in U, sourcePairing (η y) (residual A y + J y)) =
            ∫ y, g y • R y := by
          simp only [η, R, map_smul, smul_apply]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgU h)), zero_smul]
        exact heq.symm.trans hv)
    have hrestrict : R =ᵐ[volume.restrict U] (fun _ => 0) :=
      (ae_restrict_iff' hU.measurableSet).2 hae
    exact Measure.eqOn_open_of_ae_eq hrestrict hU hRc.continuousOn
      continuous_const.continuousOn hx
  · intro h η hη
    have hv := hasDerivAt_action hJ hA hη hfin
    rw [weak_form hJ hA hη] at hv
    have hz : (∫ x in U, sourcePairing (η x) (residual A x + J x)) = 0 :=
      setIntegral_eq_zero_of_ae_eq_zero (.of_forall fun x hx => by simp [h x hx])
    simpa only [hz, neg_zero] using hv

/-- The equation in terms of the excitation `H = −⋆F`: the action is stationary if and only
if `dH = J`. -/
theorem stationary_iff_excitation {U : Set Spacetime} {A : Potential} {J : Form Spacetime 3}
    (hU : IsOpen U) (hA : ContDiff ℝ 2 A) (hJ : ContDiff ℝ 2 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian J) A ↔
      ∀ x ∈ U, exteriorDerivative (fun y => -star (fieldTensor A y)) x = J x := by
  rw [stationary_iff hU hA hJ hfin]
  refine forall₂_congr fun x _ => ?_
  have hneg : exteriorDerivative (fun y => -star (fieldTensor A y)) x = -residual A x := by
    have hfun : (fun y => -star (fieldTensor A y)) =
        (-1 : ℝ) • fun y => star (fieldTensor A y) := by
      funext y
      exact (neg_one_smul ℝ (star (fieldTensor A y))).symm
    change extDeriv (fun y => -star (fieldTensor A y)) x = _
    rw [hfun, extDeriv_smul]
    simp [VacuumAction.residual, exteriorDerivative]
  rw [hneg, neg_eq_iff_add_eq_zero]

/-- Without a current the equation is the vacuum equation. -/
theorem stationary_zero_iff {U : Set Spacetime} {A : Potential} (hU : IsOpen U)
    (hA : ContDiff ℝ 2 A)
    (hfin : Integrable (Variational.density (lagrangian 0) A) (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian 0) A ↔ ∀ x ∈ U, residual A x = 0 := by
  have hJ0 : ContDiff ℝ 2 (0 : Form Spacetime 3) := contDiff_zero_fun
  rw [stationary_iff hU hA hJ0 hfin]
  simp

/-! ### Gauge invariance and the closedness of the current -/

/-- A form of degree zero is a multiple of the unit. -/
theorem scalarForm_apply_eq (χ : Spacetime → ℝ) (x : Spacetime) :
    scalarForm χ x = χ x • (coordinateForm ![] : Spacetime [⋀^Fin 0]→L[ℝ] ℝ) := by
  ext v
  simp [scalarForm, coordinateForm_apply]

/-- The derivative of a function vanishes outside its support. -/
theorem exteriorDerivative_scalarForm_eq_zero {χ : Spacetime → ℝ} {x : Spacetime}
    (hx : x ∉ tsupport χ) : exteriorDerivative (scalarForm χ) x = 0 := by
  apply oneCovector.injective
  rw [scalar_derivative, fderiv_of_notMem_tsupport ℝ hx, map_zero]

/-- The unit of the exterior algebra does not change the coefficient of a top form. -/
theorem coefficient_wedgeFiber_one (R : Spacetime [⋀^Fin (3 + 1)]→L[ℝ] ℝ) :
    coefficient (wedgeFiber (k := 0) (coordinateForm ![] : Spacetime [⋀^Fin 0]→L[ℝ] ℝ) R) =
      coefficient R := by
  have h := wedgeFiber_one_left (n := 3 + 1) (k := 3 + 1) R
  have hc : ∀ (X : Spacetime [⋀^Fin (0 + (3 + 1))]→L[ℝ] ℝ),
      coefficient (covectorDegreeCast (Nat.zero_add (3 + 1)) X) = coefficient X := fun X => rfl
  rw [← hc, h]

/-- The Leibniz rule `d(χ J) = dχ ∧ J + χ dJ` for the coefficient of a top form. -/
theorem coefficient_exteriorDerivative_wedge {χ : Spacetime → ℝ} {J : Form Spacetime 3}
    {x : Spacetime} (hχ : DifferentiableAt ℝ (scalarForm χ) x) (hJ : DifferentiableAt ℝ J x) :
    coefficient (exteriorDerivative (wedge (scalarForm χ) J) x) =
      sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) +
        χ x * coefficient (exteriorDerivative J x) := by
  have hs : exteriorDerivative (wedge (scalarForm χ) J) x =
      wedgeFiber (exteriorDerivative (scalarForm χ) x) (J x) +
        wedgeFiber (scalarForm χ x) (exteriorDerivative J x) := by
    rw [exteriorDerivative_wedge_cast (scalarForm χ) J hχ hJ, pow_zero, one_smul]
    rfl
  rw [hs, map_add, scalarForm_apply_eq, map_smul, LinearMap.smul_apply, map_smul,
    coefficient_wedgeFiber_one, smul_eq_mul, sourcePairing_apply]

/-- Stokes's theorem for a gauge function with compact support:
`∫ dχ ∧ J = −∫ χ dJ`. -/
theorem integral_sourcePairing_exteriorDerivative {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hK : HasCompactSupport χ) {J : Form Spacetime 3} (hJ : ContDiff ℝ 1 J) :
    ∫ x, sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) =
      -∫ x, χ x * coefficient (exteriorDerivative J x) := by
  have hχf : ContDiff ℝ 2 (scalarForm χ) := scalarForm_contDiff hχ
  let P : Form Spacetime 3 := wedge (scalarForm χ) J
  have hP : ContDiff ℝ 1 P := wedge_contDiff _ _ (hχf.of_le (by norm_num)) hJ
  have hPK : HasCompactSupport P := hK.mono fun x hx hzero => hx (by
    simp [P, DifferentialForm.wedge, scalarForm_apply_eq, hzero])
  have hst := integral_exteriorDerivative_basis_zero hP hPK
  change (∫ x, coefficient (exteriorDerivative P x)) = 0 at hst
  have hdχ : Continuous fun x => exteriorDerivative (scalarForm χ) x :=
    (exteriorDerivative_contDiff (r := 1) hχf).continuous
  have hdJ : Continuous fun x => exteriorDerivative J x :=
    (exteriorDerivative_contDiff (r := 0) hJ).continuous
  have hz : ∀ x, x ∉ tsupport χ →
      sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) = 0 := fun x hx => by
    rw [exteriorDerivative_scalarForm_eq_zero hx, map_zero, zero_apply]
  have h1 : Integrable fun x => sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) :=
    ((sourcePairing.continuous.comp hdχ).clm_apply hJ.continuous).integrable_of_hasCompactSupport
      (hK.mono' fun x hx => by
        by_contra hn
        exact hx (hz x hn))
  have h2 : Integrable fun x => χ x * coefficient (exteriorDerivative J x) :=
    (hχ.continuous.mul (coefficient.continuous.comp hdJ)).integrable_of_hasCompactSupport
      hK.mul_right
  have hsum : ∀ x, coefficient (exteriorDerivative P x) =
      sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) +
        χ x * coefficient (exteriorDerivative J x) := fun x =>
    coefficient_exteriorDerivative_wedge (hχf.differentiable (by norm_num) x)
      (hJ.differentiable (by norm_num) x)
  simp_rw [hsum] at hst
  rw [integral_add h1 h2] at hst
  linarith

/-- The action changes under a gauge change with compact support in `U` by `∫ χ dJ`. -/
theorem action_gaugeShift {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 1 A U) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hK : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) {J : Form Spacetime 3}
    (hJ : ContDiff ℝ 1 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    Variational.action (volume.restrict U) (lagrangian J) (gaugeShift A χ) =
      Variational.action (volume.restrict U) (lagrangian J) A +
        ∫ x, χ x * coefficient (exteriorDerivative J x) := by
  have hdχ : Continuous fun x => exteriorDerivative (scalarForm χ) x :=
    (exteriorDerivative_contDiff (r := 1) (scalarForm_contDiff hχ)).continuous
  have hz : ∀ x, x ∉ tsupport χ →
      sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) = 0 := fun x hx => by
    rw [exteriorDerivative_scalarForm_eq_zero hx, map_zero, zero_apply]
  have h1 : Integrable fun x => sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) :=
    ((sourcePairing.continuous.comp hdχ).clm_apply hJ.continuous).integrable_of_hasCompactSupport
      (hK.mono' fun x hx => by
        by_contra hn
        exact hx (hz x hn))
  have heq : ∀ x ∈ U, Variational.density (lagrangian J) (gaugeShift A χ) x =
      Variational.density (lagrangian J) A x -
        sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) := by
    intro x hx
    rw [density_eq, density_eq, VacuumAction.density_eq, VacuumAction.density_eq,
      fieldTensor_gauge_on A χ hU hA hχ.contDiffOn hx]
    change _ - sourcePairing (A x + exteriorDerivative (scalarForm χ) x) (J x) = _
    rw [map_add, add_apply]
    ring
  rw [Variational.action, Variational.action, setIntegral_congr_fun hU.measurableSet heq,
    integral_sub hfin h1.integrableOn,
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hz x fun h => hx (hsub h)),
    integral_sourcePairing_exteriorDerivative hχ hK hJ]
  ring

/-- The action is unchanged by every gauge change with compact support in `U` if and only if
the current is closed on `U`. -/
theorem action_gaugeShift_eq_iff {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 1 A U) {J : Form Spacetime 3} (hJ : ContDiff ℝ 1 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    (∀ χ : Spacetime → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      Variational.action (volume.restrict U) (lagrangian J) (gaugeShift A χ) =
        Variational.action (volume.restrict U) (lagrangian J) A) ↔
      ∀ x ∈ U, exteriorDerivative J x = 0 := by
  have hc : Continuous fun x => coefficient (exteriorDerivative J x) :=
    coefficient.continuous.comp (exteriorDerivative_contDiff (r := 0) hJ).continuous
  constructor
  · intro h x hx
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hc.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet)
      (fun g hg hgK hgU => by
        have hgs := action_gaugeShift hU hA (hg.of_le (by simp)) hgK hgU hJ hfin
        rw [h g hg hgK hgU, left_eq_add] at hgs
        simpa only [smul_eq_mul] using hgs)
    have hrestrict : (fun y => coefficient (exteriorDerivative J y)) =ᵐ[volume.restrict U]
        (fun _ => 0) := (ae_restrict_iff' hU.measurableSet).2 hae
    have hx0 := Measure.eqOn_open_of_ae_eq hrestrict hU hc.continuousOn
      continuous_const.continuousOn hx
    exact topForm_ext_basis (Pi.basisFun ℝ (Fin 4)) (by simpa [coefficient] using hx0)
  · intro h χ hχ hK hsub
    rw [action_gaugeShift hU hA (hχ.of_le (by simp)) hK hsub hJ hfin, add_eq_left]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp [h x hx]
    · simp [image_eq_zero_of_notMem_tsupport fun hm => hx (hsub hm)]

end ProjectAinos.Electrodynamics.SourcedAction
