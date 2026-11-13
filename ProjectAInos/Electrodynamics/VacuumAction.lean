/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Field
public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeFlat
public import ProjectAInos.SmoothGeometry.DifferentialForm.WedgeAlgebra
public import ProjectAInos.SmoothGeometry.DifferentialForm.CompactStokes
public import ProjectAInos.Variational.EulerLagrange

/-! # Vacuum Maxwell action on a flat spacetime region -/

@[expose] public section
noncomputable section

open MeasureTheory Set Module exteriorPower ContinuousLinearMap
open scoped ContDiff

namespace ProjectAInos.Electrodynamics.VacuumAction

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm
open SpecialRelativity

abbrev ThreeForm := Spacetime [⋀^Fin 3]→L[ℝ] ℝ
abbrev TopForm := Spacetime [⋀^Fin 4]→L[ℝ] ℝ

/-- The standard time-first oriented coefficient of a four-form. -/
def coefficient : TopForm →L[ℝ] ℝ :=
  ContinuousAlternatingMap.apply ℝ Spacetime ℝ (Pi.basisFun ℝ (Fin 4))

theorem coefficient_wedge_eq_pairing {k l : ℕ} (h : k + l = 4)
    (α : Spacetime [⋀^Fin k]→L[ℝ] ℝ) (β : Spacetime [⋀^Fin l]→L[ℝ] ℝ) :
    coefficient (covectorDegreeCast h (wedgeFiber α β)) =
      wedgePairing (Minkowski.volume .standard 3)
        (h.trans (by simp [MinkowskiModel])) (toExterior α) (toExterior β) := by
  let b := (Pi.basisFun ℝ (Fin 4)).dualBasis
  have hdim : k + l = Module.finrank ℝ (Dual ℝ (MinkowskiModel 3)) :=
    h.trans (by simp [MinkowskiModel])
  change coefficient (covectorDegreeCast h (wedgeFiber α β)) =
    (hdim.symm ▸ (basisVolume b).toLinearMap)
      (exteriorPower.wedge ℝ (Dual ℝ Spacetime) k l (toExterior α) (toExterior β))
  rw [basisVolume, basisVolumeDegree_cast b hdim]
  have aux : ∀ {d : ℕ} (hd : d = 4) (f : Spacetime [⋀^Fin d]→L[ℝ] ℝ),
      coefficient (covectorDegreeCast hd f) = basisVolumeDegree b d hd (toExterior f) := by
    intro d hd f
    subst d
    exact (Minkowski.coordinateVolume_toExterior 4 f).symm
  rw [aux h, toExterior_wedgeFiber]

/-- The quadratic density is built from the existing Hodge and exterior maps. -/
def lagrangian : Variational.Lagrangian Spacetime OneForm := fun _ z =>
  let F : TwoForm := ContinuousAlternatingMap.alternatizeUncurryFin z.2
  (-1 / 2 : ℝ) * coefficient (wedgeFiber F (star F))

theorem density_eq (A : Potential) (x : Spacetime) :
    Variational.density lagrangian A x =
      -(1 / 2 : ℝ) * coefficient (wedgeFiber (fieldTensor A x) (star (fieldTensor A x))) := by
  simp only [Variational.density, Variational.jet, lagrangian, fieldTensor,
    exteriorDerivative, extDeriv, neg_div]

theorem lagrangian_contDiff : ContDiff ℝ 2 (Function.uncurry lagrangian) := by
  let W : TwoForm →L[ℝ] TwoForm →L[ℝ] ℝ :=
    (postcomp TwoForm coefficient).comp (wedgeCLM (n := 4) (k := 2) (l := 2))
  let D : (Spacetime →L[ℝ] OneForm) →L[ℝ] TwoForm :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ (n := 1)
  have hproj : ContDiff ℝ 2 (fun z : Spacetime × Variational.JetFiber Spacetime OneForm =>
      z.2.2) := contDiff_snd.comp contDiff_snd
  have hF : ContDiff ℝ 2 (fun z : Spacetime × Variational.JetFiber Spacetime OneForm =>
      D z.2.2) := by
    exact (ContinuousLinearMap.contDiff D).comp hproj
  have h := (contDiff_const (c := -(1 / 2 : ℝ))).mul
    ((W.contDiff.comp hF).clm_apply (star.contDiff.comp hF))
  change ContDiff ℝ 2 (fun z : Spacetime × Variational.JetFiber Spacetime OneForm =>
    (-(1 / 2 : ℝ)) * W (D z.2.2) (star (D z.2.2))) at h
  convert h using 1
  funext z
  simp only [lagrangian, Function.uncurry, neg_div]
  rfl

theorem pairing_symm (a b : TwoForm) :
    coefficient (wedgeFiber a (star b)) = coefficient (wedgeFiber b (star a)) := by
  have h := coefficient_wedge_eq_pairing (k := 2) (l := 2) rfl
  change coefficient (covectorDegreeCast rfl (wedgeFiber a (star b))) =
    coefficient (covectorDegreeCast rfl (wedgeFiber b (star a)))
  rw [h, h]
  change wedgePairing _ _ (toExterior a) (toExterior (hodgeFiber .timeNegative .standard
    (by decide : 2 + 2 = 3 + 1) b)) =
    wedgePairing _ _ (toExterior b) (toExterior (hodgeFiber .timeNegative .standard
      (by decide : 2 + 2 = 3 + 1) a))
  rw [hodgeFiber_pairing, hodgeFiber_pairing]
  exact (exteriorPower_symmetric _ (coMetric_symmetric .timeNegative 3) 2).eq _ _

theorem firstVariationDensity_eq {A η : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (hη : DifferentiableAt ℝ η x) :
    Variational.firstVariationDensity lagrangian A η x =
      -coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) := by
  let F := fieldTensor A x
  let G := fieldTensor η x
  let W : TwoForm →L[ℝ] TwoForm →L[ℝ] ℝ :=
    (postcomp TwoForm coefficient).comp (wedgeCLM (n := 4) (k := 2) (l := 2))
  have hp (ε : ℝ) : fieldTensor (Variational.perturb A η ε) x = F + ε • G := by
    change extDeriv (A + ε • η) x = _
    rw [extDeriv_add hA (hη.const_smul ε), extDeriv_smul]
    rfl
  have hquad (ε : ℝ) :
      Variational.density lagrangian (Variational.perturb A η ε) x =
        -(1 / 2 : ℝ) * (W F (star F) + ε * (W G (star F) + W F (star G)) +
          ε ^ 2 * W G (star G)) := by
    rw [density_eq, hp]
    change -(1 / 2 : ℝ) * W (F + ε • G) (star (F + ε • G)) = _
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hd := Variational.hasDerivAt_density (L := lagrangian) hA hη
    (Variational.differentiable_lagrangian_fiber lagrangian_contDiff x _)
  simp_rw [hquad] at hd
  have hpoly : HasDerivAt (fun ε : ℝ =>
      -(1 / 2 : ℝ) * (W F (star F) + ε * (W G (star F) + W F (star G)) +
        ε ^ 2 * W G (star G)))
      (-(1 / 2 : ℝ) * (W G (star F) + W F (star G))) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).mul_const (W G (star F) + W F (star G))).const_add
      (W F (star F)) |>.add (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (W G (star G)))
        |>.const_mul (-(1 / 2 : ℝ))) using 1 <;> simp
  rw [hd.unique hpoly]
  have hs : W F (star G) = W G (star F) := pairing_symm F G
  rw [hs]
  change _ = -W G (star F)
  ring

/-- The actual compact-support action derivative, with its exterior variation integrand. -/
theorem hasDerivAt_action {U : Set Spacetime} {A η : Potential}
    (hA : ContDiff ℝ 2 A) (hη : Variational.InteriorVariation U η)
    (hfin : Integrable (Variational.density lagrangian A) (volume.restrict U)) :
    HasDerivAt (fun ε => Variational.action (volume.restrict U) lagrangian
      (Variational.perturb A η ε))
      (-∫ x in U, coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x)))) 0 := by
  have h := (Variational.hasDerivAt_action_of_compactSupport lagrangian_contDiff hA
    (hη.smooth.of_le (by norm_num)) hη.compact hfin).2
  simpa only [Variational.firstVariation, firstVariationDensity_eq
    (hA.differentiable (by norm_num) _) (hη.smooth.differentiable (by simp) _), integral_neg] using h

/-- The vacuum equation is the exterior derivative of the Hodge dual of the curvature. -/
def residual (A : Potential) : Form Spacetime 3 :=
  exteriorDerivative (fun x => star (fieldTensor A x))

/-- Compact support removes the boundary integral of the three-form. -/
theorem weak_integrationByParts {U : Set Spacetime} {A η : Potential}
    (hA : ContDiff ℝ 2 A) (hη : Variational.InteriorVariation U η) :
    (∫ x in U, coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x)))) =
      ∫ x in U, coefficient (wedgeFiber (η x) (residual A x)) := by
  let G : Field := fun x => star (fieldTensor A x)
  have hG : ContDiff ℝ 1 G :=
    star.contDiff.comp (exteriorDerivative_contDiff (r := 1) hA)
  let P : Form Spacetime 3 := wedge η G
  have hP : ContDiff ℝ 1 P := wedge_contDiff η G (hη.smooth.of_le (by simp)) hG
  have hPK : HasCompactSupport P := hη.compact.mono fun x hx hzero =>
    hx (by simp [P, DifferentialForm.wedge, hzero])
  have hG0 := hG.differentiable one_ne_zero
  have hη1 := hη.smooth.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hη0 := hη.smooth.differentiable (by simp)
  let L : Spacetime → ℝ := fun x => coefficient (wedgeFiber (fieldTensor η x) (G x))
  let R : Spacetime → ℝ := fun x => coefficient (wedgeFiber (η x) (residual A x))
  have hs (x : Spacetime) : coefficient (exteriorDerivative P x) = L x - R x := by
    rw [show exteriorDerivative P x = wedgeFiber (fieldTensor η x) (G x) -
        wedgeFiber (η x) (residual A x) by
      have hw := exteriorDerivative_wedge_cast η G (hη0 x) (hG0 x)
      change exteriorDerivative P x = _
      change exteriorDerivative (DifferentialForm.wedge η G) x =
        wedgeFiber (exteriorDerivative η x) (G x) -
          wedgeFiber (η x) (exteriorDerivative G x)
      have hsign (a : TopForm) : (-1 : ℝ) ^ (1 : ℕ) • a = -a := by
        rw [pow_one]
        exact neg_one_smul ℝ a
      simpa only [covectorDegreeCast, hsign, sub_eq_add_neg] using hw]
    rw [map_sub]
  have hL : Continuous L := coefficient.continuous.comp
    (wedge_contDiff (fieldTensor η) G (exteriorDerivative_contDiff (r := 1) hη1) hG).continuous
  have hR : Continuous R := coefficient.continuous.comp
    (wedge_contDiff η (residual A) (hη.smooth.of_le (by simp))
      (exteriorDerivative_contDiff (r := 0) hG)).continuous
  have hzero (x : Spacetime) (hx : x ∉ tsupport η) : fieldTensor η x = 0 := by
    have hj := Variational.jet_eq_zero_of_notMem_tsupport hx
    change ContinuousAlternatingMap.alternatizeUncurryFin (Variational.jet η x).2 = 0
    rw [hj]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Spacetime ℝ)
  have hLs : Function.support L ⊆ tsupport η := by
    intro x hx
    by_contra hn
    exact hx (by simp [L, hzero x hn])
  have hRs : Function.support R ⊆ tsupport η := by
    intro x hx
    by_contra hn
    exact hx (by simp [R, image_eq_zero_of_notMem_tsupport hn])
  have hLi : Integrable L volume := hL.integrable_of_hasCompactSupport
    (hη.compact.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hLs (isClosed_tsupport _)))
  have hRi : Integrable R volume := hR.integrable_of_hasCompactSupport
    (hη.compact.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hRs (isClosed_tsupport _)))
  have hst := integral_exteriorDerivative_basis_zero hP hPK
  change (∫ x, coefficient (exteriorDerivative P x)) = 0 at hst
  simp_rw [hs] at hst
  rw [integral_sub hLi hRi, sub_eq_zero] at hst
  change (∫ x in U, L x) = ∫ x in U, R x
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    by_contra hn
    exact hx (hη.interior (hLs hn))),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra hn
      exact hx (hη.interior (hRs hn)))]
  exact hst

/-- Vanishing of all pairings with one-forms detects the entire three-form. -/
theorem residual_eq_zero_of_pairings (R : ThreeForm)
    (h : ∀ a : OneForm, coefficient (wedgeFiber a R) = 0) : R = 0 := by
  let hdim : 1 + 3 = Module.finrank ℝ (Dual ℝ (MinkowskiModel 3)) := by
    simp [MinkowskiModel]
  let B := wedgePairing (Minkowski.volume .standard 3) hdim
  have : B.flip.IsPerfPair := by
    dsimp [B]
    infer_instance
  have hz : B.flip (toExterior R) = 0 := by
    apply LinearMap.ext
    intro a
    obtain ⟨v, rfl⟩ := (toExterior (n := 4) (k := 1)).surjective a
    have hw := coefficient_wedge_eq_pairing (k := 1) (l := 3) rfl v R
    change B (toExterior v) (toExterior R) = 0
    exact hw.symm.trans (h v)
  apply toExterior.injective
  apply B.flip.toPerfPair.injective
  apply LinearMap.ext
  intro a
  rw [LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply, map_zero, map_zero]
  exact LinearMap.congr_fun hz a

/-- Vacuum Maxwell follows from the vanishing action derivative against every
smooth compactly supported one-form in the open integration region. -/
theorem stationary_iff_residual_zero {U : Set Spacetime} {A : Potential}
    (hU : IsOpen U) (hA : ContDiff ℝ 2 A)
    (hfin : Integrable (Variational.density lagrangian A) (volume.restrict U)) :
    Variational.Stationary volume U lagrangian A ↔ ∀ x ∈ U, residual A x = 0 := by
  constructor
  · intro hs x hx
    apply residual_eq_zero_of_pairings
    intro a
    let R : Spacetime → ℝ := fun y => coefficient (wedgeFiber a (residual A y))
    have hG : ContDiff ℝ 1 (fun y => star (fieldTensor A y)) :=
      star.contDiff.comp (exteriorDerivative_contDiff (r := 1) hA)
    have hR : Continuous R := coefficient.continuous.comp
      (wedge_contDiff (fun _ => a) (residual A) contDiff_const
        (exteriorDerivative_contDiff (r := 0) hG)).continuous
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hR.continuousOn.locallyIntegrableOn (μ := volume) hU.measurableSet)
      (fun g hg hgK hgU => by
        let η : Potential := fun y => g y • a
        have hsub : tsupport η ⊆ tsupport g :=
          tsupport_comp_subset (g := fun t : ℝ => t • a) (zero_smul ℝ a) g
        have hη : Variational.InteriorVariation U η :=
          ⟨hg.smul contDiff_const, hgK.of_isClosed_subset (isClosed_tsupport _) hsub,
            hsub.trans hgU⟩
        have hv := (hasDerivAt_action hA hη hfin).unique (hs η hη)
        rw [neg_eq_zero, weak_integrationByParts hA hη] at hv
        have heq : (∫ y in U, coefficient (wedgeFiber (η y) (residual A y))) =
            ∫ y, g y • R y := by
          simp only [η, R, map_smul, LinearMap.smul_apply]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgU h)), zero_smul]
        exact heq.symm.trans hv)
    have hrestrict : R =ᵐ[volume.restrict U] (fun _ => 0) :=
      (ae_restrict_iff' hU.measurableSet).2 hae
    exact Measure.eqOn_open_of_ae_eq hrestrict hU hR.continuousOn continuous_const.continuousOn hx
  · intro h η hη
    have hv := hasDerivAt_action hA hη hfin
    rw [weak_integrationByParts hA hη] at hv
    have hz : (∫ x in U, coefficient (wedgeFiber (η x) (residual A x))) = 0 :=
      setIntegral_eq_zero_of_ae_eq_zero (.of_forall fun x hx => by simp [h x hx])
    simpa only [hz, neg_zero] using hv

/-- For a potential, the homogeneous equation holds throughout the region.
Stationarity supplies the other vacuum equation. -/
theorem stationary_iff_vacuum {U : Set Spacetime} {A : Potential}
    (hU : IsOpen U) (hA : ContDiff ℝ 2 A)
    (hfin : Integrable (Variational.density lagrangian A) (volume.restrict U)) :
    Variational.Stationary volume U lagrangian A ↔
      ∀ x ∈ U, exteriorDerivative (fieldTensor A) x = 0 ∧ residual A x = 0 := by
  rw [stationary_iff_residual_zero hU hA hfin]
  exact ⟨fun h x hx => ⟨bianchi_on A hU hA.contDiffOn hx, h x hx⟩,
    fun h x hx => (h x hx).2⟩

/-- The action is unchanged by the already verified exact gauge shift. -/
theorem action_gauge {U : Set Spacetime} (hU : IsOpen U) (A : Potential)
    (χ : Spacetime → ℝ) (hA : ContDiffOn ℝ 1 A U) (hχ : ContDiffOn ℝ 2 χ U) :
    Variational.action (volume.restrict U) lagrangian (gaugeShift A χ) =
      Variational.action (volume.restrict U) lagrangian A := by
  apply setIntegral_congr_fun hU.measurableSet
  intro x hx
  rw [density_eq, density_eq, fieldTensor_gauge_on A χ hU hA hχ hx]

end ProjectAInos.Electrodynamics.VacuumAction
