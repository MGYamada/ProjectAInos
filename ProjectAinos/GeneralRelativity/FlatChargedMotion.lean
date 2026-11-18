/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.ChargedMotion
public import ProjectAinos.Electrodynamics.LorentzForce
public import ProjectAinos.SmoothGeometry.Lorentzian.FlatTransport
public import ProjectAinos.SmoothGeometry.Lorentzian.Geodesic

/-!
# The flat case of the motion of a charge

On an open set `U` of spacetime with the Minkowski coordinate metric, take the covector field
`potentialCovector A` of a flat potential `A`. The curved equation of motion of
`chargedStationary_iff` is then the flat Lorentz-force equation
`m dU/dt = lorentzForce e (dA) γ̇` of `Electrodynamics.stationary_iff_lorentzForce`, and the two
stationarity notions agree (`chargedStationary_minkowski_iff`): the curved action, varied by
families of curves in `U`, and the flat action, varied in the flat configuration space.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric SpecialRelativity Electrodynamics

local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

/-- The field covector of a flat potential is minus the contraction of its field tensor. -/
theorem fieldCovector_potentialCovector {A : Electrodynamics.Potential} {z : Spacetime}
    (hA : DifferentiableAt ℝ A z) (v : Spacetime) :
    fieldCovector (potentialCovector A) z v = -oneCovector ((fieldTensor A z).curryLeft v) := by
  have hd : fderiv ℝ (potentialCovector A) z = potentialDifferential A z :=
    (hasFDerivAt_potentialCovector hA).fderiv
  ext w
  rw [fieldCovector_apply, hd, neg_apply, oneCovector_curryLeft,
    fieldTensor_apply]
  simp only [potentialDifferential, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  ring

/-- **The flat case of the motion of a charge**: for the Minkowski coordinate metric on an open
set `U` of spacetime, the action of a charge is stationary under the families of curves in `U`
if and only if the flat action is stationary. -/
theorem chargedStationary_minkowski_iff (m e : ℝ) {A : Electrodynamics.Potential}
    {U : Opens Spacetime} (hA : ContDiffOn ℝ 2 A U) {γ : ℝ → U} {a b : ℝ} (hab : a < b)
    (hγ : ContDiff ℝ 2 (fun t => (γ t : Spacetime)))
    (hv : ∀ t ∈ Icc a b, Minkowski.Timelike (deriv (fun s => (γ s : Spacetime)) t)) :
    ChargedStationary (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric m e
        (potentialCovector A) γ a b ↔
      Mechanics.Stationary a b (chargedLagrangian m e A) (fun t => (γ t : Spacetime)) := by
  have hγ' (t : ℝ) : ContMDiffAt 𝓘(ℝ) I 2 γ t :=
    contMDiffAt_iff_contDiffAt_val.mpr hγ.contDiffAt
  have hvel (t : ℝ) : curveVelocity γ t = deriv (fun s => (γ s : Spacetime)) t :=
    curveVelocity_val ((hγ' t).mdifferentiableAt (by norm_num))
  have hS : speedAlong (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric γ =
      fun s => SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) s) := by
    funext s
    unfold speedAlong GeneralRelativity.properSpeed SpecialRelativity.properSpeed
    rw [hvel s, ← Minkowski.intervalQuadratic_convention .timeNegative]
    congr 1
    change -(minkowskiForm .timeNegative 3 _ _) = LorentzConvention.timeSign .timeNegative * _
    rw [show LorentzConvention.timeSign .timeNegative = -1 from rfl]
    ring
  have hv' : ∀ t ∈ uIcc a b,
      Timelike (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric (curveVelocity γ t) := by
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    have h := hv t ht
    have hc := Minkowski.intervalQuadratic_convention .timeNegative
      (deriv (fun s => (γ s : Spacetime)) t)
    rw [show LorentzConvention.timeSign .timeNegative = -1 from rfl] at hc
    unfold Minkowski.Timelike at h
    change minkowskiForm .timeNegative 3 (curveVelocity γ t) (curveVelocity γ t) < 0
    rw [hvel t]
    linarith
  have hcov (t : ℝ) : @Eq Spacetime
      ((minkowski (σ := .timeNegative) (U := U)).toLorentzMetric.covariantAlong
        (curveVelocity γ) t) (deriv (deriv (fun s => (γ s : Spacetime))) t) := by
    have he := physicalChart_mem (γ t)
    have hsrc : γ t ∈ (physicalChart (γ t)).source := by simp
    have hΓ (k i j : Fin 4) :
        (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric.chartChristoffel
        (physicalChart (γ t)) (γ t) k i j = 0 :=
      chartChristoffel_eq_zero_of_minkowskiChart _ he
        (fun y _ v w => by rw [physicalChart_tangentMap, physicalChart_tangentMap]; rfl) hsrc k i j
    have hcomp : (physicalChart (γ t) ∘ γ) = fun s => (γ s : Spacetime) :=
      funext fun s => physicalChart_apply (γ t) (γ s)
    ext k
    have h :=
      (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric.covariantAcceleration_coordinates
      he hsrc (hγ' t) k
    rw [physicalChart_tangentMap, hcomp] at h
    simpa only [hΓ, zero_mul, Finset.sum_const_zero, add_zero] using h
  have hA' : ContDiffOn ℝ 1 (potentialCovector A) U :=
    oneCovector.contDiff.comp_contDiffOn (hA.of_le (by norm_num))
  rw [chargedStationary_iff _ m e hA' hab (fun t _ => hγ' t) hv',
    stationary_iff_lorentzForce m e hab hγ U.isOpen hA (fun t _ => (γ t).2) hv]
  refine forall₂_congr fun t ht => ?_
  have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact ⟨ht.1.le, ht.2.le⟩
  have hSpos : 0 < SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t) := by
    have h := (properSpeed_pos_iff _ _).mpr (hv' t ht')
    change 0 < speedAlong _ γ t at h
    rwa [hS] at h
  have hSd : HasDerivAt
      (fun s => SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) s))
      (deriv (fun s => SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) s)) t)
      t := by
    have h := contDiffAt_speedAlong _ (hγ' t) (hv' t ht')
    rw [hS] at h
    exact (h.differentiableAt one_ne_zero).hasDerivAt
  have hxd : HasDerivAt (deriv (fun s => (γ s : Spacetime)))
      (deriv (deriv (fun s => (γ s : Spacetime))) t) t :=
    ((Mechanics.contDiff_positionVelocity hγ).snd.differentiable one_ne_zero t).hasDerivAt
  have hfour :
      deriv (fun s => SpecialRelativity.fourVelocity (deriv (fun s => (γ s : Spacetime)) s)) t =
      (SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t))⁻¹ •
          deriv (deriv (fun s => (γ s : Spacetime))) t +
        (-deriv (fun s => SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) s)) t /
          SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t) ^ 2) •
          deriv (fun s => (γ s : Spacetime)) t :=
    ((hSd.inv hSpos.ne').smul hxd).deriv
  have hlhs : (m / speedAlong (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric γ t) •
      ((minkowski (σ := .timeNegative) (U := U)).toLorentzMetric.covariantAlong
          (curveVelocity γ) t -
        (deriv (speedAlong (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric γ) t /
          speedAlong (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric γ t) •
          curveVelocity γ t) =
      (m • deriv (fun s => SpecialRelativity.fourVelocity
          (deriv (fun s => (γ s : Spacetime)) s)) t :
        Spacetime) := by
    have key : @Eq Spacetime
        ((m / SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t)) •
          (deriv (deriv (fun s => (γ s : Spacetime))) t -
            (deriv (fun s => SpecialRelativity.properSpeed
                (deriv (fun s => (γ s : Spacetime)) s)) t /
              SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t)) •
              deriv (fun s => (γ s : Spacetime)) t))
        (m • ((SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t))⁻¹ •
            deriv (deriv (fun s => (γ s : Spacetime))) t +
          (-deriv (fun s => SpecialRelativity.properSpeed
              (deriv (fun s => (γ s : Spacetime)) s)) t /
            SpecialRelativity.properSpeed (deriv (fun s => (γ s : Spacetime)) t) ^ 2) •
            deriv (fun s => (γ s : Spacetime)) t)) := by
      ext i
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
      field_simp
      ring
    rw [hcov t, hvel t, hS, hfour]
    exact key
  have hrhs : e • (minkowski (σ := .timeNegative) (U := U)).toLorentzMetric.sharp (γ t)
        (fieldCovector (potentialCovector A) (γ t) (curveVelocity γ t)) =
      (lorentzForce e (fieldTensor A (γ t)) (deriv (fun s => (γ s : Spacetime)) t) :
        Spacetime) := by
    have hAt : DifferentiableAt ℝ A (γ t) :=
      ((hA.contDiffAt (U.isOpen.mem_nhds (γ t).2)).differentiableAt (by norm_num))
    rw [hvel t, fieldCovector_potentialCovector hAt]
    change e • ((minkowski (σ := .timeNegative) (U := U)).toLorentzMetric.sharp (γ t)
        (-oneCovector ((fieldTensor A (γ t)).curryLeft (deriv (fun s => (γ s : Spacetime)) t))) :
          Spacetime) = _
    have key : @Eq Spacetime (e • Minkowski.sharp .timeNegative
        (-oneCovector ((fieldTensor A (γ t)).curryLeft (deriv (fun s => (γ s : Spacetime)) t))))
        (lorentzForce e (fieldTensor A (γ t)) (deriv (fun s => (γ s : Spacetime)) t)) := by
      ext i
      simp only [lorentzForce, Pi.smul_apply, Minkowski.sharp_apply, smul_eq_mul, neg_apply,
        smul_apply]
      ring
    rw [minkowski_sharp]
    exact key
  constructor
  · intro h
    exact hlhs.symm.trans (h.trans hrhs)
  · intro h
    exact hlhs.trans (h.trans hrhs.symm)

end ProjectAinos.GeneralRelativity
