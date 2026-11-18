/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinatePotential
public import ProjectAinos.Electrodynamics.CurvedComponents
public import ProjectAinos.Electrodynamics.MatterCurrent
public import ProjectAinos.Electrodynamics.Covariance
public import ProjectAinos.Electrodynamics.HilbertStress
public import ProjectAinos.Electrodynamics.ParticleAction

/-!
# The action of the field on a curved background

Landau–Lifshitz, §90. The background is a coordinate metric `g` on an open set `U` of the model
space, held fixed during the variation; the potential `A` is a field of covectors smooth on `U`
and the current is prescribed. The action is that of `CoordinateMetric.potentialAction`, with the
density `(−¼ F_{ab} F^{ab} − A_b j^b) √|g|`.

* `potentialStationary_iff_sourced`: the action is stationary under every smooth variation with
  compact support in `U` if and only if the native field `F` with the components
  `∂_a A_b − ∂_b A_a` satisfies the sourced equation `dH = J` of `Curved.Maxwell`, with
  `H = −⋆F` and `J = ⋆(j♭)`; with `dF = 0` this is the system `Curved.Maxwell`
  (`maxwell_iff_potentialStationary`). With the positive coupling `+A_b k^b` of a matter current
  `k` the source is `−k` (`potentialStationary_matter_iff`).
* `potentialDensity_minkowski`, `potentialAction_minkowski`: for the Minkowski coordinate metric
  and the covector field of a flat potential, the density and the relative action are those of
  the flat sourced functional `SourcedAction.lagrangian` with the current form `ι_j vol`, in the
  time-first orientation and with the density `√|g| = 1`.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.DifferentialForm

namespace Curved

variable {U : Opens (MinkowskiModel 3)}

/-- **The sourced Maxwell equation from the action on a curved background**: the action of the
potential is stationary under every smooth variation with compact support in `U` if and only if
`dH = J` for the native field `F = dA` and the native current `j`. -/
theorem potentialStationary_iff_sourced (g : CoordinateMetric .timeNegative 3 U)
    (o : OrientedAtlas 4 U) {A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ}
    (hA : ContDiffOn ℝ ∞ A U) (F : Field (M := U))
    (hF : ∀ (y : U) (a b : Fin 4), F y ![Pi.single a 1, Pi.single b 1] =
      CoordinateMetric.potentialField A y a b)
    (j : CurrentVector (M := U)) {jc : MinkowskiModel 3 → Fin 4 → ℝ}
    (hj : ∀ (y : U) (b : Fin 4), (j y : MinkowskiModel 3) b = jc y b)
    (hjc : ∀ b, ContinuousOn (fun z => jc z b) U) :
    (∀ η : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → HasDerivAt (g.potentialAction jc A η) 0 0) ↔
      smoothExteriorDerivative (excitation g.toLorentzMetric o F) =
        currentForm g.toLorentzMetric o j := by
  rw [CoordinateMetric.isPotentialStationary_iff hA hjc, sourced_iff_divergence,
    ← DFunLike.coe_fn_eq, CoordinateMetric.twoFormDivergence_eq_iff hA F hF j hj]

/-- **The Maxwell equations from the action on a curved background**: for a closed native field
`F = dA`, the action is stationary if and only if `F` and `j` satisfy `Curved.Maxwell`. -/
theorem maxwell_iff_potentialStationary (g : CoordinateMetric .timeNegative 3 U)
    (o : OrientedAtlas 4 U) {A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ}
    (hA : ContDiffOn ℝ ∞ A U) (F : Field (M := U))
    (hF : ∀ (y : U) (a b : Fin 4), F y ![Pi.single a 1, Pi.single b 1] =
      CoordinateMetric.potentialField A y a b)
    (hdF : smoothExteriorDerivative F = 0)
    (j : CurrentVector (M := U)) {jc : MinkowskiModel 3 → Fin 4 → ℝ}
    (hj : ∀ (y : U) (b : Fin 4), (j y : MinkowskiModel 3) b = jc y b)
    (hjc : ∀ b, ContinuousOn (fun z => jc z b) U) :
    Maxwell g.toLorentzMetric o F j ↔
      ∀ η : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
        tsupport η ⊆ U → HasDerivAt (g.potentialAction jc A η) 0 0 := by
  rw [potentialStationary_iff_sourced g o hA F hF j hj hjc, Maxwell]
  exact ⟨fun h => h.2, fun h => ⟨hdF, h⟩⟩

/-- With the positive coupling `+A_b k^b` of a matter current `k`, the density is that of the
current `−k`. -/
theorem potentialDensity_matter (g : CoordinateMetric .timeNegative 3 U)
    (k : MinkowskiModel 3 → Fin 4 → ℝ) (A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ)
    (z : MinkowskiModel 3) :
    g.potentialDensity (fun y b => -k y b) A z =
      (-(g.fieldPairing (CoordinateMetric.potentialField A)
          (CoordinateMetric.potentialField A) z / 4) +
        ∑ b, A z (Pi.single b 1) * k z b) * CoordinateMetric.densityOf g.coefficient z := by
  simp only [CoordinateMetric.potentialDensity, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- **The sign of a matter current on a curved background**: with the positive coupling
`+A_b k^b` of a matter current `k`, the action is stationary if and only if `dH = J` for the
current `−k`. -/
theorem potentialStationary_matter_iff (g : CoordinateMetric .timeNegative 3 U)
    (o : OrientedAtlas 4 U) {A : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ}
    (hA : ContDiffOn ℝ ∞ A U) (F : Field (M := U))
    (hF : ∀ (y : U) (a b : Fin 4), F y ![Pi.single a 1, Pi.single b 1] =
      CoordinateMetric.potentialField A y a b)
    (k : CurrentVector (M := U)) {kc : MinkowskiModel 3 → Fin 4 → ℝ}
    (hk : ∀ (y : U) (b : Fin 4), (k y : MinkowskiModel 3) b = kc y b)
    (hkc : ∀ b, ContinuousOn (fun z => kc z b) U) :
    (∀ η : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → HasDerivAt (g.potentialAction (fun y b => -kc y b) A η) 0 0) ↔
      smoothExteriorDerivative (excitation g.toLorentzMetric o F) =
        currentForm g.toLorentzMetric o (-k) :=
  potentialStationary_iff_sourced g o hA F hF (-k)
    (fun y b => by
      change -(k y : MinkowskiModel 3) b = -kc y b
      rw [hk])
    (fun b => (hkc b).neg)

end Curved

open Module exteriorPower
open SmoothGeometry.Minkowski SpecialRelativity VacuumAction

/-- The coefficient of `F ∧ ⋆G` is the induced pairing of two-forms. -/
theorem coefficient_wedge_star (F G : TwoForm) :
    coefficient (wedgeFiber F (star G)) = exteriorPairing F G := by
  have h := coefficient_wedge_eq_pairing (k := 2) (l := 2) rfl
  change coefficient (covectorDegreeCast rfl (wedgeFiber F (star G))) = _
  rw [h]
  change wedgePairing _ _ (toExterior F) (toExterior (hodgeFiber .timeNegative .standard
    (by decide : 2 + 2 = 3 + 1) G)) = _
  rw [hodgeFiber_pairing]
  rfl

/-- The flat vacuum density is `−¼ F_{ab} F^{ab}`. -/
theorem vacuumDensity_eq (A : Potential) (x : Spacetime) :
    Variational.density VacuumAction.lagrangian A x =
      -(tensorContraction (fieldTensor A x) (fieldTensor A x) / 4) := by
  rw [density_eq, coefficient_wedge_star, exteriorPairing_coordinates]
  ring

/-- The field of the covector field of a flat potential has the components of its field
tensor. -/
theorem potentialField_potentialCovector {A : Potential} {z : Spacetime}
    (hA : DifferentiableAt ℝ A z) (a b : Fin 4) :
    CoordinateMetric.potentialField (potentialCovector A) z a b =
      component (fieldTensor A z) a b := by
  have hd (c : Fin 4) : fderiv ℝ (fun w => potentialCovector A w (Pi.single c 1)) z =
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : Spacetime)).comp
        (potentialDifferential A z) :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1 : Spacetime)).hasFDerivAt.comp z
      (hasFDerivAt_potentialCovector hA)).fderiv
  simp only [CoordinateMetric.potentialField, Matrix.of_apply, hd, component, fieldTensor_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, potentialDifferential,
    ContinuousLinearEquiv.coe_coe]

/-- **The flat density**: for the Minkowski coordinate metric, the density of the action of the
covector field of a flat potential with the current `j` is the flat density with the current
form `ι_j vol`. -/
theorem potentialDensity_minkowski {U : Opens Spacetime} {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (j : Spacetime → Spacetime) :
    (CoordinateMetric.minkowski .timeNegative 3 U).potentialDensity j (potentialCovector A) x =
      Variational.density (SourcedAction.lagrangian fun z => interior (j z) (coordinateForm id))
        A x := by
  have hinv : ((CoordinateMetric.minkowski .timeNegative 3 U).coefficient x)⁻¹ =
      Matrix.diagonal (lorentzSign .timeNegative) := by
    rw [CoordinateMetric.minkowski_coefficient]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp only [SmoothGeometry.lorentzSign_sq, Matrix.diagonal_one]
  have hdet : CoordinateMetric.densityOf
      (CoordinateMetric.minkowski .timeNegative 3 U).coefficient x = 1 := by
    simp [CoordinateMetric.densityOf, CoordinateMetric.minkowski_coefficient,
      Matrix.det_diagonal, lorentzSign, LorentzConvention.timeSign]
  have hpair : (CoordinateMetric.minkowski .timeNegative 3 U).fieldPairing
      (CoordinateMetric.potentialField (potentialCovector A))
      (CoordinateMetric.potentialField (potentialCovector A)) x =
      tensorContraction (fieldTensor A x) (fieldTensor A x) := by
    rw [CoordinateMetric.fieldPairing, hinv, tensorContraction]
    simp only [mul_assoc, ← Finset.mul_sum, sum_diagonal_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [potentialField_potentialCovector hA, raisedComponent]
    ring
  have hsrc : ∑ b, potentialCovector A x (Pi.single b 1) * j x b =
      oneCovector (A x) (j x) := by
    conv_rhs => rw [pi_eq_sum_univ' (j x)]
    simp only [map_sum, map_smul, smul_eq_mul, potentialCovector, mul_comm]
  rw [CoordinateMetric.potentialDensity, hdet, mul_one, hpair, hsrc, SourcedAction.density_eq,
    vacuumDensity_eq, SourcedAction.sourcePairing_apply,
    SourcedAction.coefficient_wedge_interior_volume]

/-- **The flat functional**: for the Minkowski coordinate metric, the relative action of the
covector field of a flat potential is that of the flat sourced functional. -/
theorem potentialAction_minkowski {U : Opens Spacetime} {A η : Potential}
    (hA : Differentiable ℝ A) (hη : Differentiable ℝ η) (j : Spacetime → Spacetime) (ε : ℝ) :
    (CoordinateMetric.minkowski .timeNegative 3 U).potentialAction j (potentialCovector A)
        (potentialCovector η) ε =
      ∫ x, (Variational.density
          (SourcedAction.lagrangian fun z => interior (j z) (coordinateForm id))
          (Variational.perturb A η ε) x -
        Variational.density
          (SourcedAction.lagrangian fun z => interior (j z) (coordinateForm id)) A x) := by
  have hp : (fun z => potentialCovector A z + ε • potentialCovector η z) =
      potentialCovector (Variational.perturb A η ε) := by
    funext z
    simp only [potentialCovector, Variational.perturb, map_add, map_smul]
  unfold CoordinateMetric.potentialAction
  rw [hp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  have hpx : DifferentiableAt ℝ (Variational.perturb A η ε) x :=
    (hA x).add ((hη x).const_smul ε)
  rw [potentialDensity_minkowski hpx j,
    potentialDensity_minkowski (hA x) j]

end ProjectAinos.Electrodynamics
