/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.SourcedAction
public import ProjectAinos.Electrodynamics.Current
public import ProjectAinos.SmoothGeometry.Minkowski.HodgeCurrent
public import ProjectAinos.SmoothGeometry.Lorentzian.VolumeExamples
import Mathlib.Tactic.FinCases

/-!
# The current of the matter and the sign of the source

A matter current is a vector field `k` on space-time with the charge density `k⁰ = ρ` and the
current density `kⁱ` (Landau–Lifshitz, *The Classical Theory of Fields*, §28). Its current
three-form is `matterCurrentForm k = −ι_k vol` with the volume `dt ∧ dx ∧ dy ∧ dz`.

* `coefficient_wedge_interior_volume`: `a ∧ ι_v vol = a(v) vol` for a one-form `a`.
* `lagrangian_matterCurrentForm`: with this current the source term of the Lagrangian of the
  field is `+A(k) = −φρ + a · 𝐤`, the sign of the coupling `e A(γ̇)` of a charge in
  `chargedLagrangian`.
* `currentForm_minkowski`, `matterCurrentForm_eq_currentForm`: the current form of the
  equations on a manifold is `ι_j vol`, so the matter current is `k = −j` for the vector `j`
  of `Curved.Maxwell`.
* `stationary_iff_matterCurrent`: the action with the matter current is stationary if and only
  if `dH = −ι_k vol`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff

namespace ProjectAinos.Electrodynamics.SourcedAction

open Module
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm
open SpecialRelativity VacuumAction ContinuousLinearMap

theorem oneForm_eq_ofCovectors (a : OneForm) : a = ofCovectors ![oneCovector a] := by
  ext v
  rw [ofCovectors_apply, Matrix.det_unique]
  change a v = a (fun _ => v default)
  congr 1
  funext i
  rw [Subsingleton.elim i default]

/-- `a ∧ ι_v vol = a(v) vol` for a one-form `a` and a vector `v`. -/
theorem coefficient_wedge_interior_volume (a : OneForm) (v : Spacetime) :
    coefficient (wedgeFiber a (interior v (coordinateForm id))) = oneCovector a v := by
  have hv : oneCovector a v = ∑ i : Fin 4, v i * oneCovector a (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hv, oneForm_eq_ofCovectors a, interior_coordinate_volume, map_sum, map_sum]
  simp only [map_smul, coordinateForm, wedge_ofCovectors]
  simp only [coefficient, ContinuousAlternatingMap.apply_apply, ofCovectors_apply]
  rw [Fin.sum_univ_four, Fin.sum_univ_four]
  norm_num [-Basis.coe_dualBasis, Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Basis.coord_apply, Fin.append, Fin.addCases, Pi.single_apply]
  all_goals norm_num [Basis.dualBasis_apply, Basis.coord_apply, Pi.single_apply, Fin.succAbove]

/-- The current three-form `−ι_k vol` of a matter current `k`. -/
def matterCurrentForm (k : Spacetime → Spacetime) : Form Spacetime 3 :=
  fun x => -interior (k x) (coordinateForm id)

/-- With the current of the matter, the source term of the Lagrangian is `+A(k)`. -/
theorem lagrangian_matterCurrentForm (k : Spacetime → Spacetime) (x : Spacetime)
    (z : Variational.JetFiber Spacetime OneForm) :
    lagrangian (matterCurrentForm k) x z = VacuumAction.lagrangian x z + oneCovector z.1 (k x) := by
  rw [lagrangian, matterCurrentForm, map_neg, sourcePairing_apply,
    coefficient_wedge_interior_volume, sub_neg_eq_add]

/-- The density of the action with the current of the matter. -/
theorem density_matterCurrentForm (k : Spacetime → Spacetime) (A : Potential) (x : Spacetime) :
    Variational.density (lagrangian (matterCurrentForm k)) A x =
      Variational.density VacuumAction.lagrangian A x + oneCovector (A x) (k x) :=
  lagrangian_matterCurrentForm k x _

/-- The current form of a vector field `j` on Minkowski space is `ι_j vol`. -/
theorem currentForm_minkowski (j : Curved.CurrentVector (M := Spacetime)) (x : Spacetime) :
    Curved.currentForm (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4) j x =
      interior (j x) (coordinateForm id) := by
  rw [Curved.currentForm_volume, LorentzianVolumeExamples.minkowski_volume]
  rfl

/-- The current three-form of `−j` is `ι_j vol`. -/
theorem matterCurrentForm_neg (j : Spacetime → Spacetime) (x : Spacetime) :
    matterCurrentForm (fun y => -j y) x = interior (j x) (coordinateForm id) := by
  have h : interior (-j x) (coordinateForm (n := 4) id) =
      -interior (j x) (coordinateForm (n := 4) id) := by
    ext w
    simp only [interior_apply, ContinuousAlternatingMap.neg_apply]
    have hc : Matrix.vecCons (-j x) w = Function.update (Matrix.vecCons (j x) w) 0 (-j x) := by
      ext i : 1
      refine Fin.cases ?_ (fun l => ?_) i
      · simp
      · simp
    have h1 := (coordinateForm (n := 4) id).toMultilinearMap.map_update_neg
      (Matrix.vecCons (j x) w) 0 (j x)
    have hu : Function.update (Matrix.vecCons (j x) w) 0 (j x) = Matrix.vecCons (j x) w := by
      ext i : 1
      refine Fin.cases ?_ (fun l => ?_) i
      · simp
      · simp
    rw [hu] at h1
    rw [hc]
    exact h1
  change -interior (-j x) (coordinateForm (n := 4) id) = _
  rw [h, neg_neg]

/-- The matter current `k` is minus the vector `j` of the equations on a manifold. -/
theorem matterCurrentForm_eq_currentForm (j : Curved.CurrentVector (M := Spacetime))
    (x : Spacetime) :
    matterCurrentForm (fun y => -(j y : Spacetime)) x =
      Curved.currentForm (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4) j x :=
  (matterCurrentForm_neg (fun y => (j y : Spacetime)) x).trans (currentForm_minkowski j x).symm

/-- The current three-form of a smooth matter current is smooth. -/
theorem contDiff_matterCurrentForm {n : ℕ∞ω} {k : Spacetime → Spacetime} (hk : ContDiff ℝ n k) :
    ContDiff ℝ n (matterCurrentForm k) := by
  have h : matterCurrentForm k = fun x => -∑ i : Fin 4,
      ((-1 : ℝ) ^ (i : ℕ) * k x i) • coordinateForm (n := 4) i.succAbove := by
    funext x
    simp only [matterCurrentForm, interior_coordinate_volume]
  rw [h]
  exact (ContDiff.sum fun i _ =>
    (contDiff_const.mul ((contDiff_apply ℝ (fun _ : Fin 4 => ℝ) i).comp hk)).smul
      contDiff_const).neg

/-- The action of the field with the current of the matter `k` is stationary if and only if
`dH = −ι_k vol`. -/
theorem stationary_iff_matterCurrent {U : Set Spacetime} {A : Potential}
    {k : Spacetime → Spacetime} (hU : IsOpen U) (hA : ContDiff ℝ 2 A) (hk : ContDiff ℝ 2 k)
    (hfin : Integrable (Variational.density (lagrangian (matterCurrentForm k)) A)
      (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian (matterCurrentForm k)) A ↔
      ∀ x ∈ U, exteriorDerivative (fun y => -star (fieldTensor A y)) x = matterCurrentForm k x :=
  stationary_iff_excitation hU hA (contDiff_matterCurrentForm hk) hfin

end ProjectAinos.Electrodynamics.SourcedAction
