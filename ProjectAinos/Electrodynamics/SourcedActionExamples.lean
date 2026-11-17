/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ChargeBalance
public import ProjectAinos.Electrodynamics.CurvedExamples
import Mathlib.Tactic.FinCases

/-!
# A stationary field with a nonzero current

The potential `A = (t²/2) dx` has the field `F = t dt ∧ dx`, the excitation `H = t dy ∧ dz`
and `dH = dt ∧ dy ∧ dz`. This is the current form `−ι_k vol` of the matter current `k = ∂x`.

* `stationary_example`: on every bounded open set the action of the field with this current
  is stationary at `A`. This fixes the sign of the source against the example
  `Curved.Examples.electric_source`, whose vector current is `j = −∂x = −k`.
* `maxwell_example`: in the unit ball the field satisfies the four equations of Maxwell in the
  frame of the co-ordinates, with `div E = 0 = k⁰` and `curl B − ∂_t E = (1, 0, 0) = 𝐤`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace ProjectAinos.Electrodynamics.SourcedAction.Examples

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open VacuumAction ContinuousLinearMap

/-- The matter current `∂x`. -/
def current : Spacetime → Spacetime := fun _ => Pi.single 1 1

/-- The potential `(t²/2) dx`. -/
def potential : Potential :=
  fun x => (x 0 ^ 2 / 2) • oneCovector.symm (ContinuousLinearMap.proj 1)

theorem hasFDerivAt_potential (x : Spacetime) :
    HasFDerivAt potential
      ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).smulRight
        (x 0 • oneCovector.symm (ContinuousLinearMap.proj 1))) x := by
  have hh : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (x 0) (x 0) := by
    convert (hasDerivAt_pow 2 (x 0)).div_const 2 using 1
    norm_num
  have hφ : HasFDerivAt (fun y : Spacetime => y 0 ^ 2 / 2)
      (x 0 • (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ)) x :=
    hh.comp_hasFDerivAt (f := fun y : Spacetime => y 0) x (hasFDerivAt_apply 0 x)
  refine (hφ.smul_const (oneCovector.symm (ContinuousLinearMap.proj 1))).congr_fderiv ?_
  ext v w
  simp [smul_smul, mul_comm]

theorem contDiff_potential : ContDiff ℝ ∞ potential :=
  ((contDiff_apply ℝ (fun _ : Fin 4 => ℝ) 0).pow 2 |>.div_const 2).smul contDiff_const

/-- The field of the potential is `t dt ∧ dx`. -/
theorem fieldTensor_potential (x : Spacetime) :
    fieldTensor potential x = x 0 • coordinateForm ![0, 1] := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, fieldTensor_apply, (hasFDerivAt_potential x).fderiv]
  simp [coordinateForm_apply, Matrix.det_fin_two]
  ring

/-- The excitation is `t dy ∧ dz`. -/
theorem excitation_potential (x : Spacetime) :
    -star (fieldTensor potential x) = x 0 • coordinateForm ![2, 3] := by
  rw [fieldTensor_potential, map_smul]
  change -(x 0 • hodgeFiber .timeNegative .standard (by decide) (coordinateForm ![0, 1])) = _
  rw [hodge_dt_dx, smul_neg, neg_neg]

/-- The current form of `∂x` is `dt ∧ dy ∧ dz`. -/
theorem matterCurrentForm_current (x : Spacetime) :
    matterCurrentForm current x = coordinateForm ![0, 2, 3] := by
  ext w
  simp only [matterCurrentForm, current, ContinuousAlternatingMap.neg_apply, interior_apply,
    coordinateForm_apply]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove]

/-- `dH = −ι_k vol` for the excitation of the potential and the current `∂x`. -/
theorem exteriorDerivative_excitation (x : Spacetime) :
    exteriorDerivative (fun y => -star (fieldTensor potential y)) x =
      matterCurrentForm current x := by
  have hfun : (fun y => -star (fieldTensor potential y)) =
      fun y : Spacetime => y 0 • coordinateForm (n := 4) ![2, 3] :=
    funext excitation_potential
  have hd : exteriorDerivative (fun y : Spacetime => y 0 • coordinateForm (n := 4) ![2, 3]) x =
      smoothExteriorDerivative Curved.Examples.magneticExcitation x :=
    (congrFun (smoothExteriorDerivative_flat
      (fun y : Spacetime => y 0 • coordinateForm (n := 4) ![2, 3])
      ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).smulRight
        (coordinateForm ![2, 3])).contDiff) x).symm
  have h2 : smoothExteriorDerivative Curved.Examples.magneticExcitation x =
      Curved.Examples.spatialCurrent x :=
    congrArg (fun α : Curved.CurrentForm (M := Spacetime) => α x)
      Curved.Examples.magneticExcitation_derivative
  rw [hfun, hd, h2, matterCurrentForm_current]
  rfl

/-- The density of the action is continuous. -/
theorem continuous_density :
    Continuous (Variational.density (lagrangian (matterCurrentForm current)) potential) := by
  have hj : Continuous fun x : Spacetime => (x, Variational.jet potential x) :=
    continuous_id.prodMk (contDiff_potential.continuous.prodMk
      (contDiff_potential.continuous_fderiv (by simp)))
  have hJ : ContDiff ℝ 2 (matterCurrentForm current) := contDiff_matterCurrentForm contDiff_const
  have hL : Continuous (Function.uncurry (lagrangian (matterCurrentForm current))) :=
    (lagrangian_contDiff hJ).continuous
  have hfun : Variational.density (lagrangian (matterCurrentForm current)) potential =
      Function.uncurry (lagrangian (matterCurrentForm current)) ∘
        fun x : Spacetime => (x, Variational.jet potential x) := rfl
  rw [hfun]
  exact hL.comp hj

/-- On a bounded set the density of the action is integrable. -/
theorem integrable_density {U : Set Spacetime} (hb : Bornology.IsBounded U) :
    Integrable (Variational.density (lagrangian (matterCurrentForm current)) potential)
      (volume.restrict U) :=
  (continuous_density.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set
    subset_closure

/-- On every bounded open set the action of the field with the current `∂x` is stationary at
the potential `(t²/2) dx`. -/
theorem stationary_example {U : Set Spacetime} (hU : IsOpen U) (hb : Bornology.IsBounded U) :
    Variational.Stationary volume U (lagrangian (matterCurrentForm current)) potential :=
  (stationary_iff_matterCurrent hU (contDiff_potential.of_le (by simp)) contDiff_const
    (integrable_density hb)).mpr fun x _ => exteriorDerivative_excitation x

/-- In the unit ball the field `t dt ∧ dx` satisfies the equations of Maxwell with the current
`∂x`: `div B = 0`, `∂_t B + curl E = 0`, `div E = 0` and `curl B − ∂_t E = (1, 0, 0)`. -/
theorem maxwell_example {x : Spacetime} (hx : x ∈ Metric.ball 0 1) :
    (divergence3 (magneticField (fieldTensor potential)) x = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor potential) i) 0 x +
        curl (electricField (fieldTensor potential)) x i = 0) ∧
    (divergence3 (electricField (fieldTensor potential)) x = 0 ∧
      ∀ i, curl (magneticField (fieldTensor potential)) x i -
        partialAt (electricField (fieldTensor potential) i) 0 x =
          (Pi.single 1 1 : Spacetime) i.succ) := by
  have h := maxwell_of_stationary Metric.isOpen_ball (contDiff_potential.of_le (by simp))
    (contDiff_const : ContDiff ℝ 2 current) (integrable_density Metric.isBounded_ball)
    (stationary_example Metric.isOpen_ball Metric.isBounded_ball) hx
  refine ⟨h.1, ?_, h.2.2⟩
  rw [h.2.1]
  rfl

end ProjectAinos.Electrodynamics.SourcedAction.Examples
