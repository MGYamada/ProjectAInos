/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ThreePlusOne
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic.FinCases

/-!
# The conservation of the charge

For a matter current `k` on flat space-time, `divergence4 k = Σ_μ ∂_μ k^μ` is its divergence
(Landau–Lifshitz, *The Classical Theory of Fields*, §29).

* `coefficient_exteriorDerivative_matterCurrentForm`: `d(−ι_k vol) = −(div k) vol`, so the
  current three-form is closed if and only if `div k = 0`
  (`exteriorDerivative_matterCurrentForm_eq_zero_iff`).
* `divergence4_eq_zero_of_stationary`: where the action of the field with the current `k` is
  stationary, `div k = 0`: the equation of continuity follows from the equation of the field.
* `charge_balance`: for a box `[a, b]` of space-time and a current with `div k = 0` on it, the
  charge `∫ k⁰ d³x` in the spatial box at the time `b⁰` minus that at `a⁰` is minus the flux
  of the current through the six faces of the spatial box during `[a⁰, b⁰]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open SourcedAction VacuumAction ContinuousLinearMap

/-- The four-divergence `Σ_μ ∂_μ k^μ` of a vector field. -/
def divergence4 (k : Spacetime → Spacetime) (x : Spacetime) : ℝ :=
  ∑ μ : Fin 4, fderiv ℝ k x (Pi.single μ 1) μ

/-! ### The current form and the divergence -/

/-- The linear map `v ↦ −ι_v vol`. -/
def matterCurrentMap : Spacetime →L[ℝ] (Spacetime [⋀^Fin 3]→L[ℝ] ℝ) :=
  -∑ i : Fin 4, ((-1 : ℝ) ^ (i : ℕ)) •
    (ContinuousLinearMap.proj i : Spacetime →L[ℝ] ℝ).smulRight
      (coordinateForm (n := 4) i.succAbove)

theorem matterCurrentMap_apply (v : Spacetime) :
    matterCurrentMap v = -interior v (coordinateForm id) := by
  rw [interior_coordinate_volume, matterCurrentMap]
  simp only [neg_apply, sum_apply, smul_apply, smulRight_apply, proj_apply, smul_smul]

theorem matterCurrentForm_eq_comp (k : Spacetime → Spacetime) :
    matterCurrentForm k = fun y => matterCurrentMap (k y) := by
  funext y
  rw [matterCurrentMap_apply]
  rfl

/-- The volume form with a vector and all but one of the axes: `(−1)^i vⁱ`. -/
theorem volume_cons_removeNth (v : Spacetime) (i : Fin 4) :
    coordinateForm (n := 4) id
        (Matrix.vecCons v (Fin.removeNth i (Pi.basisFun ℝ (Fin 4) : Fin 4 → Spacetime))) =
      (-1 : ℝ) ^ (i : ℕ) * v i := by
  rw [coordinateForm_apply]
  fin_cases i <;>
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove, Fin.tail,
      Pi.basisFun_apply, Pi.single_apply]

/-- `d(−ι_k vol) = −(div k) vol`. -/
theorem coefficient_exteriorDerivative_matterCurrentForm {k : Spacetime → Spacetime}
    {x : Spacetime} (hk : DifferentiableAt ℝ k x) :
    coefficient (exteriorDerivative (matterCurrentForm k) x) = -divergence4 k x := by
  have hd : HasFDerivAt (matterCurrentForm k) (matterCurrentMap.comp (fderiv ℝ k x)) x := by
    rw [matterCurrentForm_eq_comp]
    exact matterCurrentMap.hasFDerivAt.comp x hk.hasFDerivAt
  change (extDeriv (matterCurrentForm k) x) (Pi.basisFun ℝ (Fin 4)) = _
  rw [extDeriv, hd.fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, divergence4,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [comp_apply, matterCurrentMap_apply, ContinuousAlternatingMap.neg_apply, interior_apply]
  change (-1 : ℝ) ^ (i : ℕ) * -(coordinateForm (n := 4) id (Matrix.vecCons
    (fderiv ℝ k x (Pi.basisFun ℝ (Fin 4) i)) (Fin.removeNth i (Pi.basisFun ℝ (Fin 4))))) = _
  rw [volume_cons_removeNth, Pi.basisFun_apply]
  have hsq : ((-1 : ℝ) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (-(fderiv ℝ k x (Pi.single i 1) i)) * hsq

/-- The current three-form of the matter is closed if and only if `div k = 0`. -/
theorem exteriorDerivative_matterCurrentForm_eq_zero_iff {k : Spacetime → Spacetime}
    {x : Spacetime} (hk : DifferentiableAt ℝ k x) :
    exteriorDerivative (matterCurrentForm k) x = 0 ↔ divergence4 k x = 0 := by
  rw [← neg_eq_zero (a := divergence4 k x), ← coefficient_exteriorDerivative_matterCurrentForm hk]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact topForm_ext_basis (Pi.basisFun ℝ (Fin 4)) (by simpa [coefficient] using h)

/-- The equation of continuity follows from the equation of the field: where the action with
the current of the matter is stationary, `div k = 0`. -/
theorem divergence4_eq_zero_of_stationary {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiff ℝ 3 A) {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    (hfin : Integrable (Variational.density (lagrangian (matterCurrentForm k)) A)
      (volume.restrict U))
    (hs : Variational.Stationary volume U (lagrangian (matterCurrentForm k)) A)
    {x : Spacetime} (hx : x ∈ U) : divergence4 k x = 0 := by
  have hA2 : ContDiff ℝ 2 A := hA.of_le (by norm_num)
  have heq := (stationary_iff_matterCurrent hU hA2 hk hfin).mp hs
  let H : Form Spacetime 2 := fun y => -star (fieldTensor A y)
  have hH : ContDiff ℝ 2 H :=
    (star.contDiff.comp (exteriorDerivative_contDiff (r := 2) hA)).neg
  have hev : matterCurrentForm k =ᶠ[𝓝 x] exteriorDerivative H :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => (heq y hy).symm
  have hdd : exteriorDerivative (matterCurrentForm k) x = 0 := by
    change extDeriv (matterCurrentForm k) x = 0
    rw [extDeriv, hev.fderiv_eq]
    exact extDeriv_extDeriv_apply hH.contDiffAt (by simp)
  exact (exteriorDerivative_matterCurrentForm_eq_zero_iff
    (hk.differentiable (by norm_num) x)).mp hdd

/-! ### The balance of the charge in a box -/

/-- The charge `∫ k⁰ d³x` in the spatial box of `[a, b]` at the time `t`. -/
def charge (k : Spacetime → Spacetime) (a b : Spacetime) (t : ℝ) : ℝ :=
  ∫ y in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), k (Fin.insertNth 0 t y) 0

/-- The flux of the component `k^i` through the two faces `x^i = aⁱ, bⁱ` of the box `[a, b]`,
integrated over the other co-ordinates. -/
def faceFlux (k : Spacetime → Spacetime) (a b : Spacetime) (i : Fin 4) : ℝ :=
  (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), k (Fin.insertNth i (b i) y) i) -
    ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), k (Fin.insertNth i (a i) y) i

theorem faceFlux_zero (k : Spacetime → Spacetime) (a b : Spacetime) :
    faceFlux k a b 0 = charge k a b (b 0) - charge k a b (a 0) := rfl

/-- The balance of the charge: for a `C¹` current with `div k = 0` on the box `[a, b]`, the
change of the charge in the spatial box from the time `a⁰` to the time `b⁰` is minus the flux
through its six faces. -/
theorem charge_balance {k : Spacetime → Spacetime} (hk : ContDiff ℝ 1 k) {a b : Spacetime}
    (hle : a ≤ b) (hdiv : ∀ x ∈ Icc a b, divergence4 k x = 0) :
    charge k a b (b 0) - charge k a b (a 0) = -∑ i : Fin 3, faceFlux k a b i.succ := by
  have hcont : Continuous fun x => ∑ μ : Fin 4, fderiv ℝ k x (Pi.single μ 1) μ :=
    continuous_finsetSum _ fun μ _ =>
      (continuous_apply μ).comp ((hk.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have h := integral_divergence_of_hasFDerivAt_off_countable a b hle k (fderiv ℝ k) ∅
    countable_empty hk.continuous.continuousOn
    (fun x _ => (hk.differentiable one_ne_zero x).hasFDerivAt)
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
  have hzero : (∫ x in Icc a b, ∑ μ : Fin 4, fderiv ℝ k x (Pi.single μ 1) μ) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hdiv x hx
  rw [hzero, Fin.sum_univ_succ] at h
  change 0 = faceFlux k a b 0 + ∑ i : Fin 3, faceFlux k a b i.succ at h
  rw [faceFlux_zero] at h
  linarith

end ProjectAinos.Electrodynamics
