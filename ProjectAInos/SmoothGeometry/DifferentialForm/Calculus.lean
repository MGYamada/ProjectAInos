/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.DifferentialForm.Naturality
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! # Differentiation of exterior products -/
@[expose] public section
noncomputable section
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.DifferentialForm
variable {n k l : ℕ}

def wedgeCLM : ((Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
    ((Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ((Fin n → ℝ) [⋀^Fin (k+l)]→L[ℝ] ℝ) :=
  let T : (((Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin n → ℝ) [⋀^Fin (k+l)]→L[ℝ] ℝ)) ≃ₗ[ℝ]
      (((Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ((Fin n → ℝ) [⋀^Fin (k+l)]→L[ℝ] ℝ)) :=
    LinearMap.toContinuousLinearMap
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (F' := ((Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ((Fin n → ℝ) [⋀^Fin (k+l)]→L[ℝ] ℝ)))
    (T.toLinearMap.comp (wedgeFiber (n := n) (k := k) (l := l)))

@[simp] theorem wedgeCLM_apply (a : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (b : (Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) : wedgeCLM a b = wedgeFiber a b := rfl

/-- Exterior product preserves regularity locally, without global extensions. -/
theorem wedge_contDiffAt {α : Form (Fin n → ℝ) k} {β : Form (Fin n → ℝ) l}
    {r : WithTop ℕ∞} {x : Fin n → ℝ}
    (hα : ContDiffAt ℝ r α x) (hβ : ContDiffAt ℝ r β x) :
    ContDiffAt ℝ r (wedge α β) x := by
  change ContDiffAt ℝ r (fun y => wedgeFiber (α y) (β y)) x
  simpa only [Function.comp_def, wedgeCLM_apply] using
    wedgeCLM.isBoundedBilinearMap.contDiff.contDiffAt.comp x (hα.prodMk hβ)

theorem wedge_contDiff (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l)
    {r : WithTop ℕ∞} (hα : ContDiff ℝ r α) (hβ : ContDiff ℝ r β) :
    ContDiff ℝ r (wedge α β) := by
  change ContDiff ℝ r (fun x => wedgeFiber (α x) (β x))
  simpa only [Function.comp_def, wedgeCLM_apply] using
    wedgeCLM.isBoundedBilinearMap.contDiff.comp (hα.prodMk hβ)

theorem fderiv_wedge (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l)
    {x : Fin n → ℝ} (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x)
    (v : Fin n → ℝ) :
    fderiv ℝ (wedge α β) x v = wedgeFiber (α x) (fderiv ℝ β x v) +
      wedgeFiber (fderiv ℝ α x v) (β x) := by
  change fderiv ℝ (fun y => wedgeFiber (α y) (β y)) x v = _
  simpa only [wedgeCLM_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, add_apply] using
    congrArg (fun f => f v) (wedgeCLM.fderiv_of_bilinear hα hβ)

/-- Left multiplication by a covector, with degree `k+1`. -/
def wedgeLeft (a : (Fin n → ℝ) →L[ℝ] ℝ) (β : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    (Fin n → ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin (a.smulRight β)

theorem wedgeLeft_ofCovectors (a : (Fin n → ℝ) →L[ℝ] ℝ)
    (b : Fin k → Dual ℝ (Fin n → ℝ)) :
    wedgeLeft a (ofCovectors b) = ofCovectors (Fin.cons a.toLinearMap b) := by
  ext v
  simp only [wedgeLeft, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    ofCovectors_apply]
  rw [Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.of_apply, Fin.cons_zero, ContinuousLinearMap.coe_coe,
    Fin.removeNth]
  change ((-1 : ℤ)^i.val) • (a (v i) * (Matrix.of fun r j => b j (v (i.succAbove r))).det) =
    (-1 : ℝ)^i.val * a (v i) * (Matrix.of fun r j => b j (v (i.succAbove r))).det
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp [mul_assoc]

def wedgeLeftL (a : (Fin n → ℝ) →L[ℝ] ℝ) :
    ((Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ((Fin n → ℝ) [⋀^Fin (k+1)]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin n → ℝ) ℝ).comp
    (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) _ a)

@[simp] theorem wedgeLeftL_apply (a : (Fin n → ℝ) →L[ℝ] ℝ)
    (β : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) : wedgeLeftL a β = wedgeLeft a β := rfl

theorem coe_wedgeLeft (a : (Fin n → ℝ) →L[ℝ] ℝ) (β : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    (toExterior (wedgeLeft a β) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) =
      ExteriorAlgebra.ι ℝ a.toLinearMap * (toExterior β : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) := by
  suffices H : (Submodule.subtype (⋀[ℝ]^(k+1) (Dual ℝ (Fin n → ℝ)))).comp
      (toExterior.toLinearMap.comp ((wedgeLeftL a).toLinearMap.comp toExterior.symm.toLinearMap)) =
      (LinearMap.mulLeft ℝ (ExteriorAlgebra.ι ℝ a.toLinearMap)).comp
        (Submodule.subtype (⋀[ℝ]^k (Dual ℝ (Fin n → ℝ)))) by
    have h := congrArg (fun f => f (toExterior β)) H
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe, wedgeLeftL_apply,
      LinearMap.mulLeft_apply, Submodule.subtype_apply] using h
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro b
  change (toExterior (wedgeLeft a (ofCovectors b)) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) = _
  rw [wedgeLeft_ofCovectors]
  simp only [ofCovectors, LinearEquiv.apply_symm_apply, ιMulti_apply_coe]
  simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

theorem exteriorDerivative_coordinates (ω : Form (Fin n → ℝ) k) (x : Fin n → ℝ) :
    (toExterior (exteriorDerivative ω x) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) =
      ∑ i : Fin n, ExteriorAlgebra.ι ℝ (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).toLinearMap *
        (toExterior (fderiv ℝ ω x (Pi.single i 1)) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) := by
  have hd : fderiv ℝ ω x = ∑ i : Fin n,
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (fderiv ℝ ω x (Pi.single i 1)) := by
    ext v w
    have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by ext i; simp [Pi.single_apply, mul_ite]
    have h := congrArg (fun z => fderiv ℝ ω x z) hv
    simpa only [map_sum, map_smul, sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply] using congrArg (fun z => z w) h
  unfold exteriorDerivative extDeriv
  conv_lhs => rw [hd]
  change (toExterior ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin n → ℝ) ℝ) _) :
    ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) = _
  rw [map_sum, map_sum]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact coe_wedgeLeft _ _

theorem ι_mul_homogeneous (a : Dual ℝ (Fin n → ℝ)) (α : ExteriorCovector n k) :
    ExteriorAlgebra.ι ℝ a * (α : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) =
      (-1 : ℝ)^k • ((α : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) * ExteriorAlgebra.ι ℝ a) := by
  suffices H : (LinearMap.mulLeft ℝ (ExteriorAlgebra.ι ℝ a)).comp (Submodule.subtype (ExteriorCovector n k)) =
      (-1 : ℝ)^k • (LinearMap.mulRight ℝ (ExteriorAlgebra.ι ℝ a)).comp
        (Submodule.subtype (ExteriorCovector n k)) from congrArg (fun f => f α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro b
  change ExteriorAlgebra.ι ℝ a * (ExteriorAlgebra.ιMulti ℝ k b) =
    (-1 : ℝ)^k • (ExteriorAlgebra.ιMulti ℝ k b * ExteriorAlgebra.ι ℝ a)
  have h := ExteriorAlgebra.ι_mul_ιMulti_anticomm ℝ a b
  change ExteriorAlgebra.ι ℝ a * (ExteriorAlgebra.ιMulti ℝ k b) =
    (-1 : ℤ)^k • (ExteriorAlgebra.ιMulti ℝ k b * ExteriorAlgebra.ι ℝ a) at h
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using h

/-- Graded Leibniz rule, stated in the exterior algebra to avoid casts between
`(k+l)+1`, `(k+1)+l` and `k+(l+1)`. Each term is homogeneous of the same degree. -/
theorem exteriorDerivative_wedge (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l)
    {x : Fin n → ℝ} (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    (toExterior (exteriorDerivative (wedge α β) x) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) =
      (toExterior (exteriorDerivative α x) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) * toExterior (β x) +
      (-1 : ℝ)^k • ((toExterior (α x) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) *
        toExterior (exteriorDerivative β x)) := by
  simp only [exteriorDerivative_coordinates, fderiv_wedge α β hα hβ, map_add,
    toExterior_wedgeFiber, Submodule.coe_add, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]
  rw [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add]
  have h := ι_mul_homogeneous (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).toLinearMap (toExterior (α x))
  rw [← mul_assoc, h, smul_mul_assoc, mul_assoc]
  noncomm_ring

end ProjectAInos.SmoothGeometry.DifferentialForm
