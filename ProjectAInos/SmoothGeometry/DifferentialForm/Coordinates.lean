/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.DifferentialForm.Exterior

/-! # Coordinate formulas and normalized exterior products -/
@[expose] public section
noncomputable section
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.DifferentialForm
variable {n k l : ℕ}

theorem pairing_toExterior (ω : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → Fin n → ℝ) :
    pairingDual ℝ (Fin n → ℝ) k (toExterior ω) (ιMulti ℝ k v) = ω v := by
  simp [toExterior, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, forgetContinuous]
  rfl

theorem fromExterior_apply (α : ExteriorCovector n k) (v : Fin k → Fin n → ℝ) :
    toExterior.symm α v = pairingDual ℝ (Fin n → ℝ) k α (ιMulti ℝ k v) := by
  rw [← pairing_toExterior, LinearEquiv.apply_symm_apply]

def ofCovectors (a : Fin k → Dual ℝ (Fin n → ℝ)) : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ :=
  toExterior.symm (ιMulti ℝ k a)

@[simp] theorem ofCovectors_apply (a : Fin k → Dual ℝ (Fin n → ℝ)) (v : Fin k → Fin n → ℝ) :
    ofCovectors a v = (Matrix.of fun i j => a j (v i)).det := by
  rw [ofCovectors, fromExterior_apply, pairingDual_ιMulti_ιMulti]

theorem wedge_ofCovectors (a : Fin k → Dual ℝ (Fin n → ℝ))
    (b : Fin l → Dual ℝ (Fin n → ℝ)) :
    wedgeFiber (ofCovectors a) (ofCovectors b) = ofCovectors (Fin.append a b) := by
  apply toExterior.injective
  simp only [toExterior_wedgeFiber, ofCovectors, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ιMulti_apply_coe]
  exact ExteriorAlgebra.ιMulti_mul_ιMulti a b

/-- In degree one the wedge uses no factorial normalization. -/
theorem wedge_one_one (a b : Dual ℝ (Fin n → ℝ)) (v w : Fin n → ℝ) :
    wedgeFiber (ofCovectors ![a]) (ofCovectors ![b]) ![v,w] = a v * b w - a w * b v := by
  rw [wedge_ofCovectors, ofCovectors_apply]
  rw [Matrix.det_fin_two]
  change a v * b w - b v * a w = _
  ring

/-- The ordered elementary form `dxⁱ₁ ∧ ... ∧ dxⁱₖ`. -/
def coordinateForm (is : Fin k → Fin n) : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ :=
  ofCovectors (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis (is j))

@[simp] theorem coordinateForm_apply (is : Fin k → Fin n) (v : Fin k → Fin n → ℝ) :
    coordinateForm is v = (Matrix.of fun i j => v i (is j)).det := by
  simp [coordinateForm]

end ProjectAInos.SmoothGeometry.DifferentialForm
