/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Calculus

/-! # Degree transport and exterior product identities

Explicit transport of the natural-number degree makes the algebraic identities
equalities of alternating maps, rather than only equalities in an ambient algebra.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {n k l q : ℕ}

/-- Transport an alternating covector along an equality of degrees. -/
def covectorDegreeCast (h : k = l) (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    (Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ := h ▸ α

@[simp] theorem coe_toExterior_degreeCast (h : k = l)
    (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    (toExterior (covectorDegreeCast h α) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) =
      (toExterior α : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) := by cases h; rfl

theorem covector_eq_of_coe_toExterior {α β : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ}
    (h : (toExterior α : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) = toExterior β) : α = β :=
  toExterior.injective (Subtype.ext h)

/-- Homogeneous exterior powers obey the usual real graded commutation sign. -/
theorem homogeneous_mul_comm (α : ExteriorCovector n k) (β : ExteriorCovector n l) :
    (α : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) * β =
      (-1 : ℝ) ^ (k * l) • ((β : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) * α) := by
  have ha := α.property
  have hb := β.property
  rw [← (Submodule.ext_iff.mp (ExteriorAlgebra.ιMulti_span_fixedDegree ℝ _))] at ha hb
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y = (-1 : ℝ) ^ (k * l) • (y * x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    have h := ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm ℝ a b
    change ExteriorAlgebra.ιMulti ℝ k a * ExteriorAlgebra.ιMulti ℝ l b =
      (-1 : ℤ) ^ (l * k) • (ExteriorAlgebra.ιMulti ℝ l b * ExteriorAlgebra.ιMulti ℝ k a) at h
    rw [← Int.cast_smul_eq_zsmul ℝ] at h
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one, Nat.mul_comm] using h
  all_goals simp +contextual [add_mul, mul_add, smul_smul, mul_comm]

/-- Associativity with the exact degree transport made explicit. -/
theorem wedgeFiber_assoc (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (β : (Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) (γ : (Fin n → ℝ) [⋀^Fin q]→L[ℝ] ℝ) :
    covectorDegreeCast (Nat.add_assoc k l q) (wedgeFiber (wedgeFiber α β) γ) =
      wedgeFiber α (wedgeFiber β γ) := by
  apply covector_eq_of_coe_toExterior
  simp only [coe_toExterior_degreeCast, toExterior_wedgeFiber,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, mul_assoc]

/-- Graded commutativity with the exact degree transport made explicit. -/
theorem wedgeFiber_comm (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (β : (Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) :
    wedgeFiber α β = (-1 : ℝ) ^ (k * l) •
      covectorDegreeCast (Nat.add_comm l k) (wedgeFiber β α) := by
  apply covector_eq_of_coe_toExterior
  simpa only [map_smul, Submodule.coe_smul, coe_toExterior_degreeCast, toExterior_wedgeFiber,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul] using homogeneous_mul_comm (toExterior α) (toExterior β)

@[simp] theorem coe_toExterior_unit :
    (toExterior (coordinateForm (n := n) ![]) : ExteriorAlgebra ℝ (Dual ℝ (Fin n → ℝ))) = 1 := by
  simp [coordinateForm, ofCovectors, exteriorPower.ιMulti_apply_coe]

theorem wedgeFiber_one_left (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    covectorDegreeCast (Nat.zero_add k) (wedgeFiber (coordinateForm ![]) α) = α := by
  apply covector_eq_of_coe_toExterior
  simp only [coe_toExterior_degreeCast, toExterior_wedgeFiber, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul, coe_toExterior_unit, one_mul]

theorem wedgeFiber_one_right (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :
    wedgeFiber α (coordinateForm ![]) = α := by
  apply covector_eq_of_coe_toExterior
  simp only [toExterior_wedgeFiber, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul, coe_toExterior_unit, mul_one]
  rfl

/-- The model Leibniz rule as an equality in its native alternating-map degree. -/
theorem exteriorDerivative_wedge_cast (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l)
    {x : Fin n → ℝ} (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    exteriorDerivative (wedge α β) x =
      covectorDegreeCast (by omega : (k + 1) + l = (k + l) + 1)
        (wedgeFiber (exteriorDerivative α x) (β x)) +
      (-1 : ℝ) ^ k • covectorDegreeCast (Nat.add_assoc k l 1).symm
        (wedgeFiber (α x) (exteriorDerivative β x)) := by
  apply covector_eq_of_coe_toExterior
  simpa only [map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
    coe_toExterior_degreeCast, toExterior_wedgeFiber, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul] using! exteriorDerivative_wedge α β hα hβ

end ProjectAInos.SmoothGeometry.DifferentialForm
