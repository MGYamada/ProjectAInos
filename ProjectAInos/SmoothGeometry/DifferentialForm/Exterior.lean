/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Flat
public import Mathlib.LinearAlgebra.ExteriorPower.HodgeStar
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! # Continuous forms and exterior powers of the dual

The determinant pairing fixes the wedge normalization, including degrees zero
and one. Continuity is proved from finite coordinate expansions.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
open Module
namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {n k l : ℕ}

theorem coordinate_multilinear_continuous
    (f : MultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ℝ) : Continuous f := by
  have h (v : Fin k → Fin n → ℝ) :
      f v = ∑ r : Fin k → Fin n, (∏ i, v i (r i)) * f (fun i => Pi.single (r i) 1) := by
    have hv : v = fun i => ∑ j, v i j • Pi.single j (1 : ℝ) := by
      ext i j
      simp [Pi.single_apply, mul_ite]
    conv_lhs => rw [hv]
    rw [f.map_sum]
    simp only [f.map_smul_univ, smul_eq_mul]
  have he : (f : (Fin k → Fin n → ℝ) → ℝ) =
      fun v => ∑ r : Fin k → Fin n, (∏ i, v i (r i)) * f (fun i => Pi.single (r i) 1) := funext h
  rw [he]
  fun_prop

def continuousAlternating (f : (Fin n → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ) :
    (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ :=
  { f with cont := coordinate_multilinear_continuous f.toMultilinearMap }

def forgetContinuous : ((Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ]
    ((Fin n → ℝ) [⋀^Fin k]→ₗ[ℝ] ℝ) where
  toLinearMap := ContinuousAlternatingMap.toAlternatingMapLinear
  invFun := continuousAlternating
  left_inv f := by ext v; rfl
  right_inv f := rfl

abbrev ExteriorCovector (n k : ℕ) := ⋀[ℝ]^k (Dual ℝ (Fin n → ℝ))

/-- Continuous alternating covectors are exterior powers of the algebraic dual. -/
def toExterior : ((Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) ≃ₗ[ℝ] ExteriorCovector n k :=
  forgetContinuous.trans (exteriorPower.alternatingMapLinearEquiv.trans
    (LinearEquiv.ofBijective _ (exteriorPower.bijective_pairingDual ℝ (Fin n → ℝ) k)).symm)

instance : FiniteDimensional ℝ ((Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) :=
  Module.Finite.equiv toExterior.symm

def wedgeFiber : ((Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ]
    ((Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin n → ℝ) [⋀^Fin (k+l)]→L[ℝ] ℝ) :=
  ((exteriorPower.wedge ℝ (Dual ℝ (Fin n → ℝ)) k l).compl₁₂
    toExterior.toLinearMap toExterior.toLinearMap).compr₂ toExterior.symm.toLinearMap

def wedge (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l) :
    Form (Fin n → ℝ) (k+l) := fun x => wedgeFiber (α x) (β x)

@[simp] theorem toExterior_wedgeFiber
    (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ) (β : (Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) :
    toExterior (wedgeFiber α β) =
      exteriorPower.wedge ℝ (Dual ℝ (Fin n → ℝ)) k l (toExterior α) (toExterior β) := by
  exact toExterior.apply_symm_apply _

end ProjectAInos.SmoothGeometry.DifferentialForm
