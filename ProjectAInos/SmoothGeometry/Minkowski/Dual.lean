/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Basic

/-! # Raising and lowering Minkowski covectors -/

@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski

variable (σ : LorentzConvention) {d : ℕ}

def sharpLinear : (MinkowskiModel d →L[ℝ] ℝ) →ₗ[ℝ] MinkowskiModel d where
  toFun α i := lorentzSign σ i * α (Pi.single i 1)
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]

theorem sharp_flat (v : MinkowskiModel d) :
    sharpLinear σ (minkowskiForm σ d v) = v := by
  ext i
  simp [sharpLinear, minkowskiForm_apply, Pi.single_apply, mul_ite,
    ← mul_assoc]

theorem flat_sharp (α : MinkowskiModel d →L[ℝ] ℝ) :
    minkowskiForm σ d (sharpLinear σ α) = α := by
  ext w
  have hw : (∑ i : Fin (d+1), w i • Pi.single i (1 : ℝ)) = w := by
    ext i; simp [Pi.single_apply, mul_ite]
  calc
    minkowskiForm σ d (sharpLinear σ α) w =
        ∑ i, w i * α (Pi.single i 1) := by
      rw [minkowskiForm_apply]
      apply Finset.sum_congr rfl
      intro i _
      change lorentzSign σ i * (lorentzSign σ i * α (Pi.single i 1) * w i) = _
      calc
        _ = (lorentzSign σ i * lorentzSign σ i) * (w i * α (Pi.single i 1)) := by ring
        _ = _ := by rw [lorentzSign_sq, one_mul]
    _ = α (∑ i, w i • Pi.single i 1) := by simp
    _ = α w := by rw [hw]

/-- Metric duality as a continuous linear equivalence. -/
def flat : MinkowskiModel d ≃L[ℝ] (MinkowskiModel d →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toLinearMap := (minkowskiForm σ d).toLinearMap
      invFun := sharpLinear σ
      left_inv := sharp_flat σ
      right_inv := flat_sharp σ }

def sharp : (MinkowskiModel d →L[ℝ] ℝ) ≃L[ℝ] MinkowskiModel d := (flat σ).symm

@[simp] theorem flat_apply (v w : MinkowskiModel d) :
    flat σ v w = minkowskiForm σ d v w := rfl

@[simp] theorem sharp_apply (α : MinkowskiModel d →L[ℝ] ℝ) (i : Fin (d+1)) :
    sharp σ α i = lorentzSign σ i * α (Pi.single i 1) := rfl

end ProjectAInos.SmoothGeometry.Minkowski
