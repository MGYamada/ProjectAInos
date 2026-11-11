/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Isometry

/-! # Reflections in non-null Minkowski directions -/
@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski
variable {d : ℕ}

def reflectionLinear (u : MinkowskiModel d) : MinkowskiModel d →ₗ[ℝ] MinkowskiModel d :=
  LinearMap.id - (pair u).toLinearMap.smulRight ((2 / intervalQuadratic u) • u)

theorem reflectionLinear_apply (u v : MinkowskiModel d) :
    reflectionLinear u v = v - (2 / intervalQuadratic u * pair u v) • u := by
  simp [reflectionLinear, smul_smul, mul_comm]

theorem pair_reflection (u v : MinkowskiModel d) (hu : intervalQuadratic u ≠ 0) :
    pair u (reflectionLinear u v) = -pair u v := by
  rw [reflectionLinear_apply, map_sub, map_smul]
  change pair u v - (2 / intervalQuadratic u * pair u v) * intervalQuadratic u = _
  field_simp
  ring

theorem reflection_involutive (u : MinkowskiModel d) (hu : intervalQuadratic u ≠ 0) :
    Function.Involutive (reflectionLinear u) := by
  intro v
  rw [reflectionLinear_apply, pair_reflection u v hu, reflectionLinear_apply]
  simp [mul_neg, neg_smul]

theorem reflection_preserves_pair (u v w : MinkowskiModel d) (hu : intervalQuadratic u ≠ 0) :
    pair (reflectionLinear u v) (reflectionLinear u w) = pair v w := by
  simp only [reflectionLinear_apply, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  rw [pair_comm v u]
  rw [← intervalQuadratic_apply u]
  field_simp
  ring

def reflection (u : MinkowskiModel d) (hu : intervalQuadratic u ≠ 0) : LorentzGroup d :=
  ⟨{ toLinearMap := reflectionLinear u
     invFun := reflectionLinear u
     left_inv := reflection_involutive u hu
     right_inv := reflection_involutive u hu },
    fun v w => reflection_preserves_pair u v w hu⟩

theorem reflectionLinear_neg (u v : MinkowskiModel d) :
    reflectionLinear (-u) v = reflectionLinear u v := by
  simp [reflectionLinear_apply, map_neg, neg_smul]

theorem reflection_natural (L : LorentzGroup d) (u v : MinkowskiModel d) :
    L.val (reflectionLinear u v) = reflectionLinear (L.val u) (L.val v) := by
  simp only [reflectionLinear_apply, map_sub, map_smul,
    LorentzGroup.preserves_interval, LorentzGroup.preserves_pair]

end ProjectAInos.SmoothGeometry.Minkowski
