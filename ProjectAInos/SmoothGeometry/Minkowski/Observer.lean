/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Isometry

/-! # Unit future observers and their rest spaces -/

@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski

@[ext] structure Observer (d : ℕ) where
  velocity : MinkowskiModel d
  unit : intervalQuadratic velocity = 1
  future : 0 < time velocity

namespace Observer
variable {d : ℕ} (u : Observer d)

def clock : MinkowskiModel d →L[ℝ] ℝ := pair u.velocity

@[simp] theorem clock_velocity : u.clock u.velocity = 1 := u.unit

def restSpace : Submodule ℝ (MinkowskiModel d) := u.clock.toLinearMap.ker

def project : MinkowskiModel d →ₗ[ℝ] u.restSpace where
  toFun v := ⟨v - u.clock v • u.velocity, by simp [restSpace, map_sub, map_smul]⟩
  map_add' v w := by apply Subtype.ext; simp [map_add, add_smul]; abel
  map_smul' a v := by apply Subtype.ext; simp [map_smul, smul_sub, smul_smul]

@[simp] theorem project_coe (v : MinkowskiModel d) :
    (u.project v : MinkowskiModel d) = v - u.clock v • u.velocity := rfl

theorem decomposition (v : MinkowskiModel d) :
    u.clock v • u.velocity + u.project v = v := by simp

theorem clock_rest (v : u.restSpace) : u.clock v = 0 := v.property

def split : MinkowskiModel d ≃ₗ[ℝ] ℝ × u.restSpace where
  toFun v := (u.clock v, u.project v)
  invFun p := p.1 • u.velocity + p.2
  left_inv := u.decomposition
  right_inv p := by
    apply Prod.ext
    · simp [u.clock_rest]
    · apply Subtype.ext; simp [u.clock_rest]
  map_add' v w := by simp
  map_smul' a v := by simp

theorem restSpace_finrank : Module.finrank ℝ u.restSpace = d := by
  have h := u.split.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_pi,
    Fintype.card_fin] at h
  omega

def restForm : LinearMap.BilinForm ℝ u.restSpace :=
  -(pair.toLinearMap₁₂.compl₁₂ u.restSpace.subtype u.restSpace.subtype)

/-- A vector orthogonal to a unit timelike vector has negative Q unless it is zero. -/
theorem rest_negative (v : u.restSpace) (hne : v ≠ 0) :
    intervalQuadratic (v : MinkowskiModel d) < 0 := by
  have hu := u.unit
  rw [intervalQuadratic_coordinates] at hu
  have ho := u.clock_rest v
  change pair u.velocity (v : MinkowskiModel d) = 0 at ho
  rw [pair_apply] at ho
  have hc : (inner ℝ (space u.velocity) (space (v : MinkowskiModel d))) ^ 2 ≤
      ‖space u.velocity‖ ^ 2 * ‖space (v : MinkowskiModel d)‖ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _)
      (abs_real_inner_le_norm (space u.velocity) (space (v : MinkowskiModel d)))
    simpa only [← pow_two, sq_abs, mul_pow] using h
  have ht : time u.velocity ^ 2 > 0 := sq_pos_of_pos u.future
  have hn : 0 < ‖space (v : MinkowskiModel d)‖ ^ 2 := by
    by_contra h
    have hz : space (v : MinkowskiModel d) = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (space (v : MinkowskiModel d))])
    have hv0 : time (v : MinkowskiModel d) = 0 := by
      rw [hz, inner_zero_right] at ho
      exact (mul_eq_zero.mp (sub_eq_zero.mp ho)).resolve_left (ne_of_gt u.future)
    apply hne
    apply Subtype.ext
    rw [← vector_time_space (v : MinkowskiModel d), hz, hv0]
    ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [intervalQuadratic_coordinates]
  have hc' : (time u.velocity * time (v : MinkowskiModel d)) ^ 2 ≤
      ‖space u.velocity‖ ^ 2 * ‖space (v : MinkowskiModel d)‖ ^ 2 := by
    rw [sub_eq_zero.mp ho]
    exact hc
  nlinarith [sq_nonneg (time (v : MinkowskiModel d))]

theorem restForm_posDef : (LinearMap.BilinMap.toQuadraticMap u.restForm).PosDef := by
  intro v hv
  exact neg_pos.mpr (u.rest_negative v hv)

def transform (L : orthochronousLorentzGroup d) : Observer d where
  velocity := L.val.val u.velocity
  unit := (LorentzGroup.preserves_interval L.val u.velocity).trans u.unit
  future := by
    apply time_pos_of_futureCausal_ne_zero
    · apply (L.property u.velocity).mpr
      exact (futureCausal_iff _).mpr ⟨by unfold Causal; rw [u.unit]; norm_num, u.future.le⟩
    · intro h
      have hv : u.velocity = 0 := L.val.val.injective (by simpa using h)
      have := u.future
      simp [hv] at this

theorem clock_transform (L : orthochronousLorentzGroup d) (v : MinkowskiModel d) :
    (u.transform L).clock (L.val.val v) = u.clock v := L.val.property _ _

theorem decomposition_unique (v : MinkowskiModel d) (t : ℝ) (w : u.restSpace)
    (h : v = t • u.velocity + w) : t = u.clock v ∧ w = u.project v := by
  have hv : u.split v = (t,w) := by rw [h]; exact u.split.apply_symm_apply (t,w)
  exact ⟨(congrArg Prod.fst hv).symm, (congrArg Prod.snd hv).symm⟩

theorem restForm_convention (σ : LorentzConvention) (v w : u.restSpace) :
    u.restForm v w = -σ.timeSign * minkowskiForm σ d v w := by
  change -pair (v : MinkowskiModel d) (w : MinkowskiModel d) = _
  rw [metric_eq]
  simp [← mul_assoc]

theorem project_transform (L : orthochronousLorentzGroup d) (v : MinkowskiModel d) :
    ((u.transform L).project (L.val.val v) : MinkowskiModel d) =
      L.val.val (u.project v : MinkowskiModel d) := by
  rw [project_coe, clock_transform, project_coe, map_sub, map_smul]
  rfl

end Observer
end ProjectAInos.SmoothGeometry.Minkowski
