/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SpecialRelativity.Spacetime
public import ProjectAInos.SmoothGeometry.Minkowski.ReflectionDeterminant

/-! # Subluminal velocities and passive Lorentz boosts

Boosts are constructed as products of two Lorentz reflections. This proves
metric preservation before deriving their coordinate formulas.
-/
@[expose] public section
noncomputable section
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry SmoothGeometry.Minkowski
variable {d : ℕ}

abbrev Velocity (d : ℕ) := {v : Space d // ‖v‖ < 1}

namespace Velocity

def gamma (β : Velocity d) : ℝ := (Real.sqrt (1 - ‖β.val‖ ^ 2))⁻¹

theorem gap_pos (β : Velocity d) : 0 < 1 - ‖β.val‖ ^ 2 := by
  have h := β.property
  nlinarith [norm_nonneg β.val]

theorem gamma_pos (β : Velocity d) : 0 < β.gamma :=
  inv_pos.mpr (Real.sqrt_pos.mpr β.gap_pos)

theorem gamma_identity (β : Velocity d) : β.gamma ^ 2 * (1 - ‖β.val‖ ^ 2) = 1 := by
  rw [gamma, inv_pow, Real.sq_sqrt β.gap_pos.le, inv_mul_cancel₀ (ne_of_gt β.gap_pos)]

def observer (β : Velocity d) : Observer d where
  velocity := vector β.gamma (β.gamma • β.val)
  unit := by
    rw [intervalQuadratic_coordinates, time_vector, space_vector, norm_smul,
      Real.norm_eq_abs, abs_of_pos β.gamma_pos]
    nlinarith [β.gamma_identity]
  future := β.gamma_pos

def neg (β : Velocity d) : Velocity d := ⟨-β.val, by simpa using β.property⟩

@[simp] theorem neg_val (β : Velocity d) : β.neg.val = -β.val := rfl

@[simp] theorem gamma_neg (β : Velocity d) : β.neg.gamma = β.gamma := by
  simp [gamma, neg]

end Velocity

def timeAxis (d : ℕ) : MinkowskiModel d := vector 1 0

@[simp] theorem timeAxis_interval (d : ℕ) : intervalQuadratic (timeAxis d) = 1 := by
  simp [intervalQuadratic_coordinates, timeAxis]

def boostNormal (β : Velocity d) : MinkowskiModel d := timeAxis d + β.observer.velocity

theorem boostNormal_interval (β : Velocity d) :
    intervalQuadratic (boostNormal β) = 2 * (1 + β.gamma) := by
  have h := β.observer.unit
  simp only [intervalQuadratic_coordinates, Velocity.observer, time_vector, space_vector,
    norm_smul, Real.norm_eq_abs, abs_of_pos β.gamma_pos] at h
  simp only [boostNormal, intervalQuadratic_coordinates, map_add, timeAxis, time_vector,
    space_vector, Velocity.observer, zero_add, norm_smul, Real.norm_eq_abs,
    abs_of_pos β.gamma_pos]
  nlinarith

theorem boostNormal_nonnull (β : Velocity d) : intervalQuadratic (boostNormal β) ≠ 0 := by
  rw [boostNormal_interval]; have := β.gamma_pos; positivity

def boost (β : Velocity d) : LorentzGroup d :=
  reflection (timeAxis d) (by simp) * reflection (boostNormal β) (boostNormal_nonnull β)

theorem time_reflection_timeAxis (v : MinkowskiModel d) :
    time (reflectionLinear (timeAxis d) v) = -time v := by
  rw [reflectionLinear_apply, timeAxis_interval]
  simp [pair_apply, timeAxis]
  ring

theorem space_reflection_timeAxis (v : MinkowskiModel d) :
    space (reflectionLinear (timeAxis d) v) = space v := by
  simp [reflectionLinear_apply, timeAxis]

theorem boost_time (β : Velocity d) (v : MinkowskiModel d) :
    time ((boost β).val v) = β.gamma * (time v - inner ℝ β.val (space v)) := by
  change time (reflectionLinear (timeAxis d) (reflectionLinear (boostNormal β) v)) = _
  rw [time_reflection_timeAxis, reflectionLinear_apply]
  rw [boostNormal_interval]
  simp only [map_sub, map_smul, smul_eq_mul]
  rw [pair_apply]
  simp only [
    boostNormal, map_add, timeAxis, time_vector, space_vector, Velocity.observer,
    zero_add, real_inner_smul_left]
  have h : 1 + β.gamma ≠ 0 := by have := β.gamma_pos; linarith
  field_simp
  ring

theorem boost_space (β : Velocity d) (v : MinkowskiModel d) :
    space ((boost β).val v) = space v +
      (β.gamma ^ 2 / (1 + β.gamma) * inner ℝ β.val (space v) - β.gamma * time v) • β.val := by
  change space (reflectionLinear (timeAxis d) (reflectionLinear (boostNormal β) v)) = _
  rw [space_reflection_timeAxis, reflectionLinear_apply]
  rw [boostNormal_interval]
  simp only [map_sub, map_smul]
  rw [pair_apply]
  simp only [boostNormal,
    map_add, timeAxis, time_vector, space_vector, Velocity.observer, zero_add,
    real_inner_smul_left, smul_smul]
  have h : 1 + β.gamma ≠ 0 := by have := β.gamma_pos; linarith
  have he : -(2 / (2 * (1 + β.gamma)) *
      ((1 + β.gamma) * time v - β.gamma * inner ℝ β.val (space v)) * β.gamma) =
      β.gamma ^ 2 / (1 + β.gamma) * inner ℝ β.val (space v) - β.gamma * time v := by
    field_simp; ring
  rw [sub_eq_add_neg, ← neg_smul, he]

theorem boost_future (β : Velocity d) (v : MinkowskiModel d) :
    FutureCausal ((boost β).val v) ↔ FutureCausal v := by
  rw [futureCausal_iff, futureCausal_iff]
  simp only [Causal, LorentzGroup.preserves_interval, boost_time]
  have hg := β.gamma_pos
  have hb := β.property
  have hn := norm_nonneg (space v)
  have hb0 := norm_nonneg β.val
  have hi := abs_real_inner_le_norm β.val (space v)
  have hil := neg_abs_le (inner ℝ β.val (space v))
  have hir := le_abs_self (inner ℝ β.val (space v))
  rw [intervalQuadratic_coordinates]
  constructor
  · rintro ⟨hq, ht⟩
    refine ⟨hq, ?_⟩
    have htd := (mul_nonneg_iff_of_pos_left hg).mp ht
    by_contra h
    have ht0 : time v < 0 := lt_of_not_ge h
    have hnle : ‖space v‖ ≤ -time v := by nlinarith
    nlinarith
  · rintro ⟨hq, ht⟩
    refine ⟨hq, mul_nonneg hg.le ?_⟩
    have hnle : ‖space v‖ ≤ time v := by nlinarith
    nlinarith

def boostOrthochronous (β : Velocity d) : orthochronousLorentzGroup d :=
  ⟨boost β, boost_future β⟩

theorem reflected_boostNormal_neg (β : Velocity d) :
    reflectionLinear (timeAxis d) (boostNormal β.neg) = -boostNormal β := by
  rw [← vector_time_space (reflectionLinear (timeAxis d) (boostNormal β.neg)),
    ← vector_time_space (-boostNormal β)]
  congr 1
  · rw [time_reflection_timeAxis]
    simp [boostNormal, timeAxis, Velocity.observer]
  · rw [space_reflection_timeAxis]
    simp [boostNormal, timeAxis, Velocity.observer]

theorem boost_neg_inverse (β : Velocity d) : boost β.neg = (boost β)⁻¹ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change reflectionLinear (timeAxis d) (reflectionLinear (boostNormal β.neg) v) =
    reflectionLinear (boostNormal β) (reflectionLinear (timeAxis d) v)
  have h := reflection_natural (reflection (timeAxis d) (by simp)) (boostNormal β.neg) v
  change reflectionLinear (timeAxis d) (reflectionLinear (boostNormal β.neg) v) =
    reflectionLinear (reflectionLinear (timeAxis d) (boostNormal β.neg))
      (reflectionLinear (timeAxis d) v) at h
  simpa only [reflected_boostNormal_neg, reflectionLinear_neg] using h

theorem boost_det (β : Velocity d) : (boost β).val.toLinearMap.det = 1 := by
  change (reflectionLinear (timeAxis d) ∘ₗ reflectionLinear (boostNormal β)).det = 1
  rw [LinearMap.det_comp, reflectionLinear_det _ (by simp),
    reflectionLinear_det _ (boostNormal_nonnull β)]
  norm_num

def boostProperOrthochronous (β : Velocity d) : properOrthochronousLorentzGroup d :=
  ⟨boost β, ⟨by
    change (boost β).val.det = 1
    apply Units.ext
    simpa only [LinearEquiv.coe_det, Units.val_one] using boost_det β,
    boost_future β⟩⟩

end ProjectAInos.SpecialRelativity
