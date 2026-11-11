/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SpecialRelativity.Boost
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-! # The Lorentz action on the open velocity ball -/
@[expose] public section
noncomputable section
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry SmoothGeometry.Minkowski
variable {d : ℕ}

namespace Velocity

def zero (d : ℕ) : Velocity d := ⟨0, by simp⟩

@[simp] theorem gamma_zero : (zero d).gamma = 1 := by simp [gamma, zero]

def ofObserver (u : Observer d) : Velocity d :=
  ⟨(time u.velocity)⁻¹ • space u.velocity, by
    have hu := u.unit
    rw [intervalQuadratic_coordinates] at hu
    have hn : ‖space u.velocity‖ < time u.velocity := by
      nlinarith [norm_nonneg (space u.velocity), u.future]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos u.future]
    exact (inv_mul_lt_iff₀ u.future).mpr (by simpa using hn)⟩

theorem gamma_ofObserver (u : Observer d) : (ofObserver u).gamma = time u.velocity := by
  have ht := u.future
  have hu := u.unit
  rw [intervalQuadratic_coordinates] at hu
  have hs : Real.sqrt (1 - ‖(ofObserver u).val‖ ^ 2) = (time u.velocity)⁻¹ := by
    apply (Real.sqrt_eq_iff_eq_sq (ofObserver u).gap_pos.le (by positivity)).mpr
    simp only [ofObserver, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]
    field_simp
    nlinarith
  rw [gamma, hs, inv_inv]

@[simp] theorem observer_ofObserver (u : Observer d) : (ofObserver u).observer = u := by
  apply Observer.ext
  change vector (ofObserver u).gamma ((ofObserver u).gamma • (ofObserver u).val) = u.velocity
  rw [gamma_ofObserver]
  simp only [ofObserver, smul_smul, mul_inv_cancel₀ (ne_of_gt u.future), one_smul,
    vector_time_space]

@[simp] theorem ofObserver_observer (β : Velocity d) : ofObserver β.observer = β := by
  apply Subtype.ext
  simp only [ofObserver, observer, time_vector, space_vector, smul_smul,
    inv_mul_cancel₀ (ne_of_gt β.gamma_pos), one_smul]

def observerEquiv : Velocity d ≃ Observer d where
  toFun := observer
  invFun := ofObserver
  left_inv := ofObserver_observer
  right_inv := observer_ofObserver

/-- Passive velocity transformation, including rotations as well as boosts. -/
def transform (L : orthochronousLorentzGroup d) (β : Velocity d) : Velocity d :=
  ofObserver (β.observer.transform L)

@[simp] theorem transform_one (β : Velocity d) : transform 1 β = β := by
  have h : β.observer.transform 1 = β.observer := by rfl
  rw [transform, h, ofObserver_observer]

theorem transform_mul (L K : orthochronousLorentzGroup d) (β : Velocity d) :
    transform (L*K) β = transform L (transform K β) := by
  simp only [transform, observer_ofObserver]
  rfl

instance : MulAction (orthochronousLorentzGroup d) (Velocity d) where
  smul := transform
  one_smul := transform_one
  mul_smul := transform_mul

/-- Subluminality is preserved by the entire time-oriented Lorentz group. -/
theorem norm_transform_lt_one (L : orthochronousLorentzGroup d) (β : Velocity d) :
    ‖(transform L β).val‖ < 1 := (transform L β).property

theorem transform_boost (β v : Velocity d) :
    (transform (boostOrthochronous β) v).val =
      (β.gamma * (1 - inner ℝ β.val v.val))⁻¹ •
        (v.val + (β.gamma^2 / (1+β.gamma) * inner ℝ β.val v.val - β.gamma) • β.val) := by
  change (time ((boost β).val v.observer.velocity))⁻¹ •
    space ((boost β).val v.observer.velocity) = _
  rw [boost_time, boost_space]
  simp only [observer, time_vector, space_vector, real_inner_smul_right]
  have ht : β.gamma * (v.gamma - v.gamma * inner ℝ β.val v.val) =
      v.gamma * (β.gamma * (1-inner ℝ β.val v.val)) := by ring
  have hx : v.gamma • v.val +
      (β.gamma^2 / (1+β.gamma) * (v.gamma * inner ℝ β.val v.val) - β.gamma * v.gamma) • β.val =
      v.gamma • (v.val + (β.gamma^2 / (1+β.gamma) * inner ℝ β.val v.val - β.gamma) • β.val) := by
    rw [smul_add, smul_smul]
    congr 1
    congr 1
    ring
  rw [ht, hx, mul_inv_rev, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt v.gamma_pos), mul_one]

end Velocity

@[simp] theorem boost_zero : boost (Velocity.zero d) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [← vector_time_space ((boost (Velocity.zero d)).val v)]
  rw [boost_time, boost_space]
  simpa [Velocity.gamma, Velocity.zero] using vector_time_space v

end ProjectAInos.SpecialRelativity
