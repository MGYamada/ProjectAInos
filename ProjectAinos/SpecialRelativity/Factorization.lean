/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.Rapidity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# A Lorentz transformation is a rotation after a boost

Fix the inertial frame of the co-ordinates, whose observer has the velocity `timeAxis d`
(Landau–Lifshitz, *The Classical Theory of Fields*, §4). The rotations of this frame are the
Lorentz transformations that fix the time axis, `rotationGroup d`; they preserve the time and
the length of the space part of every vector.

Every orthochronous Lorentz transformation `L` is a rotation after a boost, in one way only:

* `boostPart L` is the velocity of the observer that `L` brings to rest, and
  `rotationPart L = L · (boost (boostPart L))⁻¹`;
* `rotationPart_mem`, `rotationPart_mul_boost`: `L = rotationPart L · boost (boostPart L)` with
  `rotationPart L` a rotation;
* `eq_of_mul_boost_eq`: if `L = R · boost β` with a rotation `R`, then `β = boostPart L` and
  `R = rotationPart L`.

For a boost the rotation is the identity (`rotationPart_boost`), and `L` is a rotation if and
only if its boost part is zero (`boostPart_eq_zero_iff`).

The product of two boosts is in general not a boost. `boostPart_boost_mul_boost` shows that its
boost part is the composition of the two velocities, and `wignerRotation β₁ β₂` is its rotation
part: `boost β₁ · boost β₂ = wignerRotation β₁ β₂ · boost β₃`
(`wignerRotation_mul_boost`). It is the identity if one of the velocities is zero, and if the
two velocities have the same direction: `boost_collinear_mul` shows that the product of the
boosts with the velocities `a e` and `b e` is the boost with the velocity
`((a + b)/(1 + ab)) e` (`wignerRotation_collinear`).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

/-! ### The rotations of the frame -/

theorem pair_timeAxis (v : MinkowskiModel d) : pair (timeAxis d) v = time v := by
  rw [pair_apply]
  simp [timeAxis]

/-- The observer at rest in the frame of the co-ordinates. -/
def restObserver (d : ℕ) : Observer d where
  velocity := timeAxis d
  unit := timeAxis_interval d
  future := by simp [timeAxis]

/-- The rotations of the frame: the Lorentz transformations that fix the time axis. -/
def rotationGroup (d : ℕ) : Subgroup (LorentzGroup d) where
  carrier := {R | R.val (timeAxis d) = timeAxis d}
  one_mem' := rfl
  mul_mem' := by
    intro R S hR hS
    change R.val (S.val (timeAxis d)) = timeAxis d
    rw [hS, hR]
  inv_mem' := by
    intro R hR
    change R.val.symm (timeAxis d) = timeAxis d
    rw [LinearEquiv.symm_apply_eq]
    exact hR.symm

theorem mem_rotationGroup_iff (R : LorentzGroup d) :
    R ∈ rotationGroup d ↔ R.val (timeAxis d) = timeAxis d := Iff.rfl

/-- A rotation preserves the time of every vector. -/
theorem time_rotation {R : LorentzGroup d} (hR : R ∈ rotationGroup d) (v : MinkowskiModel d) :
    time (R.val v) = time v := by
  rw [← pair_timeAxis, ← pair_timeAxis v]
  have h := LorentzGroup.preserves_pair R (timeAxis d) v
  rwa [(mem_rotationGroup_iff R).mp hR] at h

/-- A rotation preserves the length of the space part of every vector. -/
theorem norm_space_rotation {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (v : MinkowskiModel d) : ‖space (R.val v)‖ = ‖space v‖ := by
  have hQ := LorentzGroup.preserves_interval R v
  rw [intervalQuadratic_coordinates, intervalQuadratic_coordinates, time_rotation hR] at hQ
  have hsq : ‖space (R.val v)‖ ^ 2 = ‖space v‖ ^ 2 := by linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The rotations are orthochronous. -/
theorem rotationGroup_le_orthochronous : rotationGroup d ≤ orthochronousLorentzGroup d := by
  intro R hR v
  change ‖space (R.val v)‖ ≤ time (R.val v) ↔ ‖space v‖ ≤ time v
  rw [time_rotation hR, norm_space_rotation hR]

/-! ### Boosts and the time axis -/

/-- The boost of a velocity brings the observer with that velocity to rest. -/
theorem boost_observer (β : Velocity d) :
    (boost β).val β.observer.velocity = timeAxis d := by
  have hg := β.gamma_identity
  have hgp := β.gamma_pos
  have hinner : inner ℝ β.val (β.gamma • β.val) = β.gamma * ‖β.val‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hsq : β.gamma ^ 2 * ‖β.val‖ ^ 2 = β.gamma ^ 2 - 1 := by linarith
  rw [← vector_time_space ((boost β).val β.observer.velocity), timeAxis]
  congr 1
  · rw [boost_time]
    simp only [Velocity.observer, time_vector, space_vector, hinner]
    linarith
  · rw [boost_space]
    simp only [Velocity.observer, time_vector, space_vector, hinner]
    rw [← add_smul]
    have hcoef : β.gamma + (β.gamma ^ 2 / (1 + β.gamma) * (β.gamma * ‖β.val‖ ^ 2) -
        β.gamma * β.gamma) = 0 := by
      have h1 : β.gamma ^ 2 / (1 + β.gamma) * (β.gamma * ‖β.val‖ ^ 2) =
          β.gamma * (β.gamma ^ 2 * ‖β.val‖ ^ 2) / (1 + β.gamma) := by ring
      rw [h1, hsq]
      field_simp
      ring
    rw [hcoef, zero_smul]

theorem boost_symm_timeAxis (β : Velocity d) :
    (boost β).val.symm (timeAxis d) = β.observer.velocity := by
  rw [LinearEquiv.symm_apply_eq]
  exact (boost_observer β).symm

/-! ### The factorization -/

/-- The velocity of the observer that `L` brings to rest. -/
def boostPart (L : orthochronousLorentzGroup d) : Velocity d :=
  Velocity.ofObserver ((restObserver d).transform L⁻¹)

/-- The rotation that remains after the boost. -/
def rotationPart (L : orthochronousLorentzGroup d) : LorentzGroup d :=
  L.val * (boost (boostPart L))⁻¹

theorem observer_boostPart (L : orthochronousLorentzGroup d) :
    (boostPart L).observer.velocity = L.val.val.symm (timeAxis d) := by
  rw [boostPart, Velocity.observer_ofObserver]
  rfl

/-- `L` brings the observer with the velocity `boostPart L` to rest. -/
theorem apply_observer_boostPart (L : orthochronousLorentzGroup d) :
    L.val.val (boostPart L).observer.velocity = timeAxis d := by
  rw [observer_boostPart, LinearEquiv.apply_symm_apply]

/-- The rotation part is a rotation. -/
theorem rotationPart_mem (L : orthochronousLorentzGroup d) : rotationPart L ∈ rotationGroup d := by
  change L.val.val ((boost (boostPart L)).val.symm (timeAxis d)) = timeAxis d
  rw [boost_symm_timeAxis, apply_observer_boostPart]

/-- Every orthochronous Lorentz transformation is a rotation after a boost. -/
theorem rotationPart_mul_boost (L : orthochronousLorentzGroup d) :
    rotationPart L * boost (boostPart L) = L.val := by
  rw [rotationPart, inv_mul_cancel_right]

/-- The factorization is unique. -/
theorem eq_of_mul_boost_eq (L : orthochronousLorentzGroup d) {R : LorentzGroup d}
    (hR : R ∈ rotationGroup d) {β : Velocity d} (h : R * boost β = L.val) :
    β = boostPart L ∧ R = rotationPart L := by
  have hβ : β = boostPart L := by
    apply Velocity.observerEquiv.injective
    apply Observer.ext
    change β.observer.velocity = (boostPart L).observer.velocity
    rw [observer_boostPart, ← h, LinearEquiv.eq_symm_apply]
    change R.val ((boost β).val β.observer.velocity) = timeAxis d
    rw [boost_observer]
    exact hR
  refine ⟨hβ, ?_⟩
  rw [rotationPart, ← h, hβ, mul_inv_cancel_right]

/-- The boost part of a boost is its velocity. -/
theorem boostPart_boost (β : Velocity d) : boostPart (boostOrthochronous β) = β :=
  ((eq_of_mul_boost_eq (boostOrthochronous β) (rotationGroup d).one_mem
    (one_mul (boost β))).1).symm

/-- The rotation part of a boost is the identity. -/
theorem rotationPart_boost (β : Velocity d) : rotationPart (boostOrthochronous β) = 1 :=
  ((eq_of_mul_boost_eq (boostOrthochronous β) (rotationGroup d).one_mem
    (one_mul (boost β))).2).symm

/-- A transformation is a rotation if and only if its boost part is zero. -/
theorem boostPart_eq_zero_iff (L : orthochronousLorentzGroup d) :
    boostPart L = Velocity.zero d ↔ L.val ∈ rotationGroup d := by
  constructor
  · intro h
    have hmem := rotationPart_mem L
    have hmul := rotationPart_mul_boost L
    rw [h, boost_zero, mul_one] at hmul
    rwa [hmul] at hmem
  · intro h
    have hmul : L.val * boost (Velocity.zero d) = L.val := by rw [boost_zero, mul_one]
    exact ((eq_of_mul_boost_eq L h hmul).1).symm

/-! ### The product of two boosts -/

/-- The boost part of a product of two boosts is the composition of the velocities. -/
theorem boostPart_boost_mul_boost (β₁ β₂ : Velocity d) :
    boostPart (boostOrthochronous β₁ * boostOrthochronous β₂) =
      Velocity.transform (boostOrthochronous β₂)⁻¹ β₁ := by
  apply Velocity.observerEquiv.injective
  apply Observer.ext
  change (boostPart (boostOrthochronous β₁ * boostOrthochronous β₂)).observer.velocity =
    (Velocity.transform (boostOrthochronous β₂)⁻¹ β₁).observer.velocity
  rw [observer_boostPart, Velocity.transform, Velocity.observer_ofObserver]
  change (boost β₂).val.symm ((boost β₁).val.symm (timeAxis d)) =
    (boost β₂).val.symm β₁.observer.velocity
  rw [boost_symm_timeAxis]

/-- The rotation that remains in the product of two boosts. -/
def wignerRotation (β₁ β₂ : Velocity d) : LorentzGroup d :=
  rotationPart (boostOrthochronous β₁ * boostOrthochronous β₂)

theorem wignerRotation_mem (β₁ β₂ : Velocity d) : wignerRotation β₁ β₂ ∈ rotationGroup d :=
  rotationPart_mem _

/-- The product of two boosts is a rotation after the boost of the composed velocity. -/
theorem wignerRotation_mul_boost (β₁ β₂ : Velocity d) :
    wignerRotation β₁ β₂ * boost (Velocity.transform (boostOrthochronous β₂)⁻¹ β₁) =
      boost β₁ * boost β₂ := by
  have h := rotationPart_mul_boost (boostOrthochronous β₁ * boostOrthochronous β₂)
  rw [boostPart_boost_mul_boost] at h
  exact h

/-- If the product of two boosts is a boost, the rotation is the identity. -/
theorem wignerRotation_eq_one_of_boost {β₁ β₂ β₃ : Velocity d}
    (h : boost β₁ * boost β₂ = boost β₃) : wignerRotation β₁ β₂ = 1 :=
  ((eq_of_mul_boost_eq (boostOrthochronous β₁ * boostOrthochronous β₂)
    (rotationGroup d).one_mem (β := β₃) (by rw [one_mul]; exact h.symm)).2).symm

/-- No rotation remains if the second velocity is zero. -/
theorem wignerRotation_zero_right (β : Velocity d) :
    wignerRotation β (Velocity.zero d) = 1 :=
  wignerRotation_eq_one_of_boost (β₃ := β) (by rw [boost_zero, mul_one])

/-- No rotation remains if the first velocity is zero. -/
theorem wignerRotation_zero_left (β : Velocity d) :
    wignerRotation (Velocity.zero d) β = 1 :=
  wignerRotation_eq_one_of_boost (β₃ := β) (by rw [boost_zero, one_mul])

/-! ### Collinear boosts -/

section Collinear

variable (e : Space d) (he : ‖e‖ = 1)

include he in
theorem inner_self_of_norm_one : inner ℝ e e = 1 := by
  rw [real_inner_self_eq_norm_sq, he, one_pow]

/-- `γ² (1 − b²) = 1` for the velocity `b e`. -/
theorem gamma_collinear_identity (b : ℝ) (hb : |b| < 1) :
    (collinearVelocity e he b hb).gamma ^ 2 * (1 - b ^ 2) = 1 := by
  have h := (collinearVelocity e he b hb).gamma_identity
  have hn : ‖(collinearVelocity e he b hb).val‖ ^ 2 = b ^ 2 := by
    change ‖b • e‖ ^ 2 = b ^ 2
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  rwa [hn] at h

/-- The factor `γ` of the composed velocity is `γ₁ γ₂ (1 + ab)`. -/
theorem gamma_collinear_composed (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    (collinearVelocity e he ((a + b) / (1 + a * b)) (composed_speed_lt_one a b ha hb)).gamma =
      (collinearVelocity e he a ha).gamma * (collinearVelocity e he b hb).gamma *
        (1 + a * b) := by
  have hab : 0 < 1 + a * b := by
    have h1 := abs_lt.mp ha
    have h2 := abs_lt.mp hb
    nlinarith
  have hga := gamma_collinear_identity e he a ha
  have hgb := gamma_collinear_identity e he b hb
  have hgc := gamma_collinear_identity e he ((a + b) / (1 + a * b))
    (composed_speed_lt_one a b ha hb)
  have hpa := (collinearVelocity e he a ha).gamma_pos
  have hpb := (collinearVelocity e he b hb).gamma_pos
  have hpc := (collinearVelocity e he ((a + b) / (1 + a * b))
    (composed_speed_lt_one a b ha hb)).gamma_pos
  have hgap : 1 - ((a + b) / (1 + a * b)) ^ 2 =
      (1 - a ^ 2) * (1 - b ^ 2) / (1 + a * b) ^ 2 := by
    field_simp
    ring
  have ha2 : 0 < 1 - a ^ 2 := by
    have h1 := abs_lt.mp ha
    nlinarith
  have hb2 : 0 < 1 - b ^ 2 := by
    have h1 := abs_lt.mp hb
    nlinarith
  refine (sq_eq_sq₀ hpc.le (by positivity)).mp ?_
  rw [hgap] at hgc
  have hprod : ((collinearVelocity e he a ha).gamma * (collinearVelocity e he b hb).gamma *
      (1 + a * b)) ^ 2 * ((1 - a ^ 2) * (1 - b ^ 2) / (1 + a * b) ^ 2) = 1 := by
    field_simp
    nlinarith [hga, hgb]
  have hne : (1 - a ^ 2) * (1 - b ^ 2) / (1 + a * b) ^ 2 ≠ 0 := by positivity
  exact mul_right_cancel₀ hne (hgc.trans hprod.symm)

/-- `γ²/(1 + γ) · b² = γ − 1` for the velocity `b e`. -/
theorem gamma_collinear_ratio (b : ℝ) (hb : |b| < 1) :
    (collinearVelocity e he b hb).gamma ^ 2 / (1 + (collinearVelocity e he b hb).gamma) *
      b ^ 2 = (collinearVelocity e he b hb).gamma - 1 := by
  have h := gamma_collinear_identity e he b hb
  have hp := (collinearVelocity e he b hb).gamma_pos
  field_simp
  nlinarith

/-- The time of a vector after a boost along `e`: `γ (t − b s)` with `s` its component along
`e`. -/
theorem boost_collinear_time (b : ℝ) (hb : |b| < 1) (v : MinkowskiModel d) :
    time ((boost (collinearVelocity e he b hb)).val v) =
      (collinearVelocity e he b hb).gamma * (time v - b * inner ℝ e (space v)) := by
  rw [boost_time]
  change _ * (time v - inner ℝ (b • e) (space v)) = _
  rw [real_inner_smul_left]

/-- The space part of a vector after a boost along `e`:
`x + ((γ − 1) s − γ b t) e`. -/
theorem boost_collinear_space (b : ℝ) (hb : |b| < 1) (v : MinkowskiModel d) :
    space ((boost (collinearVelocity e he b hb)).val v) = space v +
      (((collinearVelocity e he b hb).gamma - 1) * inner ℝ e (space v) -
        (collinearVelocity e he b hb).gamma * b * time v) • e := by
  have hr := gamma_collinear_ratio e he b hb
  rw [boost_space]
  change space v + (_ * inner ℝ (b • e) (space v) - _) • (b • e) = _
  rw [real_inner_smul_left, smul_smul]
  congr 2
  linear_combination inner ℝ e (space v) * hr

/-- The product of two boosts along the same direction is the boost of the composed
velocity. -/
theorem boost_collinear_mul (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    boost (collinearVelocity e he a ha) * boost (collinearVelocity e he b hb) =
      boost (collinearVelocity e he ((a + b) / (1 + a * b))
        (composed_speed_lt_one a b ha hb)) := by
  have hab : 1 + a * b ≠ 0 := by
    have h1 := abs_lt.mp ha
    have h2 := abs_lt.mp hb
    nlinarith
  have hgc := gamma_collinear_composed e he a b ha hb
  have hee := inner_self_of_norm_one e he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (boost (collinearVelocity e he a ha)).val
    ((boost (collinearVelocity e he b hb)).val v) = _
  have hin : inner ℝ e (space ((boost (collinearVelocity e he b hb)).val v)) =
      (collinearVelocity e he b hb).gamma * (inner ℝ e (space v) - b * time v) := by
    rw [boost_collinear_space, inner_add_right, real_inner_smul_right, hee]
    ring
  have hc : (1 + a * b) * ((a + b) / (1 + a * b)) = a + b := by
    field_simp
  rw [← vector_time_space ((boost (collinearVelocity e he a ha)).val _),
    ← vector_time_space ((boost (collinearVelocity e he ((a + b) / (1 + a * b)) _)).val v)]
  congr 1
  · rw [boost_collinear_time e he a ha, hin, boost_collinear_time e he b hb,
      boost_collinear_time e he ((a + b) / (1 + a * b)) (composed_speed_lt_one a b ha hb) v, hgc]
    linear_combination ((collinearVelocity e he a ha).gamma *
      (collinearVelocity e he b hb).gamma * inner ℝ e (space v)) * hc
  · rw [boost_collinear_space e he a ha, hin, boost_collinear_time e he b hb,
      boost_collinear_space e he b hb,
      boost_collinear_space e he ((a + b) / (1 + a * b)) (composed_speed_lt_one a b ha hb) v,
      hgc, add_assoc, ← add_smul]
    congr 2
    linear_combination ((collinearVelocity e he a ha).gamma *
      (collinearVelocity e he b hb).gamma * time v) * hc

/-- No rotation remains in the product of two boosts along the same direction. -/
theorem wignerRotation_collinear (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    wignerRotation (collinearVelocity e he a ha) (collinearVelocity e he b hb) = 1 :=
  wignerRotation_eq_one_of_boost (boost_collinear_mul e he a b ha hb)

end Collinear

end ProjectAinos.SpecialRelativity
