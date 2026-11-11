/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SpecialRelativity.Velocity

/-! # Collinear velocity composition and rapidity -/
@[expose] public section
noncomputable section
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry SmoothGeometry.Minkowski
variable {d : ℕ}

def collinearVelocity (e : Space d) (he : ‖e‖ = 1) (b : ℝ) (hb : |b| < 1) : Velocity d :=
  ⟨b • e, by simpa [norm_smul, he] using hb⟩

theorem transform_collinear (e : Space d) (he : ‖e‖ = 1) (a b : ℝ)
    (ha : |a| < 1) (hb : |b| < 1) :
    (Velocity.transform (boostOrthochronous (collinearVelocity e he b hb))
      (collinearVelocity e he a ha)).val = ((a-b)/(1-b*a)) • e := by
  let β := collinearVelocity e he b hb
  have hg := β.gamma_identity
  have hg0 := β.gamma_pos
  have hn : ‖β.val‖^2 = b^2 := by simp [β, collinearVelocity, norm_smul, he, sq_abs]
  rw [hn] at hg
  have hi : inner ℝ (b • e) (a • e) = b*a := by
    simp [real_inner_smul_left, real_inner_smul_right, he, mul_comm]
  rw [Velocity.transform_boost]
  change (β.gamma * (1-inner ℝ (b • e) (a • e)))⁻¹ •
    (a • e + (β.gamma^2 / (1+β.gamma) * inner ℝ (b • e) (a • e) - β.gamma) • (b • e)) = _
  rw [hi, smul_smul, ← add_smul, smul_smul]
  congr 1
  have hp : 1+β.gamma ≠ 0 := by positivity
  have hab : 1-b*a ≠ 0 := by
    have h := abs_mul b a
    have hba : |b*a| < 1 := by rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg b]
    exact ne_of_gt (by linarith [le_abs_self (b*a)])
  field_simp
  linear_combination -a * hg

def rapidity (b : ℝ) : ℝ := Real.artanh b

theorem tanh_add (x y : ℝ) :
    Real.tanh (x+y) = (Real.tanh x + Real.tanh y)/(1+Real.tanh x*Real.tanh y) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem rapidity_add (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    rapidity ((a+b)/(1+a*b)) = rapidity a + rapidity b := by
  have ha' : a ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp ha
  have hb' : b ∈ Set.Ioo (-1 : ℝ) 1 := abs_lt.mp hb
  have h := tanh_add (Real.artanh a) (Real.artanh b)
  rw [Real.tanh_artanh ha', Real.tanh_artanh hb'] at h
  rw [rapidity, ← h, Real.artanh_tanh]
  rfl

theorem composed_speed_lt_one (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    |(a+b)/(1+a*b)| < 1 := by
  rw [← Real.tanh_artanh (show a ∈ Set.Ioo (-1 : ℝ) 1 from abs_lt.mp ha),
    ← Real.tanh_artanh (show b ∈ Set.Ioo (-1 : ℝ) 1 from abs_lt.mp hb), ← tanh_add]
  exact Real.abs_tanh_lt_one _

end ProjectAInos.SpecialRelativity
