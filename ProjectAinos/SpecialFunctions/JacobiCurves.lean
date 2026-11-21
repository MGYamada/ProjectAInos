/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.JacobiElliptic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-! # Curves of Jacobi elliptic functions in three coordinates -/

@[expose] public section
noncomputable section

open scoped Real

namespace ProjectAinos.SpecialFunctions.JacobiElliptic

/-! ### Curves of Jacobi's functions -/

/-- The curve `(A cn, B sn, C dn)(p t)`. -/
def jacobiCurve (A B C p k t : ℝ) : Fin 3 → ℝ :=
  ![A * cn k (p * t), B * sn k (p * t), C * dn k (p * t)]

theorem jacobiCurve_zero (A B C p k : ℝ) : jacobiCurve A B C p k 0 = ![A, 0, C] := by
  simp [jacobiCurve]

/-- A curve `(A cn, B sn, C dn)(p t)` solves `L̇₀ = a₀ L₁ L₂`, `L̇₁ = a₁ L₂ L₀`,
`L̇₂ = a₂ L₀ L₁` when the amplitudes, the rate and the modulus satisfy three
relations. -/
theorem hasDerivAt_jacobiCurve {k : ℝ} (hk : k ^ 2 < 1) {a₀ a₁ a₂ A B C p : ℝ}
    (h0 : -(A * p) = a₀ * (B * C)) (h1 : B * p = a₁ * (C * A))
    (h2 : -(C * p * k ^ 2) = a₂ * (A * B)) (t : ℝ) :
    HasDerivAt (jacobiCurve A B C p k)
      ![a₀ * (jacobiCurve A B C p k t 1 * jacobiCurve A B C p k t 2),
        a₁ * (jacobiCurve A B C p k t 2 * jacobiCurve A B C p k t 0),
        a₂ * (jacobiCurve A B C p k t 0 * jacobiCurve A B C p k t 1)] t := by
  have hlin : HasDerivAt (fun t : ℝ => p * t) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  have hs := (hasDerivAt_sn hk (p * t)).comp t hlin
  have hc := (hasDerivAt_cn hk (p * t)).comp t hlin
  have hd := (hasDerivAt_dn hk (p * t)).comp t hlin
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · refine (hc.const_mul A).congr_deriv ?_
    change A * (-(sn k (p * t) * dn k (p * t)) * p) =
      a₀ * (B * sn k (p * t) * (C * dn k (p * t)))
    linear_combination (sn k (p * t) * dn k (p * t)) * h0
  · refine (hs.const_mul B).congr_deriv ?_
    change B * (cn k (p * t) * dn k (p * t) * p) =
      a₁ * (C * dn k (p * t) * (A * cn k (p * t)))
    linear_combination (cn k (p * t) * dn k (p * t)) * h1
  · refine (hd.const_mul C).congr_deriv ?_
    change C * (-(k ^ 2 * sn k (p * t) * cn k (p * t)) * p) =
      a₂ * (A * cn k (p * t) * (B * sn k (p * t)))
    linear_combination (sn k (p * t) * cn k (p * t)) * h2

/-- The same with the roles of the first and the last co-ordinate exchanged:
the curve `(A dn, B sn, C cn)(p t)`. -/
def jacobiCurve' (A B C p k t : ℝ) : Fin 3 → ℝ :=
  ![A * dn k (p * t), B * sn k (p * t), C * cn k (p * t)]

theorem jacobiCurve'_zero (A B C p k : ℝ) : jacobiCurve' A B C p k 0 = ![A, 0, C] := by
  simp [jacobiCurve']

theorem hasDerivAt_jacobiCurve' {k : ℝ} (hk : k ^ 2 < 1) {a₀ a₁ a₂ A B C p : ℝ}
    (h0 : -(A * p * k ^ 2) = a₀ * (B * C)) (h1 : B * p = a₁ * (C * A))
    (h2 : -(C * p) = a₂ * (A * B)) (t : ℝ) :
    HasDerivAt (jacobiCurve' A B C p k)
      ![a₀ * (jacobiCurve' A B C p k t 1 * jacobiCurve' A B C p k t 2),
        a₁ * (jacobiCurve' A B C p k t 2 * jacobiCurve' A B C p k t 0),
        a₂ * (jacobiCurve' A B C p k t 0 * jacobiCurve' A B C p k t 1)] t := by
  have hlin : HasDerivAt (fun t : ℝ => p * t) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  have hs := (hasDerivAt_sn hk (p * t)).comp t hlin
  have hc := (hasDerivAt_cn hk (p * t)).comp t hlin
  have hd := (hasDerivAt_dn hk (p * t)).comp t hlin
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · refine (hd.const_mul A).congr_deriv ?_
    change A * (-(k ^ 2 * sn k (p * t) * cn k (p * t)) * p) =
      a₀ * (B * sn k (p * t) * (C * cn k (p * t)))
    linear_combination (sn k (p * t) * cn k (p * t)) * h0
  · refine (hs.const_mul B).congr_deriv ?_
    change B * (cn k (p * t) * dn k (p * t) * p) =
      a₁ * (C * cn k (p * t) * (A * dn k (p * t)))
    linear_combination (cn k (p * t) * dn k (p * t)) * h1
  · refine (hc.const_mul C).congr_deriv ?_
    change C * (-(sn k (p * t) * dn k (p * t)) * p) =
      a₂ * (A * dn k (p * t) * (B * sn k (p * t)))
    linear_combination (sn k (p * t) * dn k (p * t)) * h2
/-- A point of the plane with `u² + w² = 1` is `(cos φ, sin φ)`. -/
theorem exists_cos_sin_eq {u w : ℝ} (h : u ^ 2 + w ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = u ∧ Real.sin φ = w := by
  have hu1 : -1 ≤ u := by nlinarith [sq_nonneg w, sq_nonneg (u + 1)]
  have hu2 : u ≤ 1 := by nlinarith [sq_nonneg w, sq_nonneg (u - 1)]
  have hsin : Real.sin (Real.arccos u) = |w| := by
    rw [Real.sin_arccos, show 1 - u ^ 2 = w ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_total 0 w with hw | hw
  · exact ⟨Real.arccos u, Real.cos_arccos hu1 hu2, by rw [hsin, abs_of_nonneg hw]⟩
  · refine ⟨-Real.arccos u, by rw [Real.cos_neg, Real.cos_arccos hu1 hu2], ?_⟩
    rw [Real.sin_neg, hsin, abs_of_nonpos hw, neg_neg]

/-- Every point with `a z² < c x²`, for coefficients `a < 0 < b` and `c < 0`,
lies on a curve of Jacobi's functions that solves the system with these
coefficients. -/
theorem exists_jacobiCurve_eq {a b c : ℝ} (ha : a < 0) (hb : 0 < b) (hc : c < 0)
    {x y z : ℝ} (hreg : a * z ^ 2 < c * x ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ (√(c / a) * A / C) ^ 2 < 1 ∧
      jacobiCurve A (b * A / √(-(a * b))) C (C * √(-(a * b))) (√(c / a) * A / C) t₀ =
        ![x, y, z] := by
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at hreg
    nlinarith [sq_nonneg x]
  have hz2 : 0 < z ^ 2 := by positivity
  have hane : a ≠ 0 := ha.ne
  have hbne : b ≠ 0 := hb.ne'
  have hrad : 0 < -(a * b) := by nlinarith
  have hq : 0 < √(-(a * b)) := Real.sqrt_pos.mpr hrad
  have hq2 : √(-(a * b)) ^ 2 = -(a * b) := Real.sq_sqrt hrad.le
  have hab : a / b < 0 := div_neg_of_neg_of_pos ha hb
  have hcb : c / b < 0 := div_neg_of_neg_of_pos hc hb
  have hca : 0 ≤ c / a := div_nonneg_of_nonpos hc.le ha.le
  have hAsq : 0 ≤ x ^ 2 - a / b * y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hCsq : 0 < z ^ 2 - c / b * y ^ 2 := by nlinarith [sq_nonneg y]
  obtain ⟨A, hA0, hA2⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ 2 = x ^ 2 - a / b * y ^ 2 :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt hAsq⟩
  obtain ⟨C, hCne, hC2, hCz⟩ : ∃ C : ℝ, C ≠ 0 ∧ C ^ 2 = z ^ 2 - c / b * y ^ 2 ∧ 0 < C * z := by
    have hS : 0 < √(z ^ 2 - c / b * y ^ 2) := Real.sqrt_pos.mpr hCsq
    have habs : 0 < |z| := abs_pos.mpr hz
    have hr : 0 < √(z ^ 2 - c / b * y ^ 2) / |z| := div_pos hS habs
    refine ⟨z * (√(z ^ 2 - c / b * y ^ 2) / |z|), mul_ne_zero hz hr.ne', ?_, by nlinarith⟩
    rw [mul_pow, div_pow, Real.sq_sqrt hCsq.le, sq_abs]
    field_simp
  have hk2 : (√(c / a) * A / C) ^ 2 = c / a * A ^ 2 / C ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hca]
  have hk : (√(c / a) * A / C) ^ 2 < 1 := by
    rw [hk2, hA2, hC2, div_lt_one hCsq]
    have h1 : c / a * (x ^ 2 - a / b * y ^ 2) = c / a * x ^ 2 - c / b * y ^ 2 := by
      field_simp
    have h2 : c / a * x ^ 2 < z ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff_of_neg ha]
      linarith
    linarith
  rcases eq_or_lt_of_le hA0 with hA | hA
  · -- the point is on the axis of the co-ordinate `z`
    have hzero : x ^ 2 - a / b * y ^ 2 = 0 := by rw [← hA2, ← hA]; ring
    have hy : y = 0 := by
      by_contra hy0
      have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x]
    have hx : x = 0 := by
      rw [hy] at hzero
      simpa using hzero
    have hCz' : C = z := by
      rw [hy] at hC2
      have h1 : (C - z) * (C + z) = 0 := by nlinarith
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exfalso
        have : C = -z := by linarith
        rw [this] at hCz
        nlinarith
    refine ⟨A, C, 0, hCne, hk, ?_⟩
    rw [jacobiCurve_zero, ← hA, hx, hy, hCz']
  · -- the angle of the point `(x / A, y / B)` on the circle
    have hA2ne : A ^ 2 ≠ 0 := pow_ne_zero 2 hA.ne'
    have hB2 : (b * A / √(-(a * b))) ^ 2 = -(b / a) * A ^ 2 := by
      rw [div_pow, mul_pow, hq2]
      field_simp
    have hcirc : (x / A) ^ 2 + (y / (b * A / √(-(a * b)))) ^ 2 = 1 := by
      rw [div_pow, div_pow, hB2]
      have h1 : y ^ 2 / (-(b / a) * A ^ 2) = -(a / b * y ^ 2) / A ^ 2 := by
        field_simp
      rw [h1, ← add_div, div_eq_one_iff_eq hA2ne]
      linarith
    obtain ⟨φ, hcos, hsin⟩ := exists_cos_sin_eq hcirc
    obtain ⟨u₀, hu₀⟩ := am_surjective hk φ
    have harg : C * √(-(a * b)) * (u₀ / (C * √(-(a * b)))) = u₀ := by
      field_simp
    have hB : b * A / √(-(a * b)) ≠ 0 := (div_pos (mul_pos hb hA) hq).ne'
    refine ⟨A, C, u₀ / (C * √(-(a * b))), hCne, hk, ?_⟩
    funext i
    fin_cases i
    · change A * cn (√(c / a) * A / C) (C * √(-(a * b)) * (u₀ / (C * √(-(a * b))))) = x
      rw [harg, cn, hu₀, hcos, mul_comm, div_mul_cancel₀ x hA.ne']
    · change b * A / √(-(a * b)) *
        sn (√(c / a) * A / C) (C * √(-(a * b)) * (u₀ / (C * √(-(a * b))))) = y
      rw [harg, sn, hu₀, hsin, mul_comm, div_mul_cancel₀ y hB]
    · change C * dn (√(c / a) * A / C) (C * √(-(a * b)) * (u₀ / (C * √(-(a * b))))) = z
      have hC2ne : C ^ 2 ≠ 0 := pow_ne_zero 2 hCne
      have h1 : c / a * A ^ 2 / C ^ 2 * (y ^ 2 / (-(b / a) * A ^ 2)) =
          -(c / b * y ^ 2) / C ^ 2 := by
        field_simp
      have h2 : (1 - -(c / b * y ^ 2) / C ^ 2) * C ^ 2 = C ^ 2 + c / b * y ^ 2 := by
        field_simp
        ring
      have hval : 1 - (√(c / a) * A / C) ^ 2 * (y / (b * A / √(-(a * b)))) ^ 2 =
          z ^ 2 / C ^ 2 := by
        rw [hk2, div_pow y, hB2, h1, eq_div_iff hC2ne, h2, hC2]
        ring
      have hsqrt : √(z ^ 2 / C ^ 2) = |z| / |C| := by
        rw [Real.sqrt_div (sq_nonneg z), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
      have hdn : dn (√(c / a) * A / C) u₀ = |z| / |C| := by
        rw [dn, hu₀, amplitudeField, hsin, hval, hsqrt]
      rw [harg, hdn]
      rcases lt_or_gt_of_ne hCne with hCneg | hCpos
      · have hzneg : z < 0 := (neg_iff_neg_of_mul_pos hCz).mp hCneg
        rw [abs_of_neg hzneg, abs_of_neg hCneg]
        field_simp
      · have hzpos : 0 < z := (pos_iff_pos_of_mul_pos hCz).mp hCpos
        rw [abs_of_pos hzpos, abs_of_pos hCpos]
        field_simp
/-- The curve with the first and the last co-ordinate exchanged. -/
theorem jacobiCurve'_eq (A B C p k t : ℝ) :
    jacobiCurve' A B C p k t =
      ![jacobiCurve C B A p k t 2, jacobiCurve C B A p k t 1, jacobiCurve C B A p k t 0] := by
  funext i
  fin_cases i <;> rfl

end ProjectAinos.SpecialFunctions.JacobiElliptic
