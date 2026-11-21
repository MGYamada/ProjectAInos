/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Zeros of integer-order Bessel functions

Two consecutive orders cannot vanish together: the recurrence would annihilate every Laurent
coefficient of the nonzero generating function. For existence of positive zeros, test the real
Bessel equation against `1 − cos(t − a)`. Its value and derivative vanish at both endpoints
of an interval of length 2π. Rolle's theorem applied to the weighted Wronskian forces a zero
inside every such interval sufficiently far from the origin.
-/

@[expose] public section
noncomputable section

open Complex Real Set
namespace ProjectAinos.SpecialFunctions.Bessel

/-- Distinct consecutive integer orders have no common zero on the principal slit plane. -/
theorem adjacent_ne_zero (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) (hn : besselJ n z = 0) :
    besselJ (n + 1 : ℤ) z ≠ 0 := by
  intro hnext
  have hrec (k : ℤ) : besselJ (k - 1 : ℤ) z + besselJ (k + 1 : ℤ) z =
      2 * k / z * besselJ k z := by simpa using recurrence k z hz
  have hpair (k : ℤ) : besselJ k z = 0 ∧ besselJ (k + 1 : ℤ) z = 0 := by
    induction k using Int.inductionOn' (b := n) with
    | zero => exact ⟨hn, hnext⟩
    | succ j _ ih =>
      refine ⟨ih.2, ?_⟩
      simpa only [add_sub_cancel_right, ih.1, ih.2, mul_zero, zero_add] using hrec (j + 1)
    | pred j _ ih =>
      rw [sub_add_cancel]
      exact ⟨by simpa only [ih.1, ih.2, mul_zero, add_zero] using hrec j, ih.1⟩
  have hs := hasSum_generating z (w := 1) one_ne_zero
  simp [fun k => (hpair k).1] at hs
  exact one_ne_zero (hs.unique hasSum_zero)

/-- Every integer-order zero on the slit plane is simple. -/
theorem deriv_ne_zero_of_zero (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) (hn : besselJ n z = 0) :
    deriv (besselJ n) z ≠ 0 := by
  rw [(hasDerivAt_besselJ n z hz).deriv, hn, mul_zero, zero_sub, neg_ne_zero]
  simpa using adjacent_ne_zero n hz hn

private def j (n : ℤ) (t : ℝ) := (besselJ n t).re
private def j' (n : ℤ) (t : ℝ) := (deriv (besselJ n) t).re
private def j'' (n : ℤ) (t : ℝ) := (deriv (deriv (besselJ n)) t).re

private theorem dj (n : ℤ) (t : ℝ) : HasDerivAt (j n) (j' n t) t :=
  (analyticAt_besselJ_int n t).differentiableAt.hasDerivAt.real_of_complex

private theorem dj' (n : ℤ) (t : ℝ) : HasDerivAt (j' n) (j'' n t) t :=
  (analyticAt_besselJ_int n t).deriv.differentiableAt.hasDerivAt.real_of_complex

private theorem real_equation (n : ℤ) {t : ℝ} (ht : 0 < t) :
    t ^ 2 * j'' n t + t * j' n t + (t ^ 2 - n ^ 2 : ℝ) * j n t = 0 := by
  have h := congrArg Complex.re (equation n t (by simp [mem_slitPlane_iff, ht]))
  simpa [j, j', j'', ← Complex.ofReal_intCast, ← Complex.ofReal_pow, ← Complex.ofReal_sub] using h

/-- Every open interval of length `2π` starting beyond `2|n|+2` contains a positive zero. -/
theorem exists_zero_Ioo (n : ℤ) {a : ℝ} (ha : 2 * |(n : ℝ)| + 2 < a) :
    ∃ t ∈ Ioo a (a + 2 * π), besselJ n (t : ℂ) = 0 := by
  let φ (t : ℝ) := 1 - Real.cos (t - a)
  let s (t : ℝ) := Real.sin (t - a)
  let W (t : ℝ) := t * (j' n t * φ t - j n t * s t)
  have dφ t : HasDerivAt φ (s t) t := by
    simpa [φ, s] using (((hasDerivAt_id t).sub_const a).cos.const_sub 1)
  have ds t : HasDerivAt s (Real.cos (t - a)) t := by
    simpa [s] using ((hasDerivAt_id t).sub_const a).sin
  have dW t : HasDerivAt W ((j' n t * φ t - j n t * s t) + t *
      (j'' n t * φ t - j n t * Real.cos (t - a))) t := by
    convert (hasDerivAt_id t).mul (((dj' n t).mul (dφ t)).sub ((dj n t).mul (ds t))) using 1
    · rfl
    · dsimp only [id_eq, Pi.sub_apply, Pi.mul_apply]; ring
  have hcont : Continuous W := continuous_iff_continuousAt.mpr fun t => (dW t).continuousAt
  have end_eq : W a = W (a + 2 * π) := by simp [W, φ, s]
  obtain ⟨t, ht, hW⟩ := exists_hasDerivAt_eq_zero (show a < a + 2 * π by linarith [pi_pos])
    hcont.continuousOn end_eq (fun t _ => dW t)
  have hsize : 2 * |(n : ℝ)| + 2 < t := ha.trans ht.1
  have hpos : 0 < t := by linarith [abs_nonneg (n : ℝ)]
  have hq : 0 < t ^ 2 + t * s t - (n : ℝ) ^ 2 * φ t := by
    have hsin : -t ≤ t * s t := by
      simpa [s] using mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (t - a)) hpos.le
    have hcos : (n : ℝ) ^ 2 * φ t ≤ (n : ℝ) ^ 2 * 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      dsimp [φ]; linarith [Real.neg_one_le_cos (t - a)]
    have hsq := (sq_lt_sq₀ (show 0 ≤ 2 * |(n : ℝ)| by positivity) hpos.le).mpr
      (show 2 * |(n : ℝ)| < t by linarith)
    nlinarith [sq_abs (n : ℝ), mul_pos hpos
      (show 0 < t - 2 by linarith [abs_nonneg (n : ℝ)])]
  have hz : j n t * (t ^ 2 + t * s t - (n : ℝ) ^ 2 * φ t) = 0 := by
    dsimp only [φ] at *
    linear_combination φ t * real_equation n hpos - t * hW
  have hj := (mul_eq_zero.mp hz).resolve_right hq.ne'
  refine ⟨t, ht, ?_⟩
  have he := integral n t
  rw [j, he, Complex.ofReal_re] at hj
  rw [he, hj, Complex.ofReal_zero]

end ProjectAinos.SpecialFunctions.Bessel
