/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ProperTime
public import ProjectAinos.SmoothGeometry.Minkowski.ReverseCauchySchwarz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The inertial clock measures the greatest proper time

Let `γ` be a curve that is `C¹` near every point of `[a, b]`, with a future timelike velocity
there, and let `a < b` (Landau–Lifshitz, *The Classical Theory of Fields*, §3).

* `TimelikeSegment.futureTimelike_displacement`: the displacement `γ b − γ a` is future
  timelike.
* `TimelikeSegment.properTime_le_properSpeed`: `τ[γ] ≤ √Q(γ b − γ a)`. The right-hand side is
  the proper time of the inertial motion between the same two events
  (`properTime_inertialSegment`).
* `TimelikeSegment.properTime_eq_properSpeed_iff`: equality holds if and only if the unit
  four-velocity of `γ` is that of the displacement at every time of `[a, b]`. The curve is then
  an inertial motion with a new parameter; it need not be affine in the given one.
* `sum_properTime_le_properSpeed`: the inequality for a curve made of finitely many such
  pieces with matching endpoints.

The proof integrates the reverse Cauchy–Schwarz inequality against the observer whose velocity
is the direction of the displacement.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {γ : ℝ → MinkowskiModel d} {a b : ℝ}

/-- The proper speed of a future timelike vector is positive. -/
theorem properSpeed_pos {v : MinkowskiModel d} (hv : FutureTimelike v) : 0 < properSpeed v :=
  Real.sqrt_pos.mpr ((futureTimelike_iff v).mp hv).1

/-- A future timelike vector is its proper speed times its unit four-velocity. -/
theorem properSpeed_smul_fourVelocity {v : MinkowskiModel d} (hv : FutureTimelike v) :
    properSpeed v • fourVelocity v = v := by
  rw [fourVelocity, smul_smul, mul_inv_cancel₀ (properSpeed_pos hv).ne', one_smul]

/-- The observer of a future timelike vector measures its proper speed. -/
theorem clock_fourVelocityObserver {v : MinkowskiModel d} (hv : FutureTimelike v) :
    (fourVelocityObserver v hv).clock v = properSpeed v := by
  have hQ : intervalQuadratic v = properSpeed v ^ 2 :=
    (Real.sq_sqrt ((futureTimelike_iff v).mp hv).1.le).symm
  change pair (fourVelocity v) v = properSpeed v
  rw [fourVelocity, map_smul, smul_apply, smul_eq_mul, ← intervalQuadratic_apply, hQ, pow_two,
    ← mul_assoc, inv_mul_cancel₀ (properSpeed_pos hv).ne', one_mul]

/-- The proper time of the inertial motion from `p` to `p + w` in the parameter interval
`[a, b]` is the proper speed of `w`. -/
theorem properTime_inertialSegment (p w : MinkowskiModel d) (hab : a < b) :
    properTime (fun t : ℝ => p + ((t - a) / (b - a)) • w) a b = properSpeed w := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hfun : (fun t : ℝ => p + ((t - a) / (b - a)) • w) =
      fun t : ℝ => (p - (a / (b - a)) • w) + t • ((b - a)⁻¹ • w) := by
    funext t
    rw [smul_smul, sub_add_eq_add_sub, add_sub_assoc, ← sub_smul]
    congr 2
    field_simp
  rw [hfun, properTime_inertial, properSpeed_smul, abs_of_pos (inv_pos.mpr hba), ← mul_assoc,
    mul_inv_cancel₀ hba.ne', one_mul]

namespace TimelikeSegment

/-- The velocity is continuous on the segment. -/
theorem continuousOn_deriv (h : TimelikeSegment γ a b) : ContinuousOn (deriv γ) (uIcc a b) :=
  fun t ht => ((h.regular t ht).derivWithin (m := 0) (by norm_num)).continuousAt
    |>.continuousWithinAt

/-- The displacement is the integral of the velocity. -/
theorem displacement_eq_integral (h : TimelikeSegment γ a b) :
    γ b - γ a = ∫ t in a..b, deriv γ t :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => ((h.regular t ht).differentiableAt (by norm_num)).hasDerivAt)
    h.continuousOn_deriv.intervalIntegrable).symm

/-- The displacement of a future timelike curve is future timelike. -/
theorem futureTimelike_displacement (h : TimelikeSegment γ a b) (hab : a < b) :
    FutureTimelike (γ b - γ a) := by
  have hint := h.continuousOn_deriv.intervalIntegrable (μ := volume)
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hcont : ContinuousOn (deriv γ) (Icc a b) := hIcc ▸ h.continuousOn_deriv
  rw [FutureTimelike, h.displacement_eq_integral,
    ← ContinuousLinearMap.intervalIntegral_comp_comm space hint,
    ← ContinuousLinearMap.intervalIntegral_comp_comm time hint]
  refine (intervalIntegral.norm_integral_le_integral_norm hab.le).trans_lt ?_
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    (space.continuous.norm.comp_continuousOn hcont) (time.continuous.comp_continuousOn hcont)
    (fun t ht => (h.future t (hIcc ▸ Ioc_subset_Icc_self ht)).le)
    ⟨a, left_mem_Icc.mpr hab.le, h.future a (hIcc ▸ left_mem_Icc.mpr hab.le)⟩

/-- The inertial clock measures the greatest proper time: `τ[γ] ≤ √Q(γ b − γ a)`. -/
theorem properTime_le_properSpeed (h : TimelikeSegment γ a b) (hab : a < b) :
    properTime γ a b ≤ properSpeed (γ b - γ a) := by
  have hΔ := h.futureTimelike_displacement hab
  have hint := h.continuousOn_deriv.intervalIntegrable (μ := volume)
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  calc properTime γ a b
      ≤ ∫ t in a..b, (fourVelocityObserver _ hΔ).clock (deriv γ t) :=
        intervalIntegral.integral_mono_on hab.le (properTime_integrable γ a b h.regular)
          (((fourVelocityObserver _ hΔ).clock.continuous.comp_continuousOn
            h.continuousOn_deriv).intervalIntegrable)
          fun t ht => (fourVelocityObserver _ hΔ).sqrt_le_clock
            (h.future t (hIcc ▸ ht)).futureCausal
    _ = (fourVelocityObserver _ hΔ).clock (γ b - γ a) := by
        rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hint, ← h.displacement_eq_integral]
    _ = properSpeed (γ b - γ a) := clock_fourVelocityObserver hΔ

/-- Equality holds exactly when the unit four-velocity is that of the displacement at every
time: the curve is an inertial motion with a new parameter. -/
theorem properTime_eq_properSpeed_iff (h : TimelikeSegment γ a b) (hab : a < b) :
    properTime γ a b = properSpeed (γ b - γ a) ↔
      ∀ t ∈ Icc a b, fourVelocity (deriv γ t) = fourVelocity (γ b - γ a) := by
  have hΔ := h.futureTimelike_displacement hab
  have hint := h.continuousOn_deriv.intervalIntegrable (μ := volume)
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hcont : ContinuousOn (deriv γ) (Icc a b) := hIcc ▸ h.continuousOn_deriv
  have hclock : ∫ t in a..b, (fourVelocityObserver _ hΔ).clock (deriv γ t) =
      properSpeed (γ b - γ a) := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hint, ← h.displacement_eq_integral]
    exact clock_fourVelocityObserver hΔ
  have hle : ∀ t ∈ Icc a b, properSpeed (deriv γ t) ≤
      (fourVelocityObserver _ hΔ).clock (deriv γ t) := fun t ht =>
    (fourVelocityObserver _ hΔ).sqrt_le_clock (h.future t (hIcc ▸ ht)).futureCausal
  constructor
  · intro heq t ht
    have hft := h.future t (hIcc ▸ ht)
    have hpoint : (fourVelocityObserver _ hΔ).clock (deriv γ t) = properSpeed (deriv γ t) := by
      by_contra hne
      have hlt : (∫ s in a..b, properSpeed (deriv γ s)) <
          ∫ s in a..b, (fourVelocityObserver _ hΔ).clock (deriv γ s) :=
        intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
          (properSpeed_continuous.comp_continuousOn hcont)
          ((fourVelocityObserver _ hΔ).clock.continuous.comp_continuousOn hcont)
          (fun s hs => hle s (Ioc_subset_Icc_self hs))
          ⟨t, ht, lt_of_le_of_ne (hle t ht) (Ne.symm hne)⟩
      rw [hclock] at hlt
      exact hlt.ne heq
    have hvec := (fourVelocityObserver _ hΔ).eq_smul_of_clock_eq_sqrt hpoint
      ((futureTimelike_iff _).mp hft).1.le
    rw [hpoint] at hvec
    have hU : (fourVelocityObserver _ hΔ).velocity = fourVelocity (γ b - γ a) := rfl
    rw [hU] at hvec
    calc fourVelocity (deriv γ t)
        = (properSpeed (deriv γ t))⁻¹ •
            (properSpeed (deriv γ t) • fourVelocity (γ b - γ a)) :=
          congrArg (fun w : MinkowskiModel d => (properSpeed (deriv γ t))⁻¹ • w) hvec
      _ = fourVelocity (γ b - γ a) := by
          rw [smul_smul, inv_mul_cancel₀ (properSpeed_pos hft).ne', one_smul]
  · intro hall
    rw [← hclock]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc a b := hIcc ▸ ht
    have hft := h.future t (hIcc ▸ ht')
    have hvec : deriv γ t = properSpeed (deriv γ t) • fourVelocity (γ b - γ a) := by
      rw [← hall t ht', properSpeed_smul_fourVelocity hft]
    have hunit : (fourVelocityObserver _ hΔ).clock (fourVelocity (γ b - γ a)) = 1 :=
      (fourVelocityObserver _ hΔ).unit
    change properSpeed (deriv γ t) = (fourVelocityObserver _ hΔ).clock (deriv γ t)
    conv_rhs => rw [hvec, map_smul, hunit, smul_eq_mul, mul_one]

end TimelikeSegment

/-- The inequality for a curve made of finitely many pieces: the pieces are timelike segments
on the consecutive intervals of the times `s 0 < s 1 < … < s n`, and they match the curve `γ`
at these times. The sum of their proper times is at most `√Q(γ (s n) − γ (s 0))`. -/
theorem sum_properTime_le_properSpeed (γ : ℝ → MinkowskiModel d)
    (pieces : ℕ → ℝ → MinkowskiModel d) (s : ℕ → ℝ) (n : ℕ)
    (hs : ∀ i < n, s i < s (i + 1))
    (hseg : ∀ i < n, TimelikeSegment (pieces i) (s i) (s (i + 1)))
    (hmatch : ∀ i < n, pieces i (s i) = γ (s i) ∧ pieces i (s (i + 1)) = γ (s (i + 1))) :
    FutureCausal (γ (s n) - γ (s 0)) ∧
      ∑ i ∈ Finset.range n, properTime (pieces i) (s i) (s (i + 1)) ≤
        properSpeed (γ (s n) - γ (s 0)) := by
  induction n with
  | zero =>
    simp only [sub_self, futureCausal_zero, Finset.range_zero, Finset.sum_empty, true_and]
    exact Real.sqrt_nonneg _
  | succ n ih =>
    obtain ⟨hcausal, hsum⟩ := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
      (fun i hi => hseg i (Nat.lt_succ_of_lt hi)) (fun i hi => hmatch i (Nat.lt_succ_of_lt hi))
    have hlast := (hseg n (Nat.lt_succ_self n)).futureTimelike_displacement
      (hs n (Nat.lt_succ_self n))
    have hle := (hseg n (Nat.lt_succ_self n)).properTime_le_properSpeed
      (hs n (Nat.lt_succ_self n))
    rw [(hmatch n (Nat.lt_succ_self n)).1, (hmatch n (Nat.lt_succ_self n)).2] at hlast hle
    have hsplit : γ (s (n + 1)) - γ (s 0) = (γ (s n) - γ (s 0)) + (γ (s (n + 1)) - γ (s n)) := by
      abel
    refine ⟨hsplit ▸ hcausal.add hlast.futureCausal, ?_⟩
    rw [Finset.sum_range_succ, hsplit]
    exact (add_le_add hsum hle).trans (sqrt_add_sqrt_le hcausal hlast.futureCausal)

end ProjectAinos.SpecialRelativity
