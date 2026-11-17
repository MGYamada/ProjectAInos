/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Oscillations.ParametricExistence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The trace of the monodromy matrix decides stability

For a coefficient `p` of period `T` let `M` be the monodromy matrix. A solution
whose state at time zero is an eigenvector of `M` with eigenvalue `ν` satisfies
`x(t + T) = ν x(t)`. It is bounded for `t ≥ 0` if `|ν| ≤ 1`, and unbounded if
`|ν| > 1` and it is not zero.

* `|tr M| > 2`: `M` has real eigenvalues `μ` and `μ⁻¹` with `|μ| > 1`. A
  solution is bounded for `t ≥ 0` exactly when its state at time zero is an
  eigenvector for `μ⁻¹`; the other solutions are unbounded.
* `tr M = 2σ` with `σ = ±1` and `M ≠ σ`: then `(M − σ)² = 0`, and a solution
  is bounded exactly when `M − σ` annihilates its state at time zero; the
  other solutions grow linearly.

Together with the bounded cases of `Parametric`, every solution is bounded for
`t ≥ 0` if and only if `|tr M| < 2` or `M = ±1` (Landau–Lifshitz §27).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Mechanics.Parametric

open Matrix SmoothAlgebra

/-! ### Linear combinations of solutions -/

theorem IsHill.const_mul {p x : TimeFunction} (hx : IsHill p x) (c : ℝ) :
    IsHill p (algebraMap ℝ TimeFunction c * x) := by
  unfold IsHill at hx ⊢
  rw [SmoothDerivation.map_algebraMap_mul, smul_eq_mul, SmoothDerivation.map_algebraMap_mul,
    smul_eq_mul, hx]
  ring

theorem IsHill.add {p x y : TimeFunction} (hx : IsHill p x) (hy : IsHill p y) :
    IsHill p (x + y) := by
  unfold IsHill at hx hy ⊢
  rw [map_add, map_add, hx, hy]
  ring

theorem isHill_zero (p : TimeFunction) : IsHill p 0 := by
  unfold IsHill
  simp

@[simp] theorem state_hillSolution_zero (p : TimeFunction) (c : Fin 2 → ℝ) :
    state (hillSolution p (c 0) (c 1)) 0 = c := by
  ext i
  fin_cases i <;> simp [state]

/-- A solution whose state at time zero vanishes is zero. -/
theorem IsHill.eq_zero_of_state_eq_zero {p x : TimeFunction} (hx : IsHill p x)
    (h : state x 0 = 0) : x = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [state, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  exact hx.eq_of_initial (isHill_zero p) (by simpa using h0) (by simpa using h1)

/-- The state after one period is the monodromy matrix applied to the state. -/
theorem IsHill.state_period {p x : TimeFunction} (hx : IsHill p x) (T : ℝ) :
    state x T = monodromy p T *ᵥ state x 0 :=
  (FundamentalSystem.ofCoefficient p).state_eq hx T

/-! ### Solutions with a multiplier -/

/-- A solution whose state at time zero is an eigenvector of the monodromy
matrix is multiplied by the eigenvalue after each period. -/
theorem IsHill.shift_eq_of_mulVec_eq {p x : TimeFunction} {T ν : ℝ}
    (hp : TimeFunction.shift T p = p) (hx : IsHill p x)
    (h : monodromy p T *ᵥ state x 0 = ν • state x 0) :
    TimeFunction.shift T x = algebraMap ℝ TimeFunction ν * x := by
  have hs := hx.state_period T
  rw [h] at hs
  have h0 := congrFun hs 0
  have h1 := congrFun hs 1
  simp only [state, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    at h0 h1
  apply (hx.shift hp).eq_of_initial (hx.const_mul ν)
  · simpa [TimeFunction.shift_apply] using h0
  · rw [TimeFunction.timeDerivative_shift, SmoothDerivation.map_algebraMap_mul]
    simpa [TimeFunction.shift_apply] using h1

theorem apply_add_nat_mul_period_of_shift_eq {x : TimeFunction} {T ν : ℝ}
    (h : TimeFunction.shift T x = algebraMap ℝ TimeFunction ν * x) (n : ℕ) (t : ℝ) :
    x (fun _ => t + n * T) = ν ^ n * x fun _ => t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := congrArg (fun f : TimeFunction => f fun _ => t + n * T) h
    simp only [TimeFunction.shift_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply]
      at hs
    have e : t + ((n + 1 : ℕ) : ℝ) * T = t + n * T + T := by
      push_cast
      ring
    rw [e, hs, ih]
    ring

/-- A multiplier of absolute value at most one gives a solution bounded for `t ≥ 0`. -/
theorem exists_abs_apply_le_of_shift_eq {x : TimeFunction} {T ν : ℝ} (hT : 0 < T)
    (h : TimeFunction.shift T x = algebraMap ℝ TimeFunction ν * x) (hν : |ν| ≤ 1) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  have hc : ContinuousOn (fun s : ℝ => x fun _ => s) (Set.Icc 0 T) :=
    x.contDiff_apply_const.continuous.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨B, fun t ht => ?_⟩
  obtain ⟨n, s, hs, rfl⟩ : ∃ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 T ∧ t = s + n * T := by
    refine ⟨⌊t / T⌋₊, t - ⌊t / T⌋₊ * T, ⟨?_, ?_⟩, by ring⟩
    · have h1 := Nat.floor_le (div_nonneg ht hT.le)
      have h2 := (le_div_iff₀ hT).mp h1
      linarith
    · have h1 := Nat.lt_floor_add_one (t / T)
      have h2 := (div_lt_iff₀ hT).mp h1
      linarith
  rw [apply_add_nat_mul_period_of_shift_eq h, abs_mul, abs_pow]
  have h1 : |ν| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg ν) hν
  have h2 := hB s hs
  rw [Real.norm_eq_abs] at h2
  calc |ν| ^ n * |x fun _ => s| ≤ 1 * B := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = B := one_mul B

/-- A multiplier of absolute value greater than one gives an unbounded
solution, unless the solution is zero. -/
theorem not_exists_abs_apply_le_of_shift_eq {x : TimeFunction} {T ν : ℝ} (hT : 0 < T)
    (h : TimeFunction.shift T x = algebraMap ℝ TimeFunction ν * x) (hν : 1 < |ν|)
    (hx : x ≠ 0) : ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, (x fun _ => t₀) ≠ 0 := by
    by_contra hall
    refine hx (TimeFunction.ext_apply_const fun t => ?_)
    by_contra h
    exact hall ⟨t, h⟩
  have hpos : 0 < |x fun _ => t₀| := abs_pos.mpr ht₀
  have hlim := tendsto_pow_atTop_atTop_of_one_lt hν
  have hev1 := hlim.eventually (Filter.eventually_gt_atTop (B / |x fun _ => t₀|))
  have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ t₀ + n * T := by
    have hT' : Filter.Tendsto (fun n : ℕ => t₀ + (n : ℝ) * T) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hT)
    exact hT'.eventually (Filter.eventually_ge_atTop 0)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hb := hB _ hn2
  rw [apply_add_nat_mul_period_of_shift_eq h, abs_mul, abs_pow] at hb
  have hgt := (div_lt_iff₀ hpos).mp hn1
  linarith

/-! ### The hyperbolic case -/

/-- A real matrix of determinant one whose trace has absolute value greater
than two has a real eigenvalue of absolute value greater than one. -/
theorem exists_mulVec_eq_smul_of_two_lt_abs_trace {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : A.det = 1) (htr : 2 < |A.trace|) :
    ∃ μ : ℝ, 1 < |μ| ∧ μ ^ 2 - A.trace * μ + 1 = 0 ∧
      ∃ c : Fin 2 → ℝ, c ≠ 0 ∧ A *ᵥ c = μ • c := by
  have hdisc : 0 < A.trace ^ 2 - 4 := by
    have h := sq_lt_sq' (by linarith [abs_nonneg A.trace]) htr
    rw [sq_abs] at h
    linarith
  set d := Real.sqrt (A.trace ^ 2 - 4) with hd
  have hdpos : 0 < d := Real.sqrt_pos.mpr hdisc
  have hdsq : d ^ 2 = A.trace ^ 2 - 4 := Real.sq_sqrt hdisc.le
  obtain ⟨μ, hμabs, hμeq⟩ : ∃ μ : ℝ, 1 < |μ| ∧ μ ^ 2 - A.trace * μ + 1 = 0 := by
    rcases lt_abs.mp htr with h | h
    · refine ⟨(A.trace + d) / 2, ?_, by nlinarith⟩
      rw [abs_of_pos (by linarith)]
      linarith
    · refine ⟨(A.trace - d) / 2, ?_, by nlinarith⟩
      rw [abs_of_neg (by linarith)]
      linarith
  refine ⟨μ, hμabs, hμeq, ?_⟩
  have hdet0 : (A - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
    rw [Matrix.det_fin_two] at hdet ⊢
    rw [Matrix.trace_fin_two] at hμeq
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero]
    linarith
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  refine ⟨c, hc, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hc0
  exact hc0

/-- If `|tr M| > 2` there is an unbounded solution. -/
theorem exists_isHill_not_bounded_of_two_lt_abs_trace {p : TimeFunction} {T : ℝ}
    (hp : TimeFunction.shift T p = p) (hT : 0 < T) (htr : 2 < |(monodromy p T).trace|) :
    ∃ x, IsHill p x ∧ ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  obtain ⟨μ, hμ, -, c, hc, hMc⟩ :=
    exists_mulVec_eq_smul_of_two_lt_abs_trace (det_monodromy p T) htr
  have hx := isHill_hillSolution p (c 0) (c 1)
  refine ⟨hillSolution p (c 0) (c 1), hx, ?_⟩
  have hshift := hx.shift_eq_of_mulVec_eq hp (by rw [state_hillSolution_zero]; exact hMc)
  refine not_exists_abs_apply_le_of_shift_eq hT hshift hμ fun h0 => hc ?_
  have hs := state_hillSolution_zero p c
  rw [h0] at hs
  rw [← hs]
  ext i
  fin_cases i <;> simp [state]

/-- In the hyperbolic case a solution is bounded for `t ≥ 0` exactly when its
state at time zero is an eigenvector of the monodromy matrix whose eigenvalue
has absolute value less than one. -/
theorem IsHill.exists_abs_apply_le_iff_of_two_lt_abs_trace {p x : TimeFunction} {T : ℝ}
    (hp : TimeFunction.shift T p = p) (hT : 0 < T) (htr : 2 < |(monodromy p T).trace|)
    (hx : IsHill p x) :
    (∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B) ↔
      ∃ ν : ℝ, |ν| < 1 ∧ monodromy p T *ᵥ state x 0 = ν • state x 0 := by
  constructor
  · intro hb
    obtain ⟨μ, hμ, hμeq, -⟩ :=
      exists_mulVec_eq_smul_of_two_lt_abs_trace (det_monodromy p T) htr
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      norm_num at hμ
    refine ⟨μ⁻¹, ?_, ?_⟩
    · rw [abs_inv]
      exact inv_lt_one_of_one_lt₀ hμ
    · -- the component along the eigenvalue `μ` is `u = (M − μ⁻¹) c`
      set M := monodromy p T with hM
      set c := state x 0 with hcdef
      let u : Fin 2 → ℝ := M *ᵥ c - μ⁻¹ • c
      have hMM : M * M = M.trace • M - 1 := mul_self_eq (det_monodromy p T)
      have hinv : μ + μ⁻¹ = M.trace := by
        field_simp
        linarith
      have hMu : M *ᵥ u = μ • u := by
        change M *ᵥ (M *ᵥ c - μ⁻¹ • c) = μ • (M *ᵥ c - μ⁻¹ • c)
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_smul, hMM, Matrix.sub_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, ← hinv, smul_sub, smul_smul,
          mul_inv_cancel₀ hμ0, one_smul, add_smul]
        abel
      by_contra hne
      have hu : u ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
      -- the solution with state `u` is unbounded, and it is a combination of
      -- `x` and of its translate by a period
      have hxu := isHill_hillSolution p (u 0) (u 1)
      have hshift := hxu.shift_eq_of_mulVec_eq hp (by rw [state_hillSolution_zero]; exact hMu)
      have hunb := not_exists_abs_apply_le_of_shift_eq hT hshift hμ fun h0 => hu (by
        have hs := state_hillSolution_zero p u
        rw [h0] at hs
        rw [← hs]
        ext i
        fin_cases i <;> simp [state])
      have hcomb : hillSolution p (u 0) (u 1) =
          TimeFunction.shift T x + algebraMap ℝ TimeFunction (-μ⁻¹) * x := by
        have h0 : (x fun _ => T) = (M *ᵥ c) 0 := congrFun (hx.state_period T) 0
        have h1 : (timeDerivative x fun _ => T) = (M *ᵥ c) 1 :=
          congrFun (hx.state_period T) 1
        apply hxu.eq_of_initial ((hx.shift hp).add (hx.const_mul _))
        · simp only [hillSolution_zero, TimeFunction.add_apply, TimeFunction.mul_apply,
            TimeFunction.algebraMap_apply, TimeFunction.shift_apply, zero_add]
          rw [h0]
          change (M *ᵥ c) 0 - μ⁻¹ * c 0 = (M *ᵥ c) 0 + -μ⁻¹ * c 0
          ring
        · rw [timeDerivative_hillSolution_zero, map_add, TimeFunction.timeDerivative_shift,
            SmoothDerivation.map_algebraMap_mul]
          simp only [TimeFunction.add_apply, TimeFunction.shift_apply, zero_add, smul_eq_mul,
            TimeFunction.mul_apply, TimeFunction.algebraMap_apply]
          rw [h1]
          change (M *ᵥ c) 1 - μ⁻¹ * c 1 = (M *ᵥ c) 1 + -μ⁻¹ * c 1
          ring
      apply hunb
      obtain ⟨B, hB⟩ := hb
      refine ⟨B + |μ⁻¹| * B, fun t ht => ?_⟩
      rw [hcomb]
      simp only [TimeFunction.add_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply,
        TimeFunction.shift_apply]
      have h1 := hB (t + T) (by linarith)
      have h2 := hB t ht
      calc |(x fun _ => t + T) + -μ⁻¹ * x fun _ => t|
          ≤ |x fun _ => t + T| + |-μ⁻¹ * x fun _ => t| := abs_add_le _ _
        _ = |x fun _ => t + T| + |μ⁻¹| * |x fun _ => t| := by rw [abs_mul, abs_neg]
        _ ≤ B + |μ⁻¹| * B := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
  · rintro ⟨ν, hν, h⟩
    exact exists_abs_apply_le_of_shift_eq hT (hx.shift_eq_of_mulVec_eq hp h) hν.le

/-! ### The parabolic case -/

/-- If `tr A = 2σ` with `σ² = 1`, then `A` applied to `A c − σ c` is `σ (A c − σ c)`:
the matrix `A − σ` has square zero. -/
theorem mulVec_mulVec_sub_of_trace_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1)
    {σ : ℝ} (hσ : σ * σ = 1) (htr : A.trace = 2 * σ) (c : Fin 2 → ℝ) :
    A *ᵥ (A *ᵥ c - σ • c) = σ • (A *ᵥ c - σ • c) := by
  have hAA : A * A = A.trace • A - 1 := mul_self_eq hdet
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_smul, hAA, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, htr, smul_sub, smul_smul, hσ, one_smul, two_mul,
    add_smul]
  abel

/-- In the parabolic case a solution is bounded for `t ≥ 0` exactly when its
state at time zero is an eigenvector of the monodromy matrix. The other
solutions grow linearly. -/
theorem IsHill.exists_abs_apply_le_iff_of_trace_eq {p x : TimeFunction} {T σ : ℝ}
    (hp : TimeFunction.shift T p = p) (hT : 0 < T) (hσ : σ * σ = 1)
    (htr : (monodromy p T).trace = 2 * σ) (hx : IsHill p x) :
    (∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B) ↔
      monodromy p T *ᵥ state x 0 = σ • state x 0 := by
  have hσabs : |σ| = 1 := by
    have h : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  constructor
  · intro hb
    by_contra hne
    set M := monodromy p T with hM
    set c := state x 0 with hcdef
    let w : Fin 2 → ℝ := M *ᵥ c - σ • c
    have hw : w ≠ 0 := fun h0 => hne (sub_eq_zero.mp h0)
    have hMw : M *ᵥ w = σ • w := mulVec_mulVec_sub_of_trace_eq (det_monodromy p T) hσ htr c
    have hy := isHill_hillSolution p (w 0) (w 1)
    set y := hillSolution p (w 0) (w 1) with hydef
    have hyshift : TimeFunction.shift T y = algebraMap ℝ TimeFunction σ * y :=
      hy.shift_eq_of_mulVec_eq hp (by rw [state_hillSolution_zero]; exact hMw)
    have hy0 : y ≠ 0 := fun h0 => hw (by
      have hs := state_hillSolution_zero p w
      rw [← hydef, h0] at hs
      rw [← hs]
      ext i
      fin_cases i <;> simp [state])
    have hxshift : TimeFunction.shift T x = algebraMap ℝ TimeFunction σ * x + y := by
      have h0 : (x fun _ => T) = (M *ᵥ c) 0 := congrFun (hx.state_period T) 0
      have h1 : (timeDerivative x fun _ => T) = (M *ᵥ c) 1 := congrFun (hx.state_period T) 1
      apply (hx.shift hp).eq_of_initial ((hx.const_mul σ).add hy)
      · simp only [TimeFunction.add_apply, TimeFunction.mul_apply,
          TimeFunction.algebraMap_apply, TimeFunction.shift_apply, zero_add, hydef,
          hillSolution_zero]
        rw [h0]
        change (M *ᵥ c) 0 = σ * c 0 + ((M *ᵥ c) 0 - σ * c 0)
        ring
      · rw [TimeFunction.timeDerivative_shift, map_add, SmoothDerivation.map_algebraMap_mul,
          TimeFunction.add_apply, hydef, timeDerivative_hillSolution_zero]
        simp only [TimeFunction.shift_apply, zero_add, smul_eq_mul, TimeFunction.mul_apply,
          TimeFunction.algebraMap_apply]
        rw [h1]
        change (M *ᵥ c) 1 = σ * c 1 + ((M *ᵥ c) 1 - σ * c 1)
        ring
    have hstep : ∀ (n : ℕ) (t : ℝ), x (fun _ => t + n * T) =
        σ ^ n * ((x fun _ => t) + n * σ * y fun _ => t) := by
      intro n t
      induction n with
      | zero => simp
      | succ n ih =>
        have hs := congrArg (fun f : TimeFunction => f fun _ => t + n * T) hxshift
        simp only [TimeFunction.shift_apply, TimeFunction.add_apply, TimeFunction.mul_apply,
          TimeFunction.algebraMap_apply] at hs
        have e : t + ((n + 1 : ℕ) : ℝ) * T = t + n * T + T := by
          push_cast
          ring
        rw [e, hs, ih, apply_add_nat_mul_period_of_shift_eq hyshift]
        push_cast
        have hσn : σ ^ (n + 2) = σ ^ n := by rw [pow_add, pow_two, hσ, mul_one]
        linear_combination (-(y fun _ => t)) * hσn
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, (y fun _ => t₀) ≠ 0 := by
      by_contra hall
      refine hy0 (TimeFunction.ext_apply_const fun t => ?_)
      by_contra h
      exact hall ⟨t, h⟩
    have hpos : 0 < |y fun _ => t₀| := abs_pos.mpr ht₀
    obtain ⟨B, hB⟩ := hb
    have hev1 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Filter.eventually_gt_atTop ((B + |x fun _ => t₀|) / |y fun _ => t₀|))
    have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ t₀ + n * T := by
      have hT' : Filter.Tendsto (fun n : ℕ => t₀ + (n : ℝ) * T) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_left _ _
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hT)
      exact hT'.eventually (Filter.eventually_ge_atTop 0)
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    have hb' := hB _ hn2
    rw [hstep, abs_mul, abs_pow, hσabs, one_pow, one_mul] at hb'
    have hgt := (div_lt_iff₀ hpos).mp hn1
    have htri : (n : ℝ) * |y fun _ => t₀| - |x fun _ => t₀| ≤
        |(x fun _ => t₀) + n * σ * y fun _ => t₀| := by
      have h1 : |(n : ℝ) * σ * y fun _ => t₀| = n * |y fun _ => t₀| := by
        rw [abs_mul, abs_mul, hσabs, mul_one, Nat.abs_cast]
      have h2 := abs_sub_abs_le_abs_sub ((n : ℝ) * σ * y fun _ => t₀) (-(x fun _ => t₀))
      rw [h1, abs_neg, sub_neg_eq_add, add_comm] at h2
      exact h2
    linarith
  · intro h
    exact exists_abs_apply_le_of_shift_eq hT (hx.shift_eq_of_mulVec_eq hp h) hσabs.le

/-- A vector that a nonzero difference `A − σ` does not annihilate. -/
theorem exists_mulVec_ne_smul {A : Matrix (Fin 2) (Fin 2) ℝ} {σ : ℝ}
    (hA : A ≠ σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) : ∃ c : Fin 2 → ℝ, A *ᵥ c ≠ σ • c := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  apply hA
  have h0 := hall ![1, 0]
  have h1 := hall ![0, 1]
  ext i j
  fin_cases j
  · have h := congrFun h0 i
    fin_cases i <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  · have h := congrFun h1 i
    fin_cases i <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

/-- If `tr M = 2σ` with `σ = ±1` and `M ≠ σ`, there is an unbounded solution. -/
theorem exists_isHill_not_bounded_of_trace_eq {p : TimeFunction} {T σ : ℝ}
    (hp : TimeFunction.shift T p = p) (hT : 0 < T) (hσ : σ * σ = 1)
    (htr : (monodromy p T).trace = 2 * σ)
    (hM : monodromy p T ≠ σ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∃ x, IsHill p x ∧ ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  obtain ⟨c, hc⟩ := exists_mulVec_ne_smul hM
  have hx := isHill_hillSolution p (c 0) (c 1)
  refine ⟨hillSolution p (c 0) (c 1), hx, fun hb => hc ?_⟩
  have h := (hx.exists_abs_apply_le_iff_of_trace_eq hp hT hσ htr).mp hb
  rwa [state_hillSolution_zero] at h

/-! ### The criterion -/

/-- Stability of the equation `ẍ + p(t) x = 0` with a periodic coefficient
(Landau–Lifshitz §27): every solution is bounded for `t ≥ 0` if and only if the
trace of the monodromy matrix has absolute value less than two, or the
monodromy matrix is `1` or `−1`. -/
theorem forall_isHill_bounded_iff {p : TimeFunction} {T : ℝ}
    (hp : TimeFunction.shift T p = p) (hT : 0 < T) :
    (∀ x, IsHill p x → ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B) ↔
      |(monodromy p T).trace| < 2 ∨ monodromy p T = 1 ∨ monodromy p T = -1 := by
  constructor
  · intro hall
    rcases lt_trichotomy |(monodromy p T).trace| 2 with h | h | h
    · exact Or.inl h
    · right
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 2) |>.mp h with h2 | h2
      · left
        by_contra hM
        obtain ⟨x, hx, hnb⟩ := exists_isHill_not_bounded_of_trace_eq (σ := 1) hp hT
          (by norm_num) (by rw [h2]; norm_num) (by rwa [one_smul])
        exact hnb (hall x hx)
      · right
        by_contra hM
        obtain ⟨x, hx, hnb⟩ := exists_isHill_not_bounded_of_trace_eq (σ := -1) hp hT
          (by norm_num) (by rw [h2]; norm_num) (by rwa [neg_one_smul])
        exact hnb (hall x hx)
    · obtain ⟨x, hx, hnb⟩ := exists_isHill_not_bounded_of_two_lt_abs_trace hp hT h
      exact (hnb (hall x hx)).elim
  · intro h x hx
    rcases h with h | h
    · exact (FundamentalSystem.ofCoefficient p).exists_abs_apply_le_of_abs_trace_lt hp hT h hx
    · exact (FundamentalSystem.ofCoefficient p).exists_abs_apply_le_of_eq hp hT h hx

/-- The oscillator with constant frequency `ω`, regarded as periodic with a
period `T`: all solutions are bounded, and the criterion holds with
`tr M = 2 cos ωT`. -/
theorem abs_trace_monodromy_harmonic_le {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    |(monodromy (algebraMap ℝ TimeFunction (ω ^ 2)) T).trace| ≤ 2 := by
  rw [trace_monodromy_harmonic hω, abs_mul, abs_two]
  have h := Real.abs_cos_le_one (ω * T)
  linarith

end ProjectAinos.Mechanics.Parametric
