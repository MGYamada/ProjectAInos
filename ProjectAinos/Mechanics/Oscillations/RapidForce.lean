/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Averaging
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Motion in a rapidly oscillating field

Landau–Lifshitz §30. A particle of mass `m` moves in the potential `U` under
the force `ω g(x) cos ωt`, whose amplitude grows with the frequency so that its
effect does not vanish for large `ω`:

`m ẍ = −U′(x) + ω g(x) cos ωt`.

The velocity is `v = w + (g(x)/m) sin ωt`, a smooth part `w` and an
oscillation of the amplitude `g/m` (`slowVelocity`). The pair `(x, w)` follows
the motion in the effective potential `U + g²/4m` (`effectivePotential`) up to
terms that oscillate with the frequencies `ω` and `2ω`
(`IsRapidMotion.hasDerivAt_pair`).

* `exists_forall_abs_sub_le`: for `U′`, `U″`, `g`, `g′`, `g″` bounded there is
  a constant `C`, which depends on the bounds, the mass, a bound `V` of the
  velocity and the length `L` of the interval of time, such that for every
  frequency `ω` the motion and the motion in the effective potential with the
  same initial position and velocity differ by at most `C/ω` on `[0, L]`.
* `IsRapidMotion.abs_velocity_le`: the velocity is bounded on `[0, L]` by a
  constant that does not depend on `ω`, so the bound `V` exists;
  `exists_forall_abs_sub_le_of_initial` is the statement with a bound of the
  initial velocity only.
* `Pendulum`: for a pendulum whose point of support oscillates vertically,
  `U = −a cos x` and `g = b sin x`, the effective potential has a minimum at
  the upper position exactly when `b² > 2 m a`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff NNReal

namespace ProjectAinos.Mechanics.RapidForce

open SmoothGeometry.Averaging

/-- The effective potential `U + g²/4m` of the slow motion. -/
def effectivePotential (m : ℝ) (U g : ℝ → ℝ) (x : ℝ) : ℝ := U x + g x ^ 2 / (4 * m)

/-- Bounds on the potential and on the amplitude of the force. -/
structure RapidBounds (U g : ℝ → ℝ) (A B : ℝ) : Prop where
  contDiff_potential : ContDiff ℝ ∞ U
  contDiff_amplitude : ContDiff ℝ ∞ g
  deriv_potential : ∀ x, |deriv U x| ≤ A
  deriv_deriv_potential : ∀ x, |deriv (deriv U) x| ≤ A
  amplitude : ∀ x, |g x| ≤ B
  deriv_amplitude : ∀ x, |deriv g x| ≤ B
  deriv_deriv_amplitude : ∀ x, |deriv (deriv g) x| ≤ B

/-- A motion under the rapidly oscillating force: `ẋ = v` and
`m v̇ = −U′(x) + ω g(x) cos ωt`. -/
def IsRapidMotion (m Ω : ℝ) (U g x v : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt x (v t) t) ∧
    ∀ t, HasDerivAt v ((-deriv U (x t) + Ω * g (x t) * Real.cos (Ω * t)) / m) t

/-- A motion in the effective potential: `Ẋ = W` and
`m Ẇ = −(U + g²/4m)′(X)`. -/
def IsSlowMotion (m : ℝ) (U g X W : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt X (W t) t) ∧
    ∀ t, HasDerivAt W (-(deriv U (X t) + g (X t) * deriv g (X t) / (2 * m)) / m) t

/-- The smooth part `w = v − (g(x)/m) sin ωt` of the velocity. -/
def slowVelocity (m Ω : ℝ) (g x v : ℝ → ℝ) (t : ℝ) : ℝ :=
  v t - g (x t) / m * Real.sin (Ω * t)

/-- The vector field of the motion in the effective potential. -/
def slowField (m : ℝ) (U g : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.2, -(deriv U p.1 + g p.1 * deriv g p.1 / (2 * m)) / m)

variable {m Ω A B : ℝ} {U g x v X W : ℝ → ℝ}

theorem hasDerivAt_effectivePotential (hU : ContDiff ℝ ∞ U) (hg : ContDiff ℝ ∞ g) (m x : ℝ) :
    HasDerivAt (effectivePotential m U g) (deriv U x + g x * deriv g x / (2 * m)) x := by
  have h1 := (hU.differentiable (by simp) x).hasDerivAt
  have h2 := (hg.differentiable (by simp) x).hasDerivAt
  refine (h1.add ((h2.pow 2).div_const (4 * m))).congr_deriv ?_
  norm_num
  ring

/-! ### Derivatives along a motion -/

theorem hasDerivAt_deriv (hg : ContDiff ℝ ∞ g) (y : ℝ) :
    HasDerivAt (deriv g) (deriv (deriv g) y) y :=
  ((hg.iterate_deriv 1).differentiable (by simp) y).hasDerivAt

/-- The derivative of the smooth part of the velocity:
`ẇ = −U′(x)/m − (g′(x) v/m) sin ωt`. -/
theorem IsRapidMotion.hasDerivAt_slowVelocity (h : IsRapidMotion m Ω U g x v)
    (hg : ContDiff ℝ ∞ g) (hm : m ≠ 0) (t : ℝ) :
    HasDerivAt (slowVelocity m Ω g x v)
      (-deriv U (x t) / m - deriv g (x t) * v t / m * Real.sin (Ω * t)) t := by
  have hgx : HasDerivAt (fun s => g (x s)) (deriv g (x t) * v t) t :=
    ((hg.differentiable (by simp) (x t)).hasDerivAt).comp t (h.1 t)
  have hsin : HasDerivAt (fun s => Real.sin (Ω * s)) (Real.cos (Ω * t) * Ω) t := by
    have h1 := ((hasDerivAt_id t).const_mul Ω).sin
    simpa using h1
  have h1 := (h.2 t).sub ((hgx.div_const m).mul hsin)
  refine h1.congr_deriv ?_
  field_simp
  ring

/-- The oscillating term of the equation of the position. -/
def oscillation₁ (m Ω : ℝ) (g x : ℝ → ℝ) (t : ℝ) : ℝ := g (x t) / m * Real.sin (Ω * t)

/-- The oscillating terms of the equation of the smooth part of the velocity. -/
def oscillation₂ (m Ω : ℝ) (g x v : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(deriv g (x t) * slowVelocity m Ω g x v t / m * Real.sin (Ω * t)) +
    g (x t) * deriv g (x t) / (2 * m ^ 2) * Real.cos (2 * Ω * t)

/-- The pair of the position and of the smooth part of the velocity follows
the field of the effective potential up to the oscillating terms. -/
theorem IsRapidMotion.hasDerivAt_pair (h : IsRapidMotion m Ω U g x v) (hg : ContDiff ℝ ∞ g)
    (hm : m ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => (x s, slowVelocity m Ω g x v s))
      (slowField m U g (x t, slowVelocity m Ω g x v t) +
        (oscillation₁ m Ω g x t, oscillation₂ m Ω g x v t)) t := by
  have h1 : HasDerivAt x (slowVelocity m Ω g x v t + oscillation₁ m Ω g x t) t := by
    refine (h.1 t).congr_deriv ?_
    simp only [slowVelocity, oscillation₁]
    ring
  have hcos : Real.cos (2 * Ω * t) = 1 - 2 * Real.sin (Ω * t) ^ 2 := by
    rw [mul_assoc, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (Ω * t)
    linarith
  have h2 : HasDerivAt (slowVelocity m Ω g x v)
      (-(deriv U (x t) + g (x t) * deriv g (x t) / (2 * m)) / m + oscillation₂ m Ω g x v t)
      t := by
    refine (h.hasDerivAt_slowVelocity hg hm t).congr_deriv ?_
    simp only [oscillation₂, hcos, slowVelocity]
    field_simp
    ring
  exact h1.prodMk h2

theorem IsSlowMotion.hasDerivAt_pair (h : IsSlowMotion m U g X W) (t : ℝ) :
    HasDerivAt (fun s => (X s, W s)) (slowField m U g (X t, W t)) t :=
  (h.1 t).prodMk (h.2 t)

/-! ### Bounds -/

section Bounds

variable (hb : RapidBounds U g A B)
include hb

theorem RapidBounds.nonneg_potential : 0 ≤ A := (abs_nonneg _).trans (hb.deriv_potential 0)

theorem RapidBounds.nonneg_amplitude : 0 ≤ B := (abs_nonneg _).trans (hb.amplitude 0)

/-- The field of the effective potential is Lipschitz. -/
theorem RapidBounds.exists_lipschitzWith (hm : 0 < m) :
    ∃ K : ℝ≥0, LipschitzWith K (slowField m U g) := by
  have hB := hb.nonneg_amplitude
  let G : ℝ → ℝ := fun y => -(deriv U y + g y * deriv g y / (2 * m)) / m
  have hG : ∀ y, HasDerivAt G
      (-(deriv (deriv U) y +
        (deriv g y * deriv g y + g y * deriv (deriv g) y) / (2 * m)) / m) y := by
    intro y
    have h1 := hasDerivAt_deriv hb.contDiff_potential y
    have h2 := (hb.contDiff_amplitude.differentiable (by simp) y).hasDerivAt
    have h3 := hasDerivAt_deriv hb.contDiff_amplitude y
    exact ((h1.add ((h2.mul h3).div_const (2 * m))).neg).div_const m
  have hbound : ∀ y, ‖deriv G y‖ ≤ (A + B ^ 2 / m) / m := by
    intro y
    rw [(hG y).deriv, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hm]
    refine div_le_div_of_nonneg_right ?_ hm.le
    refine (abs_add_le _ _).trans (add_le_add (hb.deriv_deriv_potential y) ?_)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * m), div_le_div_iff₀ (by positivity) hm]
    have h4 : |deriv g y * deriv g y + g y * deriv (deriv g) y| ≤ B * B + B * B := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul (hb.deriv_amplitude y) (hb.deriv_amplitude y) (abs_nonneg _) hB
      · rw [abs_mul]
        exact mul_le_mul (hb.amplitude y) (hb.deriv_deriv_amplitude y) (abs_nonneg _) hB
    nlinarith [h4, abs_nonneg (deriv g y * deriv g y + g y * deriv (deriv g) y)]
  have hGl : LipschitzWith (Real.toNNReal ((A + B ^ 2 / m) / m)) G :=
    LipschitzWith.of_dist_le' fun y₁ y₂ => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (convex_univ.norm_image_sub_le_of_norm_deriv_le
        (fun y _ => (hG y).differentiableAt) (fun y _ => hbound y) (mem_univ _) (mem_univ _))
  exact ⟨_, LipschitzWith.prodMk LipschitzWith.prod_snd (hGl.comp LipschitzWith.prod_fst)⟩

end Bounds

/-! ### The integrals of the oscillating terms -/

section Integrals

variable {V L : ℝ}

theorem IsRapidMotion.abs_slowVelocity_le (hb : RapidBounds U g A B) (hm : 0 < m) {t : ℝ}
    (hv : |v t| ≤ V) : |slowVelocity m Ω g x v t| ≤ V + B / m := by
  have h1 : |g (x t) / m * Real.sin (Ω * t)| ≤ B / m := by
    rw [abs_mul, abs_div, abs_of_pos hm]
    calc |g (x t)| / m * |Real.sin (Ω * t)| ≤ B / m * 1 :=
          mul_le_mul (div_le_div_of_nonneg_right (hb.amplitude _) hm.le)
            (Real.abs_sin_le_one _) (abs_nonneg _)
            (div_nonneg hb.nonneg_amplitude hm.le)
      _ = B / m := mul_one _
  exact (abs_sub _ _).trans (add_le_add hv h1)

/-- The integral of the oscillating term of the position. -/
theorem IsRapidMotion.abs_integral_oscillation₁_le (h : IsRapidMotion m Ω U g x v)
    (hb : RapidBounds U g A B) (hm : 0 < m) (hΩ : 0 < Ω)
    (hV : ∀ t ∈ Icc 0 L, |v t| ≤ V) {t : ℝ} (ht : t ∈ Icc 0 L) :
    |∫ s in 0..t, oscillation₁ m Ω g x s| ≤ (2 * (B / m) + L * (B * V / m)) / Ω := by
  have hB := hb.nonneg_amplitude
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun s => (h.1 s).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun s => (h.2 s).continuousAt
  have hg'c : Continuous (deriv g) := (hb.contDiff_amplitude.iterate_deriv 1).continuous
  have hd : ∀ s, HasDerivAt (fun s => g (x s) / m) (deriv g (x s) * v s / m) s := fun s =>
    (((hb.contDiff_amplitude.differentiable (by simp) (x s)).hasDerivAt).comp s
      (h.1 s)).div_const m
  have hmain := abs_integral_mul_sin_le (φ := fun s => g (x s) / m)
    (φ' := fun s => deriv g (x s) * v s / m) (M₀ := B / m) (M₁ := B * V / m) ht.1 hΩ
    (fun s _ => hd s) (by fun_prop)
    (fun s _ => by
      rw [abs_div, abs_of_pos hm]
      exact div_le_div_of_nonneg_right (hb.amplitude _) hm.le)
    (fun s hs => by
      rw [abs_div, abs_of_pos hm, abs_mul]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hb.deriv_amplitude _) (hV s ⟨hs.1, hs.2.trans ht.2⟩) (abs_nonneg _) hB)
        hm.le)
  refine hmain.trans ?_
  have hM : 0 ≤ B * V / m := div_nonneg (mul_nonneg hB hV0) hm.le
  exact div_le_div_of_nonneg_right
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2 hM)) hΩ.le

/-- The integral of the oscillating terms of the smooth part of the velocity. -/
theorem IsRapidMotion.abs_integral_oscillation₂_le (h : IsRapidMotion m Ω U g x v)
    (hb : RapidBounds U g A B) (hm : 0 < m) (hΩ : 0 < Ω)
    (hV : ∀ t ∈ Icc 0 L, |v t| ≤ V) {t : ℝ} (ht : t ∈ Icc 0 L) :
    |∫ s in 0..t, oscillation₂ m Ω g x v s| ≤
      ((2 * (B * (V + B / m) / m) +
          L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) +
        (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) / 2) /
        Ω := by
  have hA := hb.nonneg_potential
  have hB := hb.nonneg_amplitude
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  have hg := hb.contDiff_amplitude
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun s => (h.1 s).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun s => (h.2 s).continuousAt
  have hwc : Continuous (slowVelocity m Ω g x v) :=
    continuous_iff_continuousAt.mpr fun s =>
      (h.hasDerivAt_slowVelocity hg hm.ne' s).continuousAt
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := (hg.iterate_deriv 1).continuous
  have hg''c : Continuous (deriv (deriv g)) := (hg.iterate_deriv 2).continuous
  have hU'c : Continuous (deriv U) := (hb.contDiff_potential.iterate_deriv 1).continuous
  have hgx : ∀ s, HasDerivAt (fun s => g (x s)) (deriv g (x s) * v s) s := fun s =>
    ((hg.differentiable (by simp) (x s)).hasDerivAt).comp s (h.1 s)
  have hg'x : ∀ s, HasDerivAt (fun s => deriv g (x s)) (deriv (deriv g) (x s) * v s) s :=
    fun s => (hasDerivAt_deriv hg (x s)).comp s (h.1 s)
  -- the term with the frequency `Ω`
  have hd₂ : ∀ s, HasDerivAt (fun s => deriv g (x s) * slowVelocity m Ω g x v s / m)
      ((deriv (deriv g) (x s) * v s * slowVelocity m Ω g x v s +
        deriv g (x s) * (-deriv U (x s) / m - deriv g (x s) * v s / m * Real.sin (Ω * s))) /
          m) s := fun s =>
    ((hg'x s).mul (h.hasDerivAt_slowVelocity hg hm.ne' s)).div_const m
  have hVw : ∀ s ∈ Icc 0 t, |slowVelocity m Ω g x v s| ≤ V + B / m := fun s hs =>
    IsRapidMotion.abs_slowVelocity_le hb hm (hV s ⟨hs.1, hs.2.trans ht.2⟩)
  have hVw0 : 0 ≤ V + B / m := add_nonneg hV0 (div_nonneg hB hm.le)
  have hDw : ∀ s ∈ Icc 0 t,
      |-deriv U (x s) / m - deriv g (x s) * v s / m * Real.sin (Ω * s)| ≤
        A / m + B * V / m := fun s hs => by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_neg, abs_of_pos hm]
      exact div_le_div_of_nonneg_right (hb.deriv_potential _) hm.le
    · rw [abs_mul, abs_div, abs_of_pos hm, abs_mul]
      calc |deriv g (x s)| * |v s| / m * |Real.sin (Ω * s)| ≤ B * V / m * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right
              (mul_le_mul (hb.deriv_amplitude _) (hV s ⟨hs.1, hs.2.trans ht.2⟩) (abs_nonneg _)
                hB) hm.le) (Real.abs_sin_le_one _) (abs_nonneg _)
              (div_nonneg (mul_nonneg hB hV0) hm.le)
        _ = B * V / m := mul_one _
  have hDw0 : 0 ≤ A / m + B * V / m :=
    add_nonneg (div_nonneg hA hm.le) (div_nonneg (mul_nonneg hB hV0) hm.le)
  have h₂ := abs_integral_mul_sin_le
    (φ := fun s => deriv g (x s) * slowVelocity m Ω g x v s / m)
    (φ' := fun s => (deriv (deriv g) (x s) * v s * slowVelocity m Ω g x v s +
      deriv g (x s) * (-deriv U (x s) / m - deriv g (x s) * v s / m * Real.sin (Ω * s))) / m)
    (M₀ := B * (V + B / m) / m)
    (M₁ := (B * V * (V + B / m) + B * (A / m + B * V / m)) / m) ht.1 hΩ
    (fun s _ => hd₂ s) (by fun_prop)
    (fun s hs => by
      rw [abs_div, abs_of_pos hm, abs_mul]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hb.deriv_amplitude _) (hVw s hs) (abs_nonneg _) hB) hm.le)
    (fun s hs => by
      rw [abs_div, abs_of_pos hm]
      refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hm.le
      · rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hb.deriv_deriv_amplitude _) (hV s ⟨hs.1, hs.2.trans ht.2⟩)
            (abs_nonneg _) hB) (hVw s hs) (abs_nonneg _) (mul_nonneg hB hV0)
      · rw [abs_mul]
        exact mul_le_mul (hb.deriv_amplitude _) (hDw s hs) (abs_nonneg _) hB)
  -- the term with the frequency `2 Ω`
  have hd₃ : ∀ s, HasDerivAt (fun s => g (x s) * deriv g (x s) / (2 * m ^ 2))
      ((deriv g (x s) * v s * deriv g (x s) + g (x s) * (deriv (deriv g) (x s) * v s)) /
        (2 * m ^ 2)) s := fun s => ((hgx s).mul (hg'x s)).div_const _
  have hm2 : (0 : ℝ) < 2 * m ^ 2 := by positivity
  have h₃ := abs_integral_mul_cos_le (φ := fun s => g (x s) * deriv g (x s) / (2 * m ^ 2))
    (φ' := fun s => (deriv g (x s) * v s * deriv g (x s) +
      g (x s) * (deriv (deriv g) (x s) * v s)) / (2 * m ^ 2))
    (M₀ := B * B / (2 * m ^ 2)) (M₁ := (B * V * B + B * (B * V)) / (2 * m ^ 2)) ht.1
    (mul_pos two_pos hΩ) (fun s _ => hd₃ s) (by fun_prop)
    (fun s _ => by
      rw [abs_div, abs_of_pos hm2, abs_mul]
      exact div_le_div_of_nonneg_right
        (mul_le_mul (hb.amplitude _) (hb.deriv_amplitude _) (abs_nonneg _) hB) hm2.le)
    (fun s hs => by
      rw [abs_div, abs_of_pos hm2]
      refine div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hm2.le
      · rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hb.deriv_amplitude _) (hV s ⟨hs.1, hs.2.trans ht.2⟩) (abs_nonneg _) hB)
          (hb.deriv_amplitude _) (abs_nonneg _) (mul_nonneg hB hV0)
      · rw [abs_mul, abs_mul]
        exact mul_le_mul (hb.amplitude _)
          (mul_le_mul (hb.deriv_deriv_amplitude _) (hV s ⟨hs.1, hs.2.trans ht.2⟩)
            (abs_nonneg _) hB) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hB)
  -- the sum
  have hc₂ : Continuous fun s =>
      deriv g (x s) * slowVelocity m Ω g x v s / m * Real.sin (Ω * s) := by fun_prop
  have hc₃ : Continuous fun s =>
      g (x s) * deriv g (x s) / (2 * m ^ 2) * Real.cos (2 * Ω * s) := by fun_prop
  have hsplit : (∫ s in 0..t, oscillation₂ m Ω g x v s) =
      -(∫ s in 0..t, deriv g (x s) * slowVelocity m Ω g x v s / m * Real.sin (Ω * s)) +
        ∫ s in 0..t, g (x s) * deriv g (x s) / (2 * m ^ 2) * Real.cos (2 * Ω * s) := by
    have hc₂n : Continuous fun s =>
        -(deriv g (x s) * slowVelocity m Ω g x v s / m * Real.sin (Ω * s)) := hc₂.neg
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_add
      (hc₂n.intervalIntegrable 0 t) (hc₃.intervalIntegrable 0 t)]
    rfl
  rw [hsplit]
  have hM₂ : 0 ≤ (B * V * (V + B / m) + B * (A / m + B * V / m)) / m :=
    div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hB hV0) hVw0) (mul_nonneg hB hDw0)) hm.le
  have hM₃ : 0 ≤ (B * V * B + B * (B * V)) / (2 * m ^ 2) :=
    div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hB hV0) hB)
      (mul_nonneg hB (mul_nonneg hB hV0))) hm2.le
  have e₂ : (2 * (B * (V + B / m) / m) +
      t * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) / Ω ≤
      (2 * (B * (V + B / m) / m) +
        L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) / Ω :=
    div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2 hM₂)) hΩ.le
  have e₃ : (2 * (B * B / (2 * m ^ 2)) + t * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) /
      (2 * Ω) ≤
      (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) / (2 * Ω) :=
    div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2 hM₃))
      (mul_pos two_pos hΩ).le
  calc |-(∫ s in 0..t, deriv g (x s) * slowVelocity m Ω g x v s / m * Real.sin (Ω * s)) +
        ∫ s in 0..t, g (x s) * deriv g (x s) / (2 * m ^ 2) * Real.cos (2 * Ω * s)|
      ≤ |∫ s in 0..t, deriv g (x s) * slowVelocity m Ω g x v s / m * Real.sin (Ω * s)| +
          |∫ s in 0..t, g (x s) * deriv g (x s) / (2 * m ^ 2) * Real.cos (2 * Ω * s)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ (2 * (B * (V + B / m) / m) +
          L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) / Ω +
        (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) /
          (2 * Ω) := add_le_add (h₂.trans e₂) (h₃.trans e₃)
    _ = _ := by
        field_simp

end Integrals

/-! ### The motion in the effective potential -/

/-- Averaging for a rapidly oscillating force. For bounded `U′`, `U″`, `g`,
`g′`, `g″` there is a constant `C`, depending on the mass, the bounds, a bound
`V` of the velocity and the length `L` of the interval of time, such that for
every frequency `ω` a motion under the force `ω g(x) cos ωt` and the motion in
the effective potential `U + g²/4m` from the same position with the same
velocity differ by at most `C/ω` on `[0, L]`. -/
theorem exists_forall_abs_sub_le (hm : 0 < m) (hb : RapidBounds U g A B) (V L : ℝ) :
    ∃ C : ℝ, ∀ Ω : ℝ, 0 < Ω → ∀ x v X W : ℝ → ℝ, IsRapidMotion m Ω U g x v →
      IsSlowMotion m U g X W → x 0 = X 0 → v 0 = W 0 → (∀ t ∈ Icc 0 L, |v t| ≤ V) →
      ∀ t ∈ Icc 0 L, |x t - X t| ≤ C / Ω := by
  obtain ⟨K, hK⟩ := hb.exists_lipschitzWith hm
  refine ⟨((2 * (B / m) + L * (B * V / m)) +
    ((2 * (B * (V + B / m) / m) +
        L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) +
      (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) / 2)) *
    Real.exp (K * L), ?_⟩
  intro Ω hΩ x v X W hxv hXW h0 hv0 hV t ht
  have hL : 0 ≤ L := ht.1.trans ht.2
  have hA := hb.nonneg_potential
  have hB := hb.nonneg_amplitude
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, hL⟩)
  have hg := hb.contDiff_amplitude
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun s => (hxv.1 s).continuousAt
  have hwc : Continuous (slowVelocity m Ω g x v) :=
    continuous_iff_continuousAt.mpr fun s =>
      (hxv.hasDerivAt_slowVelocity hg hm.ne' s).continuousAt
  have hgc : Continuous g := hg.continuous
  have hg'c : Continuous (deriv g) := (hg.iterate_deriv 1).continuous
  have hc₁ : Continuous (oscillation₁ m Ω g x) := by
    unfold oscillation₁
    fun_prop
  have hc₂ : Continuous (oscillation₂ m Ω g x v) := by
    unfold oscillation₂
    fun_prop
  have hc1 : 0 ≤ 2 * (B / m) + L * (B * V / m) :=
    add_nonneg (mul_nonneg zero_le_two (div_nonneg hB hm.le))
      (mul_nonneg hL (div_nonneg (mul_nonneg hB hV0) hm.le))
  have hVw0 : 0 ≤ V + B / m := add_nonneg hV0 (div_nonneg hB hm.le)
  have hDw0 : 0 ≤ A / m + B * V / m :=
    add_nonneg (div_nonneg hA hm.le) (div_nonneg (mul_nonneg hB hV0) hm.le)
  have hm2 : (0 : ℝ) < 2 * m ^ 2 := by positivity
  have hc2 : 0 ≤ (2 * (B * (V + B / m) / m) +
      L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) +
      (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) / 2 := by
    have h1 : 0 ≤ B * (V + B / m) / m := div_nonneg (mul_nonneg hB hVw0) hm.le
    have h2 : 0 ≤ (B * V * (V + B / m) + B * (A / m + B * V / m)) / m :=
      div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hB hV0) hVw0) (mul_nonneg hB hDw0)) hm.le
    have h3 : 0 ≤ B * B / (2 * m ^ 2) := div_nonneg (mul_nonneg hB hB) hm2.le
    have h4 : 0 ≤ (B * V * B + B * (B * V)) / (2 * m ^ 2) :=
      div_nonneg (add_nonneg (mul_nonneg (mul_nonneg hB hV0) hB)
        (mul_nonneg hB (mul_nonneg hB hV0))) hm2.le
    have h5 := mul_nonneg hL h2
    have h6 := mul_nonneg hL h4
    linarith
  have hδ : ∀ s ∈ Icc 0 L,
      ‖∫ u in 0..s, (oscillation₁ m Ω g x u, oscillation₂ m Ω g x v u)‖ ≤
        ((2 * (B / m) + L * (B * V / m)) +
          ((2 * (B * (V + B / m) / m) +
              L * ((B * V * (V + B / m) + B * (A / m + B * V / m)) / m)) +
            (2 * (B * B / (2 * m ^ 2)) + L * ((B * V * B + B * (B * V)) / (2 * m ^ 2))) / 2)) /
          Ω := by
    intro s hs
    refine norm_integral_prodMk_le hc₁ hc₂ ?_ ?_
    · refine (hxv.abs_integral_oscillation₁_le hb hm hΩ hV hs).trans ?_
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_right hc2) hΩ.le
    · refine (hxv.abs_integral_oscillation₂_le hb hm hΩ hV hs).trans ?_
      exact div_le_div_of_nonneg_right (le_add_of_nonneg_left hc1) hΩ.le
  have hinit : (fun s => (x s, slowVelocity m Ω g x v s)) 0 = (fun s => (X s, W s)) 0 := by
    simp [slowVelocity, h0, hv0]
  have hcomp := norm_sub_le_of_norm_integral_le (hK.lipschitzOnWith (s := univ))
    (z := fun s => (x s, slowVelocity m Ω g x v s)) (Z := fun s => (X s, W s))
    (r := fun s => (oscillation₁ m Ω g x s, oscillation₂ m Ω g x v s)) (hc₁.prodMk hc₂)
    (fun s _ => hxv.hasDerivAt_pair hg hm.ne' s) (fun s _ => hXW.hasDerivAt_pair s)
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _) hδ hinit t ht
  have hfst : |x t - X t| ≤ ‖(x t, slowVelocity m Ω g x v t) - (X t, W t)‖ := by
    rw [Prod.mk_sub_mk, ← Real.norm_eq_abs]
    exact norm_fst_le (x t - X t, slowVelocity m Ω g x v t - W t)
  refine hfst.trans (hcomp.trans ?_)
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hΩ]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (add_nonneg hc1 hc2)
  exact mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg

/-- The velocity is bounded on an interval of time by a constant that does not
depend on the frequency. -/
theorem IsRapidMotion.abs_velocity_le (h : IsRapidMotion m Ω U g x v)
    (hb : RapidBounds U g A B) (hm : 0 < m) {L t : ℝ} (ht : t ∈ Icc 0 L) :
    |v t| ≤ (|v 0| + (A / m + B / m * (B / m)) * L) * Real.exp (B / m * L) + B / m := by
  have hA := hb.nonneg_potential
  have hB := hb.nonneg_amplitude
  have hg := hb.contDiff_amplitude
  have hw := h.hasDerivAt_slowVelocity hg hm.ne'
  have hBm : 0 ≤ B / m := div_nonneg hB hm.le
  have hosc : ∀ s, |g (x s) / m * Real.sin (Ω * s)| ≤ B / m := fun s => by
    rw [abs_mul, abs_div, abs_of_pos hm]
    calc |g (x s)| / m * |Real.sin (Ω * s)| ≤ B / m * 1 :=
          mul_le_mul (div_le_div_of_nonneg_right (hb.amplitude _) hm.le)
            (Real.abs_sin_le_one _) (abs_nonneg _) hBm
      _ = B / m := mul_one _
  have hvw : ∀ s, |v s| ≤ |slowVelocity m Ω g x v s| + B / m := fun s => by
    have h1 : v s = slowVelocity m Ω g x v s + g (x s) / m * Real.sin (Ω * s) := by
      simp only [slowVelocity]
      ring
    calc |v s| = |slowVelocity m Ω g x v s + g (x s) / m * Real.sin (Ω * s)| := by rw [← h1]
      _ ≤ |slowVelocity m Ω g x v s| + |g (x s) / m * Real.sin (Ω * s)| := abs_add_le _ _
      _ ≤ |slowVelocity m Ω g x v s| + B / m := add_le_add le_rfl (hosc s)
  have hbound : ∀ s ∈ Ico 0 L,
      ‖-deriv U (x s) / m - deriv g (x s) * v s / m * Real.sin (Ω * s)‖ ≤
        B / m * ‖slowVelocity m Ω g x v s‖ + (A / m + B / m * (B / m)) := by
    intro s _
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |-deriv U (x s) / m| ≤ A / m := by
      rw [abs_div, abs_neg, abs_of_pos hm]
      exact div_le_div_of_nonneg_right (hb.deriv_potential _) hm.le
    have h2 : |deriv g (x s) * v s / m * Real.sin (Ω * s)| ≤
        B / m * (|slowVelocity m Ω g x v s| + B / m) := by
      rw [abs_mul, abs_div, abs_of_pos hm, abs_mul]
      calc |deriv g (x s)| * |v s| / m * |Real.sin (Ω * s)|
          ≤ B * (|slowVelocity m Ω g x v s| + B / m) / m * 1 :=
            mul_le_mul (div_le_div_of_nonneg_right
              (mul_le_mul (hb.deriv_amplitude _) (hvw s) (abs_nonneg _) hB) hm.le)
              (Real.abs_sin_le_one _) (abs_nonneg _)
              (div_nonneg (mul_nonneg hB (add_nonneg (abs_nonneg _) hBm)) hm.le)
        _ = B / m * (|slowVelocity m Ω g x v s| + B / m) := by ring
    calc |-deriv U (x s) / m - deriv g (x s) * v s / m * Real.sin (Ω * s)|
        ≤ |-deriv U (x s) / m| + |deriv g (x s) * v s / m * Real.sin (Ω * s)| := abs_sub _ _
      _ ≤ A / m + B / m * (|slowVelocity m Ω g x v s| + B / m) := add_le_add h1 h2
      _ = B / m * |slowVelocity m Ω g x v s| + (A / m + B / m * (B / m)) := by ring
  have hinit : ‖slowVelocity m Ω g x v 0‖ ≤ |v 0| := by
    simp [slowVelocity]
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun s _ => (hw s).continuousAt.continuousWithinAt)
    (fun s _ => (hw s).hasDerivWithinAt) hinit hbound t ht
  rw [sub_zero, Real.norm_eq_abs] at hgron
  have hle := gronwallBound_le_mul_exp (abs_nonneg (v 0)) hBm
    (add_nonneg (div_nonneg hA hm.le) (mul_nonneg hBm hBm)) ht.1 ht.2
  exact (hvw t).trans (add_le_add (hgron.trans hle) le_rfl)

/-- Averaging for a rapidly oscillating force, with a bound of the initial
velocity only: the constant does not depend on the frequency. -/
theorem exists_forall_abs_sub_le_of_initial (hm : 0 < m) (hb : RapidBounds U g A B)
    (V₀ L : ℝ) :
    ∃ C : ℝ, ∀ Ω : ℝ, 0 < Ω → ∀ x v X W : ℝ → ℝ, IsRapidMotion m Ω U g x v →
      IsSlowMotion m U g X W → x 0 = X 0 → v 0 = W 0 → |v 0| ≤ V₀ →
      ∀ t ∈ Icc 0 L, |x t - X t| ≤ C / Ω := by
  obtain ⟨C, hC⟩ := exists_forall_abs_sub_le hm hb
    ((V₀ + (A / m + B / m * (B / m)) * L) * Real.exp (B / m * L) + B / m) L
  refine ⟨C, fun Ω hΩ x v X W hxv hXW h0 hv0 hV₀ t ht => ?_⟩
  refine hC Ω hΩ x v X W hxv hXW h0 hv0 (fun s hs => ?_) t ht
  refine (hxv.abs_velocity_le hb hm hs).trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_right (add_le_add hV₀ le_rfl) (Real.exp_pos _).le

/-! ### The pendulum with an oscillating point of support -/

namespace Pendulum

variable (a b : ℝ)

/-- The potential `−a cos x` of the pendulum and the amplitude `b sin x` of the
force of the oscillating support satisfy the bounds. -/
theorem rapidBounds :
    RapidBounds (fun y => -(a * Real.cos y)) (fun y => b * Real.sin y) |a| |b| := by
  have hU' : deriv (fun y => -(a * Real.cos y)) = fun y => a * Real.sin y := by
    funext y
    have h : HasDerivAt (fun y => -(a * Real.cos y)) (-(a * -Real.sin y)) y :=
      ((Real.hasDerivAt_cos y).const_mul a).neg
    rw [h.deriv]
    ring
  have hU'' : deriv (fun y => a * Real.sin y) = fun y => a * Real.cos y := by
    funext y
    exact ((Real.hasDerivAt_sin y).const_mul a).deriv
  have hg' : deriv (fun y => b * Real.sin y) = fun y => b * Real.cos y := by
    funext y
    exact ((Real.hasDerivAt_sin y).const_mul b).deriv
  have hg'' : deriv (fun y => b * Real.cos y) = fun y => -(b * Real.sin y) := by
    funext y
    have h := (Real.hasDerivAt_cos y).const_mul b
    rw [h.deriv]
    ring
  have hsin : ∀ (c y : ℝ), |c * Real.sin y| ≤ |c| := fun c y => by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one y)
  have hcos : ∀ (c y : ℝ), |c * Real.cos y| ≤ |c| := fun c y => by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one y)
  refine ⟨(contDiff_const.mul Real.contDiff_cos).neg, contDiff_const.mul Real.contDiff_sin,
    fun y => ?_, fun y => ?_, fun y => hsin b y, fun y => ?_, fun y => ?_⟩
  · rw [hU']
    exact hsin a y
  · rw [hU', hU'']
    exact hcos a y
  · rw [hg']
    exact hcos b y
  · rw [hg', hg'', abs_neg]
    exact hsin b y

/-- The force of the effective potential of the pendulum, and its derivative at
the upper position: the effective potential has a minimum there exactly when
`b² > 2 m a`. -/
theorem hasDerivAt_effectiveForce (m : ℝ) :
    HasDerivAt (fun y => a * Real.sin y + b * Real.sin y * (b * Real.cos y) / (2 * m))
      (-a + b ^ 2 / (2 * m)) Real.pi := by
  have h1 := (Real.hasDerivAt_sin Real.pi).const_mul a
  have h2 := (((Real.hasDerivAt_sin Real.pi).const_mul b).mul
    ((Real.hasDerivAt_cos Real.pi).const_mul b)).div_const (2 * m)
  refine (h1.add h2).congr_deriv ?_
  simp only [Real.sin_pi, Real.cos_pi]
  ring

theorem pos_iff {m : ℝ} (hm : 0 < m) : 0 < -a + b ^ 2 / (2 * m) ↔ 2 * m * a < b ^ 2 := by
  rw [neg_add_eq_sub, sub_pos, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

end Pendulum

end ProjectAinos.Mechanics.RapidForce
