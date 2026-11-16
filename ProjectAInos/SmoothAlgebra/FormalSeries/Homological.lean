/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.FormalSeries.Bracket
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-!
# The homological equation of the harmonic oscillator

`action = (q² + p²)/2`. On the homogeneous series of degree `k` the bracket
with `action` is skew for the positive pairing `fischer k`, so that every
homogeneous `G` of degree `k` is `{action, F} + c · resonant k`
(`exists_homological`), where `resonant k` is `action ^ (k/2)` for even `k` and
zero for odd `k`. The kernel of the bracket with `action` on the homogeneous
series of degree `k` is spanned by `resonant k` (`eq_smul_resonant`).
-/

@[expose] public section
noncomputable section

open MvPowerSeries Finset Module
open scoped Nat

namespace ProjectAInos.SmoothAlgebra.FormalSeries

/-! ### Exponents of monomials -/

/-- The exponent of the monomial `qᵃ pᵇ`. -/
def mono (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem mono_apply_zero (a b : ℕ) : mono a b 0 = a := by simp [mono]

@[simp] theorem mono_apply_one (a b : ℕ) : mono a b 1 = b := by simp [mono]

theorem degree_mono (a b : ℕ) : (mono a b).degree = a + b := by
  simp [mono, Finsupp.degree_single]

theorem eq_mono (d : Fin 2 →₀ ℕ) : d = mono (d 0) (d 1) := by
  ext i
  fin_cases i <;> simp

theorem degree_eq_add (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  conv_lhs => rw [eq_mono d]
  exact degree_mono _ _

theorem mono_add_single_zero (a b : ℕ) : mono a b + Finsupp.single 0 1 = mono (a + 1) b := by
  ext i
  fin_cases i <;> simp

theorem mono_add_single_one (a b : ℕ) : mono a b + Finsupp.single 1 1 = mono a (b + 1) := by
  ext i
  fin_cases i <;> simp

theorem coeff_mono_pderiv_zero (f : PhaseSeries) (a b : ℕ) :
    coeff (mono a b) (pderiv 0 f) = coeff (mono (a + 1) b) f * (a + 1) := by
  rw [coeff_pderiv, mono_add_single_zero, mono_apply_zero]

theorem coeff_mono_pderiv_one (f : PhaseSeries) (a b : ℕ) :
    coeff (mono a b) (pderiv 1 f) = coeff (mono a (b + 1)) f * (b + 1) := by
  rw [coeff_pderiv, mono_add_single_one, mono_apply_one]

theorem coeff_mono_succ_X_zero_mul (f : PhaseSeries) (a b : ℕ) :
    coeff (mono (a + 1) b) (X 0 * f) = coeff (mono a b) f := by
  rw [← mono_add_single_zero, add_comm, X_def, coeff_add_monomial_mul, one_mul]

theorem coeff_mono_zero_X_zero_mul (f : PhaseSeries) (b : ℕ) :
    coeff (mono 0 b) (X 0 * f) = 0 := by
  rw [X_def, coeff_monomial_mul]
  split_ifs with h
  · have := h 0
    simp at this
  · rfl

theorem coeff_mono_succ_X_one_mul (f : PhaseSeries) (a b : ℕ) :
    coeff (mono a (b + 1)) (X 1 * f) = coeff (mono a b) f := by
  rw [← mono_add_single_one, add_comm, X_def, coeff_add_monomial_mul, one_mul]

theorem coeff_mono_zero_X_one_mul (f : PhaseSeries) (a : ℕ) :
    coeff (mono a 0) (X 1 * f) = 0 := by
  rw [X_def, coeff_monomial_mul]
  split_ifs with h
  · have := h 1
    simp at this
  · rfl

/-! ### Homogeneous series -/

/-- The series all of whose terms have degree `k`. -/
def homogeneous (k : ℕ) : Submodule ℝ PhaseSeries where
  carrier := {f | ∀ d : Fin 2 →₀ ℕ, d.degree ≠ k → coeff d f = 0}
  add_mem' := by
    intro f g hf hg d hd
    simp [hf d hd, hg d hd]
  zero_mem' := by
    intro d _
    simp
  smul_mem' := by
    intro c f hf d hd
    simp [hf d hd]

variable {k : ℕ} {f g : PhaseSeries}

theorem mem_homogeneous : f ∈ homogeneous k ↔ ∀ d : Fin 2 →₀ ℕ, d.degree ≠ k → coeff d f = 0 :=
  Iff.rfl

theorem mem_homogeneous_iff_isHomogeneous : f ∈ homogeneous k ↔ f.IsHomogeneous k := by
  constructor
  · intro hf d hd
    by_contra h
    exact hd (hf d (by rwa [Finsupp.degree_eq_weight_one]))
  · intro hf d hd
    exact hf.coeff_eq_zero hd

theorem mul_mem_homogeneous {a b : ℕ} (hf : f ∈ homogeneous a) (hg : g ∈ homogeneous b) :
    f * g ∈ homogeneous (a + b) := by
  rw [mem_homogeneous_iff_isHomogeneous] at hf hg ⊢
  exact hf.mul hg

theorem one_mem_homogeneous : (1 : PhaseSeries) ∈ homogeneous 0 := by
  classical
  intro d hd
  rw [coeff_one]
  split_ifs with h
  · exact absurd (by rw [h]; simp) hd
  · rfl

theorem pow_mem_homogeneous {a : ℕ} (hf : f ∈ homogeneous a) (n : ℕ) :
    f ^ n ∈ homogeneous (n * a) := by
  induction n with
  | zero => simpa using one_mem_homogeneous
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_homogeneous ih hf

theorem X_mem_homogeneous (i : Fin 2) : (X i : PhaseSeries) ∈ homogeneous 1 := by
  classical
  intro d hd
  rw [coeff_X]
  split_ifs with h
  · exact absurd (by rw [h, Finsupp.degree_single]) hd
  · rfl

theorem homogeneous_le_orderGE (k : ℕ) : homogeneous k ≤ orderGE (Fin 2) k :=
  fun _ hf d hd => hf d (Nat.ne_of_lt hd)

theorem pderiv_mem_homogeneous (hf : f ∈ homogeneous (k + 1)) (i : Fin 2) :
    pderiv i f ∈ homogeneous k := by
  intro d hd
  rw [coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.degree_single]
  omega

theorem pderiv_eq_zero_of_mem_homogeneous_zero (hf : f ∈ homogeneous 0) (i : Fin 2) :
    pderiv i f = 0 := by
  ext d
  rw [coeff_pderiv, hf, zero_mul, map_zero]
  rw [map_add, Finsupp.degree_single]
  omega

theorem bracket_mem_homogeneous {a b : ℕ} (hf : f ∈ homogeneous (a + 1))
    (hg : g ∈ homogeneous (b + 1)) : bracket f g ∈ homogeneous (a + b) :=
  sub_mem (mul_mem_homogeneous (pderiv_mem_homogeneous hf 0) (pderiv_mem_homogeneous hg 1))
    (mul_mem_homogeneous (pderiv_mem_homogeneous hf 1) (pderiv_mem_homogeneous hg 0))

theorem homogeneousComponent_mem (k : ℕ) (f : PhaseSeries) :
    homogeneousComponent k f ∈ homogeneous k := by
  intro d hd
  rw [coeff_homogeneousComponent]
  simp only [hd, ↓reduceIte]

theorem homogeneousComponent_eq_self (hf : f ∈ homogeneous k) :
    homogeneousComponent k f = f := by
  ext d
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · rfl
  · exact (hf d h).symm

theorem homogeneousComponent_eq_zero_of_mem {n : ℕ} (hf : f ∈ homogeneous k) (h : n ≠ k) :
    homogeneousComponent n f = 0 := by
  ext d
  rw [coeff_homogeneousComponent, map_zero]
  split_ifs with hd
  · exact hf d (by omega)
  · rfl

theorem homogeneousComponent_eq_zero (hf : f ∈ orderGE (Fin 2) (k + 1)) :
    homogeneousComponent k f = 0 := by
  ext d
  rw [coeff_homogeneousComponent, map_zero]
  split_ifs with hd
  · exact hf d (by omega)
  · rfl

theorem sub_homogeneousComponent_mem (hf : f ∈ orderGE (Fin 2) k) :
    f - homogeneousComponent k f ∈ orderGE (Fin 2) (k + 1) := by
  intro d hd
  rw [map_sub, coeff_homogeneousComponent]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    exact hf d (by omega)

/-- Two series that agree to the order `k + 1` have the same component of
degree `k`. -/
theorem homogeneousComponent_congr (h : f - g ∈ orderGE (Fin 2) (k + 1)) :
    homogeneousComponent k f = homogeneousComponent k g := by
  have := homogeneousComponent_eq_zero h
  rwa [map_sub, sub_eq_zero] at this

/-! ### The action and the rotation -/

/-- The action `(q² + p²)/2` of the harmonic oscillator. -/
def action : PhaseSeries := (2⁻¹ : ℝ) • (X 0 ^ 2 + X 1 ^ 2)

theorem action_mem_homogeneous : action ∈ homogeneous 2 :=
  Submodule.smul_mem _ _ (add_mem (pow_mem_homogeneous (X_mem_homogeneous 0) 2)
    (pow_mem_homogeneous (X_mem_homogeneous 1) 2))

theorem pderiv_zero_action : pderiv 0 action = X 0 := by
  rw [action, Derivation.map_smul, map_add, Derivation.leibniz_pow, Derivation.leibniz_pow,
    pderiv_X_self, pderiv_X_of_ne (by decide)]
  simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul, mul_one, mul_zero]
  module

theorem pderiv_one_action : pderiv 1 action = X 1 := by
  rw [action, Derivation.map_smul, map_add, Derivation.leibniz_pow, Derivation.leibniz_pow,
    pderiv_X_self, pderiv_X_of_ne (by decide)]
  simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul, mul_one, mul_zero]
  module

/-- The bracket with the action is the generator of the rotations. -/
theorem bracket_action (g : PhaseSeries) :
    bracket action g = X 0 * pderiv 1 g - X 1 * pderiv 0 g := by
  rw [bracket, pderiv_zero_action, pderiv_one_action]

theorem bracket_action_mem_homogeneous (hg : g ∈ homogeneous k) :
    bracket action g ∈ homogeneous k := by
  cases k with
  | zero =>
    rw [bracket_action, pderiv_eq_zero_of_mem_homogeneous_zero hg,
      pderiv_eq_zero_of_mem_homogeneous_zero hg]
    simp
  | succ k =>
    have := bracket_mem_homogeneous (a := 1) (b := k) action_mem_homogeneous hg
    rwa [Nat.add_comm] at this

theorem coeff_mono_bracket_action (f : PhaseSeries) (a b : ℕ) :
    coeff (mono (a + 1) (b + 1)) (bracket action f) =
      coeff (mono a (b + 2)) f * (b + 2) - coeff (mono (a + 2) b) f * (a + 2) := by
  rw [bracket_action, map_sub, coeff_mono_succ_X_zero_mul, coeff_mono_succ_X_one_mul,
    coeff_mono_pderiv_one, coeff_mono_pderiv_zero]
  push_cast
  ring_nf

theorem coeff_mono_zero_bracket_action (f : PhaseSeries) (b : ℕ) :
    coeff (mono 0 (b + 1)) (bracket action f) = -coeff (mono 1 b) f := by
  rw [bracket_action, map_sub, coeff_mono_zero_X_zero_mul, coeff_mono_succ_X_one_mul,
    coeff_mono_pderiv_zero]
  simp

theorem coeff_mono_bracket_action_zero (f : PhaseSeries) (a : ℕ) :
    coeff (mono (a + 1) 0) (bracket action f) = coeff (mono a 1) f := by
  rw [bracket_action, map_sub, coeff_mono_succ_X_zero_mul, coeff_mono_zero_X_one_mul,
    coeff_mono_pderiv_one]
  simp

theorem coeff_zero_bracket_action (f : PhaseSeries) :
    coeff (mono 0 0) (bracket action f) = 0 := by
  rw [bracket_action, map_sub, coeff_mono_zero_X_zero_mul, coeff_mono_zero_X_one_mul, sub_zero]

/-! ### The kernel of the rotation -/

theorem coeff_odd_left_eq_zero (h : bracket action f = 0) (m b : ℕ) :
    coeff (mono (2 * m + 1) b) f = 0 := by
  induction m generalizing b with
  | zero =>
    have h1 := coeff_mono_zero_bracket_action f b
    rw [h, map_zero] at h1
    simpa using h1.symm
  | succ m ih =>
    have h1 := coeff_mono_bracket_action f (2 * m + 1) b
    rw [h, map_zero, ih (b + 2), zero_mul, zero_sub] at h1
    have hne : ((2 * m + 1 : ℕ) : ℝ) + 2 ≠ 0 := by positivity
    have h2 : coeff (mono (2 * m + 1 + 2) b) f = 0 := by
      rcases mul_eq_zero.mp (neg_eq_zero.mp h1.symm) with h3 | h3
      · exact h3
      · exact absurd (by exact_mod_cast h3) hne
    rwa [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]

theorem coeff_odd_right_eq_zero (h : bracket action f = 0) (a m : ℕ) :
    coeff (mono a (2 * m + 1)) f = 0 := by
  induction m generalizing a with
  | zero =>
    have h1 := coeff_mono_bracket_action_zero f a
    rw [h, map_zero] at h1
    simpa using h1.symm
  | succ m ih =>
    have h1 := coeff_mono_bracket_action f a (2 * m + 1)
    rw [h, map_zero, ih (a + 2), zero_mul, sub_zero] at h1
    have hne : ((2 * m + 1 : ℕ) : ℝ) + 2 ≠ 0 := by positivity
    have h2 : coeff (mono a (2 * m + 1 + 2)) f = 0 := by
      rcases mul_eq_zero.mp h1.symm with h3 | h3
      · exact h3
      · exact absurd (by exact_mod_cast h3) hne
    rwa [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]

theorem coeff_even_left_eq_zero (h : bracket action f = 0)
    (h0 : ∀ b, coeff (mono 0 b) f = 0) (m b : ℕ) : coeff (mono (2 * m) b) f = 0 := by
  induction m generalizing b with
  | zero => exact h0 b
  | succ m ih =>
    have h1 := coeff_mono_bracket_action f (2 * m) b
    rw [h, map_zero, ih (b + 2), zero_mul, zero_sub] at h1
    have hne : ((2 * m : ℕ) : ℝ) + 2 ≠ 0 := by positivity
    have h2 : coeff (mono (2 * m + 2) b) f = 0 := by
      rcases mul_eq_zero.mp (neg_eq_zero.mp h1.symm) with h3 | h3
      · exact h3
      · exact absurd (by exact_mod_cast h3) hne
    rwa [show 2 * (m + 1) = 2 * m + 2 by ring]

/-- A series that is invariant under the rotation and has no power of `p`
alone is zero. -/
theorem eq_zero_of_bracket_action_eq_zero (h : bracket action f = 0)
    (h0 : ∀ b, coeff (mono 0 b) f = 0) : f = 0 := by
  ext d
  rw [map_zero, eq_mono d]
  rcases Nat.even_or_odd' (d 0) with ⟨m, hm | hm⟩
  · rw [hm]
    exact coeff_even_left_eq_zero h h0 m _
  · rw [hm]
    exact coeff_odd_left_eq_zero h m _

theorem bracket_action_action_pow (m : ℕ) : bracket action (action ^ m) = 0 := by
  induction m with
  | zero => simp [bracket]
  | succ m ih => rw [pow_succ, bracket_mul_right, ih, bracket_self, zero_mul, mul_zero, add_zero]

theorem action_eq : action = (2⁻¹ : ℝ) • X 1 ^ 2 + X 0 * ((2⁻¹ : ℝ) • X 0) := by
  rw [action, smul_add, mul_smul_comm, ← pow_two, add_comm]

theorem exists_action_pow (m : ℕ) :
    ∃ w : PhaseSeries, action ^ m = ((2⁻¹ : ℝ) • X 1 ^ 2) ^ m + X 0 * w := by
  have key : ∀ u v : PhaseSeries, ∃ w : PhaseSeries, (u + X 0 * v) ^ m = u ^ m + X 0 * w := by
    intro u v
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨u ^ m * v + w * (u + X 0 * v), by rw [pow_succ, hw]; ring⟩
  rw [action_eq]
  exact key _ _

theorem coeff_mono_zero_action_pow (m : ℕ) :
    coeff (mono 0 (2 * m)) (action ^ m) = (2⁻¹ : ℝ) ^ m := by
  obtain ⟨w, hw⟩ := exists_action_pow m
  rw [hw, map_add, coeff_mono_zero_X_zero_mul, add_zero, smul_pow, ← pow_mul, X_pow_eq]
  have : mono 0 (2 * m) = Finsupp.single 1 (2 * m) := by simp [mono]
  rw [this, map_smul, coeff_monomial_same, smul_eq_mul, mul_one]

/-- The resonant series of degree `k`: a power of the action for even `k`,
zero for odd `k`. -/
def resonant (k : ℕ) : PhaseSeries := if Even k then action ^ (k / 2) else 0

theorem resonant_two_mul (m : ℕ) : resonant (2 * m) = action ^ m := by
  simp [resonant]

theorem resonant_two_mul_add_one (m : ℕ) : resonant (2 * m + 1) = 0 := by
  simp [resonant]

theorem resonant_mem_homogeneous (k : ℕ) : resonant k ∈ homogeneous k := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [resonant_two_mul, Nat.mul_comm]
    exact pow_mem_homogeneous action_mem_homogeneous m
  · rw [resonant_two_mul_add_one]
    exact zero_mem _

theorem bracket_action_resonant (k : ℕ) : bracket action (resonant k) = 0 := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [resonant_two_mul, bracket_action_action_pow]
  · rw [resonant_two_mul_add_one]
    simp [bracket]

/-- A homogeneous series that is invariant under the rotation is a multiple of
the resonant series of its degree. -/
theorem eq_smul_resonant {z : PhaseSeries} (hz : z ∈ homogeneous k)
    (h : bracket action z = 0) : ∃ c : ℝ, z = c • resonant k := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · refine ⟨coeff (mono 0 (2 * m)) z * 2 ^ m, ?_⟩
    rw [resonant_two_mul]
    have hpow : action ^ m ∈ homogeneous (2 * m) := by
      rw [Nat.mul_comm]
      exact pow_mem_homogeneous action_mem_homogeneous m
    refine sub_eq_zero.mp (eq_zero_of_bracket_action_eq_zero ?_ fun b => ?_)
    · rw [sub_eq_add_neg, bracket_add_right, ← neg_smul, bracket_smul_right, h,
        bracket_action_action_pow, smul_zero, add_zero]
    · by_cases hb : b = 2 * m
      · subst hb
        rw [map_sub, map_smul, coeff_mono_zero_action_pow, smul_eq_mul, mul_assoc, ← mul_pow]
        norm_num
      · have hd : (mono 0 b).degree ≠ 2 * m := by
          rw [degree_mono]
          omega
        exact sub_mem hz (Submodule.smul_mem _ _ hpow) _ hd
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    refine eq_zero_of_bracket_action_eq_zero h fun b => ?_
    by_cases hb : b = 2 * m + 1
    · subst hb
      exact coeff_odd_right_eq_zero h 0 m
    · exact hz _ (by rw [degree_mono]; omega)

/-! ### The pairing -/

/-- The pairing `∑ a! b! f_{ab} g_{ab}` over the monomials `qᵃ pᵇ` of degree
`k`. -/
def fischer (k : ℕ) (f g : PhaseSeries) : ℝ :=
  ∑ i ∈ range (k + 1),
    (i ! : ℝ) * ((k - i)! : ℝ) * (coeff (mono i (k - i)) f * coeff (mono i (k - i)) g)

theorem fischer_comm (k : ℕ) (f g : PhaseSeries) : fischer k f g = fischer k g f :=
  sum_congr rfl fun _ _ => by ring

theorem fischer_sub_left (k : ℕ) (f₁ f₂ g : PhaseSeries) :
    fischer k (f₁ - f₂) g = fischer k f₁ g - fischer k f₂ g := by
  simp only [fischer, map_sub, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem fischer_X_zero_mul (k : ℕ) (f g : PhaseSeries) :
    fischer (k + 1) (X 0 * f) g = fischer k f (pderiv 0 g) := by
  unfold fischer
  rw [sum_range_succ' _ (k + 1)]
  simp only [coeff_mono_zero_X_zero_mul, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.add_sub_add_right, coeff_mono_succ_X_zero_mul, coeff_mono_pderiv_zero,
    Nat.factorial_succ]
  push_cast
  ring

theorem fischer_X_one_mul (k : ℕ) (f g : PhaseSeries) :
    fischer (k + 1) (X 1 * f) g = fischer k f (pderiv 1 g) := by
  unfold fischer
  rw [sum_range_succ _ (k + 1), Nat.sub_self, coeff_mono_zero_X_one_mul]
  simp only [zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (mem_range.1 hi)
  rw [Nat.succ_sub hi', coeff_mono_succ_X_one_mul, coeff_mono_pderiv_one, Nat.factorial_succ]
  push_cast
  ring

/-- The bracket with the action is skew for the pairing. -/
theorem fischer_bracket_action (k : ℕ) (f g : PhaseSeries) :
    fischer k (bracket action f) g = -fischer k f (bracket action g) := by
  cases k with
  | zero => simp [fischer, coeff_zero_bracket_action]
  | succ k =>
    rw [fischer_comm (k + 1) f, bracket_action, bracket_action, fischer_sub_left,
      fischer_sub_left, fischer_X_zero_mul, fischer_X_one_mul, fischer_X_zero_mul,
      fischer_X_one_mul, fischer_comm k (pderiv 1 g), fischer_comm k (pderiv 0 g)]
    ring

theorem eq_zero_of_fischer_self (hf : f ∈ homogeneous k) (h : fischer k f f = 0) : f = 0 := by
  have hnn : ∀ i ∈ range (k + 1), 0 ≤ (i ! : ℝ) * ((k - i)! : ℝ) *
      (coeff (mono i (k - i)) f * coeff (mono i (k - i)) f) :=
    fun i _ => mul_nonneg (by positivity) (mul_self_nonneg _)
  have hz := (sum_eq_zero_iff_of_nonneg hnn).mp h
  ext d
  rw [map_zero]
  by_cases hd : d.degree = k
  · have hdeg := degree_eq_add d
    have h1 := hz (d 0) (mem_range.2 (by omega))
    have hpos : (0 : ℝ) < ((d 0)! : ℝ) * ((k - d 0)! : ℝ) := by positivity
    have hsq := (mul_eq_zero.mp h1).resolve_left hpos.ne'
    rw [eq_mono d, show d 1 = k - d 0 by omega]
    exact mul_self_eq_zero.mp hsq
  · exact hf d hd

/-! ### The homological equation -/

theorem finiteDimensional_homogeneous (k : ℕ) : FiniteDimensional ℝ (homogeneous k) := by
  let Φ : homogeneous k →ₗ[ℝ] (Fin (k + 1) → ℝ) :=
    { toFun := fun f i => coeff (mono i (k - i)) (f : PhaseSeries)
      map_add' := fun f g => by
        ext i
        simp
      map_smul' := fun c f => by
        ext i
        simp }
  refine FiniteDimensional.of_injective Φ fun f g hfg => ?_
  refine Subtype.ext (MvPowerSeries.ext fun d => ?_)
  by_cases hd : d.degree = k
  · have hdeg := degree_eq_add d
    have h1 := congrFun hfg ⟨d 0, by omega⟩
    rw [eq_mono d, show d 1 = k - d 0 by omega]
    exact h1
  · rw [f.2 d hd, g.2 d hd]

/-- The homological equation of the harmonic oscillator: a homogeneous series
of degree `k` is a bracket with the action plus a multiple of the resonant
series. -/
theorem exists_homological (k : ℕ) {G : PhaseSeries} (hG : G ∈ homogeneous k) :
    ∃ F ∈ homogeneous k, ∃ c : ℝ, G = bracket action F + c • resonant k := by
  have hfin : FiniteDimensional ℝ (homogeneous k) := finiteDimensional_homogeneous k
  obtain ⟨R, hR⟩ : ∃ R : homogeneous k →ₗ[ℝ] homogeneous k,
      ∀ f : homogeneous k, (R f : PhaseSeries) = bracket action f :=
    ⟨(ad action).restrict fun f hf => bracket_action_mem_homogeneous hf, fun f => rfl⟩
  have hdisj : Disjoint (LinearMap.range R) (LinearMap.ker R) := by
    rw [Submodule.disjoint_def]
    rintro x ⟨y, rfl⟩ hx
    have hx' : bracket action (R y : PhaseSeries) = 0 := by
      rw [← hR (R y), LinearMap.mem_ker.mp hx]
      rfl
    have h1 : fischer k (bracket action (y : PhaseSeries)) (R y : PhaseSeries) = 0 := by
      rw [fischer_bracket_action, hx']
      simp [fischer]
    rw [← hR y] at h1
    exact Subtype.ext (eq_zero_of_fischer_self (R y).2 h1)
  have htop := Submodule.eq_top_of_disjoint _ _
    (LinearMap.finrank_range_add_finrank_ker R).ge hdisj
  have hmem : (⟨G, hG⟩ : homogeneous k) ∈ LinearMap.range R ⊔ LinearMap.ker R := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, ⟨F, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  have hz' : bracket action (z : PhaseSeries) = 0 := by
    rw [← hR z, LinearMap.mem_ker.mp hz]
    rfl
  obtain ⟨c, hc⟩ := eq_smul_resonant z.2 hz'
  refine ⟨F, F.2, c, ?_⟩
  have h2 := congrArg Subtype.val hyz
  rw [Submodule.coe_add, hR F, hc] at h2
  exact h2.symm

end ProjectAInos.SmoothAlgebra.FormalSeries
