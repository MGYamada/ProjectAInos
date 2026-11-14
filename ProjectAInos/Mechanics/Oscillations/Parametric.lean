/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Harmonic
public import ProjectAInos.Mechanics.TimePrimitive
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Parametric resonance

The equation `ẍ + p(t) x = 0` with a coefficient `p` of period `T`
(Landau–Lifshitz §27).

The Wronskian of two solutions is constant. Given a fundamental system, that
is, the two solutions with the initial data `(1, 0)` and `(0, 1)`, every
solution is the combination with its own initial data, and the matrix
`Φ(t)` of the fundamental system has determinant one. Periodicity of `p` gives
`Φ(s + nT) = Φ(s) Mⁿ` with the monodromy matrix `M = Φ(T)`.

For a real `2 × 2` matrix `A` of determinant one with `|tr A| < 2`, put
`tr A = 2 cos θ`. Then `sin θ · Aᵏ⁺¹ = sin (k+1)θ · A − sin kθ · 1`, so the
powers of `A` are bounded. Hence, if `|tr M| < 2`, every solution is bounded
for `t ≥ 0`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Parametric

open Matrix SmoothAlgebra SmoothRing

/-! ### Powers of a matrix of determinant one -/

/-- The Cayley–Hamilton identity for a `2 × 2` matrix of determinant one:
`A² = (tr A) A − 1`. -/
theorem mul_self_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1) :
    A * A = A.trace • A - 1 := by
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply, Matrix.one_apply_eq]
    linear_combination (-1 : ℝ) * hdet
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply, ne_eq, zero_ne_one,
      not_false_eq_true, Matrix.one_apply_ne]
    ring
  · simp only [Fin.zero_eta, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply, ne_eq, one_ne_zero,
      not_false_eq_true, Matrix.one_apply_ne]
    ring
  · simp only [Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag_apply, Matrix.one_apply_eq]
    linear_combination (-1 : ℝ) * hdet

/-- The powers of a matrix of determinant one with `tr A = 2 cos θ`:
`sin θ · Aᵏ⁺¹ = sin (k+1)θ · A − sin kθ · 1`. -/
theorem sin_smul_pow_succ {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1) {θ : ℝ}
    (hθ : A.trace = 2 * Real.cos θ) (k : ℕ) :
    Real.sin θ • A ^ (k + 1) =
      Real.sin ((k + 1 : ℕ) * θ) • A - Real.sin ((k : ℕ) * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : Real.sin ((k + 1 + 1 : ℕ) * θ) =
        2 * Real.cos θ * Real.sin ((k + 1 : ℕ) * θ) - Real.sin ((k : ℕ) * θ) := by
      have h1 : ((k + 1 + 1 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by
        push_cast
        ring
      have h2 : ((k : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by
        push_cast
        ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      ring
    rw [pow_succ, ← smul_mul_assoc, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul,
      mul_self_eq hdet, hθ, hs]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- The powers of a real `2 × 2` matrix of determinant one with `|tr A| < 2`
are bounded. -/
theorem exists_abs_pow_apply_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1)
    (htr : |A.trace| < 2) : ∃ C : ℝ, ∀ (k : ℕ) (i j : Fin 2), |(A ^ k) i j| ≤ C := by
  have hlt := abs_lt.mp htr
  have hcos : Real.cos (Real.arccos (A.trace / 2)) = A.trace / 2 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hθ : A.trace = 2 * Real.cos (Real.arccos (A.trace / 2)) := by
    rw [hcos]
    ring
  have hsin : 0 < Real.sin (Real.arccos (A.trace / 2)) := by
    rw [Real.sin_arccos]
    exact Real.sqrt_pos.mpr (by nlinarith)
  refine ⟨(∑ i, ∑ j, |A i j| + 1) / Real.sin (Real.arccos (A.trace / 2)) + 1, fun k i j => ?_⟩
  have hsum : |A i j| ≤ ∑ i, ∑ j, |A i j| :=
    (Finset.single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have hnonneg : 0 ≤ (∑ i, ∑ j, |A i j| + 1) / Real.sin (Real.arccos (A.trace / 2)) :=
    div_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      abs_nonneg _) zero_le_one) hsin.le
  cases k with
  | zero =>
    have h1 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [pow_zero]
    linarith
  | succ k =>
    have h := congrFun (congrFun (sin_smul_pow_succ hdet hθ k) i) j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have h1 : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have hbound : |Real.sin (Real.arccos (A.trace / 2)) * (A ^ (k + 1)) i j| ≤
        ∑ i, ∑ j, |A i j| + 1 := by
      rw [h]
      calc |Real.sin ((k + 1 : ℕ) * Real.arccos (A.trace / 2)) * A i j -
            Real.sin ((k : ℕ) * Real.arccos (A.trace / 2)) *
              (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|
          ≤ |Real.sin ((k + 1 : ℕ) * Real.arccos (A.trace / 2)) * A i j| +
            |Real.sin ((k : ℕ) * Real.arccos (A.trace / 2)) *
              (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := abs_sub _ _
        _ ≤ |A i j| + 1 := by
          rw [abs_mul, abs_mul]
          have s1 := Real.abs_sin_le_one ((k + 1 : ℕ) * Real.arccos (A.trace / 2))
          have s2 := Real.abs_sin_le_one ((k : ℕ) * Real.arccos (A.trace / 2))
          nlinarith [abs_nonneg (A i j), abs_nonneg ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)]
        _ ≤ ∑ i, ∑ j, |A i j| + 1 := by linarith
    rw [abs_mul, abs_of_pos hsin] at hbound
    have hdiv : |(A ^ (k + 1)) i j| ≤
        (∑ i, ∑ j, |A i j| + 1) / Real.sin (Real.arccos (A.trace / 2)) := by
      rw [le_div_iff₀ hsin]
      linarith
    linarith

/-- The powers of `1` and of `−1` are bounded. -/
theorem exists_abs_pow_apply_le_of_eq {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A = 1 ∨ A = -1) :
    ∃ C : ℝ, ∀ (k : ℕ) (i j : Fin 2), |(A ^ k) i j| ≤ C := by
  have h1 (i j : Fin 2) : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨1, fun k i j => ?_⟩
  rcases hA with rfl | rfl
  · rw [one_pow]
    exact h1 i j
  · rcases neg_one_pow_eq_or (Matrix (Fin 2) (Fin 2) ℝ) k with h | h
    · rw [h]
      exact h1 i j
    · rw [h, Matrix.neg_apply, abs_neg]
      exact h1 i j

/-! ### The equation `ẍ + p x = 0` -/

/-- `x` is a solution of `ẍ + p x = 0` (Landau–Lifshitz (27.1), with
`p = ω(t)²`). -/
def IsHill (p x : TimeFunction) : Prop :=
  timeDerivative (timeDerivative x) = -(p * x)

/-- The Wronskian `x ẏ − ẋ y` of two functions of time. -/
def wronskian (x y : TimeFunction) : TimeFunction :=
  x * timeDerivative y - timeDerivative x * y

theorem wronskian_apply (x y : TimeFunction) (t : ℝ) :
    wronskian x y (fun _ => t) =
      x (fun _ => t) * timeDerivative y (fun _ => t) -
        timeDerivative x (fun _ => t) * y (fun _ => t) := rfl

/-- The Wronskian of two solutions has zero derivative. -/
theorem IsHill.timeDerivative_wronskian {p x y : TimeFunction} (hx : IsHill p x)
    (hy : IsHill p y) : timeDerivative (wronskian x y) = 0 := by
  unfold IsHill at hx hy
  rw [wronskian, map_sub, SmoothDerivation.map_mul, SmoothDerivation.map_mul, hx, hy]
  simp only [smul_eq_mul]
  ring

/-- The Wronskian of two solutions is constant. -/
theorem IsHill.wronskian_eq {p x y : TimeFunction} (hx : IsHill p x) (hy : IsHill p y) :
    wronskian x y = algebraMap ℝ TimeFunction (wronskian x y fun _ => 0) :=
  TimeFunction.eq_algebraMap_of_timeDerivative_eq_zero (hx.timeDerivative_wronskian hy)

/-- The translate `t ↦ f(t + T)` of a function of time. -/
def _root_.ProjectAInos.Mechanics.TimeFunction.shift (T : ℝ) (f : TimeFunction) : TimeFunction :=
  SmoothOperation.ofContDiff (fun x => f fun _ => x 0 + T)
    (f.contDiff_apply_const.comp ((contDiff_apply ℝ (fun _ => ℝ) 0).add contDiff_const))

theorem _root_.ProjectAInos.Mechanics.TimeFunction.shift_apply (T : ℝ) (f : TimeFunction)
    (t : ℝ) : TimeFunction.shift T f (fun _ => t) = f fun _ => t + T := rfl

theorem _root_.ProjectAInos.Mechanics.TimeFunction.timeDerivative_shift (T : ℝ)
    (f : TimeFunction) :
    timeDerivative (TimeFunction.shift T f) = TimeFunction.shift T (timeDerivative f) := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rw [TimeFunction.timeDerivative_apply]
  exact ((TimeFunction.hasDerivAt_apply_const f (t + T)).comp_add_const t T).deriv

/-- If the coefficient has period `T`, the translate of a solution by `T` is a
solution. -/
theorem IsHill.shift {p x : TimeFunction} {T : ℝ} (hp : TimeFunction.shift T p = p)
    (hx : IsHill p x) : IsHill p (TimeFunction.shift T x) := by
  unfold IsHill at hx ⊢
  rw [TimeFunction.timeDerivative_shift, TimeFunction.timeDerivative_shift, hx]
  refine TimeFunction.ext_apply_const fun t => ?_
  have hpt := congrArg (fun f : TimeFunction => f fun _ => t) hp
  simp only [TimeFunction.shift_apply] at hpt
  simp only [TimeFunction.shift_apply, TimeFunction.neg_apply, TimeFunction.mul_apply, hpt]

/-- The position and the velocity at time `t`. -/
def state (x : TimeFunction) (t : ℝ) : Fin 2 → ℝ :=
  ![x fun _ => t, timeDerivative x fun _ => t]

/-- A fundamental system of `ẍ + p x = 0`: the solutions with the initial data
`(1, 0)` and `(0, 1)`. -/
structure FundamentalSystem (p : TimeFunction) where
  /-- The solution with `x(0) = 1`, `ẋ(0) = 0`. -/
  x₁ : TimeFunction
  /-- The solution with `x(0) = 0`, `ẋ(0) = 1`. -/
  x₂ : TimeFunction
  isHill₁ : IsHill p x₁
  isHill₂ : IsHill p x₂
  x₁_zero : x₁ (fun _ => 0) = 1
  dx₁_zero : timeDerivative x₁ (fun _ => 0) = 0
  x₂_zero : x₂ (fun _ => 0) = 0
  dx₂_zero : timeDerivative x₂ (fun _ => 0) = 1

namespace FundamentalSystem

variable {p : TimeFunction} (Φ : FundamentalSystem p)

/-- The Wronskian of a fundamental system is one. -/
theorem wronskian_eq_one : wronskian Φ.x₁ Φ.x₂ = 1 := by
  rw [Φ.isHill₁.wronskian_eq Φ.isHill₂, wronskian_apply, Φ.x₁_zero, Φ.dx₁_zero, Φ.x₂_zero,
    Φ.dx₂_zero, mul_one, zero_mul, sub_zero, map_one]

/-- Every solution is the combination of the fundamental system with its own
initial data. In particular a solution is determined by its position and
velocity at time zero. -/
theorem eq_combination {x : TimeFunction} (hx : IsHill p x) :
    x = algebraMap ℝ TimeFunction (x fun _ => 0) * Φ.x₁ +
      algebraMap ℝ TimeFunction (timeDerivative x fun _ => 0) * Φ.x₂ := by
  have h1 := hx.wronskian_eq Φ.isHill₂
  have h2 := Φ.isHill₁.wronskian_eq hx
  rw [wronskian_apply, Φ.x₂_zero, Φ.dx₂_zero, mul_one, mul_zero, sub_zero] at h1
  rw [wronskian_apply, Φ.x₁_zero, Φ.dx₁_zero, one_mul, zero_mul, sub_zero] at h2
  rw [← h1, ← h2]
  have hW := Φ.wronskian_eq_one
  unfold wronskian at hW ⊢
  linear_combination (-x) * hW

/-- The matrix of the fundamental system at time `t`. -/
def matrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Φ.x₁ fun _ => t, Φ.x₂ fun _ => t;
    timeDerivative Φ.x₁ fun _ => t, timeDerivative Φ.x₂ fun _ => t]

theorem matrix_zero : Φ.matrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Φ.x₁_zero, Φ.dx₁_zero, Φ.x₂_zero, Φ.dx₂_zero]

/-- Liouville's theorem for the equation: the matrix of the fundamental
system has determinant one at every time. -/
theorem det_matrix (t : ℝ) : (Φ.matrix t).det = 1 := by
  have h : Φ.x₁ (fun _ => t) * timeDerivative Φ.x₂ (fun _ => t) -
      timeDerivative Φ.x₁ (fun _ => t) * Φ.x₂ (fun _ => t) = 1 :=
    congrArg (fun f : TimeFunction => f fun _ => t) Φ.wronskian_eq_one
  rw [Matrix.det_fin_two]
  simp only [matrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linarith

/-- The state of a solution at time `t` is the matrix of the fundamental
system applied to its initial state. -/
theorem state_eq {x : TimeFunction} (hx : IsHill p x) (t : ℝ) :
    state x t = Φ.matrix t *ᵥ state x 0 := by
  have h0 := congrArg (fun f : TimeFunction => f fun _ => t) (Φ.eq_combination hx)
  have h1 := congrArg (fun f : TimeFunction => timeDerivative f fun _ => t)
    (Φ.eq_combination hx)
  simp only [map_add, SmoothDerivation.map_algebraMap_mul, smul_eq_mul, TimeFunction.add_apply,
    TimeFunction.mul_apply, TimeFunction.algebraMap_apply] at h0 h1
  ext i
  fin_cases i
  · simp only [state, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linarith
  · simp only [state, matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    linarith

/-- For a coefficient of period `T`, the state of a solution after one more
period. -/
theorem state_add_period {T : ℝ} (hp : TimeFunction.shift T p = p) {x : TimeFunction}
    (hx : IsHill p x) (s : ℝ) : state x (s + T) = Φ.matrix s *ᵥ state x T := by
  have h := Φ.state_eq (hx.shift hp) s
  have e1 : state (TimeFunction.shift T x) s = state x (s + T) := by
    simp only [state, TimeFunction.timeDerivative_shift, TimeFunction.shift_apply]
  have e2 : state (TimeFunction.shift T x) 0 = state x T := by
    simp only [state, TimeFunction.timeDerivative_shift, TimeFunction.shift_apply, zero_add]
  rw [e1, e2] at h
  exact h

/-- The monodromy relation: `Φ(s + T) = Φ(s) Φ(T)`. -/
theorem matrix_add_period {T : ℝ} (hp : TimeFunction.shift T p = p) (s : ℝ) :
    Φ.matrix (s + T) = Φ.matrix s * Φ.matrix T := by
  have h1 := Φ.state_add_period hp Φ.isHill₁ s
  have h2 := Φ.state_add_period hp Φ.isHill₂ s
  ext i j
  fin_cases j
  · have h := congrFun h1 i
    fin_cases i <;>
      simpa [state, matrix, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
        using h
  · have h := congrFun h2 i
    fin_cases i <;>
      simpa [state, matrix, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two]
        using h

/-- `Φ(s + nT) = Φ(s) Mⁿ` with the monodromy matrix `M = Φ(T)`. -/
theorem matrix_add_nat_mul_period {T : ℝ} (hp : TimeFunction.shift T p = p) (n : ℕ) (s : ℝ) :
    Φ.matrix (s + n * T) = Φ.matrix s * Φ.matrix T ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : s + ((n + 1 : ℕ) : ℝ) * T = s + n * T + T := by
      push_cast
      ring
    rw [e, Φ.matrix_add_period hp, ih, pow_succ, Matrix.mul_assoc]

/-- If the powers of the monodromy matrix are bounded, every solution is
bounded for `t ≥ 0`. -/
theorem exists_abs_apply_le {T : ℝ} (hp : TimeFunction.shift T p = p) (hT : 0 < T)
    (hC : ∃ C : ℝ, ∀ (k : ℕ) (i j : Fin 2), |(Φ.matrix T ^ k) i j| ≤ C) {x : TimeFunction}
    (hx : IsHill p x) : ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  obtain ⟨C, hC⟩ := hC
  obtain ⟨A₁, hA₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Φ.x₁.continuous_apply_const.continuousOn (s := Set.Icc 0 T))
  obtain ⟨A₂, hA₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Φ.x₂.continuous_apply_const.continuousOn (s := Set.Icc 0 T))
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hT.le⟩
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0 h0mem)
  have hA₂0 : 0 ≤ A₂ := (norm_nonneg _).trans (hA₂ 0 h0mem)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 0 0)
  refine ⟨(A₁ * C + A₂ * C) * |x fun _ => 0| +
    (A₁ * C + A₂ * C) * |timeDerivative x fun _ => 0|, fun t ht => ?_⟩
  have hfl : (⌊t / T⌋₊ : ℝ) ≤ t / T := Nat.floor_le (div_nonneg ht hT.le)
  have hfl' : t / T < ⌊t / T⌋₊ + 1 := Nat.lt_floor_add_one (t / T)
  have hs0 : 0 ≤ t - ⌊t / T⌋₊ * T := by
    have := (le_div_iff₀ hT).mp hfl
    linarith
  have hsT : t - ⌊t / T⌋₊ * T ≤ T := by
    have := (div_lt_iff₀ hT).mp hfl'
    linarith
  have hsmem : t - ⌊t / T⌋₊ * T ∈ Set.Icc 0 T := ⟨hs0, hsT⟩
  have ht_eq : t = t - ⌊t / T⌋₊ * T + ⌊t / T⌋₊ * T := by ring
  have hstate := congrFun (Φ.state_eq hx t) 0
  rw [ht_eq, Φ.matrix_add_nat_mul_period hp] at hstate
  simp only [state, matrix, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hstate
  rw [← ht_eq] at hstate
  have b1 : |Φ.x₁ fun _ => t - ⌊t / T⌋₊ * T| ≤ A₁ := hA₁ _ hsmem
  have b2 : |Φ.x₂ fun _ => t - ⌊t / T⌋₊ * T| ≤ A₂ := hA₂ _ hsmem
  have c00 := hC ⌊t / T⌋₊ 0 0
  have c01 := hC ⌊t / T⌋₊ 0 1
  have c10 := hC ⌊t / T⌋₊ 1 0
  have c11 := hC ⌊t / T⌋₊ 1 1
  have e0 : |(Φ.x₁ fun _ => t - ⌊t / T⌋₊ * T) * (Φ.matrix T ^ ⌊t / T⌋₊) 0 0 +
      (Φ.x₂ fun _ => t - ⌊t / T⌋₊ * T) * (Φ.matrix T ^ ⌊t / T⌋₊) 1 0| ≤ A₁ * C + A₂ * C := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul b1 c00 (abs_nonneg _) hA₁0)
      (mul_le_mul b2 c10 (abs_nonneg _) hA₂0)
  have e1 : |(Φ.x₁ fun _ => t - ⌊t / T⌋₊ * T) * (Φ.matrix T ^ ⌊t / T⌋₊) 0 1 +
      (Φ.x₂ fun _ => t - ⌊t / T⌋₊ * T) * (Φ.matrix T ^ ⌊t / T⌋₊) 1 1| ≤ A₁ * C + A₂ * C := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul b1 c01 (abs_nonneg _) hA₁0)
      (mul_le_mul b2 c11 (abs_nonneg _) hA₂0)
  rw [hstate]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right e0 (abs_nonneg _))
    (mul_le_mul_of_nonneg_right e1 (abs_nonneg _))

/-- Stability (Landau–Lifshitz §27): if the trace of the monodromy matrix has
absolute value less than two, every solution is bounded for `t ≥ 0`. -/
theorem exists_abs_apply_le_of_abs_trace_lt {T : ℝ} (hp : TimeFunction.shift T p = p)
    (hT : 0 < T) (htr : |(Φ.matrix T).trace| < 2) {x : TimeFunction} (hx : IsHill p x) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B :=
  Φ.exists_abs_apply_le hp hT (exists_abs_pow_apply_le (Φ.det_matrix T) htr) hx

/-- If the monodromy matrix is `1` or `−1`, every solution is bounded for
`t ≥ 0`. -/
theorem exists_abs_apply_le_of_eq {T : ℝ} (hp : TimeFunction.shift T p = p) (hT : 0 < T)
    (hM : Φ.matrix T = 1 ∨ Φ.matrix T = -1) {x : TimeFunction} (hx : IsHill p x) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B :=
  Φ.exists_abs_apply_le hp hT (exists_abs_pow_apply_le_of_eq hM) hx

end FundamentalSystem

/-- The fundamental system of the oscillator `ẍ + ω² x = 0`: `cos ωt` and
`sin ωt / ω`. Fundamental systems exist. -/
def FundamentalSystem.harmonic {ω : ℝ} (hω : ω ≠ 0) :
    FundamentalSystem (algebraMap ℝ TimeFunction (ω ^ 2)) where
  x₁ := TimeFunction.cosMul ω
  x₂ := algebraMap ℝ TimeFunction ω⁻¹ * TimeFunction.sinMul ω
  isHill₁ := isHarmonic_cosMul ω
  isHill₂ := (isHarmonic_sinMul ω).const_mul ω⁻¹
  x₁_zero := by simp
  dx₁_zero := by
    rw [TimeFunction.timeDerivative_cosMul]
    simp
  x₂_zero := by simp
  dx₂_zero := by
    rw [SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_sinMul]
    simp [hω]

/-- The trace of the matrix of the oscillator at time `T` is `2 cos ωT`. -/
theorem FundamentalSystem.trace_matrix_harmonic {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ((FundamentalSystem.harmonic hω).matrix T).trace = 2 * Real.cos (ω * T) := by
  rw [Matrix.trace_fin_two]
  simp only [matrix, harmonic, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_sinMul]
  simp only [smul_eq_mul, TimeFunction.mul_apply, TimeFunction.algebraMap_apply,
    TimeFunction.cosMul_apply]
  field_simp
  ring

end ProjectAInos.Mechanics.Parametric
