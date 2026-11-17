/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.Basic.Real.Basic

/-!
# The filtration of formal power series by the order

`orderGE σ n` is the space of the formal power series over `ℝ` all of whose
terms have degree at least `n`. A sequence whose successive differences lie in
`orderGE σ n` has the limit `seqLimit`, and a series that lies in every
`orderGE σ n` is zero. A product adds the orders, and a partial derivative
lowers the order by one.
-/

@[expose] public section
noncomputable section

open MvPowerSeries

namespace ProjectAinos.SmoothAlgebra.FormalSeries

variable {σ : Type*}

/-- The formal power series all of whose terms have degree at least `n`. -/
def orderGE (σ : Type*) (n : ℕ) : Submodule ℝ (MvPowerSeries σ ℝ) where
  carrier := {f | ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0}
  add_mem' := by
    intro f g hf hg d hd
    simp [hf d hd, hg d hd]
  zero_mem' := by
    intro d _
    simp
  smul_mem' := by
    intro c f hf d hd
    simp [hf d hd]

theorem mem_orderGE {n : ℕ} {f : MvPowerSeries σ ℝ} :
    f ∈ orderGE σ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0 :=
  Iff.rfl

theorem mem_orderGE_iff_le_order {n : ℕ} {f : MvPowerSeries σ ℝ} :
    f ∈ orderGE σ n ↔ (n : ℕ∞) ≤ f.order := by
  constructor
  · intro h
    exact nat_le_order fun d hd => h d hd
  · intro h d hd
    exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)

theorem orderGE_anti {m n : ℕ} (h : m ≤ n) : orderGE σ n ≤ orderGE σ m :=
  fun _ hf d hd => hf d (lt_of_lt_of_le hd h)

theorem mem_orderGE_of_le {m n : ℕ} {f : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ n)
    (h : m ≤ n) : f ∈ orderGE σ m :=
  orderGE_anti h hf

theorem mem_orderGE_zero (f : MvPowerSeries σ ℝ) : f ∈ orderGE σ 0 :=
  fun _ hd => absurd hd (Nat.not_lt_zero _)

/-- The order of a product is at least the sum of the orders. -/
theorem mul_mem_orderGE {m n : ℕ} {f g : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ m)
    (hg : g ∈ orderGE σ n) : f * g ∈ orderGE σ (m + n) := by
  rw [mem_orderGE_iff_le_order] at hf hg ⊢
  refine le_trans ?_ le_order_mul
  rw [Nat.cast_add]
  exact add_le_add hf hg

theorem X_mem_orderGE (i : σ) : (X i : MvPowerSeries σ ℝ) ∈ orderGE σ 1 := by
  classical
  intro d hd
  have hd0 : d = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  have hne : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
    intro h
    have := congrArg (fun e : σ →₀ ℕ => e i) h
    simp at this
  rw [hd0, coeff_X]
  simp only [hne, ↓reduceIte]

theorem pow_mem_orderGE {m : ℕ} {f : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ m) (k : ℕ) :
    f ^ k ∈ orderGE σ (k * m) := by
  induction k with
  | zero => simpa using mem_orderGE_zero (σ := σ) 1
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_orderGE ih hf

/-- A partial derivative lowers the order by at most one. -/
theorem pderiv_mem_orderGE {n : ℕ} {f : MvPowerSeries σ ℝ} (hf : f ∈ orderGE σ n) (i : σ) :
    pderiv i f ∈ orderGE σ (n - 1) := by
  intro d hd
  rw [coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.degree_single]
  omega

/-- A series that has every order is zero. -/
theorem eq_zero_of_forall_mem_orderGE {f : MvPowerSeries σ ℝ} (h : ∀ n, f ∈ orderGE σ n) :
    f = 0 := by
  ext d
  simpa using h (d.degree + 1) d (Nat.lt_succ_self _)

theorem eq_of_forall_sub_mem_orderGE {f g : MvPowerSeries σ ℝ}
    (h : ∀ n, f - g ∈ orderGE σ n) : f = g :=
  sub_eq_zero.mp (eq_zero_of_forall_mem_orderGE h)

/-- The limit of a sequence of series: the coefficient at `d` is that of the
term of index `degree d + 1`. -/
def seqLimit (s : ℕ → MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun d => coeff d (s (d.degree + 1))

theorem coeff_seqLimit (s : ℕ → MvPowerSeries σ ℝ) (d : σ →₀ ℕ) :
    coeff d (seqLimit s) = coeff d (s (d.degree + 1)) :=
  rfl

theorem sub_mem_orderGE_of_le {s : ℕ → MvPowerSeries σ ℝ} {m : ℕ}
    (h : ∀ n, s (n + 1) - s n ∈ orderGE σ (n + m)) {n N : ℕ} (hn : n ≤ N) :
    s N - s n ∈ orderGE σ (n + m) := by
  induction N, hn using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have h1 : s (N + 1) - s n = (s (N + 1) - s N) + (s N - s n) := by ring
    rw [h1]
    exact add_mem (mem_orderGE_of_le (h N) (by omega)) ih

/-- The limit differs from the `n`-th term by a series of order at least `n`,
when the successive differences have increasing orders. -/
theorem seqLimit_sub_mem {s : ℕ → MvPowerSeries σ ℝ} {m : ℕ}
    (h : ∀ n, s (n + 1) - s n ∈ orderGE σ (n + m)) (n : ℕ) :
    seqLimit s - s n ∈ orderGE σ (n + m) := by
  intro d hd
  rw [map_sub, coeff_seqLimit, ← map_sub]
  rcases le_total (d.degree + 1) n with hle | hle
  · have h1 := sub_mem_orderGE_of_le h hle d (by omega)
    rw [← neg_sub, map_neg, h1, neg_zero]
  · exact sub_mem_orderGE_of_le h hle d hd

end ProjectAinos.SmoothAlgebra.FormalSeries
