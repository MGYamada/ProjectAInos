/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.FormalSeries.Filtration
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The exponential of a linear map that raises the order

A linear map `D` of formal power series that raises the order by at least one
has the exponential `lieExp D = ∑ Dᵏ/k!`, defined as the limit of the partial
sums. If `D` is a derivation of a bilinear map `B` that lowers the order by a
fixed amount, then `lieExp D` preserves `B` (`lieExp_bilinear`); the product
and the Poisson bracket are the two cases used. A linear map that differs from
the identity by a map raising the order is bijective
(`bijective_of_raises_sub_id`).
-/

@[expose] public section
noncomputable section

open MvPowerSeries Finset
open scoped Nat

namespace ProjectAinos.SmoothAlgebra.FormalSeries

variable {σ : Type*}

/-- A linear map of formal power series that raises the order by `j`. -/
def Raises (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (j : ℕ) : Prop :=
  ∀ (n : ℕ) (g : MvPowerSeries σ ℝ), g ∈ orderGE σ n → D g ∈ orderGE σ (n + j)

variable {D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ} {j m : ℕ}
  {f g : MvPowerSeries σ ℝ}

theorem Raises.mono {i : ℕ} (h : Raises D j) (hi : i ≤ j) : Raises D i :=
  fun n g hg => mem_orderGE_of_le (h n g hg) (by omega)

theorem Raises.pow (h : Raises D j) (k : ℕ) : Raises (D ^ k) (k * j) := by
  induction k with
  | zero =>
    intro n g hg
    simpa using hg
  | succ k ih =>
    intro n g hg
    rw [pow_succ', Module.End.mul_apply]
    exact mem_orderGE_of_le (h _ _ (ih n g hg)) (by rw [Nat.succ_mul]; omega)

theorem Raises.neg (h : Raises D j) : Raises (-D) j :=
  fun n g hg => by
    rw [LinearMap.neg_apply]
    exact neg_mem (h n g hg)

/-- The term of index `k` of the exponential series. -/
def expTerm (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (k : ℕ)
    (g : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  ((k ! : ℝ)⁻¹) • (D ^ k) g

/-- The partial sum of the exponential series with `n` terms. -/
def expPartial (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (n : ℕ)
    (g : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  ∑ k ∈ range n, expTerm D k g

theorem expTerm_zero (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) : expTerm D 0 g = g := by
  simp [expTerm]

theorem expPartial_succ (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) (n : ℕ)
    (g : MvPowerSeries σ ℝ) : expPartial D (n + 1) g = expPartial D n g + expTerm D n g :=
  sum_range_succ _ _

theorem expPartial_one (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) : expPartial D 1 g = g := by
  simp [expPartial, expTerm_zero]

theorem expPartial_two (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) : expPartial D 2 g = g + D g := by
  simp [expPartial, sum_range_succ, expTerm]

theorem expPartial_three (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) :
    expPartial D 3 g = g + D g + (2⁻¹ : ℝ) • D (D g) := by
  simp [expPartial, sum_range_succ, expTerm, pow_succ, Nat.factorial]

theorem expTerm_mem (hD : Raises D j) (hg : g ∈ orderGE σ m) (k : ℕ) :
    expTerm D k g ∈ orderGE σ (m + k * j) :=
  Submodule.smul_mem _ _ (hD.pow k m g hg)

theorem expPartial_sub_mem (hD : Raises D j) (hg : g ∈ orderGE σ m) {a b : ℕ} (h : a ≤ b) :
    expPartial D b g - expPartial D a g ∈ orderGE σ (m + a * j) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have h1 : expPartial D (b + 1) g - expPartial D a g =
        (expPartial D b g - expPartial D a g) + expTerm D b g := by
      rw [expPartial_succ]
      ring
    rw [h1]
    exact add_mem ih (mem_orderGE_of_le (expTerm_mem hD hg b)
      (Nat.add_le_add_left (Nat.mul_le_mul_right j hb) m))

/-- The exponential of a linear map that raises the order. -/
def lieExp (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ) :
    MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ where
  toFun g := seqLimit fun n => expPartial D n g
  map_add' f g := by
    ext d
    simp [coeff_seqLimit, expPartial, expTerm, sum_add_distrib]
  map_smul' c g := by
    ext d
    simp [coeff_seqLimit, expPartial, expTerm, mul_sum, mul_left_comm]

theorem lieExp_apply (D : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ)
    (g : MvPowerSeries σ ℝ) : lieExp D g = seqLimit fun n => expPartial D n g :=
  rfl

/-- The exponential differs from the partial sum with `a` terms by a series of
order `m + a j`. -/
theorem lieExp_sub_expPartial_mem (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m)
    (a : ℕ) : lieExp D g - expPartial D a g ∈ orderGE σ (m + a * j) := by
  have hstep : ∀ n, expPartial D (n + 1) g - expPartial D n g ∈ orderGE σ (n + m) := by
    intro n
    rw [expPartial_succ, add_sub_cancel_left]
    exact mem_orderGE_of_le (expTerm_mem hD hg n)
      (by nlinarith [Nat.mul_le_mul_left n hj])
  have h1 := seqLimit_sub_mem (s := fun n => expPartial D n g) hstep (a * j)
  have h2 := expPartial_sub_mem hD hg (Nat.le_mul_of_pos_right a hj)
  have h3 : lieExp D g - expPartial D a g =
      (lieExp D g - expPartial D (a * j) g) + (expPartial D (a * j) g - expPartial D a g) := by
    ring
  rw [h3]
  exact add_mem (mem_orderGE_of_le h1 (by omega)) h2

theorem lieExp_sub_self_mem (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g - g ∈ orderGE σ (m + j) := by
  simpa [expPartial_one] using lieExp_sub_expPartial_mem hD hj hg 1

theorem lieExp_mem (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g ∈ orderGE σ m := by
  have h1 := mem_orderGE_of_le (lieExp_sub_self_mem hD hj hg) (Nat.le_add_right m j)
  simpa using add_mem h1 hg

theorem lieExp_sub_add_mem (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g - (g + D g) ∈ orderGE σ (m + 2 * j) := by
  simpa [expPartial_two] using lieExp_sub_expPartial_mem hD hj hg 2

theorem lieExp_sub_three_mem (hD : Raises D j) (hj : 1 ≤ j) (hg : g ∈ orderGE σ m) :
    lieExp D g - (g + D g + (2⁻¹ : ℝ) • D (D g)) ∈ orderGE σ (m + 3 * j) := by
  simpa [expPartial_three] using lieExp_sub_expPartial_mem hD hj hg 3

theorem raises_lieExp_sub_id (hD : Raises D j) (hj : 1 ≤ j) :
    Raises (lieExp D - LinearMap.id) j :=
  fun _ _ hg => lieExp_sub_self_mem hD hj hg

/-- The exponential fixes what the map annihilates. -/
theorem lieExp_eq_self (hD : Raises D j) (hj : 1 ≤ j) (h : D g = 0) : lieExp D g = g := by
  have hpart : ∀ n, expPartial D (n + 1) g = g := by
    intro n
    rw [expPartial, sum_range_succ', expTerm_zero]
    have : ∀ k ∈ range n, expTerm D (k + 1) g = 0 := by
      intro k _
      rw [expTerm, pow_succ, Module.End.mul_apply, h, map_zero, smul_zero]
    rw [sum_eq_zero this, zero_add]
  refine eq_of_forall_sub_mem_orderGE fun n => ?_
  have h1 := lieExp_sub_expPartial_mem hD hj (mem_orderGE_zero g) (n + 1)
  rw [hpart] at h1
  exact mem_orderGE_of_le h1 (by nlinarith [Nat.mul_le_mul_left (n + 1) hj])

/-! ### A perturbation of the generator -/

section Perturbation

variable {D' : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ} {j' : ℕ}

theorem Raises.add (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j') :
    Raises (D + D') 1 :=
  fun n g hg => by
    rw [LinearMap.add_apply]
    exact add_mem (hD n g hg) (mem_orderGE_of_le (hD' n g hg) (by omega))

theorem pow_add_sub_pow_mem (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) (i : ℕ) :
    ((D + D') ^ (i + 1)) g - (D ^ (i + 1)) g ∈ orderGE σ (m + j' + i) := by
  induction i with
  | zero => simpa using hD' m g hg
  | succ i ih =>
    have e : ((D + D') ^ (i + 1 + 1)) g - (D ^ (i + 1 + 1)) g =
        (D + D') (((D + D') ^ (i + 1)) g - (D ^ (i + 1)) g) + D' ((D ^ (i + 1)) g) := by
      have e2 : (D + D') ((D ^ (i + 1)) g) = D ((D ^ (i + 1)) g) + D' ((D ^ (i + 1)) g) :=
        LinearMap.add_apply _ _ _
      rw [pow_succ' (D + D'), pow_succ' D, Module.End.mul_apply, Module.End.mul_apply, map_sub,
        e2]
      abel
    rw [e]
    refine add_mem (mem_orderGE_of_le ((hD.add hD' hj') _ _ ih) (by omega)) ?_
    exact mem_orderGE_of_le (hD' _ _ (hD.pow (i + 1) m g hg)) (by omega)

theorem expPartial_add_sub_mem (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) (n : ℕ) :
    expPartial (D + D') (n + 2) g - expPartial D (n + 2) g - D' g ∈ orderGE σ (m + j' + 1) := by
  induction n with
  | zero => simp [expPartial_two]
  | succ n ih =>
    have e1 : expPartial (D + D') (n + 1 + 2) g =
        expPartial (D + D') (n + 2) g + expTerm (D + D') (n + 2) g :=
      expPartial_succ _ (n + 2) g
    have e2 : expPartial D (n + 1 + 2) g = expPartial D (n + 2) g + expTerm D (n + 2) g :=
      expPartial_succ _ (n + 2) g
    have e : expPartial (D + D') (n + 1 + 2) g - expPartial D (n + 1 + 2) g - D' g =
        (expPartial (D + D') (n + 2) g - expPartial D (n + 2) g - D' g) +
          (((n + 2) ! : ℝ)⁻¹) • (((D + D') ^ (n + 2)) g - (D ^ (n + 2)) g) := by
      rw [e1, e2, expTerm, expTerm, smul_sub]
      abel
    rw [e]
    exact add_mem ih (Submodule.smul_mem _ _
      (mem_orderGE_of_le (pow_add_sub_pow_mem hD hD' hj' hg (n + 1)) (by omega)))

/-- Adding to the generator a map that raises the order by `j'` changes the
exponential by that map, up to the order `m + j' + 1`. -/
theorem lieExp_add_sub_mem (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) :
    lieExp (D + D') g - lieExp D g - D' g ∈ orderGE σ (m + j' + 1) := by
  have h1 := lieExp_sub_expPartial_mem (hD.add hD' hj') le_rfl hg (j' + 1 + 2)
  have h2 := lieExp_sub_expPartial_mem hD le_rfl hg (j' + 1 + 2)
  have h3 := expPartial_add_sub_mem hD hD' hj' hg (j' + 1)
  have e : lieExp (D + D') g - lieExp D g - D' g =
      (lieExp (D + D') g - expPartial (D + D') (j' + 1 + 2) g) -
        (lieExp D g - expPartial D (j' + 1 + 2) g) +
        (expPartial (D + D') (j' + 1 + 2) g - expPartial D (j' + 1 + 2) g - D' g) := by
    abel
  rw [e]
  exact add_mem (sub_mem (mem_orderGE_of_le h1 (by omega)) (mem_orderGE_of_le h2 (by omega))) h3

theorem lieExp_add_sub_mem' (hD : Raises D 1) (hD' : Raises D' j') (hj' : 1 ≤ j')
    (hg : g ∈ orderGE σ m) : lieExp (D + D') g - lieExp D g ∈ orderGE σ (m + j') := by
  have h1 := lieExp_add_sub_mem hD hD' hj' hg
  have e : lieExp (D + D') g - lieExp D g = (lieExp (D + D') g - lieExp D g - D' g) + D' g := by
    abel
  rw [e]
  exact add_mem (mem_orderGE_of_le h1 (by omega)) (hD' m g hg)

end Perturbation

/-! ### Bilinear maps -/

section Bilinear

variable {B : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ}

/-- The general Leibniz rule for a derivation of a bilinear map. -/
theorem pow_apply_bilinear (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g)) (n : ℕ)
    (f g : MvPowerSeries σ ℝ) :
    (D ^ n) (B f g) =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • B ((D ^ ij.1) f) ((D ^ ij.2) g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := MvPowerSeries σ ℝ)
      (fun i j => B ((D ^ i) f) ((D ^ j) g)) n]
    rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    simp only [map_nsmul, hder, smul_add, sum_add_distrib]
    rw [add_comm]
    congr 1
    · refine sum_congr rfl fun ij _ => ?_
      rw [pow_succ', Module.End.mul_apply]
    · refine sum_congr rfl fun ij hij => ?_
      rw [pow_succ', Module.End.mul_apply,
        n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

theorem expTerm_bilinear (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g)) (n : ℕ)
    (f g : MvPowerSeries σ ℝ) :
    expTerm D n (B f g) =
      ∑ ij ∈ antidiagonal n, B (expTerm D ij.1 f) (expTerm D ij.2 g) := by
  rw [expTerm, pow_apply_bilinear hder, smul_sum]
  refine sum_congr rfl fun ij hij => ?_
  obtain ⟨i, k⟩ := ij
  have hik : i + k = n := mem_antidiagonal.1 hij
  subst hik
  simp only [expTerm, map_smul, LinearMap.smul_apply, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  have h0 : (i + k).choose i * i ! * k ! = (i + k)! := by
    rw [Nat.choose_symm_add]
    exact Nat.add_choose_mul_factorial_mul_factorial i k
  have h1 : (((i + k).choose i : ℕ) : ℝ) * (i ! : ℝ) * (k ! : ℝ) = ((i + k)! : ℝ) := by
    exact_mod_cast h0
  have hi : (i ! : ℝ) ≠ 0 := by positivity
  have hk : (k ! : ℝ) ≠ 0 := by positivity
  have hc : (((i + k).choose i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right i k)).ne'
  rw [← h1]
  field_simp

/-- The partial sum of the exponential of a bilinear expression, as a
triangular sum. -/
theorem expPartial_bilinear (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g)) (N : ℕ)
    (f g : MvPowerSeries σ ℝ) :
    expPartial D N (B f g) = ∑ i ∈ range N, B (expTerm D i f) (expPartial D (N - i) g) := by
  induction N with
  | zero => simp [expPartial]
  | succ N ih =>
    rw [expPartial_succ, ih, expTerm_bilinear hder,
      Nat.sum_antidiagonal_eq_sum_range_succ (fun i k => B (expTerm D i f) (expTerm D k g)) N,
      sum_range_succ (fun i => B (expTerm D i f) (expPartial D (N + 1 - i) g)) N,
      sum_range_succ (fun i => B (expTerm D i f) (expTerm D (N - i) g)) N,
      ← add_assoc, ← sum_add_distrib]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      have hi' : i < N := mem_range.1 hi
      rw [show N + 1 - i = (N - i) + 1 by omega, expPartial_succ, map_add]
    · simp [expPartial_one, expTerm_zero]

/-- The exponential of a derivation of a bilinear map preserves the map. -/
theorem lieExp_bilinear {c : ℕ}
    (hB : ∀ (m n : ℕ) (f g : MvPowerSeries σ ℝ), f ∈ orderGE σ m → g ∈ orderGE σ n →
      B f g ∈ orderGE σ (m + n - c))
    (hD : Raises D j) (hj : 1 ≤ j) (hder : ∀ f g, D (B f g) = B (D f) g + B f (D g))
    (f g : MvPowerSeries σ ℝ) :
    lieExp D (B f g) = B (lieExp D f) (lieExp D g) := by
  refine eq_of_forall_sub_mem_orderGE fun n => ?_
  have hjN : ∀ a : ℕ, a ≤ a * j := fun a => Nat.le_mul_of_pos_right a hj
  have h0f := mem_orderGE_zero f
  have h0g := mem_orderGE_zero g
  have h1 : lieExp D (B f g) - expPartial D (n + c) (B f g) ∈ orderGE σ n :=
    mem_orderGE_of_le (lieExp_sub_expPartial_mem hD hj (mem_orderGE_zero _) (n + c))
      (by have := hjN (n + c); omega)
  have h2 : expPartial D (n + c) (B f g) - B (expPartial D (n + c) f) (expPartial D (n + c) g)
      ∈ orderGE σ n := by
    have hsum : B (expPartial D (n + c) f) (expPartial D (n + c) g) =
        ∑ i ∈ range (n + c), B (expTerm D i f) (expPartial D (n + c) g) := by
      rw [expPartial, map_sum, LinearMap.sum_apply]
    rw [expPartial_bilinear hder, hsum, ← sum_sub_distrib]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi' : i < n + c := mem_range.1 hi
    rw [← map_sub, ← neg_sub, map_neg]
    refine neg_mem ?_
    have ha : expTerm D i f ∈ orderGE σ i :=
      mem_orderGE_of_le (expTerm_mem hD h0f i) (by have := hjN i; omega)
    have hb : expPartial D (n + c) g - expPartial D (n + c - i) g ∈ orderGE σ (n + c - i) :=
      mem_orderGE_of_le (expPartial_sub_mem hD h0g (Nat.sub_le _ _))
        (by have := hjN (n + c - i); omega)
    exact mem_orderGE_of_le (hB _ _ _ _ ha hb) (by omega)
  have h3 : B (expPartial D (n + c) f) (expPartial D (n + c) g) -
      B (lieExp D f) (lieExp D g) ∈ orderGE σ n := by
    have e : B (expPartial D (n + c) f) (expPartial D (n + c) g) - B (lieExp D f) (lieExp D g) =
        -(B (lieExp D f - expPartial D (n + c) f) (expPartial D (n + c) g) +
          B (lieExp D f) (lieExp D g - expPartial D (n + c) g)) := by
      simp only [map_sub, LinearMap.sub_apply]
      abel
    rw [e]
    have hf' : lieExp D f - expPartial D (n + c) f ∈ orderGE σ (n + c) :=
      mem_orderGE_of_le (lieExp_sub_expPartial_mem hD hj h0f (n + c))
        (by have := hjN (n + c); omega)
    have hg' : lieExp D g - expPartial D (n + c) g ∈ orderGE σ (n + c) :=
      mem_orderGE_of_le (lieExp_sub_expPartial_mem hD hj h0g (n + c))
        (by have := hjN (n + c); omega)
    refine neg_mem (add_mem ?_ ?_)
    · exact mem_orderGE_of_le (hB _ _ _ _ hf' (mem_orderGE_zero _)) (by omega)
    · exact mem_orderGE_of_le (hB _ _ _ _ (mem_orderGE_zero _) hg') (by omega)
  have e : lieExp D (B f g) - B (lieExp D f) (lieExp D g) =
      (lieExp D (B f g) - expPartial D (n + c) (B f g)) +
      (expPartial D (n + c) (B f g) - B (expPartial D (n + c) f) (expPartial D (n + c) g)) +
      (B (expPartial D (n + c) f) (expPartial D (n + c) g) - B (lieExp D f) (lieExp D g)) := by
    abel
  rw [e]
  exact add_mem (add_mem h1 h2) h3

end Bilinear

/-! ### Bijectivity -/

/-- A linear map that differs from the identity by a map raising the order is
bijective. -/
theorem bijective_of_raises_sub_id {T : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ}
    (h : Raises (T - LinearMap.id) 1) : Function.Bijective T := by
  obtain ⟨M, hMdef⟩ : ∃ M : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ,
      M = -(T - LinearMap.id) := ⟨_, rfl⟩
  have hM : Raises M 1 := by
    rw [hMdef]
    exact h.neg
  have hTM : ∀ g, T g = g - M g := by
    intro g
    rw [hMdef]
    simp
  constructor
  · refine (injective_iff_map_eq_zero T).mpr fun g hg => ?_
    have hg' : g = M g := by
      have := hTM g
      rw [hg] at this
      exact sub_eq_zero.mp this.symm
    refine eq_zero_of_forall_mem_orderGE fun n => ?_
    induction n with
    | zero => exact mem_orderGE_zero g
    | succ n ih =>
      rw [hg']
      exact hM n g ih
  · intro y
    obtain ⟨s, hs⟩ : ∃ s : ℕ → MvPowerSeries σ ℝ, s = fun n => ∑ k ∈ range n, (M ^ k) y :=
      ⟨_, rfl⟩
    have hstep : ∀ n, s (n + 1) - s n ∈ orderGE σ (n + 0) := by
      intro n
      rw [hs]
      simp only [sum_range_succ, add_sub_cancel_left, add_zero]
      simpa using hM.pow n 0 y (mem_orderGE_zero y)
    have htel : ∀ n, T (s n) = y - (M ^ n) y := by
      intro n
      rw [hTM]
      induction n with
      | zero => simp [hs]
      | succ n ih =>
        have e1 : s (n + 1) = s n + (M ^ n) y := by
          rw [hs]
          exact sum_range_succ _ _
        rw [e1, map_add, pow_succ', Module.End.mul_apply]
        have : s n + (M ^ n) y - (M (s n) + M ((M ^ n) y)) =
            (s n - M (s n)) + (M ^ n) y - M ((M ^ n) y) := by abel
        rw [this, ih]
        abel
    refine ⟨seqLimit s, eq_of_forall_sub_mem_orderGE fun n => ?_⟩
    have h1 : seqLimit s - s n ∈ orderGE σ n := by simpa using seqLimit_sub_mem hstep n
    have h2 : T (seqLimit s - s n) ∈ orderGE σ n := by
      rw [hTM]
      exact sub_mem h1 (mem_orderGE_of_le (hM n _ h1) (Nat.le_add_right n 1))
    have h3 : (M ^ n) y ∈ orderGE σ n := by simpa using hM.pow n 0 y (mem_orderGE_zero y)
    have e : T (seqLimit s) - y = T (seqLimit s - s n) - (M ^ n) y := by
      rw [map_sub, htel]
      abel
    rw [e]
    exact sub_mem h2 h3

theorem bijective_lieExp (hD : Raises D j) (hj : 1 ≤ j) : Function.Bijective (lieExp D) :=
  bijective_of_raises_sub_id ((raises_lieExp_sub_id hD hj).mono hj)

end ProjectAinos.SmoothAlgebra.FormalSeries
