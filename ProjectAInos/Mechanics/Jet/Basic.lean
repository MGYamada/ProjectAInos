/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Derivation
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Ring

/-!
# Jet C-infinity rings and the total derivative

A jet C-infinity ring carries commuting vector fields `∂ₜ` and `∂ᵢ⁽ᵏ⁾` and
elements `qᵢ⁽ᵏ⁾` dual to them, and every element has finite order. The total
derivative `D F = ∂ₜF + Σₖ Σᵢ qᵢ⁽ᵏ⁺¹⁾ ∂ᵢ⁽ᵏ⁾F` is then a finite sum. It is a vector
field with `D qᵢ⁽ᵏ⁾ = qᵢ⁽ᵏ⁺¹⁾`, it raises the order by at most one, and
`[∂ₜ, D] = 0`, `[∂ᵢ⁽⁰⁾, D] = 0`, `[∂ᵢ⁽ᵏ⁺¹⁾, D] = ∂ᵢ⁽ᵏ⁾`.

Everything here is algebra over an abstract C-infinity ring. Coordinates are
indexed by an arbitrary finite type, so that several particles in space are
covered without re-indexing.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing SmoothOperation

/-- A jet C-infinity ring over coordinates indexed by `ι`. The element `q i k`
is the `k`-th time derivative of the `i`-th coordinate, and `d i k` is the
partial derivative with respect to it. -/
structure JetRing (ι : Type*) (J : Type*) [CommRing J] [Algebra ℝ J] [SmoothRing J] where
  /-- The partial derivative with respect to time. -/
  dt : SmoothDerivation J J
  /-- The partial derivative with respect to `q i k`. -/
  d : ι → ℕ → SmoothDerivation J J
  /-- The `k`-th time derivative of the `i`-th coordinate. -/
  q : ι → ℕ → J
  /-- Each coordinate has unit derivative along itself. -/
  d_q_self : ∀ i k, d i k (q i k) = 1
  /-- Each coordinate is constant along the other coordinate directions. -/
  d_q_ne : ∀ i k j l, (i, k) ≠ (j, l) → d j l (q i k) = 0
  /-- The coordinates do not depend explicitly on time. -/
  dt_q : ∀ i k, dt (q i k) = 0
  /-- The time derivative commutes with the coordinate derivatives. -/
  dt_comm : ∀ i k (F : J), dt (d i k F) = d i k (dt F)
  /-- The coordinate derivatives commute. -/
  d_comm : ∀ i k j l (F : J), d i k (d j l F) = d j l (d i k F)
  /-- Every element involves derivatives of the coordinates up to a finite order only. -/
  finite_order : ∀ F : J, ∃ N : ℕ, ∀ i k, N < k → d i k F = 0

namespace JetRing

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] (R : JetRing ι J)

/-- `F` involves no derivative of a coordinate of order above `N`. -/
def OrderLE (F : J) (N : ℕ) : Prop := ∀ i k, N < k → R.d i k F = 0

variable {R}

theorem OrderLE.mono {F : J} {N M : ℕ} (h : R.OrderLE F N) (hNM : N ≤ M) : R.OrderLE F M :=
  fun i k hk => h i k (lt_of_le_of_lt hNM hk)

theorem OrderLE.d {F : J} {N : ℕ} (h : R.OrderLE F N) (j : ι) (l : ℕ) :
    R.OrderLE (R.d j l F) N := fun i k hk => by
  rw [R.d_comm, h i k hk, map_zero]

theorem OrderLE.dt {F : J} {N : ℕ} (h : R.OrderLE F N) : R.OrderLE (R.dt F) N :=
  fun i k hk => by rw [← R.dt_comm, h i k hk, map_zero]

theorem OrderLE.add {F G : J} {N : ℕ} (hF : R.OrderLE F N) (hG : R.OrderLE G N) :
    R.OrderLE (F + G) N := fun i k hk => by
  rw [map_add, hF i k hk, hG i k hk, add_zero]

theorem OrderLE.neg {F : J} {N : ℕ} (h : R.OrderLE F N) : R.OrderLE (-F) N :=
  fun i k hk => by rw [map_neg, h i k hk, neg_zero]

theorem OrderLE.sub {F G : J} {N : ℕ} (hF : R.OrderLE F N) (hG : R.OrderLE G N) :
    R.OrderLE (F - G) N := fun i k hk => by
  rw [map_sub, hF i k hk, hG i k hk, sub_zero]

theorem OrderLE.mul {F G : J} {N : ℕ} (hF : R.OrderLE F N) (hG : R.OrderLE G N) :
    R.OrderLE (F * G) N := fun i k hk => by
  rw [SmoothDerivation.map_mul, hF i k hk, hG i k hk, smul_zero, smul_zero, add_zero]

theorem OrderLE.sum {κ : Type*} {s : Finset κ} {F : κ → J} {N : ℕ}
    (h : ∀ c ∈ s, R.OrderLE (F c) N) : R.OrderLE (∑ c ∈ s, F c) N := fun i k hk => by
  rw [map_sum]
  exact Finset.sum_eq_zero fun c hc => h c hc i k hk

theorem OrderLE.op {n : ℕ} {a : Fin n → J} {N : ℕ} (h : ∀ j, R.OrderLE (a j) N)
    (f : SmoothOperation n) : R.OrderLE (op f a) N := fun i k hk => by
  rw [(R.d i k).chain]
  exact Finset.sum_eq_zero fun j _ => by rw [h j i k hk, smul_zero]

theorem orderLE_algebraMap (r : ℝ) (N : ℕ) : R.OrderLE (algebraMap ℝ J r) N :=
  fun i k _ => (R.d i k).map_algebraMap r

theorem orderLE_q (i : ι) (k : ℕ) : R.OrderLE (R.q i k) k := fun j l hl =>
  R.d_q_ne i k j l fun h => by
    have hkl : k = l := (Prod.mk.inj h).2
    omega

variable (R)

theorem exists_orderLE (F : J) : ∃ N, R.OrderLE F N := R.finite_order F

/-- Finitely many elements have a common order bound. -/
theorem exists_orderLE_fin {n : ℕ} (a : Fin n → J) : ∃ N, ∀ j, R.OrderLE (a j) N := by
  choose N hN using fun j => R.exists_orderLE (a j)
  exact ⟨Finset.univ.sup N, fun j => (hN j).mono (Finset.le_sup (Finset.mem_univ j))⟩

variable [Fintype ι]

/-- The function underlying the total derivative. The sum over the order `k` has
finite support because every element has finite order. -/
def totalDerivFun (F : J) : J :=
  R.dt F + ∑ᶠ k : ℕ, ∑ i, R.q i (k + 1) * R.d i k F

variable {R} in
theorem totalDerivFun_eq_sum {F : J} {N : ℕ} (h : R.OrderLE F N) :
    R.totalDerivFun F =
      R.dt F + ∑ k ∈ Finset.range (N + 1), ∑ i, R.q i (k + 1) * R.d i k F := by
  unfold totalDerivFun
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  refine hk (Finset.sum_eq_zero fun i _ => ?_)
  rw [h i k (by omega), mul_zero]

/-- The chain rule for the total derivative. -/
theorem totalDerivFun_op {n : ℕ} (f : SmoothOperation n) (a : Fin n → J) :
    R.totalDerivFun (op f a) = ∑ j, op (partialDeriv j f) a * R.totalDerivFun (a j) := by
  obtain ⟨N, hN⟩ := R.exists_orderLE_fin a
  have key : ∑ k ∈ Finset.range (N + 1), ∑ i,
        R.q i (k + 1) * ∑ j, op (partialDeriv j f) a * R.d i k (a j) =
      ∑ j, op (partialDeriv j f) a *
        ∑ k ∈ Finset.range (N + 1), ∑ i, R.q i (k + 1) * R.d i k (a j) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range (N + 1))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [totalDerivFun_eq_sum (OrderLE.op hN f)]
  simp only [fun j => totalDerivFun_eq_sum (hN j), SmoothDerivation.chain, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  rw [key]

/-- The total derivative `D F = ∂ₜF + Σₖ Σᵢ qᵢ⁽ᵏ⁺¹⁾ ∂ᵢ⁽ᵏ⁾F`, a vector field on the jet ring. -/
def totalDeriv : SmoothDerivation J J where
  toFun := R.totalDerivFun
  chain' f a := by simpa only [smul_eq_mul] using R.totalDerivFun_op f a

variable {R}

theorem totalDeriv_eq_sum {F : J} {N : ℕ} (h : R.OrderLE F N) :
    R.totalDeriv F =
      R.dt F + ∑ k ∈ Finset.range (N + 1), ∑ i, R.q i (k + 1) * R.d i k F :=
  totalDerivFun_eq_sum h

/-- A derivation commuting with all the coordinate derivatives commutes with
the total derivative up to its values on the coordinates. -/
theorem apply_totalDeriv (δ : SmoothDerivation J J) (hδt : ∀ F, δ (R.dt F) = R.dt (δ F))
    (hδd : ∀ i k F, δ (R.d i k F) = R.d i k (δ F)) {F : J} {N : ℕ} (h : R.OrderLE F N) :
    δ (R.totalDeriv F) = R.totalDeriv (δ F) +
      ∑ k ∈ Finset.range (N + 1), ∑ i, δ (R.q i (k + 1)) * R.d i k F := by
  have hδF : R.OrderLE (δ F) N := fun i k hk => by rw [← hδd, h i k hk, map_zero]
  rw [totalDeriv_eq_sum h, totalDeriv_eq_sum hδF, map_add, map_sum, hδt, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [δ.map_mul, smul_eq_mul, smul_eq_mul, hδd]
  ring

/-- `[∂ₜ, D] = 0`. -/
theorem dt_totalDeriv (F : J) : R.dt (R.totalDeriv F) = R.totalDeriv (R.dt F) := by
  obtain ⟨N, hN⟩ := R.exists_orderLE F
  rw [apply_totalDeriv R.dt (fun _ => rfl) (fun i k G => R.dt_comm i k G) hN]
  simp [R.dt_q]

/-- `[∂ᵢ⁽⁰⁾, D] = 0`. -/
theorem d_zero_totalDeriv (j : ι) (F : J) :
    R.d j 0 (R.totalDeriv F) = R.totalDeriv (R.d j 0 F) := by
  obtain ⟨N, hN⟩ := R.exists_orderLE F
  rw [apply_totalDeriv (R.d j 0) (fun G => (R.dt_comm j 0 G).symm)
    (fun i k G => R.d_comm j 0 i k G) hN]
  have hzero (i : ι) (k : ℕ) : R.d j 0 (R.q i (k + 1)) = 0 :=
    R.d_q_ne i (k + 1) j 0 fun h => by
      have : k + 1 = 0 := (Prod.mk.inj h).2
      omega
  simp [hzero]

/-- `[∂ᵢ⁽ᵏ⁺¹⁾, D] = ∂ᵢ⁽ᵏ⁾`. -/
theorem d_succ_totalDeriv (j : ι) (m : ℕ) (F : J) :
    R.d j (m + 1) (R.totalDeriv F) = R.totalDeriv (R.d j (m + 1) F) + R.d j m F := by
  obtain ⟨N, hN⟩ := R.exists_orderLE F
  have hN' : R.OrderLE F (max N m) := hN.mono (le_max_left _ _)
  rw [apply_totalDeriv (R.d j (m + 1)) (fun G => (R.dt_comm j (m + 1) G).symm)
    (fun i k G => R.d_comm j (m + 1) i k G) hN']
  congr 1
  rw [Finset.sum_eq_single m]
  · rw [Finset.sum_eq_single j]
    · rw [R.d_q_self, one_mul]
    · intro i _ hij
      rw [R.d_q_ne i (m + 1) j (m + 1) fun h => hij (Prod.mk.inj h).1, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro k _ hkm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [R.d_q_ne i (k + 1) j (m + 1) fun h => hkm (by
      have : k + 1 = m + 1 := (Prod.mk.inj h).2
      omega), zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The total derivative of a coordinate is the next coordinate. -/
@[simp] theorem totalDeriv_q (i : ι) (k : ℕ) : R.totalDeriv (R.q i k) = R.q i (k + 1) := by
  rw [totalDeriv_eq_sum (orderLE_q i k), R.dt_q, zero_add, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single i]
    · rw [R.d_q_self, mul_one]
    · intro j _ hji
      rw [R.d_q_ne i k j k fun h => hji (Prod.mk.inj h).1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · intro l _ hlk
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [R.d_q_ne i k j l fun h => hlk (Prod.mk.inj h).2.symm, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The total derivative raises the order by at most one. -/
theorem OrderLE.totalDeriv {F : J} {N : ℕ} (h : R.OrderLE F N) :
    R.OrderLE (R.totalDeriv F) (N + 1) := fun i k hk => by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [d_succ_totalDeriv, h i (m + 1) (by omega), map_zero, h i m (by omega), add_zero]

/-- The total derivative annihilates real constants. -/
theorem totalDeriv_algebraMap (r : ℝ) : R.totalDeriv (algebraMap ℝ J r) = 0 :=
  R.totalDeriv.map_algebraMap r

end JetRing

end ProjectAInos.Mechanics
