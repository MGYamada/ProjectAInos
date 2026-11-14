/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.FreeParticle
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Galilei algebra on the jet ring

Landau–Lifshitz §3. The infinitesimal transformations `δqₗ = Σₘ Aₗₘ qₘ + aₗ +
t uₗ` (a linear map, a translation and a boost) act on the standard jet ring
by their prolongations `galileiField A a u`, and the time translation acts by
`∂/∂t`. For antisymmetric `A` these are the generators of the Galilei group.

* `evolutionary_eq_prolongField`: these vector fields are the prolongations
  `pr ξ` of Noether's theorem; `boost_eq_galileiField` identifies the boost of
  `Jet/FreeParticle`.
* `commutator_galileiField`, `commutator_dt_galileiField`: the commutators.
* `euler_galileiField`: `Eₗ(X F) = X(Eₗ F) + Σᵢ Aᵢₗ Eᵢ(F)`.
* `galileiField_mem_eulerLagrangeIdeal`: a field `X` of this kind that
  changes the Lagrangian by a total derivative preserves the Euler–Lagrange
  ideal.
* `galileiField_naturalLagrangian`: the natural Lagrangian with an invariant
  potential changes by the total derivative of `Σ mᵢ uᵢ qᵢ`.
* `isInertial_naturalLagrangian`: the Euler–Lagrange ideal of a free system
  of equal masses is invariant under the Galilei algebra.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

namespace JetRing

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] {R : JetRing ι J}

theorem iterate_totalDeriv_sum_algebraMap_mul (c : ι → ℝ) (G : ι → J) (k : ℕ) :
    (R.totalDeriv^[k]) (∑ i, algebraMap ℝ J (c i) * G i) =
      ∑ i, algebraMap ℝ J (c i) * (R.totalDeriv^[k]) (G i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SmoothDerivation.map_algebraMap_mul, smul_eq_mul, Function.iterate_succ_apply']

/-- A vector field commuting with the total derivative commutes with its
iterates. -/
theorem apply_iterate_totalDeriv (X : SmoothDerivation J J)
    (hD : ∀ F, X (R.totalDeriv F) = R.totalDeriv (X F)) (k : ℕ) (F : J) :
    X ((R.totalDeriv^[k]) F) = (R.totalDeriv^[k]) (X F) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', hD, ih, Function.iterate_succ_apply']

/-- The Euler operators and a vector field `X` that commutes with the total
derivative and satisfies `[∂ₗ⁽ᵏ⁾, X] = Σᵢ cₗᵢ ∂ᵢ⁽ᵏ⁾` with constants `cₗᵢ`:
`Eₗ(X F) = X(Eₗ F) + Σᵢ cₗᵢ Eᵢ(F)`. -/
theorem euler_apply (X : SmoothDerivation J J) (c : ι → ι → ℝ)
    (hD : ∀ F, X (R.totalDeriv F) = R.totalDeriv (X F))
    (hd : ∀ l k F, R.d l k (X F) = X (R.d l k F) + ∑ i, algebraMap ℝ J (c l i) * R.d i k F)
    (l : ι) (F : J) :
    R.euler l (X F) = X (R.euler l F) + ∑ i, algebraMap ℝ J (c l i) * R.euler i F := by
  obtain ⟨N, hN⟩ := R.exists_orderLE F
  have hXF : R.OrderLE (X F) N := fun i k hk => by
    rw [hd, hN i k hk, map_zero, zero_add]
    exact Finset.sum_eq_zero fun j _ => by rw [hN j k hk, mul_zero]
  have hsign (k : ℕ) : (-1 : J) ^ k = algebraMap ℝ J ((-1) ^ k) := by
    rw [map_pow, map_neg, map_one]
  have hE (i : ι) : R.euler i F =
      ∑ k ∈ Finset.range (N + 1), (-1 : J) ^ k * (R.totalDeriv^[k]) (R.d i k F) :=
    euler_eq_sum hN i
  rw [euler_eq_sum hXF]
  simp only [hE, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (R.totalDeriv^[k]) (R.d l k (X F)) =
      X ((R.totalDeriv^[k]) (R.d l k F)) +
        ∑ i, algebraMap ℝ J (c l i) * (R.totalDeriv^[k]) (R.d i k F) := by
    rw [hd, iterate_map_add, apply_iterate_totalDeriv X hD,
      iterate_totalDeriv_sum_algebraMap_mul]
  rw [hk, hsign k, SmoothDerivation.map_algebraMap_mul, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A vector field as in `euler_apply` that changes the Lagrangian by a null
Lagrangian preserves the Euler–Lagrange ideal. -/
theorem apply_mem_eulerLagrangeIdeal (X : SmoothDerivation J J) (c : ι → ι → ℝ)
    (hD : ∀ F, X (R.totalDeriv F) = R.totalDeriv (X F))
    (hd : ∀ l k F, R.d l k (X F) = X (R.d l k F) + ∑ i, algebraMap ℝ J (c l i) * R.d i k F)
    {L : J} (hL : ∀ l, R.euler l (X L) = 0) {x : J} (hx : x ∈ R.eulerLagrangeIdeal L) :
    X x ∈ R.eulerLagrangeIdeal L := by
  refine Submodule.span_induction (p := fun x _ => X x ∈ R.eulerLagrangeIdeal L)
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, k, rfl⟩
    have h := euler_apply X c hD hd i L
    rw [hL i] at h
    have hX : X (R.euler i L) = ∑ j, algebraMap ℝ J (-c i j) * R.euler j L := by
      simp only [map_neg, neg_mul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left h.symm
    rw [apply_iterate_totalDeriv X hD, hX, iterate_totalDeriv_sum_algebraMap_mul]
    exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (iterate_totalDeriv_euler_mem L j k)
  · rw [map_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact add_mem hx hy
  · intro a x hx hXx
    rw [smul_eq_mul, SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ a hXx) (Ideal.mul_mem_right _ _ hx)

/-- The time translation `∂/∂t` preserves the Euler–Lagrange ideal of a
Lagrangian that it changes by a total derivative. -/
theorem dt_mem_eulerLagrangeIdeal {L F : J} (h : R.dt L = R.totalDeriv F) {x : J}
    (hx : x ∈ R.eulerLagrangeIdeal L) : R.dt x ∈ R.eulerLagrangeIdeal L :=
  apply_mem_eulerLagrangeIdeal R.dt (fun _ _ => 0) (fun G => dt_totalDeriv G)
    (fun l k G => by
      rw [← R.dt_comm]
      simp)
    (fun l => by rw [h, euler_totalDeriv]) hx

theorem prolong_eq_sum {F : J} {N : ℕ} (h : R.OrderLE F N) (ξ : ι → J) :
    R.prolong ξ F =
      ∑ k ∈ Finset.range (N + 1), ∑ i, (R.totalDeriv^[k]) (ξ i) * R.d i k F := by
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  refine hk (Finset.sum_eq_zero fun i _ => ?_)
  rw [h i k (by omega), mul_zero]

/-- The chain rule for the prolongation of a variation. -/
theorem prolong_op (ξ : ι → J) {n : ℕ} (f : SmoothOperation n) (a : Fin n → J) :
    R.prolong ξ (op f a) = ∑ j, op (SmoothOperation.partialDeriv j f) a * R.prolong ξ (a j) := by
  obtain ⟨N, hN⟩ := R.exists_orderLE_fin a
  rw [prolong_eq_sum (OrderLE.op hN f)]
  simp only [fun j => prolong_eq_sum (hN j) ξ, SmoothDerivation.chain, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range (N + 1))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

variable (R) in
/-- The prolongation `pr ξ = Σₖ Σᵢ (Dᵏ ξᵢ) ∂ᵢ⁽ᵏ⁾` of a variation, as a vector
field on the jet ring. -/
def prolongField (ξ : ι → J) : SmoothDerivation J J where
  toFun := R.prolong ξ
  chain' f a := by simpa only [smul_eq_mul] using prolong_op ξ f a

@[simp] theorem prolongField_apply (ξ : ι → J) (F : J) : R.prolongField ξ F = R.prolong ξ F :=
  rfl

theorem prolong_q (ξ : ι → J) (j : ι) (n : ℕ) :
    R.prolong ξ (R.q j n) = (R.totalDeriv^[n]) (ξ j) := by
  rw [prolong_eq_sum (orderLE_q j n), Finset.sum_eq_single n]
  · rw [Finset.sum_eq_single j]
    · rw [R.d_q_self, mul_one]
    · intro i _ hi
      rw [R.d_q_ne j n i n fun h => hi (Prod.mk.inj h).1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · intro k _ hk
    exact Finset.sum_eq_zero fun i _ => by
      rw [R.d_q_ne j n i k fun h => hk (Prod.mk.inj h).2.symm, mul_zero]
  · intro h
    exact absurd (Finset.self_mem_range_succ n) h

omit [SmoothRing J] in
/-- A quadratic expression with antisymmetric coefficients vanishes. -/
theorem sum_sum_antisymm_eq_zero {c : ι → ι → ℝ} (hc : ∀ i j, c i j + c j i = 0) (x : ι → J) :
    ∑ i, ∑ j, algebraMap ℝ J (c i j) * (x i * x j) = 0 := by
  have h : ∑ i, ∑ j, algebraMap ℝ J (c i j) * (x i * x j) +
      ∑ i, ∑ j, algebraMap ℝ J (c i j) * (x i * x j) = 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_comm (x j) (x i), ← add_mul, ← map_add, hc, map_zero, zero_mul]
  have h2 : (2 : ℝ) • ∑ i, ∑ j, algebraMap ℝ J (c i j) * (x i * x j) = 0 := by
    rw [two_smul, h]
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end JetRing

namespace StandardJet

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The evolutionary vector field with the characteristic `ξ`: the vector
field of the standard jet ring with `t ↦ 0` and `qᵢ⁽ᵏ⁾ ↦ Dᵏ ξᵢ`. -/
def evolutionary (ξ : ι → StandardJet ι) :
    SmoothDerivation (StandardJet ι) (StandardJet ι) :=
  FreeSmoothRing.derivation fun c =>
    match c with
    | none => 0
    | some (i, k) => ((jetRing ι).totalDeriv^[k]) (ξ i)

@[simp] theorem evolutionary_time (ξ : ι → StandardJet ι) : evolutionary ξ (time ι) = 0 :=
  FreeSmoothRing.derivation_generator _ none

@[simp] theorem evolutionary_q (ξ : ι → StandardJet ι) (i : ι) (k : ℕ) :
    evolutionary ξ ((jetRing ι).q i k) = ((jetRing ι).totalDeriv^[k]) (ξ i) :=
  FreeSmoothRing.derivation_generator _ (some (i, k))

/-- An evolutionary vector field commutes with the total derivative. -/
theorem evolutionary_totalDeriv (ξ : ι → StandardJet ι) (F : StandardJet ι) :
    evolutionary ξ ((jetRing ι).totalDeriv F) = (jetRing ι).totalDeriv (evolutionary ξ F) := by
  have h : ⁅evolutionary ξ, (jetRing ι).totalDeriv⁆ = 0 :=
    FreeSmoothRing.derivation_ext fun c => by
      rw [SmoothDerivation.commutator_apply, SmoothDerivation.zero_apply]
      rcases c with _ | ⟨i, k⟩
      · change evolutionary ξ ((jetRing ι).totalDeriv (time ι)) -
          (jetRing ι).totalDeriv (evolutionary ξ (time ι)) = 0
        rw [totalDeriv_time, SmoothDerivation.map_one, evolutionary_time, map_zero, sub_zero]
      · change evolutionary ξ ((jetRing ι).totalDeriv ((jetRing ι).q i k)) -
          (jetRing ι).totalDeriv (evolutionary ξ ((jetRing ι).q i k)) = 0
        rw [JetRing.totalDeriv_q, evolutionary_q, evolutionary_q,
          Function.iterate_succ_apply', sub_self]
  have hF := DFunLike.congr_fun h F
  rw [SmoothDerivation.commutator_apply, SmoothDerivation.zero_apply] at hF
  exact sub_eq_zero.mp hF

/-- An evolutionary vector field is the prolongation of its characteristic. -/
theorem evolutionary_eq_prolongField (ξ : ι → StandardJet ι) :
    evolutionary ξ = (jetRing ι).prolongField ξ :=
  FreeSmoothRing.derivation_ext fun c => by
    rcases c with _ | ⟨i, k⟩
    · change evolutionary ξ (time ι) = (jetRing ι).prolong ξ (time ι)
      rw [evolutionary_time, JetRing.prolong_eq_sum (N := 0) fun i k _ => d_time i k]
      exact (Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => by
        rw [d_time, mul_zero]).symm
    · change evolutionary ξ ((jetRing ι).q i k) = (jetRing ι).prolong ξ ((jetRing ι).q i k)
      rw [evolutionary_q, JetRing.prolong_q]

theorem evolutionary_apply (ξ : ι → StandardJet ι) (F : StandardJet ι) :
    evolutionary ξ F = (jetRing ι).prolong ξ F := by
  rw [evolutionary_eq_prolongField]
  rfl

omit [DecidableEq ι] [Fintype ι] in
/-- The `n`-th total derivative of `a + t u`: `a + t u`, then `u`, then
zero. -/
def affineShift (a u : ℝ) : ℕ → StandardJet ι
  | 0 => algebraMap ℝ (StandardJet ι) a + time ι * algebraMap ℝ (StandardJet ι) u
  | 1 => algebraMap ℝ (StandardJet ι) u
  | _ + 2 => 0

omit [DecidableEq ι] [Fintype ι] in
/-- A vector field that annihilates the time annihilates `a + t u` and its
derivatives. -/
theorem apply_affineShift (X : SmoothDerivation (StandardJet ι) (StandardJet ι))
    (hX : X (time ι) = 0) (a u : ℝ) (n : ℕ) : X (affineShift a u n) = 0 := by
  match n with
  | 0 =>
    change X (algebraMap ℝ (StandardJet ι) a + time ι * algebraMap ℝ (StandardJet ι) u) = 0
    rw [map_add, SmoothDerivation.map_mul, hX]
    simp
  | 1 => exact X.map_algebraMap u
  | n + 2 => exact map_zero _

theorem totalDeriv_affineShift (a u : ℝ) (n : ℕ) :
    (jetRing ι).totalDeriv (affineShift a u n) = affineShift a u (n + 1) := by
  match n with
  | 0 =>
    change (jetRing ι).totalDeriv
      (algebraMap ℝ (StandardJet ι) a + time ι * algebraMap ℝ (StandardJet ι) u) =
        algebraMap ℝ (StandardJet ι) u
    rw [map_add, SmoothDerivation.map_mul, totalDeriv_time]
    simp
  | 1 => exact JetRing.totalDeriv_algebraMap (R := jetRing ι) u
  | n + 2 => exact map_zero _

omit [Fintype ι] in
theorem dt_affineShift (a u : ℝ) (n : ℕ) :
    (jetRing ι).dt (affineShift a u n) = affineShift u 0 n := by
  match n with
  | 0 =>
    change (jetRing ι).dt
      (algebraMap ℝ (StandardJet ι) a + time ι * algebraMap ℝ (StandardJet ι) u) =
        algebraMap ℝ (StandardJet ι) u + time ι * algebraMap ℝ (StandardJet ι) 0
    rw [map_add, SmoothDerivation.map_mul, dt_time]
    simp
  | 1 =>
    change (jetRing ι).dt (algebraMap ℝ (StandardJet ι) u) = algebraMap ℝ (StandardJet ι) 0
    rw [SmoothDerivation.map_algebraMap, map_zero]
  | n + 2 => exact map_zero _

omit [DecidableEq ι] in
theorem sum_mul_affineShift (B : Matrix ι ι ℝ) (a u : ι → ℝ) (l : ι) (n : ℕ) :
    ∑ m, algebraMap ℝ (StandardJet ι) (B l m) * affineShift (a m) (u m) n =
      affineShift ((B *ᵥ a) l) ((B *ᵥ u) l) n := by
  match n with
  | 0 =>
    change ∑ m, algebraMap ℝ (StandardJet ι) (B l m) *
        (algebraMap ℝ (StandardJet ι) (a m) + time ι * algebraMap ℝ (StandardJet ι) (u m)) =
      algebraMap ℝ (StandardJet ι) ((B *ᵥ a) l) +
        time ι * algebraMap ℝ (StandardJet ι) ((B *ᵥ u) l)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum, mul_add,
      Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  | 1 =>
    change ∑ m, algebraMap ℝ (StandardJet ι) (B l m) * algebraMap ℝ (StandardJet ι) (u m) =
      algebraMap ℝ (StandardJet ι) ((B *ᵥ u) l)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  | n + 2 =>
    change ∑ m, algebraMap ℝ (StandardJet ι) (B l m) * (0 : StandardJet ι) = 0
    simp only [mul_zero, Finset.sum_const_zero]

omit [DecidableEq ι] [Fintype ι] in
theorem affineShift_sub (a a' u u' : ℝ) (n : ℕ) :
    affineShift (ι := ι) (a - a') (u - u') n = affineShift a u n - affineShift a' u' n := by
  match n with
  | 0 =>
    change algebraMap ℝ (StandardJet ι) (a - a') +
        time ι * algebraMap ℝ (StandardJet ι) (u - u') =
      algebraMap ℝ (StandardJet ι) a + time ι * algebraMap ℝ (StandardJet ι) u -
        (algebraMap ℝ (StandardJet ι) a' + time ι * algebraMap ℝ (StandardJet ι) u')
    rw [map_sub, map_sub]
    ring
  | 1 => exact map_sub _ u u'
  | n + 2 => exact (sub_zero _).symm

/-- The characteristic `δqₗ = Σₘ Aₗₘ qₘ + aₗ + t uₗ` of a linear map, a
translation and a boost. -/
def galileiCharacteristic (A : Matrix ι ι ℝ) (a u : ι → ℝ) (l : ι) : StandardJet ι :=
  ∑ m, algebraMap ℝ (StandardJet ι) (A l m) * (jetRing ι).q m 0 + affineShift (a l) (u l) 0

/-- The vector field of the jet ring generated by `δqₗ = Σₘ Aₗₘ qₘ + aₗ +
t uₗ`. For antisymmetric `A` these are the rotations, translations and boosts
of the Galilei group. -/
def galileiField (A : Matrix ι ι ℝ) (a u : ι → ℝ) :
    SmoothDerivation (StandardJet ι) (StandardJet ι) :=
  evolutionary (galileiCharacteristic A a u)

theorem iterate_totalDeriv_galileiCharacteristic (A : Matrix ι ι ℝ) (a u : ι → ℝ) (l : ι)
    (n : ℕ) :
    ((jetRing ι).totalDeriv^[n]) (galileiCharacteristic A a u l) =
      ∑ m, algebraMap ℝ (StandardJet ι) (A l m) * (jetRing ι).q m n +
        affineShift (a l) (u l) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, totalDeriv_affineShift, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [SmoothDerivation.map_algebraMap_mul, JetRing.totalDeriv_q, smul_eq_mul]

@[simp] theorem galileiField_time (A : Matrix ι ι ℝ) (a u : ι → ℝ) :
    galileiField A a u (time ι) = 0 :=
  evolutionary_time _

/-- The action on the co-ordinates:
`X qₗ⁽ⁿ⁾ = Σₘ Aₗₘ qₘ⁽ⁿ⁾ + Dⁿ(aₗ + t uₗ)`. -/
theorem galileiField_q (A : Matrix ι ι ℝ) (a u : ι → ℝ) (l : ι) (n : ℕ) :
    galileiField A a u ((jetRing ι).q l n) =
      ∑ m, algebraMap ℝ (StandardJet ι) (A l m) * (jetRing ι).q m n +
        affineShift (a l) (u l) n := by
  rw [galileiField, evolutionary_q, iterate_totalDeriv_galileiCharacteristic]

theorem galileiField_totalDeriv (A : Matrix ι ι ℝ) (a u : ι → ℝ) (F : StandardJet ι) :
    galileiField A a u ((jetRing ι).totalDeriv F) =
      (jetRing ι).totalDeriv (galileiField A a u F) :=
  evolutionary_totalDeriv _ F

theorem galileiField_sum_mul_q (A : Matrix ι ι ℝ) (a u : ι → ℝ) (c : ι → ℝ) (n : ℕ) :
    galileiField A a u (∑ m, algebraMap ℝ (StandardJet ι) (c m) * (jetRing ι).q m n) =
      ∑ m, algebraMap ℝ (StandardJet ι) (c m) *
          ∑ p, algebraMap ℝ (StandardJet ι) (A m p) * (jetRing ι).q p n +
        ∑ m, algebraMap ℝ (StandardJet ι) (c m) * affineShift (a m) (u m) n := by
  rw [map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [SmoothDerivation.map_algebraMap_mul, galileiField_q, smul_eq_mul, mul_add]

theorem sum_mul_sum_mul_q (B C : Matrix ι ι ℝ) (l : ι) (n : ℕ) :
    ∑ m, algebraMap ℝ (StandardJet ι) (B l m) *
        ∑ p, algebraMap ℝ (StandardJet ι) (C m p) * (jetRing ι).q p n =
      ∑ p, algebraMap ℝ (StandardJet ι) ((B * C) l p) * (jetRing ι).q p n := by
  simp only [Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, mul_assoc]

/-- The commutators of the fields:
`[X_{A,a,u}, X_{A',a',u'}] = X_{A'A − AA', A'a − Aa', A'u − Au'}`. -/
theorem commutator_galileiField (A A' : Matrix ι ι ℝ) (a u a' u' : ι → ℝ) :
    ⁅galileiField A a u, galileiField A' a' u'⁆ =
      galileiField (A' * A - A * A') (A' *ᵥ a - A *ᵥ a') (A' *ᵥ u - A *ᵥ u') :=
  FreeSmoothRing.derivation_ext fun c => by
    rw [SmoothDerivation.commutator_apply]
    rcases c with _ | ⟨l, n⟩
    · change galileiField A a u (galileiField A' a' u' (time ι)) -
          galileiField A' a' u' (galileiField A a u (time ι)) =
        galileiField (A' * A - A * A') (A' *ᵥ a - A *ᵥ a') (A' *ᵥ u - A *ᵥ u') (time ι)
      rw [galileiField_time, galileiField_time, galileiField_time, map_zero, map_zero, sub_zero]
    · change galileiField A a u (galileiField A' a' u' ((jetRing ι).q l n)) -
          galileiField A' a' u' (galileiField A a u ((jetRing ι).q l n)) =
        galileiField (A' * A - A * A') (A' *ᵥ a - A *ᵥ a') (A' *ᵥ u - A *ᵥ u')
          ((jetRing ι).q l n)
      rw [galileiField_q, galileiField_q, galileiField_q, map_add, map_add,
        galileiField_sum_mul_q, galileiField_sum_mul_q,
        apply_affineShift _ (galileiField_time A a u),
        apply_affineShift _ (galileiField_time A' a' u'), sum_mul_sum_mul_q, sum_mul_sum_mul_q,
        sum_mul_affineShift, sum_mul_affineShift, add_zero, add_zero, Pi.sub_apply,
        Pi.sub_apply, affineShift_sub]
      simp only [Matrix.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
      ring

/-- The commutator of the time translation with a field is a translation:
`[∂/∂t, X_{A,a,u}] = X_{0,u,0}`. -/
theorem commutator_dt_galileiField (A : Matrix ι ι ℝ) (a u : ι → ℝ) :
    ⁅(jetRing ι).dt, galileiField A a u⁆ = galileiField 0 u 0 :=
  FreeSmoothRing.derivation_ext fun c => by
    rw [SmoothDerivation.commutator_apply]
    rcases c with _ | ⟨l, n⟩
    · change (jetRing ι).dt (galileiField A a u (time ι)) -
          galileiField A a u ((jetRing ι).dt (time ι)) = galileiField 0 u 0 (time ι)
      rw [galileiField_time, galileiField_time, dt_time, SmoothDerivation.map_one, map_zero,
        sub_zero]
    · change (jetRing ι).dt (galileiField A a u ((jetRing ι).q l n)) -
          galileiField A a u ((jetRing ι).dt ((jetRing ι).q l n)) =
        galileiField 0 u 0 ((jetRing ι).q l n)
      rw [galileiField_q, galileiField_q, (jetRing ι).dt_q, map_zero, sub_zero, map_add,
        JetRing.dt_sum_mul_q, zero_add, dt_affineShift]
      simp only [Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add,
        Pi.zero_apply]

/-- `[∂ₗ⁽ᵏ⁾, X_{A,a,u}] = Σᵢ Aᵢₗ ∂ᵢ⁽ᵏ⁾`. -/
theorem d_galileiField (A : Matrix ι ι ℝ) (a u : ι → ℝ) (l : ι) (k : ℕ) (F : StandardJet ι) :
    (jetRing ι).d l k (galileiField A a u F) =
      galileiField A a u ((jetRing ι).d l k F) +
        ∑ i, algebraMap ℝ (StandardJet ι) (A i l) * (jetRing ι).d i k F := by
  have h : ⁅(jetRing ι).d l k, galileiField A a u⁆ =
      ∑ i, algebraMap ℝ (StandardJet ι) (A i l) • (jetRing ι).d i k :=
    FreeSmoothRing.derivation_ext fun c => by
      rw [SmoothDerivation.commutator_apply, SmoothDerivation.sum_apply]
      simp only [SmoothDerivation.smul_apply, smul_eq_mul]
      rcases c with _ | ⟨j, n⟩
      · change (jetRing ι).d l k (galileiField A a u (time ι)) -
            galileiField A a u ((jetRing ι).d l k (time ι)) =
          ∑ i, algebraMap ℝ (StandardJet ι) (A i l) * (jetRing ι).d i k (time ι)
        rw [galileiField_time, d_time, map_zero, map_zero, sub_zero]
        exact (Finset.sum_eq_zero fun i _ => by rw [d_time, mul_zero]).symm
      · change (jetRing ι).d l k (galileiField A a u ((jetRing ι).q j n)) -
            galileiField A a u ((jetRing ι).d l k ((jetRing ι).q j n)) =
          ∑ i, algebraMap ℝ (StandardJet ι) (A i l) * (jetRing ι).d i k ((jetRing ι).q j n)
        have hconst : galileiField A a u ((jetRing ι).d l k ((jetRing ι).q j n)) = 0 := by
          by_cases h : (j, n) = (l, k)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            rw [(jetRing ι).d_q_self, SmoothDerivation.map_one]
          · rw [(jetRing ι).d_q_ne j n l k h, map_zero]
        rw [hconst, sub_zero, galileiField_q, map_add, apply_affineShift _ (d_time l k),
          add_zero]
        by_cases hn : n = k
        · subst hn
          rw [JetRing.d_sum_mul_q, Finset.sum_eq_single j]
          · rw [(jetRing ι).d_q_self, mul_one]
          · intro i _ hi
            rw [(jetRing ι).d_q_ne j n i n fun h => hi (Prod.mk.inj h).1.symm, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ j) h
        · rw [JetRing.d_sum_mul_q_of_ne _ hn]
          exact (Finset.sum_eq_zero fun i _ => by
            rw [(jetRing ι).d_q_ne j n i k fun h => hn (Prod.mk.inj h).2, mul_zero]).symm
  have hF := DFunLike.congr_fun h F
  rw [SmoothDerivation.commutator_apply, SmoothDerivation.sum_apply] at hF
  simp only [SmoothDerivation.smul_apply, smul_eq_mul] at hF
  exact sub_eq_iff_eq_add'.mp hF

/-- The Euler operators and the fields: `Eₗ(X F) = X(Eₗ F) + Σᵢ Aᵢₗ Eᵢ(F)`. -/
theorem euler_galileiField (A : Matrix ι ι ℝ) (a u : ι → ℝ) (l : ι) (F : StandardJet ι) :
    (jetRing ι).euler l (galileiField A a u F) =
      galileiField A a u ((jetRing ι).euler l F) +
        ∑ i, algebraMap ℝ (StandardJet ι) (A i l) * (jetRing ι).euler i F :=
  JetRing.euler_apply (galileiField A a u) (fun l i => A i l) (galileiField_totalDeriv A a u)
    (d_galileiField A a u) l F

/-- A field that changes the Lagrangian by a total derivative preserves the
Euler–Lagrange ideal (Landau–Lifshitz §3: the equations of motion have the
same form in all inertial frames). -/
theorem galileiField_mem_eulerLagrangeIdeal (A : Matrix ι ι ℝ) (a u : ι → ℝ)
    {L F : StandardJet ι} (h : galileiField A a u L = (jetRing ι).totalDeriv F)
    {x : StandardJet ι} (hx : x ∈ (jetRing ι).eulerLagrangeIdeal L) :
    galileiField A a u x ∈ (jetRing ι).eulerLagrangeIdeal L :=
  JetRing.apply_mem_eulerLagrangeIdeal (galileiField A a u) (fun l i => A i l)
    (galileiField_totalDeriv A a u) (d_galileiField A a u)
    (fun l => by rw [h, JetRing.euler_totalDeriv]) hx

/-- A natural Lagrangian with `mᵢ Aᵢⱼ + mⱼ Aⱼᵢ = 0` and an invariant
potential changes by the total derivative of `Σ mᵢ uᵢ qᵢ`. -/
theorem galileiField_naturalLagrangian {m : ι → ℝ} {A : Matrix ι ι ℝ}
    (hA : ∀ i j, m i * A i j + m j * A j i = 0) (a u : ι → ℝ) {U : StandardJet ι}
    (hU : galileiField A a u U = 0) :
    galileiField A a u ((jetRing ι).naturalLagrangian m U) =
      (jetRing ι).totalDeriv
        (∑ i, algebraMap ℝ (StandardJet ι) (m i * u i) * (jetRing ι).q i 0) := by
  have hX (i : ι) : galileiField A a u ((jetRing ι).q i 1) =
      ∑ p, algebraMap ℝ (StandardJet ι) (A i p) * (jetRing ι).q p 1 +
        algebraMap ℝ (StandardJet ι) (u i) :=
    galileiField_q A a u i 1
  have hD : (jetRing ι).totalDeriv
      (∑ i, algebraMap ℝ (StandardJet ι) (m i * u i) * (jetRing ι).q i 0) =
        ∑ i, algebraMap ℝ (StandardJet ι) (m i * u i) * (jetRing ι).q i 1 := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SmoothDerivation.map_algebraMap_mul, JetRing.totalDeriv_q, smul_eq_mul]
  have hanti : ∑ i, ∑ p, algebraMap ℝ (StandardJet ι) (m i * A i p) *
      ((jetRing ι).q i 1 * (jetRing ι).q p 1) = 0 :=
    JetRing.sum_sum_antisymm_eq_zero (fun i j => hA i j) _
  have hterm (i : ι) : galileiField A a u (algebraMap ℝ (StandardJet ι) (m i / 2) *
      ((jetRing ι).q i 1 * (jetRing ι).q i 1)) =
        ∑ p, algebraMap ℝ (StandardJet ι) (m i * A i p) *
            ((jetRing ι).q i 1 * (jetRing ι).q p 1) +
          algebraMap ℝ (StandardJet ι) (m i * u i) * (jetRing ι).q i 1 := by
    have hT : ∑ p, algebraMap ℝ (StandardJet ι) (m i * A i p) *
        ((jetRing ι).q i 1 * (jetRing ι).q p 1) =
          algebraMap ℝ (StandardJet ι) (m i) * ((jetRing ι).q i 1 *
            ∑ p, algebraMap ℝ (StandardJet ι) (A i p) * (jetRing ι).q p 1) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul]
      ring
    have h2 := JetRing.algebraMap_half_mul_two (J := StandardJet ι) (m i)
    rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, hX, smul_eq_mul,
      smul_eq_mul, hT, map_mul]
    linear_combination ((jetRing ι).q i 1 *
      (∑ p, algebraMap ℝ (StandardJet ι) (A i p) * (jetRing ι).q p 1 +
        algebraMap ℝ (StandardJet ι) (u i))) * h2
  rw [JetRing.naturalLagrangian, map_sub, hU, sub_zero, map_sum, hD]
  simp only [hterm, Finset.sum_add_distrib]
  rw [hanti, zero_add]

/-- The boost of `Jet/FreeParticle` is the field `X_{0,0,u}`. -/
theorem boost_eq_galileiField (u : ι → ℝ) (L : StandardJet ι) :
    boost u L = galileiField 0 0 u L := by
  have h : galileiCharacteristic (0 : Matrix ι ι ℝ) 0 u =
      fun i => time ι * algebraMap ℝ (StandardJet ι) (u i) := by
    funext i
    change ∑ m, algebraMap ℝ (StandardJet ι) ((0 : Matrix ι ι ℝ) i m) * (jetRing ι).q m 0 +
      (algebraMap ℝ (StandardJet ι) ((0 : ι → ℝ) i) +
        time ι * algebraMap ℝ (StandardJet ι) (u i)) = _
    simp only [Matrix.zero_apply, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero,
      zero_add]
  rw [boost, galileiField, evolutionary_apply, h]

/-- The Euler–Lagrange ideal of `L` is invariant under the Galilei algebra:
under the time translation `∂/∂t` and under the fields `X_{A,a,u}` with an
antisymmetric `A` (rotations, translations and boosts). -/
def IsInertial (L : StandardJet ι) : Prop :=
  (∀ x ∈ (jetRing ι).eulerLagrangeIdeal L, (jetRing ι).dt x ∈ (jetRing ι).eulerLagrangeIdeal L) ∧
    ∀ (A : Matrix ι ι ℝ) (a u : ι → ℝ), Aᵀ = -A →
      ∀ x ∈ (jetRing ι).eulerLagrangeIdeal L,
        galileiField A a u x ∈ (jetRing ι).eulerLagrangeIdeal L

/-- A free system of equal masses is inertial. -/
theorem isInertial_naturalLagrangian (μ : ℝ) :
    IsInertial ((jetRing ι).naturalLagrangian (fun _ => μ) 0) := by
  refine ⟨fun x hx => JetRing.dt_mem_eulerLagrangeIdeal (F := 0) ?_ hx,
    fun A a u hA x hx => galileiField_mem_eulerLagrangeIdeal A a u
      (galileiField_naturalLagrangian (fun i j => ?_) a u (map_zero _)) hx⟩
  · rw [JetRing.dt_naturalLagrangian, map_zero, neg_zero, map_zero]
  · have h := congrFun (congrFun hA i) j
    rw [Matrix.transpose_apply, Matrix.neg_apply] at h
    rw [h]
    ring

end StandardJet

end ProjectAInos.Mechanics
