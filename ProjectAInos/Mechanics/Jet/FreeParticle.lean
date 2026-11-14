/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Constants
public import ProjectAInos.Mechanics.Jet.Standard
public import ProjectAInos.Mechanics.Oscillations.QuadraticLagrangian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Lagrangian of a free particle

Landau–Lifshitz §4 (Theorem 66 of the manuscript). Let `L` be a function of
the velocities in the standard jet ring. The infinitesimal boost with the
velocity `u` is the prolongation of the variation `δqᵢ = t uᵢ`, and `L` is
quasi-invariant when `pr(t u)(L) = D F_u` for a function `F_u` of the time and
the positions, for every `u`.

* `isBoostQuasiInvariant_iff`: `L` is quasi-invariant under boosts exactly
  when it is a polynomial of degree at most two in the velocities,
  `½ Σ mᵢⱼ vᵢ vⱼ + Σ bᵢ vᵢ + c` with a symmetric matrix `m`.
* `velocityPolynomial_eq_add_totalDeriv`: the terms of degree at most one are
  the total derivative of `Σ bᵢ qᵢ + c t`.
* `exists_eq_of_isIsotropic`: if moreover `L(A v) = L(v)` for every orthogonal
  matrix `A`, then `L = ½ μ |v|² + c`.

The step "a function of `v` that is also a function of `(t, q)` is a
constant" is `eq_algebraMap_of_partialDerivation_eq_zero`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

namespace JetRing

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] {R : JetRing ι J}

/-- The derivative of a linear form in the coordinates of the order `n`. -/
theorem d_sum_mul_q [DecidableEq ι] (b : ι → ℝ) (n : ℕ) (j : ι) :
    R.d j n (∑ k, algebraMap ℝ J (b k) * R.q k n) = algebraMap ℝ J (b j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [SmoothDerivation.map_algebraMap_mul, R.d_q_self, smul_eq_mul, mul_one]
  · intro k _ hk
    rw [SmoothDerivation.map_algebraMap_mul, R.d_q_ne k n j n fun h => hk (Prod.mk.inj h).1,
      smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem d_sum_mul_q_of_ne (b : ι → ℝ) {n l : ℕ} (h : n ≠ l) (j : ι) :
    R.d j l (∑ k, algebraMap ℝ J (b k) * R.q k n) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [SmoothDerivation.map_algebraMap_mul, R.d_q_ne k n j l fun h' => h (Prod.mk.inj h').2,
    smul_zero]

theorem dt_sum_mul_q (b : ι → ℝ) (n : ℕ) :
    R.dt (∑ k, algebraMap ℝ J (b k) * R.q k n) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [SmoothDerivation.map_algebraMap_mul, R.dt_q, smul_zero]

theorem dt_sum_mul_q_mul_q (N : Matrix ι ι ℝ) (n : ℕ) :
    R.dt (∑ i, ∑ k, algebraMap ℝ J (N i k / 2) * (R.q i n * R.q k n)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, R.dt_q, R.dt_q, smul_zero,
    smul_zero, add_zero, smul_zero]

/-- The derivative of a quadratic form with a symmetric matrix. -/
theorem d_sum_mul_q_mul_q_of_isSymm [DecidableEq ι] {N : Matrix ι ι ℝ} (hN : N.IsSymm) (n : ℕ)
    (j : ι) :
    R.d j n (∑ i, ∑ k, algebraMap ℝ J (N i k / 2) * (R.q i n * R.q k n)) =
      ∑ k, algebraMap ℝ J (N j k) * R.q k n := by
  rw [d_sum_mul_q_mul_q]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hN.apply j k]
  congr 2
  ring

end JetRing

namespace StandardJet

variable {ι : Type*} [DecidableEq ι]

/-- `L` is a function of the velocities only. -/
def DependsOnVelocities (L : StandardJet ι) : Prop :=
  (jetRing ι).dt L = 0 ∧ ∀ i k, k ≠ 1 → (jetRing ι).d i k L = 0

theorem DependsOnVelocities.orderLE {L : StandardJet ι} (hL : DependsOnVelocities L) :
    (jetRing ι).OrderLE L 1 :=
  fun i k hk => hL.2 i k (by omega)

/-- An element of the standard jet ring whose partial derivatives all vanish
is a constant. -/
theorem eq_algebraMap_of_dt_eq_zero_of_d_eq_zero {s : StandardJet ι}
    (ht : (jetRing ι).dt s = 0) (hd : ∀ i k, (jetRing ι).d i k s = 0) :
    s = algebraMap ℝ (StandardJet ι) (FreeSmoothRing.lift (fun _ => 0) s) :=
  eq_algebraMap_of_partialDerivation_eq_zero (fun a => by
    rcases a with _ | ⟨i, k⟩
    · exact ht
    · exact hd i k) _

variable [Fintype ι]

/-- The infinitesimal boost with the velocity `u`: the prolongation of the
variation `δqᵢ = t uᵢ`. -/
def boost (u : ι → ℝ) (L : StandardJet ι) : StandardJet ι :=
  (jetRing ι).prolong (fun i => time ι * algebraMap ℝ (StandardJet ι) (u i)) L

/-- `L` is quasi-invariant under infinitesimal boosts: for every `u` the
boost of `L` is the total derivative of a function of the time and the
positions. -/
def IsBoostQuasiInvariant (L : StandardJet ι) : Prop :=
  ∀ u : ι → ℝ, ∃ F, (jetRing ι).OrderLE F 0 ∧ boost u L = (jetRing ι).totalDeriv F

/-- On a function of the velocities, the boost is `Σ uᵢ ∂/∂vᵢ`. -/
theorem boost_eq {L : StandardJet ι} (hL : DependsOnVelocities L) (u : ι → ℝ) :
    boost u L = ∑ i, algebraMap ℝ (StandardJet ι) (u i) * (jetRing ι).d i 1 L := by
  rw [boost, JetRing.prolong_of_orderLE_one hL.orderLE]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hL.2 i 0 (by omega), mul_zero, zero_add, SmoothDerivation.map_mul,
    JetRing.totalDeriv_algebraMap, totalDeriv_time, smul_zero, zero_add, smul_eq_mul, mul_one,
    JetRing.momentum]

/-- For a function `F` of the time and the positions, `∂(D F)/∂vⱼ = ∂F/∂qⱼ`. -/
theorem d_one_totalDeriv {F : StandardJet ι} (hF : (jetRing ι).OrderLE F 0) (j : ι) :
    (jetRing ι).d j 1 ((jetRing ι).totalDeriv F) = (jetRing ι).d j 0 F := by
  have h := JetRing.d_succ_totalDeriv (R := jetRing ι) j 0 F
  simp only [zero_add] at h
  rw [h, hF j 1 (by omega), map_zero, zero_add]

/-- The second derivatives of a boost-quasi-invariant function of the
velocities are constants. -/
theorem d_one_d_one_eq_algebraMap {L : StandardJet ι} (hL : DependsOnVelocities L)
    (hq : IsBoostQuasiInvariant L) (i j : ι) :
    (jetRing ι).d j 1 ((jetRing ι).d i 1 L) =
      algebraMap ℝ (StandardJet ι)
        (FreeSmoothRing.lift (fun _ => 0) ((jetRing ι).d j 1 ((jetRing ι).d i 1 L))) := by
  obtain ⟨F, hF, hFu⟩ := hq (Pi.single i 1)
  have hsum : ∑ k, algebraMap ℝ (StandardJet ι) ((Pi.single i 1 : ι → ℝ) k) *
      (jetRing ι).d k 1 L = (jetRing ι).d i 1 L := by
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, map_one, one_mul]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [boost_eq hL, hsum] at hFu
  refine eq_algebraMap_of_dt_eq_zero_of_d_eq_zero ?_ fun k n => ?_
  · rw [(jetRing ι).dt_comm, (jetRing ι).dt_comm, hL.1, map_zero, map_zero]
  · by_cases hn : n = 1
    · subst hn
      rw [hFu, d_one_totalDeriv hF, (jetRing ι).d_comm, hF k 1 (by omega), map_zero]
    · rw [(jetRing ι).d_comm k n j 1, (jetRing ι).d_comm k n i 1, hL.2 k n hn, map_zero,
        map_zero]

/-- The polynomial `½ Σ mᵢⱼ vᵢ vⱼ + Σ bᵢ vᵢ + c` of degree at most two in the
velocities. -/
def velocityPolynomial (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) : StandardJet ι :=
  ∑ i, ∑ j, algebraMap ℝ (StandardJet ι) (m i j / 2) *
      ((jetRing ι).q i 1 * (jetRing ι).q j 1) +
    ∑ i, algebraMap ℝ (StandardJet ι) (b i) * (jetRing ι).q i 1 +
      algebraMap ℝ (StandardJet ι) c

theorem dependsOnVelocities_velocityPolynomial (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) :
    DependsOnVelocities (velocityPolynomial m b c) := by
  refine ⟨?_, fun i k hk => ?_⟩
  · rw [velocityPolynomial, map_add, map_add, JetRing.dt_sum_mul_q_mul_q, JetRing.dt_sum_mul_q,
      SmoothDerivation.map_algebraMap, add_zero, add_zero]
  · rw [velocityPolynomial, map_add, map_add, JetRing.d_sum_mul_q_mul_q_of_ne m (Ne.symm hk),
      JetRing.d_sum_mul_q_of_ne b (Ne.symm hk), SmoothDerivation.map_algebraMap, add_zero,
      add_zero]

theorem d_one_velocityPolynomial {m : Matrix ι ι ℝ} (hm : m.IsSymm) (b : ι → ℝ) (c : ℝ)
    (j : ι) :
    (jetRing ι).d j 1 (velocityPolynomial m b c) =
      ∑ k, algebraMap ℝ (StandardJet ι) (m j k) * (jetRing ι).q k 1 +
        algebraMap ℝ (StandardJet ι) (b j) := by
  rw [velocityPolynomial, map_add, map_add, JetRing.d_sum_mul_q_mul_q_of_isSymm hm,
    JetRing.d_sum_mul_q, SmoothDerivation.map_algebraMap, add_zero]

/-- The terms of degree at most one are a total derivative:
`½ Σ mᵢⱼ vᵢ vⱼ + D(Σ bᵢ qᵢ + c t)`. -/
theorem velocityPolynomial_eq_add_totalDeriv (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) :
    velocityPolynomial m b c =
      ∑ i, ∑ j, algebraMap ℝ (StandardJet ι) (m i j / 2) *
          ((jetRing ι).q i 1 * (jetRing ι).q j 1) +
        (jetRing ι).totalDeriv (∑ i, algebraMap ℝ (StandardJet ι) (b i) * (jetRing ι).q i 0 +
          algebraMap ℝ (StandardJet ι) c * time ι) := by
  rw [velocityPolynomial, add_assoc, map_add, map_sum]
  simp only [SmoothDerivation.map_algebraMap_mul, JetRing.totalDeriv_q, totalDeriv_time,
    smul_eq_mul, mul_one, zero_add]

/-- A polynomial of degree at most two in the velocities is quasi-invariant
under boosts: its boost is the total derivative of
`Σ uᵢ mᵢⱼ qⱼ + (Σ uᵢ bᵢ) t`. -/
theorem isBoostQuasiInvariant_velocityPolynomial {m : Matrix ι ι ℝ} (hm : m.IsSymm)
    (b : ι → ℝ) (c : ℝ) : IsBoostQuasiInvariant (velocityPolynomial m b c) := by
  intro u
  refine ⟨∑ j, algebraMap ℝ (StandardJet ι) (∑ i, u i * m i j) * (jetRing ι).q j 0 +
    algebraMap ℝ (StandardJet ι) (∑ i, u i * b i) * time ι, ?_, ?_⟩
  · exact (JetRing.OrderLE.sum fun j _ =>
      (JetRing.orderLE_algebraMap _ 0).mul (JetRing.orderLE_q j 0)).add
        ((JetRing.orderLE_algebraMap _ 0).mul fun i k _ => d_time i k)
  · have hD : (jetRing ι).totalDeriv
        (∑ j, algebraMap ℝ (StandardJet ι) (∑ i, u i * m i j) * (jetRing ι).q j 0 +
          algebraMap ℝ (StandardJet ι) (∑ i, u i * b i) * time ι) =
        ∑ j, algebraMap ℝ (StandardJet ι) (∑ i, u i * m i j) * (jetRing ι).q j 1 +
          algebraMap ℝ (StandardJet ι) (∑ i, u i * b i) := by
      rw [map_add, map_sum]
      simp only [SmoothDerivation.map_algebraMap_mul, JetRing.totalDeriv_q, totalDeriv_time,
        smul_eq_mul, mul_one, zero_add]
    rw [boost_eq (dependsOnVelocities_velocityPolynomial m b c), hD]
    simp only [d_one_velocityPolynomial hm, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
      map_sum, Finset.sum_mul, map_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring

/-- A function of the velocities with the constant second derivatives `mᵢⱼ`
is a polynomial of degree at most two. -/
theorem exists_eq_velocityPolynomial {L : StandardJet ι} (hL : DependsOnVelocities L)
    {m : Matrix ι ι ℝ} (hm : m.IsSymm)
    (h : ∀ i j, (jetRing ι).d j 1 ((jetRing ι).d i 1 L) = algebraMap ℝ (StandardJet ι) (m i j)) :
    ∃ (b : ι → ℝ) (c : ℝ), L = velocityPolynomial m b c := by
  have h1 (j : ι) : ∃ r : ℝ, (jetRing ι).d j 1 L -
      ∑ k, algebraMap ℝ (StandardJet ι) (m j k) * (jetRing ι).q k 1 =
        algebraMap ℝ (StandardJet ι) r := by
    refine ⟨_, eq_algebraMap_of_dt_eq_zero_of_d_eq_zero ?_ fun k n => ?_⟩
    · rw [map_sub, (jetRing ι).dt_comm, hL.1, map_zero, JetRing.dt_sum_mul_q, sub_zero]
    · by_cases hn : n = 1
      · subst hn
        rw [map_sub, h j k, JetRing.d_sum_mul_q, sub_self]
      · rw [map_sub, (jetRing ι).d_comm, hL.2 k n hn, map_zero,
          JetRing.d_sum_mul_q_of_ne _ (Ne.symm hn), sub_zero]
  choose b hb using h1
  have h0 : ∃ c : ℝ, L - (∑ i, ∑ j, algebraMap ℝ (StandardJet ι) (m i j / 2) *
      ((jetRing ι).q i 1 * (jetRing ι).q j 1) +
        ∑ i, algebraMap ℝ (StandardJet ι) (b i) * (jetRing ι).q i 1) =
          algebraMap ℝ (StandardJet ι) c := by
    refine ⟨_, eq_algebraMap_of_dt_eq_zero_of_d_eq_zero ?_ fun k n => ?_⟩
    · rw [map_sub, map_add, hL.1, JetRing.dt_sum_mul_q_mul_q, JetRing.dt_sum_mul_q, add_zero,
        sub_zero]
    · by_cases hn : n = 1
      · subst hn
        rw [map_sub, map_add, JetRing.d_sum_mul_q_mul_q_of_isSymm hm, JetRing.d_sum_mul_q,
          ← sub_sub, hb k, sub_self]
      · rw [map_sub, map_add, hL.2 k n hn, JetRing.d_sum_mul_q_mul_q_of_ne m (Ne.symm hn),
          JetRing.d_sum_mul_q_of_ne b (Ne.symm hn), add_zero, sub_zero]
  obtain ⟨c, hc⟩ := h0
  refine ⟨b, c, ?_⟩
  rw [velocityPolynomial, ← hc]
  ring

/-- The matrix of the second derivatives of a function of the velocities, at
the origin. -/
def massMatrix (L : StandardJet ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    FreeSmoothRing.lift (fun _ => 0) ((jetRing ι).d j 1 ((jetRing ι).d i 1 L))

omit [Fintype ι] in
theorem massMatrix_isSymm (L : StandardJet ι) : (massMatrix L).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    rw [massMatrix, Matrix.of_apply, Matrix.of_apply, (jetRing ι).d_comm]

/-- Landau–Lifshitz §4 (Theorem 66): a function of the velocities is
quasi-invariant under infinitesimal boosts exactly when it is a polynomial of
degree at most two in the velocities. -/
theorem isBoostQuasiInvariant_iff {L : StandardJet ι} (hL : DependsOnVelocities L) :
    IsBoostQuasiInvariant L ↔
      ∃ (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ), m.IsSymm ∧ L = velocityPolynomial m b c := by
  constructor
  · intro hq
    obtain ⟨b, c, h⟩ := exists_eq_velocityPolynomial hL (massMatrix_isSymm L)
      (fun i j => d_one_d_one_eq_algebraMap hL hq i j)
    exact ⟨massMatrix L, b, c, massMatrix_isSymm L, h⟩
  · rintro ⟨m, b, c, hm, rfl⟩
    exact isBoostQuasiInvariant_velocityPolynomial hm b c

/-! ### Isotropy -/

omit [Fintype ι] in
/-- The point of the jet space with the velocities `w` and all the other
co-ordinates zero. -/
def velocityPoint (w : ι → ℝ) : Option (ι × ℕ) → ℝ :=
  fun a => a.elim 0 fun p => if p.2 = 1 then w p.1 else 0

/-- The value `L(w)` of a function of the velocities. -/
def velocityValue (L : StandardJet ι) (w : ι → ℝ) : ℝ :=
  FreeSmoothRing.lift (velocityPoint w) L

omit [Fintype ι] in
theorem lift_velocityPoint_q (w : ι → ℝ) (i : ι) :
    FreeSmoothRing.lift (velocityPoint w) ((jetRing ι).q i 1) = w i := by
  change FreeSmoothRing.lift (velocityPoint w) (generator (some (i, 1))) = w i
  rw [lift_generator]
  rfl

/-- The value of a polynomial of degree at most two:
`L(w) = ½ w · m w + b · w + c`. -/
theorem velocityValue_velocityPolynomial (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) (w : ι → ℝ) :
    velocityValue (velocityPolynomial m b c) w = w ⬝ᵥ m *ᵥ w / 2 + b ⬝ᵥ w + c := by
  have h1 : velocityValue (velocityPolynomial m b c) w =
      ∑ i, ∑ j, m i j / 2 * (w i * w j) + ∑ i, b i * w i + c := by
    rw [velocityValue, velocityPolynomial]
    simp only [SmoothRingHom.map_add, SmoothRingHom.map_sum, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, lift_velocityPoint_q]
    rfl
  have h2 : w ⬝ᵥ m *ᵥ w / 2 = ∑ i, ∑ j, m i j / 2 * (w i * w j) := by
    rw [dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, h2]
  rfl

/-- `L(v)` is invariant under the orthogonal group: `L(A v) = L(v)` for every
matrix `A` with `Aᵀ A = 1`. -/
def IsIsotropic (L : StandardJet ι) : Prop :=
  ∀ A : Matrix ι ι ℝ, Aᵀ * A = 1 → ∀ w : ι → ℝ, velocityValue L (A *ᵥ w) = velocityValue L w

theorem mulVec_single_apply (m : Matrix ι ι ℝ) (j : ι) (y : ℝ) (k : ι) :
    (m *ᵥ Pi.single j y) k = m k j * y := by
  change (fun l => m k l) ⬝ᵥ Pi.single j y = _
  rw [dotProduct_single]

/-- The value of `½ w · m w + b · w + c` on a combination of two basis
vectors. -/
theorem quadratic_single_add_single (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) (i j : ι)
    (x y : ℝ) :
    (Pi.single i x + Pi.single j y) ⬝ᵥ m *ᵥ (Pi.single i x + Pi.single j y) / 2 +
        b ⬝ᵥ (Pi.single i x + Pi.single j y) + c =
      (m i i * x * x + m i j * x * y + m j i * y * x + m j j * y * y) / 2 +
        (b i * x + b j * y) + c := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct,
    dotProduct_single, mulVec_single_apply]
  ring

theorem quadratic_single (m : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) (i : ι) (x : ℝ) :
    Pi.single i x ⬝ᵥ m *ᵥ Pi.single i x / 2 + b ⬝ᵥ Pi.single i x + c =
      m i i * x * x / 2 + b i * x + c := by
  simp only [single_dotProduct, dotProduct_single, mulVec_single_apply]
  ring

/-- An isotropic polynomial of degree at most two in the velocities has a
scalar matrix and no linear term. -/
theorem eq_smul_one_of_isIsotropic {m : Matrix ι ι ℝ} (hm : m.IsSymm) {b : ι → ℝ} {c : ℝ}
    (h : IsIsotropic (velocityPolynomial m b c)) :
    (∃ μ : ℝ, m = μ • (1 : Matrix ι ι ℝ)) ∧ b = 0 := by
  have hQ (A : Matrix ι ι ℝ) (hA : Aᵀ * A = 1) (w : ι → ℝ) :
      (A *ᵥ w) ⬝ᵥ m *ᵥ (A *ᵥ w) / 2 + b ⬝ᵥ (A *ᵥ w) + c =
        w ⬝ᵥ m *ᵥ w / 2 + b ⬝ᵥ w + c := by
    have h' := h A hA w
    rwa [velocityValue_velocityPolynomial, velocityValue_velocityPolynomial] at h'
  have hb (i : ι) : b i = 0 := by
    have h1 := hQ (-1) (by rw [Matrix.transpose_neg, Matrix.transpose_one, neg_mul_neg, one_mul])
      (Pi.single i 1)
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec, Matrix.mulVec_neg, neg_dotProduct,
      dotProduct_neg, neg_neg, dotProduct_single_one] at h1
    linarith
  have hoff (i j : ι) (hij : i ≠ j) : m i j = 0 := by
    have hA : (Matrix.diagonal fun k => if k = i then (-1 : ℝ) else 1)ᵀ *
        Matrix.diagonal (fun k => if k = i then (-1 : ℝ) else 1) = 1 := by
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      split_ifs <;> norm_num
    have h1 := hQ _ hA (Pi.single i 1 + Pi.single j 1)
    rw [Matrix.mulVec_add, Matrix.diagonal_mulVec_single, Matrix.diagonal_mulVec_single] at h1
    simp only [↓reduceIte, hij.symm, mul_one] at h1
    rw [quadratic_single_add_single, quadratic_single_add_single] at h1
    have hs := hm.apply i j
    have hbi := hb i
    have hbj := hb j
    linarith
  have hdiag (i j : ι) : m i i = m j j := by
    have hA : ((1 : Matrix ι ι ℝ).submatrix (Equiv.swap i j) (Equiv.refl ι))ᵀ *
        (1 : Matrix ι ι ℝ).submatrix (Equiv.swap i j) (Equiv.refl ι) = 1 := by
      rw [Matrix.transpose_submatrix, Matrix.transpose_one, Matrix.submatrix_mul_equiv,
        Matrix.mul_one, Matrix.submatrix_one_equiv]
    have hcol : (1 : Matrix ι ι ℝ).submatrix (Equiv.swap i j) (Equiv.refl ι) *ᵥ
        Pi.single i 1 = Pi.single j 1 := by
      rw [Matrix.mulVec_single_one]
      funext a
      simp only [Matrix.col_apply, Matrix.submatrix_apply, Equiv.refl_apply, Matrix.one_apply,
        Pi.single_apply, ← Equiv.eq_symm_apply, Equiv.symm_swap,
        Equiv.swap_apply_left]
    have h1 := hQ _ hA (Pi.single i 1)
    rw [hcol, quadratic_single, quadratic_single] at h1
    have hbi := hb i
    have hbj := hb j
    linarith
  refine ⟨?_, funext hb⟩
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, Matrix.ext fun i => isEmptyElim i⟩
  · refine ⟨m i₀ i₀, Matrix.ext fun i j => ?_⟩
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, mul_one]
      exact hdiag i i₀
    · simp only [hij, ↓reduceIte, mul_zero]
      exact hoff i j hij

/-- The polynomial with a scalar matrix and no linear term is the Lagrangian
`½ μ |v|²` of a free particle plus a constant. -/
theorem velocityPolynomial_smul_one (μ c : ℝ) :
    velocityPolynomial (μ • (1 : Matrix ι ι ℝ)) 0 c =
      (jetRing ι).naturalLagrangian (fun _ => μ) 0 + algebraMap ℝ (StandardJet ι) c := by
  have h1 (i : ι) : ∑ j, algebraMap ℝ (StandardJet ι) ((μ • (1 : Matrix ι ι ℝ)) i j / 2) *
      ((jetRing ι).q i 1 * (jetRing ι).q j 1) =
        algebraMap ℝ (StandardJet ι) (μ / 2) * ((jetRing ι).q i 1 * (jetRing ι).q i 1) := by
    rw [Finset.sum_eq_single i]
    · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [Matrix.smul_apply, Matrix.one_apply_ne hj.symm, smul_eq_mul, mul_zero, zero_div,
        map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ i, algebraMap ℝ (StandardJet ι) ((0 : ι → ℝ) i) * (jetRing ι).q i 1 = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, map_zero, zero_mul]
  rw [velocityPolynomial, JetRing.naturalLagrangian, sub_zero, h2, add_zero]
  simp only [h1]

/-- Landau–Lifshitz §4 (Theorem 66): a function of the velocities that is
quasi-invariant under boosts and isotropic is `½ μ |v|² + c`. -/
theorem exists_eq_of_isIsotropic {L : StandardJet ι} (hL : DependsOnVelocities L)
    (hq : IsBoostQuasiInvariant L) (hiso : IsIsotropic L) :
    ∃ μ c : ℝ,
      L = (jetRing ι).naturalLagrangian (fun _ => μ) 0 + algebraMap ℝ (StandardJet ι) c := by
  obtain ⟨m, b, c, hm, rfl⟩ := (isBoostQuasiInvariant_iff hL).mp hq
  obtain ⟨⟨μ, rfl⟩, rfl⟩ := eq_smul_one_of_isIsotropic hm hiso
  exact ⟨μ, c, velocityPolynomial_smul_one μ c⟩

/-- The finite boost of the Lagrangian of a free particle (Landau–Lifshitz
(4.2)): `½ μ |v + u|² − ½ μ |v|² = D(μ u · q + ½ μ |u|² t)`. -/
theorem freeLagrangian_boost (μ : ℝ) (u : ι → ℝ) :
    ∑ i, algebraMap ℝ (StandardJet ι) (μ / 2) *
          (((jetRing ι).q i 1 + algebraMap ℝ (StandardJet ι) (u i)) *
            ((jetRing ι).q i 1 + algebraMap ℝ (StandardJet ι) (u i))) -
        ∑ i, algebraMap ℝ (StandardJet ι) (μ / 2) * ((jetRing ι).q i 1 * (jetRing ι).q i 1) =
      (jetRing ι).totalDeriv
        (∑ i, algebraMap ℝ (StandardJet ι) (μ * u i) * (jetRing ι).q i 0 +
          algebraMap ℝ (StandardJet ι) (∑ i, μ / 2 * (u i * u i)) * time ι) := by
  have hD : (jetRing ι).totalDeriv
      (∑ i, algebraMap ℝ (StandardJet ι) (μ * u i) * (jetRing ι).q i 0 +
        algebraMap ℝ (StandardJet ι) (∑ i, μ / 2 * (u i * u i)) * time ι) =
      ∑ i, algebraMap ℝ (StandardJet ι) (μ * u i) * (jetRing ι).q i 1 +
        algebraMap ℝ (StandardJet ι) (∑ i, μ / 2 * (u i * u i)) := by
    rw [map_add, map_sum]
    simp only [SmoothDerivation.map_algebraMap_mul, JetRing.totalDeriv_q, totalDeriv_time,
      smul_eq_mul, mul_one, zero_add]
  rw [hD, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := JetRing.algebraMap_half_mul_two (J := StandardJet ι) μ
  rw [map_mul, map_mul, map_mul]
  linear_combination
    (algebraMap ℝ (StandardJet ι) (u i) * (jetRing ι).q i 1) * h

end StandardJet

end ProjectAInos.Mechanics
