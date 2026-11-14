/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.NormalModes
public import ProjectAInos.Mechanics.Poisson.Quadratic
public import ProjectAInos.Mechanics.Poisson.Trajectory
public import ProjectAInos.SmoothAlgebra.Poisson.Hom
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The normal form of a quadratic Hamiltonian

For the Hamiltonian `H = ½ Σ (M⁻¹)ᵢₖ pᵢ pₖ + ½ Σ Kᵢₖ qᵢ qₖ` with a positive
definite `M` and a symmetric `K`, the simultaneous diagonalization
`Sᵀ M S = 1`, `Sᵀ K S = diag λ` gives a linear canonical transformation to
the normal form (Proposition 70 of the manuscript, Landau–Lifshitz §23): with
`Q = Sᵀ M q` and `P = Sᵀ p`,

* `{Qₐ, P_b} = δₐ_b`, `{Qₐ, Q_b} = 0` and `{Pₐ, P_b} = 0`;
* `H = Σₐ ½ (Pₐ² + λₐ Qₐ²)`.

The inverse of `M` is `S Sᵀ`. The transformation is the morphism
`linearTransformation (Sᵀ * M) Sᵀ` of phase space; it is a Poisson morphism
with the inverse `linearTransformation S (M * S)`.

The trajectories of `H` are the solutions of `M ẍ + K x = 0` together with
the momenta `p = M ẋ` (`isTrajectory_quadraticHamiltonian_iff_isSmallOscillation`).
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.NormalModes

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The linear combinations `Σₖ Aₐₖ qₖ` of the positions. -/
def linearQ (A : Matrix n n ℝ) (a : n) : PhaseSpace n :=
  ∑ k, algebraMap ℝ (PhaseSpace n) (A a k) * q k

/-- The linear combinations `Σₖ Bₐₖ pₖ` of the momenta. -/
def linearP (B : Matrix n n ℝ) (a : n) : PhaseSpace n :=
  ∑ k, algebraMap ℝ (PhaseSpace n) (B a k) * p k

/-- `{Σ Aₐₖ qₖ, Σ B_bₗ pₗ} = (A Bᵀ)ₐ_b`. -/
theorem canonical_linearQ_linearP (A B : Matrix n n ℝ) (a b : n) :
    (canonical n).bracket (linearQ A a) (linearP B b) =
      algebraMap ℝ (PhaseSpace n) ((A * Bᵀ) a b) := by
  simp only [linearQ, linearP, AlmostPoissonStructure.bracket_sum_left,
    AlmostPoissonStructure.bracket_sum_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_q_p, mul_zero, add_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.mul_apply,
    Matrix.transpose_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem canonical_linearQ_linearQ (A B : Matrix n n ℝ) (a b : n) :
    (canonical n).bracket (linearQ A a) (linearQ B b) = 0 := by
  simp only [linearQ, AlmostPoissonStructure.bracket_sum_left,
    AlmostPoissonStructure.bracket_sum_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_q_q, mul_zero, add_zero,
    Finset.sum_const_zero]

theorem canonical_linearP_linearP (A B : Matrix n n ℝ) (a b : n) :
    (canonical n).bracket (linearP A a) (linearP B b) = 0 := by
  simp only [linearP, AlmostPoissonStructure.bracket_sum_left,
    AlmostPoissonStructure.bracket_sum_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_p_p, mul_zero, add_zero,
    Finset.sum_const_zero]

theorem linearQ_one (a : n) : linearQ (1 : Matrix n n ℝ) a = q a := by
  rw [linearQ, Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.one_apply_ne hb.symm, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem linearP_one (a : n) : linearP (1 : Matrix n n ℝ) a = p a := by
  rw [linearP, Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.one_apply_ne hb.symm, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The linear transformation `q ↦ A q`, `p ↦ B p` of phase space. -/
def linearTransformation (A B : Matrix n n ℝ) : SmoothRingHom (PhaseSpace n) (PhaseSpace n) :=
  FreeSmoothRing.lift (Sum.elim (linearQ A) (linearP B))

omit [DecidableEq n] in
@[simp] theorem linearTransformation_q (A B : Matrix n n ℝ) (a : n) :
    linearTransformation A B (q a) = linearQ A a := by
  rw [linearTransformation, PhaseSpace.q, lift_generator, Sum.elim_inl]

omit [DecidableEq n] in
@[simp] theorem linearTransformation_p (A B : Matrix n n ℝ) (a : n) :
    linearTransformation A B (p a) = linearP B a := by
  rw [linearTransformation, PhaseSpace.p, lift_generator, Sum.elim_inr]

omit [DecidableEq n] in
theorem linearTransformation_linearQ (A B A' : Matrix n n ℝ) (a : n) :
    linearTransformation A B (linearQ A' a) = linearQ (A' * A) a := by
  simp only [linearQ, SmoothRingHom.map_sum, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    linearTransformation_q, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_assoc]

omit [DecidableEq n] in
theorem linearTransformation_linearP (A B B' : Matrix n n ℝ) (a : n) :
    linearTransformation A B (linearP B' a) = linearP (B' * B) a := by
  simp only [linearP, SmoothRingHom.map_sum, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    linearTransformation_p, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_assoc]

omit [DecidableEq n] in
/-- Linear transformations compose by the product of the matrices. -/
theorem linearTransformation_comp (A B A' B' : Matrix n n ℝ) :
    (linearTransformation A B).comp (linearTransformation A' B') =
      linearTransformation (A' * A) (B' * B) :=
  hom_ext fun a => by
    rcases a with i | i
    · change (linearTransformation A B) (linearTransformation A' B' (q i)) =
        linearTransformation (A' * A) (B' * B) (q i)
      rw [linearTransformation_q, linearTransformation_q, linearTransformation_linearQ]
    · change (linearTransformation A B) (linearTransformation A' B' (p i)) =
        linearTransformation (A' * A) (B' * B) (p i)
      rw [linearTransformation_p, linearTransformation_p, linearTransformation_linearP]

theorem linearTransformation_one :
    linearTransformation (1 : Matrix n n ℝ) 1 = SmoothRingHom.id (PhaseSpace n) :=
  hom_ext fun a => by
    rcases a with i | i
    · change linearTransformation 1 1 (q i) = q i
      rw [linearTransformation_q, linearQ_one]
    · change linearTransformation 1 1 (p i) = p i
      rw [linearTransformation_p, linearP_one]

/-- A linear transformation `q ↦ A q`, `p ↦ B p` with `A Bᵀ = 1` is
canonical. -/
theorem isPoissonHom_linearTransformation {A B : Matrix n n ℝ} (h : A * Bᵀ = 1) :
    IsPoissonHom (canonical n).toAlmostPoissonStructure (canonical n).toAlmostPoissonStructure
      (linearTransformation A B) :=
  FreeSmoothRing.isPoissonHom_of_generators fun a b => by
    have h' : B * Aᵀ = 1 := by
      have := congrArg Matrix.transpose h
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    rcases a with i | i <;> rcases b with j | j
    · change linearTransformation A B ((canonical n).bracket (q i) (q j)) =
        (canonical n).bracket (linearTransformation A B (q i)) (linearTransformation A B (q j))
      rw [canonical_q_q, SmoothRingHom.map_zero, linearTransformation_q, linearTransformation_q,
        canonical_linearQ_linearQ]
    · change linearTransformation A B ((canonical n).bracket (q i) (p j)) =
        (canonical n).bracket (linearTransformation A B (q i)) (linearTransformation A B (p j))
      rw [canonical_q_p, linearTransformation_q, linearTransformation_p,
        canonical_linearQ_linearP, h, Matrix.one_apply]
      split_ifs
      · rw [SmoothRingHom.map_one, map_one]
      · rw [SmoothRingHom.map_zero, map_zero]
    · change linearTransformation A B ((canonical n).bracket (p i) (q j)) =
        (canonical n).bracket (linearTransformation A B (p i)) (linearTransformation A B (q j))
      rw [canonical_p_q, linearTransformation_q, linearTransformation_p,
        (canonical n).antisymm (linearP B i) (linearQ A j), canonical_linearQ_linearP, h,
        Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, SmoothRingHom.map_neg, SmoothRingHom.map_one, map_one]
      · simp only [hij, Ne.symm hij, ↓reduceIte, SmoothRingHom.map_zero, map_zero, neg_zero]
    · change linearTransformation A B ((canonical n).bracket (p i) (p j)) =
        (canonical n).bracket (linearTransformation A B (p i)) (linearTransformation A B (p j))
      rw [canonical_p_p, SmoothRingHom.map_zero, linearTransformation_p, linearTransformation_p,
        canonical_linearP_linearP]

section NormalForm

variable {M K S : Matrix n n ℝ} {lam : n → ℝ}

/-- The normal co-ordinates `Q = Sᵀ M q` and `P = Sᵀ p` are canonical. -/
theorem canonical_normal_q_p (hSM : Sᵀ * M * S = 1) (a b : n) :
    (canonical n).bracket (linearQ (Sᵀ * M) a) (linearP Sᵀ b) = if a = b then 1 else 0 := by
  rw [canonical_linearQ_linearP, Matrix.transpose_transpose, hSM, Matrix.one_apply]
  split_ifs <;> simp

omit [DecidableEq n] in
/-- A weighted sum of squares of linear combinations. -/
theorem sum_mul_linear_sq (w : n → ℝ) (A : Matrix n n ℝ) (y : n → PhaseSpace n) :
    ∑ a, algebraMap ℝ (PhaseSpace n) (w a) *
        ((∑ j, algebraMap ℝ (PhaseSpace n) (A a j) * y j) *
          (∑ k, algebraMap ℝ (PhaseSpace n) (A a k) * y k)) =
      ∑ j, ∑ k, algebraMap ℝ (PhaseSpace n) (∑ a, w a * A a j * A a k) * (y j * y k) := by
  have hL : ∑ a, algebraMap ℝ (PhaseSpace n) (w a) *
        ((∑ j, algebraMap ℝ (PhaseSpace n) (A a j) * y j) *
          (∑ k, algebraMap ℝ (PhaseSpace n) (A a k) * y k)) =
      ∑ a, ∑ j, ∑ k, algebraMap ℝ (PhaseSpace n) (w a) *
        (algebraMap ℝ (PhaseSpace n) (A a j) * y j *
          (algebraMap ℝ (PhaseSpace n) (A a k) * y k)) :=
    Finset.sum_congr rfl fun a _ => by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  have hR : ∑ j, ∑ k, algebraMap ℝ (PhaseSpace n) (∑ a, w a * A a j * A a k) * (y j * y k) =
      ∑ j, ∑ k, ∑ a, algebraMap ℝ (PhaseSpace n) (w a) * algebraMap ℝ (PhaseSpace n) (A a j) *
        algebraMap ℝ (PhaseSpace n) (A a k) * (y j * y k) := by
    simp only [map_sum, map_mul, Finset.sum_mul]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- The Hamiltonian `½ Σ Wᵢₖ pᵢ pₖ + ½ Σ Kᵢₖ qᵢ qₖ`, the quadratic form of
the block matrix `(K, 0; 0, W)`. -/
def quadraticHamiltonian (W K : Matrix n n ℝ) : PhaseSpace n :=
  quadraticForm (Matrix.fromBlocks K 0 0 W)

omit [DecidableEq n] in
theorem quadraticHamiltonian_eq (W K : Matrix n n ℝ) :
    quadraticHamiltonian W K =
      ∑ i, ∑ k, algebraMap ℝ (PhaseSpace n) (W i k / 2) * (p i * p k) +
        ∑ i, ∑ k, algebraMap ℝ (PhaseSpace n) (K i k / 2) * (q i * q k) := by
  simp only [quadraticHamiltonian, quadraticForm, bilinearForm, Fintype.sum_sum_type,
    Matrix.smul_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul,
    one_div_mul_eq_div, PhaseSpace.q, PhaseSpace.p, zero_div, map_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add]
  rw [add_comm]

/-- The matrix `S Sᵀ` is the inverse of `M`. -/
theorem mul_mul_transpose_self (hSM : Sᵀ * M * S = 1) : M * (S * Sᵀ) = 1 := by
  rw [← Matrix.mul_assoc]
  exact mul_mul_transpose_eq_one hSM

/-- The normal form of the Hamiltonian (Proposition 70, Landau–Lifshitz
(23.12)): `½ pᵀ M⁻¹ p + ½ qᵀ K q = Σₐ ½ (Pₐ² + λₐ Qₐ²)`. -/
theorem quadraticHamiltonian_eq_normalForm (hM : M.IsSymm) (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) :
    quadraticHamiltonian (S * Sᵀ) K =
      ∑ a, (algebraMap ℝ (PhaseSpace n) (1 / 2) * (linearP Sᵀ a * linearP Sᵀ a) +
        algebraMap ℝ (PhaseSpace n) (lam a / 2) *
          (linearQ (Sᵀ * M) a * linearQ (Sᵀ * M) a)) := by
  have hK : (Sᵀ * M)ᵀ * diagonal lam * (Sᵀ * M) = K := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hM.eq,
      ← mul_eq_mul_mul_diagonal hSM hSK, Matrix.mul_assoc, mul_transpose_mul_eq_one hSM,
      Matrix.mul_one]
  have hp (j k : n) : ∑ a, (1 / 2 : ℝ) * Sᵀ a j * Sᵀ a k = (S * Sᵀ) j k / 2 := by
    rw [Matrix.mul_apply, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Matrix.transpose_apply, Matrix.transpose_apply]
      ring
  have hq (j k : n) : ∑ a, lam a / 2 * (Sᵀ * M) a j * (Sᵀ * M) a k = K j k / 2 := by
    have h := congrFun (congrFun hK j) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at h
    rw [← h, Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [quadraticHamiltonian_eq, Finset.sum_add_distrib]
  simp only [linearP, linearQ]
  rw [sum_mul_linear_sq (fun _ => 1 / 2) Sᵀ p, sum_mul_linear_sq (fun a => lam a / 2) (Sᵀ * M) q]
  simp only [hp, hq]

/-- The linear canonical transformation `Q = Sᵀ M q`, `P = Sᵀ p` takes the
normal form `Σₐ ½ (pₐ² + λₐ qₐ²)` to the Hamiltonian (Proposition 70). -/
theorem linearTransformation_normalForm (hM : M.IsSymm) (hSM : Sᵀ * M * S = 1)
    (hSK : Sᵀ * K * S = diagonal lam) :
    linearTransformation (Sᵀ * M) Sᵀ
        (∑ a, (algebraMap ℝ (PhaseSpace n) (1 / 2) * (p a * p a) +
          algebraMap ℝ (PhaseSpace n) (lam a / 2) * (q a * q a))) =
      quadraticHamiltonian (S * Sᵀ) K := by
  rw [quadraticHamiltonian_eq_normalForm hM hSM hSK]
  simp only [SmoothRingHom.map_sum, SmoothRingHom.map_add, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, linearTransformation_q, linearTransformation_p]

/-- The transformation to the normal co-ordinates is canonical. -/
theorem isPoissonHom_normalTransformation (hSM : Sᵀ * M * S = 1) :
    IsPoissonHom (canonical n).toAlmostPoissonStructure (canonical n).toAlmostPoissonStructure
      (linearTransformation (Sᵀ * M) Sᵀ) :=
  isPoissonHom_linearTransformation (by rw [Matrix.transpose_transpose, hSM])

/-- The transformation to the normal co-ordinates has the inverse
`q ↦ S q`, `p ↦ M S p`. -/
theorem linearTransformation_comp_inverse (hSM : Sᵀ * M * S = 1) :
    (linearTransformation (Sᵀ * M) Sᵀ).comp (linearTransformation S (M * S)) =
      SmoothRingHom.id (PhaseSpace n) := by
  rw [linearTransformation_comp, mul_transpose_mul_eq_one hSM, mul_mul_transpose_eq_one hSM,
    linearTransformation_one]

theorem linearTransformation_inverse_comp (hSM : Sᵀ * M * S = 1) :
    (linearTransformation S (M * S)).comp (linearTransformation (Sᵀ * M) Sᵀ) =
      SmoothRingHom.id (PhaseSpace n) := by
  rw [linearTransformation_comp, hSM, ← Matrix.mul_assoc, hSM, linearTransformation_one]

end NormalForm

section Trajectories

variable {M W K : Matrix n n ℝ}

/-- The Hamiltonian vector field of a quadratic form is linear: along a
trajectory, `ẋ = J S x`. -/
theorem isTrajectory_quadraticForm_iff {S : Matrix (n ⊕ n) (n ⊕ n) ℝ} (hS : S.IsSymm)
    (c : n ⊕ n → TimeFunction) :
    IsTrajectory (canonical n) (quadraticForm S) c ↔
      ∀ a, timeDerivative (c a) =
        ∑ b, algebraMap ℝ TimeFunction ((canonicalForm n * S) a b) * c b := by
  refine forall_congr' fun a => ?_
  rw [canonical_bracket_generator_quadraticForm hS, SmoothRingHom.map_sum]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, lift_generator]

theorem canonicalForm_mul_fromBlocks (W K : Matrix n n ℝ) :
    canonicalForm n * Matrix.fromBlocks K 0 0 W = Matrix.fromBlocks 0 W (-K) 0 := by
  rw [canonicalForm, Matrix.fromBlocks_multiply]
  simp

/-- Hamilton's equations of `½ pᵀ W p + ½ qᵀ K q`: `q̇ = W p`, `ṗ = −K q`. -/
theorem isTrajectory_quadraticHamiltonian_iff (hW : W.IsSymm) (hK : K.IsSymm)
    (c : n ⊕ n → TimeFunction) :
    IsTrajectory (canonical n) (quadraticHamiltonian W K) c ↔
      (fun i => timeDerivative (c (Sum.inl i))) =
          W.map (algebraMap ℝ TimeFunction) *ᵥ (fun k => c (Sum.inr k)) ∧
        (fun i => timeDerivative (c (Sum.inr i))) =
          -(K.map (algebraMap ℝ TimeFunction) *ᵥ fun k => c (Sum.inl k)) := by
  rw [quadraticHamiltonian,
    isTrajectory_quadraticForm_iff (Matrix.IsSymm.fromBlocks hK Matrix.transpose_zero hW),
    canonicalForm_mul_fromBlocks, Sum.forall, funext_iff, funext_iff]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
    map_zero, map_neg, zero_mul, neg_mul, Finset.sum_const_zero, zero_add, add_zero,
    Finset.sum_neg_distrib, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.neg_apply]

/-- The trajectories of `H = ½ pᵀ M⁻¹ p + ½ qᵀ K q` are the solutions of
`M ẍ + K x = 0` (Landau–Lifshitz (23.5)) together with the momenta
`p = M ẋ`. -/
theorem isTrajectory_quadraticHamiltonian_iff_isSmallOscillation (hMW : M * W = 1)
    (hW : W.IsSymm) (hK : K.IsSymm) (c : n ⊕ n → TimeFunction) :
    IsTrajectory (canonical n) (quadraticHamiltonian W K) c ↔
      IsSmallOscillation M K (fun i => c (Sum.inl i)) ∧
        (fun i => c (Sum.inr i)) =
          M.map (algebraMap ℝ TimeFunction) *ᵥ fun k => timeDerivative (c (Sum.inl k)) := by
  have hMWa : M.map (algebraMap ℝ TimeFunction) * W.map (algebraMap ℝ TimeFunction) = 1 := by
    rw [← Matrix.map_mul, hMW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hWMa : W.map (algebraMap ℝ TimeFunction) * M.map (algebraMap ℝ TimeFunction) = 1 := by
    rw [← Matrix.map_mul, mul_eq_one_comm.mp hMW, Matrix.map_one _ (map_zero _) (map_one _)]
  have hD (hπ : (fun i => c (Sum.inr i)) =
      M.map (algebraMap ℝ TimeFunction) *ᵥ fun k => timeDerivative (c (Sum.inl k))) :
      (fun i => timeDerivative (c (Sum.inr i))) =
        M.map (algebraMap ℝ TimeFunction) *ᵥ
          fun k => timeDerivative (timeDerivative (c (Sum.inl k))) := by
    funext i
    rw [← timeDerivative_map_mulVec]
    exact congrArg timeDerivative (congrFun hπ i)
  rw [isTrajectory_quadraticHamiltonian_iff hW hK, IsSmallOscillation]
  constructor
  · rintro ⟨hq, hp⟩
    have hπ : (fun i => c (Sum.inr i)) =
        M.map (algebraMap ℝ TimeFunction) *ᵥ fun k => timeDerivative (c (Sum.inl k)) := by
      rw [hq, Matrix.mulVec_mulVec, hMWa, Matrix.one_mulVec]
    refine ⟨?_, hπ⟩
    rw [← hD hπ, hp, neg_add_cancel]
  · rintro ⟨hosc, hπ⟩
    refine ⟨?_, ?_⟩
    · rw [hπ, Matrix.mulVec_mulVec, hWMa, Matrix.one_mulVec]
    · rw [hD hπ]
      exact eq_neg_of_add_eq_zero_left hosc

end Trajectories

end ProjectAInos.Mechanics.NormalModes
