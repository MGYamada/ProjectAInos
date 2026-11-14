/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Conservation
public import ProjectAInos.Mechanics.Jet.Prolongation
public import ProjectAInos.Mechanics.Oscillations.NormalForm
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Lagrangian of small oscillations

The Lagrangian of a system with several degrees of freedom near a position of
stable equilibrium is `L = ½ Σ (mᵢₖ vᵢ vₖ − kᵢₖ qᵢ qₖ)` (Landau–Lifshitz
(23.3)). For symmetric matrices `M` and `K`:

* `JetRing.euler_quadraticLagrangian`: the Euler–Lagrange expressions are
  `−Σₖ kᵢₖ qₖ − Σₖ mᵢₖ q̈ₖ`;
* `StandardJet.isSolution_quadraticLagrangian_iff`: the solutions are the
  solutions of `M ẍ + K x = 0` (23.5);
* `NormalModes.isTrajectory_quadraticHamiltonian_iff_isSolution`: they are the
  trajectories of `H = ½ pᵀ M⁻¹ p + ½ qᵀ K q` with the momenta `p = M ẋ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing Matrix

namespace JetRing

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] (R : JetRing ι J)

/-- The Lagrangian `½ Σ (mᵢₖ vᵢ vₖ − kᵢₖ qᵢ qₖ)` of small oscillations
(Landau–Lifshitz (23.3)). -/
def quadraticLagrangian (M K : Matrix ι ι ℝ) : J :=
  ∑ i, ∑ k, algebraMap ℝ J (M i k / 2) * (R.q i 1 * R.q k 1) -
    ∑ i, ∑ k, algebraMap ℝ J (K i k / 2) * (R.q i 0 * R.q k 0)

variable {R}

/-- The derivative of a quadratic form in the coordinates of the order `n`. -/
theorem d_sum_mul_q_mul_q [DecidableEq ι] (N : Matrix ι ι ℝ) (n : ℕ) (j : ι) :
    R.d j n (∑ i, ∑ k, algebraMap ℝ J (N i k / 2) * (R.q i n * R.q k n)) =
      ∑ k, algebraMap ℝ J ((N j k + N k j) / 2) * R.q k n := by
  have hd (i : ι) : R.d j n (R.q i n) = if i = j then 1 else 0 := by
    split_ifs with h
    · rw [h, R.d_q_self]
    · exact R.d_q_ne i n j n fun h' => h (Prod.mk.inj h').1
  have hterm (i k : ι) : R.d j n (algebraMap ℝ J (N i k / 2) * (R.q i n * R.q k n)) =
      (if k = j then algebraMap ℝ J (N i k / 2) * R.q i n else 0) +
        (if i = j then algebraMap ℝ J (N i k / 2) * R.q k n else 0) := by
    rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, hd, hd]
    simp only [smul_eq_mul, mul_add, mul_ite, mul_one, mul_zero]
  simp only [map_sum, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_mul, ← map_add]
  congr 2
  ring

theorem d_sum_mul_q_mul_q_of_ne (N : Matrix ι ι ℝ) {n l : ℕ} (h : n ≠ l) (j : ι) :
    R.d j l (∑ i, ∑ k, algebraMap ℝ J (N i k / 2) * (R.q i n * R.q k n)) = 0 := by
  have hd (i : ι) : R.d j l (R.q i n) = 0 :=
    R.d_q_ne i n j l fun h' => h (Prod.mk.inj h').2
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, hd, hd]
  simp

theorem orderLE_quadraticLagrangian (M K : Matrix ι ι ℝ) :
    R.OrderLE (R.quadraticLagrangian M K) 1 :=
  (OrderLE.sum fun i _ => OrderLE.sum fun k _ =>
    (orderLE_algebraMap _ 1).mul ((orderLE_q i 1).mul (orderLE_q k 1))).sub
    (OrderLE.sum fun i _ => OrderLE.sum fun k _ =>
      (orderLE_algebraMap _ 1).mul
        (((orderLE_q i 0).mono (by omega)).mul ((orderLE_q k 0).mono (by omega))))

variable [DecidableEq ι] {M K : Matrix ι ι ℝ}

/-- The momenta are `pᵢ = Σₖ mᵢₖ vₖ`. -/
theorem momentum_quadraticLagrangian (hM : M.IsSymm) (K : Matrix ι ι ℝ) (j : ι) :
    R.momentum (R.quadraticLagrangian M K) j = ∑ k, algebraMap ℝ J (M j k) * R.q k 1 := by
  rw [momentum, quadraticLagrangian, map_sub, d_sum_mul_q_mul_q,
    d_sum_mul_q_mul_q_of_ne K (by omega : (0 : ℕ) ≠ 1), sub_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hM.apply j k]
  congr 2
  ring

theorem d_zero_quadraticLagrangian (M : Matrix ι ι ℝ) (hK : K.IsSymm) (j : ι) :
    R.d j 0 (R.quadraticLagrangian M K) = -∑ k, algebraMap ℝ J (K j k) * R.q k 0 := by
  rw [quadraticLagrangian, map_sub, d_sum_mul_q_mul_q,
    d_sum_mul_q_mul_q_of_ne M (by omega : (1 : ℕ) ≠ 0), zero_sub]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hK.apply j k]
  congr 2
  ring

/-- The Euler–Lagrange expressions of the Lagrangian of small oscillations:
`Eᵢ(L) = −Σₖ kᵢₖ qₖ − Σₖ mᵢₖ q̈ₖ`. -/
theorem euler_quadraticLagrangian (hM : M.IsSymm) (hK : K.IsSymm) (j : ι) :
    R.euler j (R.quadraticLagrangian M K) =
      -∑ k, algebraMap ℝ J (K j k) * R.q k 0 - ∑ k, algebraMap ℝ J (M j k) * R.q k 2 := by
  rw [euler_of_orderLE_one (orderLE_quadraticLagrangian M K), d_zero_quadraticLagrangian M hK,
    momentum_quadraticLagrangian hM K, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [SmoothDerivation.map_algebraMap_mul, totalDeriv_q, smul_eq_mul]

end JetRing

namespace StandardJet

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {M K : Matrix ι ι ℝ}

/-- The solutions of the Euler–Lagrange equations of
`½ Σ (mᵢₖ ẋᵢ ẋₖ − kᵢₖ xᵢ xₖ)` are the solutions of `M ẍ + K x = 0`
(Landau–Lifshitz (23.5)). -/
theorem isSolution_quadraticLagrangian_iff (hM : M.IsSymm) (hK : K.IsSymm)
    (γ : ι → TimeFunction) :
    IsSolution ((jetRing ι).quadraticLagrangian M K) γ ↔
      NormalModes.IsSmallOscillation M K γ := by
  have h2 (k : ι) : (timeDerivative^[2]) (γ k) = timeDerivative (timeDerivative (γ k)) := rfl
  rw [NormalModes.IsSmallOscillation, funext_iff]
  refine forall_congr' fun i => ?_
  rw [JetRing.euler_quadraticLagrangian hM hK]
  simp only [SmoothRingHom.map_sub, SmoothRingHom.map_neg, SmoothRingHom.map_sum,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, prolongation_q, Function.iterate_zero,
    id_eq, h2, Pi.add_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

end StandardJet

namespace NormalModes

variable {n : Type*} [Fintype n] [DecidableEq n] {M W K : Matrix n n ℝ}

/-- The inverse of a symmetric matrix is symmetric. -/
theorem isSymm_of_mul_eq_one (hM : M.IsSymm) (hMW : M * W = 1) : W.IsSymm := by
  have h1 : Wᵀ * M = 1 := by
    have h := congrArg Matrix.transpose hMW
    rwa [Matrix.transpose_mul, hM.eq, Matrix.transpose_one] at h
  calc Wᵀ = Wᵀ * (M * W) := by rw [hMW, Matrix.mul_one]
    _ = W := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- The Legendre correspondence for small oscillations: the trajectories of
`H = ½ pᵀ M⁻¹ p + ½ qᵀ K q` are the solutions of the Euler–Lagrange equations
of `L = ½ Σ (mᵢₖ ẋᵢ ẋₖ − kᵢₖ xᵢ xₖ)` together with the momenta `p = M ẋ`. -/
theorem isTrajectory_quadraticHamiltonian_iff_isSolution (hM : M.IsSymm) (hMW : M * W = 1)
    (hK : K.IsSymm) (c : n ⊕ n → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical n) (quadraticHamiltonian W K) c ↔
      StandardJet.IsSolution ((StandardJet.jetRing n).quadraticLagrangian M K)
          (fun i => c (Sum.inl i)) ∧
        (fun i => c (Sum.inr i)) =
          M.map (algebraMap ℝ TimeFunction) *ᵥ fun k => timeDerivative (c (Sum.inl k)) := by
  rw [isTrajectory_quadraticHamiltonian_iff_isSmallOscillation hMW
    (isSymm_of_mul_eq_one hM hMW) hK, StandardJet.isSolution_quadraticLagrangian_iff hM hK]

end NormalModes

end ProjectAInos.Mechanics
