/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Oscillator
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Linearization at an equilibrium

A point `x₀` of the space of generators of a free C-infinity ring is an
equilibrium of the Hamiltonian `H` when the constant curve at `x₀` is a
trajectory. For the canonical bracket this means that `x₀` is a critical point
of `H`.

The linearization of the Hamiltonian vector field at `x₀` is the matrix
`∂_c {x_a, H}(x₀)`. For the canonical bracket it is the Hamiltonian vector field
of the quadratic part `½ Σ H_ab(x₀) ξ_a ξ_b` of `H`, where `ξ_a = x_a − x₀ a`
and `H_ab(x₀)` is the Hessian: the bracket of a generator with the quadratic
part is linear in the displacements with that matrix.

For one degree of freedom and `H = ½ b(q) p² + U(q)`, the point `(q₀, 0)` is an
equilibrium exactly when `U'(q₀) = 0`, and the trajectories of the quadratic
part are free oscillations of `q − q₀` with `ω² = b(q₀) U''(q₀)`
(Landau–Lifshitz §21, with `b = 1/a` the inverse of the coefficient of `q̇²/2`).
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

section Free

variable {κ : Type*}

/-- The value at a time of an observable along a curve is the value of the
observable at the point of the curve. -/
theorem lift_curve_apply (c : κ → TimeFunction) (f : FreeSmoothRing κ) (x : Fin 1 → ℝ) :
    FreeSmoothRing.lift c f x = FreeSmoothRing.lift (fun a => c a x) f := by
  have h : (SmoothOperation.eval x).comp (FreeSmoothRing.lift c) =
      FreeSmoothRing.lift fun a => c a x :=
    FreeSmoothRing.hom_ext fun a => by
      rw [lift_generator]
      change FreeSmoothRing.lift c (generator a) x = c a x
      rw [lift_generator]
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing κ) ℝ => φ f) h

/-- An observable along a constant curve is constant. -/
theorem lift_const_curve (x₀ : κ → ℝ) (f : FreeSmoothRing κ) :
    FreeSmoothRing.lift (fun a => algebraMap ℝ TimeFunction (x₀ a)) f =
      algebraMap ℝ TimeFunction (FreeSmoothRing.lift x₀ f) :=
  TimeFunction.ext_apply_const fun t => lift_curve_apply _ f fun _ => t

/-- The point `x₀` is an equilibrium of `H`, that is, the constant curve at
`x₀` is a trajectory, exactly when the Hamiltonian vector field vanishes at
`x₀`. -/
theorem isTrajectory_const_iff (π : PoissonStructure (FreeSmoothRing κ)) (H : FreeSmoothRing κ)
    (x₀ : κ → ℝ) :
    IsTrajectory π H (fun a => algebraMap ℝ TimeFunction (x₀ a)) ↔
      ∀ a, FreeSmoothRing.lift x₀ (π.bracket (generator a) H) = 0 := by
  refine forall_congr' fun a => ?_
  rw [SmoothDerivation.map_algebraMap, lift_const_curve]
  constructor
  · intro h
    exact (congrArg (fun f : TimeFunction => f fun _ => 0) h).symm
  · intro h
    rw [h, map_zero]

variable [DecidableEq κ]

/-- The displacement `x_a − x₀ a` of a generator from the point `x₀`. -/
def displacement (x₀ : κ → ℝ) (a : κ) : FreeSmoothRing κ :=
  generator a - algebraMap ℝ (FreeSmoothRing κ) (x₀ a)

theorem partialDerivation_displacement (x₀ : κ → ℝ) (c a : κ) :
    partialDerivation c (displacement x₀ a) = if a = c then 1 else 0 := by
  rw [displacement, map_sub, SmoothDerivation.map_algebraMap, sub_zero,
    partialDerivation_generator]

omit [DecidableEq κ] in
theorem lift_displacement {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] (c : κ → A)
    (x₀ : κ → ℝ) (a : κ) :
    FreeSmoothRing.lift c (displacement x₀ a) = c a - algebraMap ℝ A (x₀ a) := by
  rw [displacement, SmoothRingHom.map_sub, lift_generator, SmoothRingHom.map_algebraMap]

/-- The Hessian of `H` at the point `x₀`. -/
def hessian (H : FreeSmoothRing κ) (x₀ : κ → ℝ) (a b : κ) : ℝ :=
  FreeSmoothRing.lift x₀ (partialDerivation a (partialDerivation b H))

theorem hessian_symm (H : FreeSmoothRing κ) (x₀ : κ → ℝ) (a b : κ) :
    hessian H x₀ a b = hessian H x₀ b a := by
  rw [hessian, hessian, partialDerivation_comm]

/-- The matrix of the linearization at `x₀` of the Hamiltonian vector field of
`H`: the entry `(a, c)` is `∂_c {x_a, H}` at `x₀`. -/
def linearization (π : PoissonStructure (FreeSmoothRing κ)) (H : FreeSmoothRing κ)
    (x₀ : κ → ℝ) (a c : κ) : ℝ :=
  FreeSmoothRing.lift x₀ (partialDerivation c (π.bracket (generator a) H))

variable [Fintype κ]

/-- The quadratic part `½ Σ H_ab(x₀) ξ_a ξ_b` of `H` at the point `x₀`. -/
def quadraticPart (H : FreeSmoothRing κ) (x₀ : κ → ℝ) : FreeSmoothRing κ :=
  ∑ a, ∑ b, algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ a b / 2) *
    (displacement x₀ a * displacement x₀ b)

/-- The gradient of the quadratic part is linear in the displacements, with
the Hessian as its matrix. -/
theorem partialDerivation_quadraticPart (H : FreeSmoothRing κ) (x₀ : κ → ℝ) (c : κ) :
    partialDerivation c (quadraticPart H x₀) =
      ∑ a, algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ c a) * displacement x₀ a := by
  have hterm (a b : κ) : partialDerivation c
      (algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ a b / 2) *
        (displacement x₀ a * displacement x₀ b)) =
      (if b = c then algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ a b / 2) *
        displacement x₀ a else 0) +
      if a = c then algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ a b / 2) *
        displacement x₀ b else 0 := by
    rw [SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul,
      partialDerivation_displacement, partialDerivation_displacement]
    split_ifs <;> simp [mul_add]
  have hhalf (a : κ) : algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ a c / 2) +
      algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ c a / 2) =
      algebraMap ℝ (FreeSmoothRing κ) (hessian H x₀ c a) := by
    rw [hessian_symm H x₀ a c, ← map_add, add_halves]
  simp only [quadraticPart, map_sum, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← add_mul, hhalf]

end Free

section Canonical

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- For the canonical bracket the equilibria are the critical points of the
Hamiltonian. -/
theorem isTrajectory_canonical_const_iff (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    IsTrajectory (canonical ι) H (fun a => algebraMap ℝ TimeFunction (x₀ a)) ↔
      ∀ a, FreeSmoothRing.lift x₀ (partialDerivation a H) = 0 := by
  rw [isTrajectory_const_iff, Sum.forall, Sum.forall]
  have hq (i : ι) : (canonical ι).bracket (generator (Sum.inl i)) H =
      partialDerivation (Sum.inr i) H := canonical_q_bracket i H
  have hp (i : ι) : (canonical ι).bracket (generator (Sum.inr i)) H =
      -partialDerivation (Sum.inl i) H := canonical_p_bracket i H
  simp only [hq, hp, SmoothRingHom.map_neg, neg_eq_zero]
  exact and_comm

theorem linearization_canonical_inl (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (i : ι) (c : ι ⊕ ι) :
    linearization (canonical ι) H x₀ (Sum.inl i) c = hessian H x₀ (Sum.inr i) c := by
  have hq : (canonical ι).bracket (generator (Sum.inl i)) H =
      partialDerivation (Sum.inr i) H := canonical_q_bracket i H
  rw [linearization, hq, hessian_symm, hessian]

theorem linearization_canonical_inr (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (i : ι) (c : ι ⊕ ι) :
    linearization (canonical ι) H x₀ (Sum.inr i) c = -hessian H x₀ (Sum.inl i) c := by
  have hp : (canonical ι).bracket (generator (Sum.inr i)) H =
      -partialDerivation (Sum.inl i) H := canonical_p_bracket i H
  rw [linearization, hp, map_neg, SmoothRingHom.map_neg, hessian_symm, hessian]

/-- The Hamiltonian vector field of the quadratic part is linear in the
displacements, and its matrix is the linearization at `x₀` of the Hamiltonian
vector field of `H`. -/
theorem canonical_bracket_quadraticPart (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (a : ι ⊕ ι) :
    (canonical ι).bracket (generator a) (quadraticPart H x₀) =
      ∑ c, algebraMap ℝ (PhaseSpace ι) (linearization (canonical ι) H x₀ a c) *
        displacement x₀ c := by
  rcases a with i | i
  · have hq : (canonical ι).bracket (generator (Sum.inl i)) (quadraticPart H x₀) =
        partialDerivation (Sum.inr i) (quadraticPart H x₀) := canonical_q_bracket i _
    rw [hq, partialDerivation_quadraticPart]
    simp only [linearization_canonical_inl]
  · have hp : (canonical ι).bracket (generator (Sum.inr i)) (quadraticPart H x₀) =
        -partialDerivation (Sum.inl i) (quadraticPart H x₀) := canonical_p_bracket i _
    rw [hp, partialDerivation_quadraticPart, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [linearization_canonical_inr, map_neg]
    ring

/-- `H` and its quadratic part have the same linearization at the point. -/
theorem linearization_quadraticPart (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) (a c : ι ⊕ ι) :
    linearization (canonical ι) (quadraticPart H x₀) x₀ a c =
      linearization (canonical ι) H x₀ a c := by
  rw [linearization, canonical_bracket_quadraticPart, map_sum, Finset.sum_eq_single c]
  · simp only [SmoothDerivation.map_algebraMap_mul, partialDerivation_displacement, ↓reduceIte,
      smul_eq_mul, mul_one, SmoothRingHom.map_algebraMap]
    rfl
  · intro b _ hbc
    simp only [SmoothDerivation.map_algebraMap_mul, partialDerivation_displacement, hbc,
      ↓reduceIte, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The trajectories of the quadratic part are the solutions of the linearized
equations `d/dt ξ_a = Σ_c A_ac ξ_c`. -/
theorem isTrajectory_quadraticPart_iff (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ)
    (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (quadraticPart H x₀) c ↔
      ∀ a, timeDerivative (c a) =
        ∑ b, algebraMap ℝ TimeFunction (linearization (canonical ι) H x₀ a b) *
          (c b - algebraMap ℝ TimeFunction (x₀ b)) := by
  refine forall_congr' fun a => ?_
  rw [canonical_bracket_quadraticPart, SmoothRingHom.map_sum]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, lift_displacement]

end Canonical

/-! ### One degree of freedom -/

section OneDimension

open SmoothOperation

/-- The Hamiltonian `½ b(q) p² + U(q)` of one degree of freedom. The inverse
mass `b` and the potential `U` are smooth functions of the co-ordinate. -/
def naturalHamiltonian (b U : SmoothOperation 1) : PhaseSpace (Fin 1) :=
  algebraMap ℝ (PhaseSpace (Fin 1)) (1 / 2) * (op b (fun _ => q 0) * (p 0 * p 0)) +
    op U fun _ => q 0

/-- The point `(q₀, 0)` of the phase plane: the system at rest at `q₀`. -/
def restPoint (q₀ : ℝ) : Fin 1 ⊕ Fin 1 → ℝ := Sum.elim (fun _ => q₀) fun _ => 0

theorem partialDerivation_inl_op_q (f : SmoothOperation 1) :
    partialDerivation (Sum.inl 0) (op f fun _ : Fin 1 => q (0 : Fin 1)) =
      op (partialDeriv 0 f) fun _ => q 0 := by
  rw [SmoothDerivation.chain, Fin.sum_univ_one, q, partialDerivation_generator_self,
    smul_eq_mul, mul_one]

theorem partialDerivation_inr_op_q (f : SmoothOperation 1) :
    partialDerivation (Sum.inr 0) (op f fun _ : Fin 1 => q (0 : Fin 1)) = 0 := by
  rw [SmoothDerivation.chain, Fin.sum_univ_one, q,
    partialDerivation_generator_of_ne (c := Sum.inr 0) (i := Sum.inl 0) (by simp), smul_zero]

theorem lift_op_q (x₀ : Fin 1 ⊕ Fin 1 → ℝ) (f : SmoothOperation 1) :
    FreeSmoothRing.lift x₀ (op f fun _ : Fin 1 => q (0 : Fin 1)) =
      f fun _ => x₀ (Sum.inl 0) := by
  rw [SmoothRingHom.map_op, real_op, q]
  simp only [lift_generator]

theorem partialDerivation_inl_p :
    partialDerivation (Sum.inl 0) (p (0 : Fin 1)) = 0 :=
  partialDerivation_generator_of_ne (c := Sum.inl 0) (i := Sum.inr 0) (by simp)

theorem partialDerivation_inr_p :
    partialDerivation (Sum.inr 0) (p (0 : Fin 1)) = 1 :=
  partialDerivation_generator_self _

/-- `∂H/∂q = ½ b'(q) p² + U'(q)`. -/
theorem partialDerivation_inl_naturalHamiltonian (b U : SmoothOperation 1) :
    partialDerivation (Sum.inl 0) (naturalHamiltonian b U) =
      algebraMap ℝ (PhaseSpace (Fin 1)) (1 / 2) *
          (op (partialDeriv 0 b) (fun _ => q 0) * (p 0 * p 0)) +
        op (partialDeriv 0 U) fun _ => q 0 := by
  rw [naturalHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_mul, SmoothDerivation.map_mul, partialDerivation_inl_op_q,
    partialDerivation_inl_op_q, partialDerivation_inl_p]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- `∂H/∂p = b(q) p`. -/
theorem partialDerivation_inr_naturalHamiltonian (b U : SmoothOperation 1) :
    partialDerivation (Sum.inr 0) (naturalHamiltonian b U) = op b (fun _ => q 0) * p 0 := by
  have h2 : algebraMap ℝ (PhaseSpace (Fin 1)) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℝ (PhaseSpace (Fin 1))) 2, ← map_mul]
    norm_num
  rw [naturalHamiltonian, map_add, SmoothDerivation.map_algebraMap_mul,
    SmoothDerivation.map_mul, SmoothDerivation.map_mul, partialDerivation_inr_op_q,
    partialDerivation_inr_op_q, partialDerivation_inr_p]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
  linear_combination (op b (fun _ => q 0) * p 0) * h2

theorem hessian_naturalHamiltonian_inl_inl (b U : SmoothOperation 1) (q₀ : ℝ) :
    hessian (naturalHamiltonian b U) (restPoint q₀) (Sum.inl 0) (Sum.inl 0) =
      partialDeriv 0 (partialDeriv 0 U) fun _ => q₀ := by
  rw [hessian, partialDerivation_inl_naturalHamiltonian, map_add,
    SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul, SmoothDerivation.map_mul,
    partialDerivation_inl_op_q, partialDerivation_inl_op_q, partialDerivation_inl_p]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add, SmoothRingHom.map_add,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, lift_op_q, p, lift_generator,
    restPoint, Sum.elim_inl, Sum.elim_inr]
  simp

theorem hessian_naturalHamiltonian_inr_inr (b U : SmoothOperation 1) (q₀ : ℝ) :
    hessian (naturalHamiltonian b U) (restPoint q₀) (Sum.inr 0) (Sum.inr 0) =
      b fun _ => q₀ := by
  rw [hessian, partialDerivation_inr_naturalHamiltonian, SmoothDerivation.map_mul,
    partialDerivation_inr_op_q, partialDerivation_inr_p]
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, lift_op_q, restPoint, Sum.elim_inl]

theorem hessian_naturalHamiltonian_inl_inr (b U : SmoothOperation 1) (q₀ : ℝ) :
    hessian (naturalHamiltonian b U) (restPoint q₀) (Sum.inl 0) (Sum.inr 0) = 0 := by
  rw [hessian, partialDerivation_inr_naturalHamiltonian, SmoothDerivation.map_mul,
    partialDerivation_inl_op_q, partialDerivation_inl_p]
  simp only [smul_eq_mul, mul_zero, zero_add, SmoothRingHom.map_mul, p, lift_generator,
    restPoint, Sum.elim_inr, zero_mul]

theorem hessian_naturalHamiltonian_inr_inl (b U : SmoothOperation 1) (q₀ : ℝ) :
    hessian (naturalHamiltonian b U) (restPoint q₀) (Sum.inr 0) (Sum.inl 0) = 0 := by
  rw [hessian_symm, hessian_naturalHamiltonian_inl_inr]

/-- The system at rest at `q₀` is in equilibrium exactly when `U'(q₀) = 0`. -/
theorem isTrajectory_restPoint_iff (b U : SmoothOperation 1) (q₀ : ℝ) :
    IsTrajectory (canonical (Fin 1)) (naturalHamiltonian b U)
        (fun a => algebraMap ℝ TimeFunction (restPoint q₀ a)) ↔
      partialDeriv 0 U (fun _ => q₀) = 0 := by
  rw [isTrajectory_canonical_const_iff, Sum.forall, Fin.forall_fin_one, Fin.forall_fin_one,
    partialDerivation_inl_naturalHamiltonian, partialDerivation_inr_naturalHamiltonian]
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    lift_op_q, p, lift_generator, restPoint, Sum.elim_inl, Sum.elim_inr, mul_zero, zero_add,
    and_true]

/-- The linearized equations at `(q₀, 0)`: `d/dt ξ = b(q₀) p` and
`ṗ = −U''(q₀) ξ` for the displacement `ξ = q − q₀`. -/
theorem isTrajectory_quadraticPart_naturalHamiltonian_iff (b U : SmoothOperation 1) (q₀ : ℝ)
    (c : Fin 1 ⊕ Fin 1 → TimeFunction) :
    IsTrajectory (canonical (Fin 1)) (quadraticPart (naturalHamiltonian b U) (restPoint q₀)) c ↔
      timeDerivative (c (Sum.inl 0)) =
          algebraMap ℝ TimeFunction (b fun _ => q₀) * c (Sum.inr 0) ∧
        timeDerivative (c (Sum.inr 0)) =
          -(algebraMap ℝ TimeFunction (partialDeriv 0 (partialDeriv 0 U) fun _ => q₀) *
            (c (Sum.inl 0) - algebraMap ℝ TimeFunction q₀)) := by
  rw [isTrajectory_quadraticPart_iff, Sum.forall, Fin.forall_fin_one, Fin.forall_fin_one]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, linearization_canonical_inl,
    linearization_canonical_inr, hessian_naturalHamiltonian_inl_inl,
    hessian_naturalHamiltonian_inr_inr, hessian_naturalHamiltonian_inl_inr,
    hessian_naturalHamiltonian_inr_inl]
  simp only [restPoint, Sum.elim_inl, Sum.elim_inr, map_zero, map_neg, zero_mul, zero_add,
    sub_zero, neg_zero, add_zero, neg_mul]

/-- Small oscillations (Landau–Lifshitz (21.5), (21.6)): along a solution of
the linearized equations at `(q₀, 0)`, the displacement `q − q₀` is a free
oscillation with `ω² = b(q₀) U''(q₀)`. -/
theorem isHarmonic_of_isTrajectory_quadraticPart (b U : SmoothOperation 1) (q₀ : ℝ) {ω : ℝ}
    (hω : ω ^ 2 = b (fun _ => q₀) * partialDeriv 0 (partialDeriv 0 U) fun _ => q₀)
    {c : Fin 1 ⊕ Fin 1 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 1))
      (quadraticPart (naturalHamiltonian b U) (restPoint q₀)) c) :
    IsHarmonic ω (c (Sum.inl 0) - algebraMap ℝ TimeFunction q₀) := by
  obtain ⟨hq, hp⟩ := (isTrajectory_quadraticPart_naturalHamiltonian_iff b U q₀ c).mp h
  unfold IsHarmonic
  rw [map_sub, SmoothDerivation.map_algebraMap, sub_zero, hq,
    SmoothDerivation.map_algebraMap_mul, smul_eq_mul, hp, hω, map_mul]
  ring

/-- At a non-degenerate minimum of the potential, with a positive mass, the
frequency of the small oscillations is `ω = √(b(q₀) U''(q₀))`, that is,
`√(k/m)` with `k = U''(q₀)` and `m = 1/b(q₀)`. -/
theorem isHarmonic_sqrt_of_isTrajectory_quadraticPart (b U : SmoothOperation 1) (q₀ : ℝ)
    (hb : 0 < b fun _ => q₀) (hk : 0 < partialDeriv 0 (partialDeriv 0 U) fun _ => q₀)
    {c : Fin 1 ⊕ Fin 1 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 1))
      (quadraticPart (naturalHamiltonian b U) (restPoint q₀)) c) :
    IsHarmonic (Real.sqrt (b (fun _ => q₀) * partialDeriv 0 (partialDeriv 0 U) fun _ => q₀))
      (c (Sum.inl 0) - algebraMap ℝ TimeFunction q₀) :=
  isHarmonic_of_isTrajectory_quadraticPart b U q₀ (Real.sq_sqrt (mul_pos hb hk).le) h

end OneDimension

/-! ### The pendulum -/

section Pendulum

open SmoothOperation

/-- The Hamiltonian `p²/(2 m l²) − m g l cos q` of a pendulum of mass `m` and
length `l` in a field `g`. -/
def pendulumHamiltonian (m l g : ℝ) : PhaseSpace (Fin 1) :=
  naturalHamiltonian (algebraMap ℝ (SmoothOperation 1) (m * l ^ 2)⁻¹)
    (algebraMap ℝ (SmoothOperation 1) (-(m * g * l)) * TimeFunction.cos)

theorem partialDeriv_pendulumPotential (μ : ℝ) (x : Fin 1 → ℝ) :
    partialDeriv 0 (algebraMap ℝ (SmoothOperation 1) (-μ) * TimeFunction.cos) x =
      μ * Real.sin (x 0) := by
  change timeDerivative (algebraMap ℝ TimeFunction (-μ) * TimeFunction.cos) x = _
  rw [SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_cos, smul_eq_mul]
  change -μ * -Real.sin (x 0) = _
  ring

theorem partialDeriv_partialDeriv_pendulumPotential (μ : ℝ) (x : Fin 1 → ℝ) :
    partialDeriv 0 (partialDeriv 0 (algebraMap ℝ (SmoothOperation 1) (-μ) * TimeFunction.cos))
        x = μ * Real.cos (x 0) := by
  change timeDerivative (timeDerivative (algebraMap ℝ TimeFunction (-μ) * TimeFunction.cos)) x =
    _
  rw [SmoothDerivation.map_algebraMap_mul, TimeFunction.timeDerivative_cos, smul_eq_mul,
    SmoothDerivation.map_algebraMap_mul, map_neg timeDerivative,
    TimeFunction.timeDerivative_sin, smul_eq_mul]
  change -μ * -Real.cos (x 0) = _
  ring

/-- The pendulum hanging at rest is in equilibrium. -/
theorem isTrajectory_pendulum_restPoint (m l g : ℝ) :
    IsTrajectory (canonical (Fin 1)) (pendulumHamiltonian m l g)
      fun a => algebraMap ℝ TimeFunction (restPoint 0 a) := by
  rw [pendulumHamiltonian, isTrajectory_restPoint_iff, partialDeriv_pendulumPotential,
    Real.sin_zero, mul_zero]

/-- The small oscillations of a pendulum have `ω² = g/l`: the frequency does
not depend on the mass. -/
theorem isHarmonic_pendulum {m l g ω : ℝ} (hm : m ≠ 0) (hl : l ≠ 0) (hω : ω ^ 2 = g / l)
    {c : Fin 1 ⊕ Fin 1 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 1))
      (quadraticPart (pendulumHamiltonian m l g) (restPoint 0)) c) :
    IsHarmonic ω (c (Sum.inl 0)) := by
  have hc : c (Sum.inl 0) = c (Sum.inl 0) - algebraMap ℝ TimeFunction 0 := by
    rw [map_zero, sub_zero]
  rw [hc]
  refine isHarmonic_of_isTrajectory_quadraticPart _ _ 0 ?_ h
  rw [hω, partialDeriv_partialDeriv_pendulumPotential, Real.cos_zero]
  change g / l = (m * l ^ 2)⁻¹ * (m * g * l * 1)
  field_simp

end Pendulum

end ProjectAInos.Mechanics
