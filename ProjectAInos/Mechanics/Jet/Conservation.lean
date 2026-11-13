/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Noether
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Natural Lagrangians and the classical conservation laws

For the natural Lagrangian `L = Σᵢ ½ mᵢ vᵢ² − U` in a jet ring, with a potential
`U` of order zero, the Euler–Lagrange expressions are Newton's equations
`Eᵢ(L) = −∂ᵢU − mᵢ aᵢ`. The Noether identity then gives the conservation laws
of Landau–Lifshitz §§6–9:

* energy, when `∂ₜU = 0`;
* momentum along a direction in which the potential is invariant;
* the centre-of-mass integral `u · (t P − Σ m q)`, for the same potentials;
* the charge of a linear symmetry `ξᵢ = Σⱼ Aᵢⱼ qⱼ` with `mᵢ Aᵢⱼ + mⱼ Aⱼᵢ = 0`,
  and in particular the angular momentum of particles in space.

Each law says that a total derivative lies in the Euler–Lagrange ideal. These
are identities in an abstract jet ring; they involve no path.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.JetRing

open SmoothAlgebra

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] (R : JetRing ι J)

/-- The natural Lagrangian `Σᵢ ½ mᵢ vᵢ² − U`. -/
def naturalLagrangian (m : ι → ℝ) (U : J) : J :=
  ∑ i, algebraMap ℝ J (m i / 2) * (R.q i 1 * R.q i 1) - U

variable {R}

omit [SmoothRing J] in
theorem algebraMap_half_mul_two (r : ℝ) : algebraMap ℝ J (r / 2) * 2 = algebraMap ℝ J r := by
  have h2 : (2 : J) = algebraMap ℝ J 2 := (map_ofNat (algebraMap ℝ J) 2).symm
  rw [h2, ← map_mul]
  congr 1
  ring

theorem orderLE_naturalLagrangian (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) :
    R.OrderLE (R.naturalLagrangian m U) 1 :=
  (OrderLE.sum fun i _ =>
    (orderLE_algebraMap _ 1).mul ((orderLE_q i 1).mul (orderLE_q i 1))).sub (hU.mono (by omega))

theorem d_zero_naturalLagrangian (m : ι → ℝ) (U : J) (j : ι) :
    R.d j 0 (R.naturalLagrangian m U) = -R.d j 0 U := by
  have hq (i : ι) : R.d j 0 (R.q i 1) = 0 :=
    R.d_q_ne i 1 j 0 fun h => by
      have : (1 : ℕ) = 0 := (Prod.mk.inj h).2
      omega
  rw [naturalLagrangian, map_sub, map_sum, Finset.sum_eq_zero, zero_sub]
  intro i _
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, hq]
  simp

theorem dt_naturalLagrangian (m : ι → ℝ) (U : J) :
    R.dt (R.naturalLagrangian m U) = -R.dt U := by
  rw [naturalLagrangian, map_sub, map_sum, Finset.sum_eq_zero, zero_sub]
  intro i _
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
    R.dt_q]
  simp

/-- The momenta of the natural Lagrangian are `pᵢ = mᵢ vᵢ`. -/
theorem momentum_naturalLagrangian (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (j : ι) :
    R.momentum (R.naturalLagrangian m U) j = algebraMap ℝ J (m j) * R.q j 1 := by
  rw [momentum, naturalLagrangian, map_sub, hU j 1 (by omega), sub_zero, map_sum,
    Finset.sum_eq_single j]
  · rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
      R.d_q_self, ← algebraMap_half_mul_two (m j)]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    ring
  · intro i _ hij
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
      R.d_q_ne i 1 j 1 fun h => hij (Prod.mk.inj h).1]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Newton's equations in the jet ring: `Eᵢ(L) = −∂ᵢU − mᵢ aᵢ` (Landau–Lifshitz §5). -/
theorem euler_naturalLagrangian (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (j : ι) :
    R.euler j (R.naturalLagrangian m U) = -R.d j 0 U - algebraMap ℝ J (m j) * R.q j 2 := by
  rw [euler_of_orderLE_one (orderLE_naturalLagrangian m hU), d_zero_naturalLagrangian,
    momentum_naturalLagrangian m hU, SmoothDerivation.map_mul, totalDeriv_q,
    totalDeriv_algebraMap]
  simp

/-- The energy of the natural Lagrangian is `Σᵢ ½ mᵢ vᵢ² + U`. -/
theorem energy_naturalLagrangian (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) :
    R.energy (R.naturalLagrangian m U) =
      ∑ i, algebraMap ℝ J (m i / 2) * (R.q i 1 * R.q i 1) + U := by
  have h (i : ι) : R.q i 1 * (algebraMap ℝ J (m i) * R.q i 1) =
      algebraMap ℝ J (m i / 2) * (R.q i 1 * R.q i 1) +
        algebraMap ℝ J (m i / 2) * (R.q i 1 * R.q i 1) := by
    rw [← algebraMap_half_mul_two (m i)]
    ring
  simp only [energy, momentum_naturalLagrangian m hU, h, Finset.sum_add_distrib]
  rw [naturalLagrangian]
  ring

/-- Conservation of energy in a time-independent potential (Landau–Lifshitz §6). -/
theorem conserved_energy_naturalLagrangian (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0)
    (ht : R.dt U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, algebraMap ℝ J (m i / 2) * (R.q i 1 * R.q i 1) + U) := by
  rw [← energy_naturalLagrangian m hU]
  exact conserved_energy (orderLE_naturalLagrangian m hU)
    (by rw [dt_naturalLagrangian, ht, neg_zero])

/-- Conservation of momentum along a direction in which the potential is
invariant (Landau–Lifshitz §7). -/
theorem conserved_momentum (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (u : ι → ℝ)
    (hinv : ∑ i, algebraMap ℝ J (u i) * R.d i 0 U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 1)) := by
  have hL := orderLE_naturalLagrangian (R := R) m hU
  have h := conserved_of_prolong_eq_zero hL (fun i => algebraMap ℝ J (u i)) (by
    rw [prolong_of_orderLE_one hL]
    simp only [totalDeriv_algebraMap, zero_mul, add_zero, d_zero_naturalLagrangian, mul_neg,
      Finset.sum_neg_distrib, hinv, neg_zero])
  simpa only [momentum_naturalLagrangian m hU] using h

/-- A time coordinate has unit total derivative. -/
theorem totalDeriv_time {τ : J} (hτt : R.dt τ = 1) (hτq : ∀ i k, R.d i k τ = 0) :
    R.totalDeriv τ = 1 := by
  rw [totalDeriv_eq_sum (N := 0) fun i k _ => hτq i k, hτt]
  simp [hτq]

/-- The centre-of-mass integral (Landau–Lifshitz §8). For a potential invariant
under translation along `u`, the boost `ξ = t u` changes the Lagrangian by the
total derivative of `Σᵢ uᵢ mᵢ qᵢ`, and `u · (t P − Σ m q)` is conserved. -/
theorem conserved_boost (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) {τ : J}
    (hτt : R.dt τ = 1) (hτq : ∀ i k, R.d i k τ = 0) (u : ι → ℝ)
    (hinv : ∑ i, algebraMap ℝ J (u i) * R.d i 0 U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, τ * algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 1) -
        ∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 0)) := by
  have hL := orderLE_naturalLagrangian (R := R) m hU
  have hξ (i : ι) : R.totalDeriv (τ * algebraMap ℝ J (u i)) = algebraMap ℝ J (u i) := by
    rw [SmoothDerivation.map_mul, totalDeriv_algebraMap, totalDeriv_time hτt hτq]
    simp
  have hF : R.totalDeriv (∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 0)) =
      ∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 1) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, totalDeriv_q, totalDeriv_algebraMap,
      totalDeriv_algebraMap]
    simp
  have hτinv : ∑ i, τ * algebraMap ℝ J (u i) * R.d i 0 U = 0 := by
    have h := congrArg (fun x => τ * x) hinv
    simpa only [Finset.mul_sum, mul_zero, mul_assoc] using h
  have h := conserved_noetherCharge hL (fun i => τ * algebraMap ℝ J (u i))
    (F := ∑ i, algebraMap ℝ J (u i) * (algebraMap ℝ J (m i) * R.q i 0)) (by
      rw [prolong_of_orderLE_one hL, hF]
      simp only [hξ, d_zero_naturalLagrangian, momentum_naturalLagrangian m hU, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib, hτinv, neg_zero, zero_add])
  simpa only [momentum_naturalLagrangian m hU] using h

/-- A linear infinitesimal symmetry `ξᵢ = Σⱼ Aᵢⱼ qⱼ` with `mᵢ Aᵢⱼ + mⱼ Aⱼᵢ = 0`
conserves `Σᵢ ξᵢ pᵢ` whenever the potential is invariant. Rotations are of
this form (Landau–Lifshitz §9). -/
theorem conserved_linear (m : ι → ℝ) {U : J} (hU : R.OrderLE U 0) (A : ι → ι → ℝ)
    (hA : ∀ i j, m i * A i j + m j * A j i = 0)
    (hinv : ∑ i, (∑ j, algebraMap ℝ J (A i j) * R.q j 0) * R.d i 0 U = 0) :
    R.Conserved (R.naturalLagrangian m U)
      (∑ i, (∑ j, algebraMap ℝ J (A i j) * R.q j 0) * (algebraMap ℝ J (m i) * R.q i 1)) := by
  have hL := orderLE_naturalLagrangian (R := R) m hU
  have hξ (i : ι) : R.totalDeriv (∑ j, algebraMap ℝ J (A i j) * R.q j 0) =
      ∑ j, algebraMap ℝ J (A i j) * R.q j 1 := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SmoothDerivation.map_mul, totalDeriv_q, totalDeriv_algebraMap]
    simp
  -- The kinetic term is a symmetric form paired with an antisymmetric matrix.
  let S : J := ∑ i, ∑ j, algebraMap ℝ J (m i * A i j) * (R.q i 1 * R.q j 1)
  have hSS : S + S = 0 := by
    have hswap : S = ∑ i, ∑ j, algebraMap ℝ J (m j * A j i) * (R.q i 1 * R.q j 1) := by
      simp only [S]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    nth_rewrite 2 [hswap]
    simp only [S]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← add_mul, ← map_add, hA, map_zero, zero_mul]
  have hS : S = 0 := by
    have h2 : (2 : ℝ) • S = 0 := by rw [two_smul, hSS]
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hkin : ∑ i, (∑ j, algebraMap ℝ J (A i j) * R.q j 1) *
      (algebraMap ℝ J (m i) * R.q i 1) = S := by
    simp only [S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have h := conserved_of_prolong_eq_zero hL (fun i => ∑ j, algebraMap ℝ J (A i j) * R.q j 0) (by
    rw [prolong_of_orderLE_one hL]
    simp only [hξ, d_zero_naturalLagrangian, momentum_naturalLagrangian m hU, mul_neg,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, hinv, neg_zero, zero_add, hkin, hS])
  simpa only [momentum_naturalLagrangian m hU] using h

section AngularMomentum

open Matrix

variable {κ : Type*} [Fintype κ] {R : JetRing (κ × Fin 3) J}

/-- The position of particle `a`, a vector with entries in the jet ring. -/
def position (R : JetRing (κ × Fin 3) J) (a : κ) : Fin 3 → J := fun r => R.q (a, r) 0

/-- The velocity of particle `a`. -/
def velocity (R : JetRing (κ × Fin 3) J) (a : κ) : Fin 3 → J := fun r => R.q (a, r) 1

/-- A real axis, as a vector with constant entries in the jet ring. -/
def axis (J : Type*) [CommRing J] [Algebra ℝ J] (n : Fin 3 → ℝ) : Fin 3 → J :=
  fun r => algebraMap ℝ J (n r)

/-- The total derivative of `n × qₐ` is `n × vₐ`. -/
theorem totalDeriv_axis_cross_position (n : Fin 3 → ℝ) (a : κ) (r : Fin 3) :
    R.totalDeriv ((axis J n ⨯₃ R.position a) r) = (axis J n ⨯₃ R.velocity a) r := by
  fin_cases r <;>
    simp [cross_apply, axis, position, velocity, SmoothDerivation.map_mul]

/-- Conservation of angular momentum about the axis `n` (Landau–Lifshitz §9).
For particles in space with masses `M a` and a potential invariant under
rotation about `n`, the Noether charge `Σₐ (n × qₐ) · pₐ` is conserved. -/
theorem conserved_angularMomentum (M : κ → ℝ) {U : J} (hU : R.OrderLE U 0) (n : Fin 3 → ℝ)
    (hinv : ∑ a, ∑ r, (axis J n ⨯₃ R.position a) r * R.d (a, r) 0 U = 0) :
    R.Conserved (R.naturalLagrangian (fun i => M i.1) U)
      (∑ a, ∑ r, (axis J n ⨯₃ R.position a) r * (algebraMap ℝ J (M a) * R.velocity a r)) := by
  have hL := orderLE_naturalLagrangian (R := R) (fun i => M i.1) hU
  have hkin (a : κ) : ∑ r, (axis J n ⨯₃ R.velocity a) r *
      (algebraMap ℝ J (M a) * R.velocity a r) = 0 := by
    simp only [Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  have h := conserved_of_prolong_eq_zero hL
    (fun i : κ × Fin 3 => (axis J n ⨯₃ R.position i.1) i.2) (by
      rw [prolong_of_orderLE_one hL, Fintype.sum_prod_type]
      simp only [totalDeriv_axis_cross_position, d_zero_naturalLagrangian,
        momentum_naturalLagrangian (fun i : κ × Fin 3 => M i.1) hU, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib, hinv, neg_zero, zero_add]
      exact Finset.sum_eq_zero fun a _ => hkin a)
  rw [Fintype.sum_prod_type] at h
  simpa only [momentum_naturalLagrangian (fun i : κ × Fin 3 => M i.1) hU, velocity] using h

omit [SmoothRing J] in
/-- The Noether charge of a rotation is the component of the angular momentum
along the axis: `(n × q) · p = n · (q × p)`. -/
theorem axis_cross_dotProduct (n : Fin 3 → ℝ) (x p : Fin 3 → J) :
    ∑ r, (axis J n ⨯₃ x) r * p r = axis J n ⬝ᵥ (x ⨯₃ p) := by
  simp only [Fin.sum_univ_three, cross_apply, dotProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

end AngularMomentum

end ProjectAInos.Mechanics.JetRing
