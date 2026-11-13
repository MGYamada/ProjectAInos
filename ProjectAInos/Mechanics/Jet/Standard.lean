/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Conservation
public import ProjectAInos.SmoothAlgebra.FreeDerivation
import Mathlib.Tactic.Ring

/-!
# The standard jet ring

The standard jet ring is the ring of smooth functions of time and of finitely
many of the derivatives `qᵢ⁽ᵏ⁾`: the free C-infinity ring on the time
coordinate and the jet coordinates. Its coordinate vector fields make it a jet
ring, which shows that the abstract structure is not vacuous. No analysis is
used: the vector fields come from the universal property of the free ring.

The examples are computed in this model and have nonzero values: the Euler
operator of second-order elements, Newton's equation and the energy identity of
the isotropic oscillator, and the centre-of-mass integral of free particles.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

/-- The standard jet ring over coordinates `ι`: the free C-infinity ring on the
time coordinate `none` and the jet coordinates `some (i, k)`. -/
abbrev StandardJet (ι : Type*) := FreeSmoothRing (Option (ι × ℕ))

namespace StandardJet

variable {ι : Type*} [DecidableEq ι]

/-- The order of a generator. The time coordinate has order zero. -/
def generatorOrder : Option (ι × ℕ) → ℕ
  | none => 0
  | some p => p.2

variable (ι) in
/-- The jet-ring structure of the standard jet ring. -/
def jetRing : JetRing ι (StandardJet ι) where
  dt := FreeSmoothRing.partialDerivation none
  d i k := FreeSmoothRing.partialDerivation (some (i, k))
  q i k := FreeSmoothRing.generator (some (i, k))
  d_q_self _ _ := FreeSmoothRing.partialDerivation_generator_self _
  d_q_ne _ _ _ _ h :=
    FreeSmoothRing.partialDerivation_generator_of_ne fun hc => h (Option.some.inj hc)
  dt_q _ _ := FreeSmoothRing.partialDerivation_generator_of_ne (Option.some_ne_none _)
  dt_comm _ _ F := FreeSmoothRing.partialDerivation_comm _ _ F
  d_comm _ _ _ _ F := FreeSmoothRing.partialDerivation_comm _ _ F
  finite_order F := by
    obtain ⟨S, hS⟩ := FreeSmoothRing.exists_finset_partialDerivation_eq_zero F
    refine ⟨S.sup generatorOrder, fun i k hk => hS _ fun hmem => ?_⟩
    have hle : generatorOrder (some (i, k)) ≤ S.sup generatorOrder := Finset.le_sup hmem
    exact absurd hle (not_le.mpr hk)

variable (ι) in
/-- The time coordinate of the standard jet ring. -/
def time : StandardJet ι := FreeSmoothRing.generator none

theorem dt_time : (jetRing ι).dt (time ι) = 1 :=
  FreeSmoothRing.partialDerivation_generator_self none

theorem d_time (i : ι) (k : ℕ) : (jetRing ι).d i k (time ι) = 0 :=
  FreeSmoothRing.partialDerivation_generator_of_ne (Option.some_ne_none _).symm

variable [Fintype ι]

/-- The time coordinate has unit total derivative. -/
theorem totalDeriv_time : (jetRing ι).totalDeriv (time ι) = 1 :=
  JetRing.totalDeriv_time dt_time d_time

/-- The total derivative of the standard jet ring is the vector field sending
time to one and each jet coordinate to the next one. -/
theorem totalDeriv_eq_derivation :
    (jetRing ι).totalDeriv = FreeSmoothRing.derivation fun c =>
      match c with
      | none => 1
      | some (i, k) => (jetRing ι).q i (k + 1) := by
  refine FreeSmoothRing.derivation_ext fun c => ?_
  rw [FreeSmoothRing.derivation_generator]
  cases c with
  | none => exact totalDeriv_time
  | some p => exact JetRing.totalDeriv_q (R := jetRing ι) p.1 p.2

section Examples

local notation "R" => jetRing ι

/-- The Euler operator of `q q̈` is `2 q̈`: the second-order term contributes. -/
theorem euler_q_mul_acceleration (i : ι) :
    (R).euler i ((R).q i 0 * (R).q i 2) = 2 * (R).q i 2 := by
  have hord : (R).OrderLE ((R).q i 0 * (R).q i 2) 2 :=
    ((JetRing.orderLE_q i 0).mono (by omega)).mul (JetRing.orderLE_q i 2)
  have h0 : (R).d i 0 ((R).q i 2) = 0 :=
    (R).d_q_ne i 2 i 0 fun h => absurd (Prod.mk.inj h).2 (by omega)
  have h1a : (R).d i 1 ((R).q i 0) = 0 :=
    (R).d_q_ne i 0 i 1 fun h => absurd (Prod.mk.inj h).2 (by omega)
  have h1b : (R).d i 1 ((R).q i 2) = 0 :=
    (R).d_q_ne i 2 i 1 fun h => absurd (Prod.mk.inj h).2 (by omega)
  have h2 : (R).d i 2 ((R).q i 0) = 0 :=
    (R).d_q_ne i 0 i 2 fun h => absurd (Prod.mk.inj h).2 (by omega)
  rw [JetRing.euler_eq_sum hord, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [SmoothDerivation.map_mul, (R).d_q_self, h0, h1a, h1b, h2, smul_eq_mul, mul_zero,
    mul_one, add_zero, zero_add, pow_zero, one_mul, Function.iterate_zero, id_eq, pow_one,
    map_zero, Function.iterate_succ, Function.comp_apply, JetRing.totalDeriv_q]
  ring

/-- The Euler operator of `q̇²` is `−2 q̈`. Together with the previous example
this is `Eᵢ(D(q q̇)) = 0`, since `D(q q̇) = q̇² + q q̈`. -/
theorem euler_velocity_sq (i : ι) :
    (R).euler i ((R).q i 1 * (R).q i 1) = -(2 * (R).q i 2) := by
  have hord : (R).OrderLE ((R).q i 1 * (R).q i 1) 1 :=
    (JetRing.orderLE_q i 1).mul (JetRing.orderLE_q i 1)
  have h0 : (R).d i 0 ((R).q i 1) = 0 :=
    (R).d_q_ne i 1 i 0 fun h => absurd (Prod.mk.inj h).2 (by omega)
  rw [JetRing.euler_of_orderLE_one hord, JetRing.momentum, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, h0, (R).d_q_self]
  simp only [smul_eq_mul, mul_zero, mul_one, add_zero, map_add, JetRing.totalDeriv_q]
  ring

/-- The isotropic oscillator potential `Σᵢ ½ k qᵢ²`. -/
def oscillatorPotential (k : ℝ) : StandardJet ι :=
  ∑ i, algebraMap ℝ (StandardJet ι) (k / 2) * ((R).q i 0 * (R).q i 0)

theorem orderLE_oscillatorPotential (k : ℝ) : (R).OrderLE (oscillatorPotential (ι := ι) k) 0 :=
  JetRing.OrderLE.sum fun i _ =>
    (JetRing.orderLE_algebraMap _ 0).mul ((JetRing.orderLE_q i 0).mul (JetRing.orderLE_q i 0))

theorem d_zero_oscillatorPotential (k : ℝ) (j : ι) :
    (R).d j 0 (oscillatorPotential (ι := ι) k) =
      algebraMap ℝ (StandardJet ι) k * (R).q j 0 := by
  rw [oscillatorPotential, map_sum, Finset.sum_eq_single j]
  · rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
      (R).d_q_self, ← JetRing.algebraMap_half_mul_two k]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    ring
  · intro i _ hij
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
      (R).d_q_ne i 0 j 0 fun h => hij (Prod.mk.inj h).1]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem dt_oscillatorPotential (k : ℝ) : (R).dt (oscillatorPotential (ι := ι) k) = 0 := by
  rw [oscillatorPotential, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
    (R).dt_q]
  simp

/-- Newton's equation of the isotropic oscillator: `Eᵢ(L) = −k qᵢ − m q̈ᵢ`. -/
theorem euler_oscillator (m : ι → ℝ) (k : ℝ) (j : ι) :
    (R).euler j ((R).naturalLagrangian m (oscillatorPotential k)) =
      -(algebraMap ℝ (StandardJet ι) k * (R).q j 0) -
        algebraMap ℝ (StandardJet ι) (m j) * (R).q j 2 := by
  rw [JetRing.euler_naturalLagrangian m (orderLE_oscillatorPotential k),
    d_zero_oscillatorPotential]

/-- The Euler–Lagrange expression of the oscillator is not zero: its
derivative with respect to the acceleration is `−m`. -/
theorem d_two_euler_oscillator (m : ι → ℝ) (k : ℝ) (j : ι) :
    (R).d j 2 ((R).euler j ((R).naturalLagrangian m (oscillatorPotential k))) =
      -algebraMap ℝ (StandardJet ι) (m j) := by
  have h : (R).d j 2 ((R).q j 0) = 0 :=
    (R).d_q_ne j 0 j 2 fun h => absurd (Prod.mk.inj h).2 (by omega)
  rw [euler_oscillator]
  simp only [map_sub, map_neg, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, h,
    (R).d_q_self, smul_eq_mul, mul_zero, mul_one, add_zero, neg_zero, zero_sub]

/-- The energy of the isotropic oscillator is conserved. -/
theorem conserved_energy_oscillator (m : ι → ℝ) (k : ℝ) :
    (R).Conserved ((R).naturalLagrangian m (oscillatorPotential k))
      (∑ i, algebraMap ℝ (StandardJet ι) (m i / 2) * ((R).q i 1 * (R).q i 1) +
        oscillatorPotential k) :=
  JetRing.conserved_energy_naturalLagrangian m (orderLE_oscillatorPotential k)
    (dt_oscillatorPotential k)

/-- Free particles: the centre-of-mass integral `u · (t P − Σ m q)` is conserved. -/
theorem conserved_boost_free (m u : ι → ℝ) :
    (R).Conserved ((R).naturalLagrangian m 0)
      (∑ i, time ι * algebraMap ℝ (StandardJet ι) (u i) *
          (algebraMap ℝ (StandardJet ι) (m i) * (R).q i 1) -
        ∑ i, algebraMap ℝ (StandardJet ι) (u i) *
          (algebraMap ℝ (StandardJet ι) (m i) * (R).q i 0)) :=
  JetRing.conserved_boost m (fun _ _ _ => map_zero _) dt_time d_time u (by simp)

end Examples

end StandardJet

end ProjectAInos.Mechanics
