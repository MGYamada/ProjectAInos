/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Conservation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Natural Lagrangians with a position-dependent kinetic form

The general natural Lagrangian is `L = ½ Σᵢₖ aᵢₖ vᵢ vₖ − U`, where the
coefficients `aᵢₖ` and the potential `U` have order zero: they depend on time
and the coordinates, not on the velocities (Landau–Lifshitz §5). For a
symmetric `a`:

* the momenta are `pᵢ = Σₖ aᵢₖ vₖ`;
* Lagrange's equations are
  `Eᵢ(L) = −Σₖ aᵢₖ q̈ₖ − Σⱼₖ (∂ⱼaᵢₖ − ½ ∂ᵢaⱼₖ) vⱼ vₖ − Σₖ ∂ₜaᵢₖ vₖ − ∂ᵢU`;
* the energy is `½ Σᵢₖ aᵢₖ vᵢ vₖ + U`, and it is conserved when `a` and `U` do
  not depend explicitly on time;
* if `b` is inverse to `a`, the energy is `½ Σᵢⱼ bᵢⱼ pᵢ pⱼ + U`.

A diagonal constant `a` gives the Lagrangian of particles with constant masses.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.JetRing

open SmoothAlgebra

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] (R : JetRing ι J)

/-- The kinetic form `Σᵢₖ aᵢₖ vᵢ vₖ`. -/
def kineticForm (a : ι → ι → J) : J := ∑ i, ∑ k, a i k * (R.q i 1 * R.q k 1)

/-- The natural Lagrangian `½ Σᵢₖ aᵢₖ vᵢ vₖ − U` with kinetic coefficients `a`. -/
def metricLagrangian (a : ι → ι → J) (U : J) : J :=
  algebraMap ℝ J (1 / 2) * R.kineticForm a - U

variable {R}

omit [SmoothRing J] in
theorem algebraMap_half_add_half : algebraMap ℝ J (1 / 2) + algebraMap ℝ J (1 / 2) = 1 := by
  rw [← map_add, ← map_one (algebraMap ℝ J)]
  congr 1
  norm_num

/-- The total derivative of an element of order zero. -/
theorem totalDeriv_of_orderLE_zero {F : J} (h : R.OrderLE F 0) :
    R.totalDeriv F = R.dt F + ∑ i, R.q i 1 * R.d i 0 F := by
  rw [totalDeriv_eq_sum h, Finset.sum_range_one]

/-- A cyclic co-ordinate: if the Lagrangian does not depend on `qᵢ`, the
conjugate momentum is conserved (Landau–Lifshitz §7). -/
theorem conserved_momentum_of_cyclic {L : J} (hL : R.OrderLE L 1) (i : ι)
    (h : R.d i 0 L = 0) : R.Conserved L (R.momentum L i) := by
  have he := euler_of_orderLE_one hL i
  rw [h, zero_sub] at he
  rw [Conserved, ← neg_neg (R.totalDeriv (R.momentum L i)), ← he]
  exact neg_mem (euler_mem L i)

variable {a : ι → ι → J} {U : J}

omit [Fintype ι] in
theorem d_zero_q_one (i j : ι) : R.d j 0 (R.q i 1) = 0 :=
  R.d_q_ne i 1 j 0 fun hc => absurd (Prod.mk.inj hc).2 (by norm_num)

theorem orderLE_kineticForm (ha : ∀ i k, R.OrderLE (a i k) 0) : R.OrderLE (R.kineticForm a) 1 :=
  OrderLE.sum fun i _ => OrderLE.sum fun k _ =>
    ((ha i k).mono (Nat.zero_le 1)).mul ((orderLE_q i 1).mul (orderLE_q k 1))

theorem orderLE_metricLagrangian (ha : ∀ i k, R.OrderLE (a i k) 0) (hU : R.OrderLE U 0) :
    R.OrderLE (R.metricLagrangian a U) 1 :=
  ((orderLE_algebraMap _ 1).mul (orderLE_kineticForm ha)).sub (hU.mono (Nat.zero_le 1))

/-- The derivative of the kinetic form with respect to a coordinate. -/
theorem d_zero_kineticForm (a : ι → ι → J) (i : ι) :
    R.d i 0 (R.kineticForm a) = ∑ j, ∑ k, R.d i 0 (a j k) * (R.q j 1 * R.q k 1) := by
  simp only [kineticForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, d_zero_q_one, d_zero_q_one]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- The explicit time derivative of the kinetic form. -/
theorem dt_kineticForm (a : ι → ι → J) :
    R.dt (R.kineticForm a) = ∑ j, ∑ k, R.dt (a j k) * (R.q j 1 * R.q k 1) := by
  simp only [kineticForm, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, R.dt_q, R.dt_q]
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add]
  ring

theorem dt_metricLagrangian (a : ι → ι → J) (U : J) :
    R.dt (R.metricLagrangian a U) =
      algebraMap ℝ J (1 / 2) * ∑ j, ∑ k, R.dt (a j k) * (R.q j 1 * R.q k 1) - R.dt U := by
  rw [metricLagrangian, map_sub, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap,
    dt_kineticForm]
  simp only [smul_eq_mul, mul_zero, add_zero]

/-- The total derivative of `Σₖ aᵢₖ vₖ`. -/
theorem totalDeriv_sum_mul_velocity (ha : ∀ i k, R.OrderLE (a i k) 0) (i : ι) :
    R.totalDeriv (∑ k, a i k * R.q k 1) =
      ∑ k, a i k * R.q k 2 + ∑ k, R.dt (a i k) * R.q k 1 +
        ∑ j, ∑ k, R.d j 0 (a i k) * (R.q j 1 * R.q k 1) := by
  have hterm (k : ι) : R.totalDeriv (a i k * R.q k 1) =
      a i k * R.q k 2 + R.dt (a i k) * R.q k 1 +
        ∑ j, R.d j 0 (a i k) * (R.q j 1 * R.q k 1) := by
    rw [SmoothDerivation.map_mul, totalDeriv_q, totalDeriv_of_orderLE_zero (ha i k), smul_eq_mul,
      smul_eq_mul, mul_add, Finset.mul_sum]
    rw [add_assoc]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [map_sum, hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun k j => R.d j 0 (a i k) * (R.q j 1 * R.q k 1))]

variable [DecidableEq ι]

omit [Fintype ι] in
theorem d_one_q_one (i j : ι) : R.d j 1 (R.q i 1) = if i = j then 1 else 0 := by
  split_ifs with h
  · rw [h, R.d_q_self]
  · exact R.d_q_ne i 1 j 1 fun hc => h (Prod.mk.inj hc).1

/-- The derivative of the kinetic form with respect to a velocity. -/
theorem d_one_kineticForm (ha : ∀ i k, R.OrderLE (a i k) 0) (j : ι) :
    R.d j 1 (R.kineticForm a) = ∑ i, a i j * R.q i 1 + ∑ k, a j k * R.q k 1 := by
  have hterm (i k : ι) : R.d j 1 (a i k * (R.q i 1 * R.q k 1)) =
      (if k = j then a i k * R.q i 1 else 0) + (if i = j then a i k * R.q k 1 else 0) := by
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_mul, ha i k j 1 (by norm_num),
      d_one_q_one, d_one_q_one]
    simp only [smul_eq_mul, mul_zero, add_zero]
    split_ifs <;> ring
  simp only [kineticForm, map_sum, hterm, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- The momenta `pⱼ = Σₖ aⱼₖ vₖ`. -/
theorem momentum_metricLagrangian (ha : ∀ i k, R.OrderLE (a i k) 0)
    (hsymm : ∀ i k, a i k = a k i) (hU : R.OrderLE U 0) (j : ι) :
    R.momentum (R.metricLagrangian a U) j = ∑ k, a j k * R.q k 1 := by
  have hs : ∑ i, a i j * R.q i 1 = ∑ k, a j k * R.q k 1 :=
    Finset.sum_congr rfl fun i _ => by rw [hsymm]
  rw [momentum, metricLagrangian, map_sub, SmoothDerivation.map_mul,
    SmoothDerivation.map_algebraMap, hU j 1 (by norm_num), d_one_kineticForm ha, hs]
  simp only [smul_eq_mul, mul_zero, add_zero, sub_zero]
  linear_combination (∑ k, a j k * R.q k 1) * algebraMap_half_add_half (J := J)

/-- Lagrange's equations in compact form:
`Eᵢ(L) = ½ Σⱼₖ ∂ᵢaⱼₖ vⱼ vₖ − ∂ᵢU − D(Σₖ aᵢₖ vₖ)`. -/
theorem euler_metricLagrangian (ha : ∀ i k, R.OrderLE (a i k) 0)
    (hsymm : ∀ i k, a i k = a k i) (hU : R.OrderLE U 0) (i : ι) :
    R.euler i (R.metricLagrangian a U) =
      algebraMap ℝ J (1 / 2) * ∑ j, ∑ k, R.d i 0 (a j k) * (R.q j 1 * R.q k 1) - R.d i 0 U -
        R.totalDeriv (∑ k, a i k * R.q k 1) := by
  rw [euler_of_orderLE_one (orderLE_metricLagrangian ha hU),
    momentum_metricLagrangian ha hsymm hU, metricLagrangian, map_sub, SmoothDerivation.map_mul,
    SmoothDerivation.map_algebraMap, d_zero_kineticForm]
  simp only [smul_eq_mul, mul_zero, add_zero]

/-- Lagrange's equations (Landau–Lifshitz §5):
`Eᵢ(L) = −Σₖ aᵢₖ q̈ₖ − Σⱼₖ (∂ⱼaᵢₖ − ½ ∂ᵢaⱼₖ) vⱼ vₖ − Σₖ ∂ₜaᵢₖ vₖ − ∂ᵢU`. -/
theorem euler_metricLagrangian_eq (ha : ∀ i k, R.OrderLE (a i k) 0)
    (hsymm : ∀ i k, a i k = a k i) (hU : R.OrderLE U 0) (i : ι) :
    R.euler i (R.metricLagrangian a U) =
      -(∑ k, a i k * R.q k 2) -
          ∑ j, ∑ k, (R.d j 0 (a i k) - algebraMap ℝ J (1 / 2) * R.d i 0 (a j k)) *
            (R.q j 1 * R.q k 1) -
        ∑ k, R.dt (a i k) * R.q k 1 - R.d i 0 U := by
  have hsplit : ∑ j, ∑ k, (R.d j 0 (a i k) - algebraMap ℝ J (1 / 2) * R.d i 0 (a j k)) *
        (R.q j 1 * R.q k 1) =
      ∑ j, ∑ k, R.d j 0 (a i k) * (R.q j 1 * R.q k 1) -
        algebraMap ℝ J (1 / 2) * ∑ j, ∑ k, R.d i 0 (a j k) * (R.q j 1 * R.q k 1) := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [euler_metricLagrangian ha hsymm hU, totalDeriv_sum_mul_velocity ha, hsplit]
  ring

/-- The energy is `½ Σᵢₖ aᵢₖ vᵢ vₖ + U`. -/
theorem energy_metricLagrangian (ha : ∀ i k, R.OrderLE (a i k) 0)
    (hsymm : ∀ i k, a i k = a k i) (hU : R.OrderLE U 0) :
    R.energy (R.metricLagrangian a U) = algebraMap ℝ J (1 / 2) * R.kineticForm a + U := by
  have hk : ∑ i, R.q i 1 * ∑ k, a i k * R.q k 1 = R.kineticForm a := by
    rw [kineticForm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [energy]
  simp only [momentum_metricLagrangian ha hsymm hU]
  rw [hk, metricLagrangian]
  linear_combination (-(R.kineticForm a)) * algebraMap_half_add_half (J := J)

/-- The energy `½ Σᵢₖ aᵢₖ vᵢ vₖ + U` is conserved when the kinetic coefficients
and the potential do not depend explicitly on time. -/
theorem conserved_energy_metricLagrangian (ha : ∀ i k, R.OrderLE (a i k) 0)
    (hsymm : ∀ i k, a i k = a k i) (hU : R.OrderLE U 0) (hat : ∀ i k, R.dt (a i k) = 0)
    (hUt : R.dt U = 0) :
    R.Conserved (R.metricLagrangian a U) (algebraMap ℝ J (1 / 2) * R.kineticForm a + U) := by
  rw [← energy_metricLagrangian ha hsymm hU]
  refine conserved_energy (orderLE_metricLagrangian ha hU) ?_
  rw [dt_metricLagrangian, hUt]
  simp only [hat, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]

/-- If `b` is inverse to `a`, the kinetic form is `Σᵢⱼ bᵢⱼ pᵢ pⱼ` in the
momenta `pᵢ = Σₖ aᵢₖ vₖ`. -/
theorem sum_inverse_mul_momentum (a b : ι → ι → J)
    (hb : ∀ i l, ∑ j, b i j * a j l = if i = l then 1 else 0) :
    ∑ i, ∑ j, b i j * ((∑ k, a i k * R.q k 1) * ∑ l, a j l * R.q l 1) = R.kineticForm a := by
  have hv (i : ι) : ∑ j, b i j * ∑ l, a j l * R.q l 1 = R.q i 1 := by
    have hl (l : ι) : ∑ j, b i j * (a j l * R.q l 1) = (if i = l then 1 else 0) * R.q l 1 := by
      rw [← hb i l, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hi (i : ι) : ∑ j, b i j * ((∑ k, a i k * R.q k 1) * ∑ l, a j l * R.q l 1) =
      (∑ k, a i k * R.q k 1) * R.q i 1 := by
    rw [← hv i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hi i, kineticForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The energy in the momenta: if `b` is inverse to `a`, the energy is
`½ Σᵢⱼ bᵢⱼ pᵢ pⱼ + U` (Landau–Lifshitz §5 and §40). -/
theorem energy_metricLagrangian_eq_inverse (ha : ∀ i k, R.OrderLE (a i k) 0)
    (hsymm : ∀ i k, a i k = a k i) (hU : R.OrderLE U 0) (b : ι → ι → J)
    (hb : ∀ i l, ∑ j, b i j * a j l = if i = l then 1 else 0) :
    R.energy (R.metricLagrangian a U) =
      algebraMap ℝ J (1 / 2) *
          ∑ i, ∑ j, b i j *
            (R.momentum (R.metricLagrangian a U) i * R.momentum (R.metricLagrangian a U) j) +
        U := by
  simp only [momentum_metricLagrangian ha hsymm hU]
  rw [sum_inverse_mul_momentum a b hb, energy_metricLagrangian ha hsymm hU]

/-- The kinetic form of constant masses. -/
theorem kineticForm_diagonal (m : ι → ℝ) :
    R.kineticForm (fun i k => if i = k then algebraMap ℝ J (m i) else 0) =
      ∑ i, algebraMap ℝ J (m i) * (R.q i 1 * R.q i 1) := by
  rw [kineticForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- A diagonal constant kinetic form gives the natural Lagrangian of particles
with constant masses. -/
theorem metricLagrangian_diagonal (m : ι → ℝ) (U : J) :
    R.metricLagrangian (fun i k => if i = k then algebraMap ℝ J (m i) else 0) U =
      R.naturalLagrangian m U := by
  rw [metricLagrangian, kineticForm_diagonal, naturalLagrangian, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← map_mul]
  congr 2
  ring

end ProjectAInos.Mechanics.JetRing
