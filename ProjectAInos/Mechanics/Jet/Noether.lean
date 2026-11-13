/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Jet.Euler
import Mathlib.Tactic.Ring

/-!
# Energy and the Noether identity in a jet ring

A Lagrangian is an element of order at most one. Its momenta are `pᵢ = ∂L/∂vᵢ`
and its energy is `Σᵢ vᵢ pᵢ − L`. Two identities hold in every jet ring:

* the energy identity `D(E_L) = −Σᵢ vᵢ Eᵢ(L) − ∂ₜL`;
* the Noether identity `pr ξ(L) = Σᵢ ξᵢ Eᵢ(L) + D(Σᵢ ξᵢ pᵢ)`.

Hence the energy is conserved when `∂ₜL = 0`, and a variation that changes the
Lagrangian by a total derivative `D F` gives the conserved element
`Σᵢ ξᵢ pᵢ − F`. Conservation means membership of the total derivative in the
Euler–Lagrange ideal; no trajectory is involved.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.JetRing

open SmoothAlgebra

variable {ι J : Type*} [CommRing J] [Algebra ℝ J] [SmoothRing J] [Fintype ι] (R : JetRing ι J)

/-- The momentum conjugate to the `i`-th coordinate, `∂L/∂vᵢ`. -/
def momentum (L : J) (i : ι) : J := R.d i 1 L

/-- The energy `Σᵢ vᵢ pᵢ − L`. -/
def energy (L : J) : J := ∑ i, R.q i 1 * R.momentum L i - L

/-- The prolongation `pr ξ = Σₖ Σᵢ (Dᵏ ξᵢ) ∂ᵢ⁽ᵏ⁾` of a variation of the coordinates. -/
def prolong (ξ : ι → J) (F : J) : J :=
  ∑ᶠ k : ℕ, ∑ i, (R.totalDeriv^[k]) (ξ i) * R.d i k F

variable {R}

/-- For a Lagrangian of order at most one the Euler operator is
`∂L/∂qᵢ − D(∂L/∂vᵢ)`. -/
theorem euler_of_orderLE_one {L : J} (hL : R.OrderLE L 1) (i : ι) :
    R.euler i L = R.d i 0 L - R.totalDeriv (R.momentum L i) := by
  rw [euler_eq_sum hL, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, one_mul, Function.iterate_zero, id_eq, pow_one, Function.iterate_one,
    momentum]
  ring

theorem totalDeriv_of_orderLE_one {L : J} (hL : R.OrderLE L 1) :
    R.totalDeriv L =
      R.dt L + ∑ i, R.q i 1 * R.d i 0 L + ∑ i, R.q i 2 * R.momentum L i := by
  rw [totalDeriv_eq_sum hL, Finset.sum_range_succ, Finset.sum_range_one, add_assoc]
  rfl

theorem prolong_of_orderLE_one {L : J} (hL : R.OrderLE L 1) (ξ : ι → J) :
    R.prolong ξ L = ∑ i, (ξ i * R.d i 0 L + R.totalDeriv (ξ i) * R.momentum L i) := by
  have hsupp : (Function.support fun k : ℕ => ∑ i, (R.totalDeriv^[k]) (ξ i) * R.d i k L) ⊆
      ↑(Finset.range 2) := by
    intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    refine hk (Finset.sum_eq_zero fun i _ => ?_)
    rw [hL i k (by omega), mul_zero]
  rw [prolong, finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ,
    Finset.sum_range_one, ← Finset.sum_add_distrib]
  rfl

/-- The total derivative of `Σᵢ ξᵢ pᵢ`. -/
theorem totalDeriv_sum_mul_momentum (L : J) (ξ : ι → J) :
    R.totalDeriv (∑ i, ξ i * R.momentum L i) =
      ∑ i, (ξ i * R.totalDeriv (R.momentum L i) + R.totalDeriv (ξ i) * R.momentum L i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SmoothDerivation.map_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- The energy identity `D(E_L) = −Σᵢ vᵢ Eᵢ(L) − ∂ₜL` (Landau–Lifshitz §6). -/
theorem totalDeriv_energy {L : J} (hL : R.OrderLE L 1) :
    R.totalDeriv (R.energy L) = -∑ i, R.q i 1 * R.euler i L - R.dt L := by
  rw [energy, map_sub, totalDeriv_sum_mul_momentum, totalDeriv_of_orderLE_one hL]
  simp only [totalDeriv_q, euler_of_orderLE_one hL, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

/-- The Noether identity `pr ξ(L) = Σᵢ ξᵢ Eᵢ(L) + D(Σᵢ ξᵢ pᵢ)`
(Landau–Lifshitz §§7–9). It holds for every variation `ξ`. -/
theorem prolong_eq_euler_add_totalDeriv {L : J} (hL : R.OrderLE L 1) (ξ : ι → J) :
    R.prolong ξ L =
      ∑ i, ξ i * R.euler i L + R.totalDeriv (∑ i, ξ i * R.momentum L i) := by
  rw [prolong_of_orderLE_one hL, totalDeriv_sum_mul_momentum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euler_of_orderLE_one hL]
  ring

/-- If a variation changes the Lagrangian by a total derivative `D F`, the
Noether charge `Σᵢ ξᵢ pᵢ − F` has total derivative `−Σᵢ ξᵢ Eᵢ(L)`. -/
theorem totalDeriv_noetherCharge {L F : J} (hL : R.OrderLE L 1) (ξ : ι → J)
    (h : R.prolong ξ L = R.totalDeriv F) :
    R.totalDeriv (∑ i, ξ i * R.momentum L i - F) = -∑ i, ξ i * R.euler i L := by
  rw [map_sub, ← h, prolong_eq_euler_add_totalDeriv hL]
  ring

/-- A combination of the Euler–Lagrange expressions lies in the Euler–Lagrange ideal. -/
theorem sum_mul_euler_mem (L : J) (ξ : ι → J) :
    ∑ i, ξ i * R.euler i L ∈ R.eulerLagrangeIdeal L :=
  sum_mem fun i _ => Ideal.mul_mem_left _ _ (euler_mem L i)

/-- Noether's theorem in a jet ring: a quasi-symmetry of the Lagrangian gives a
conserved element. -/
theorem conserved_noetherCharge {L F : J} (hL : R.OrderLE L 1) (ξ : ι → J)
    (h : R.prolong ξ L = R.totalDeriv F) :
    R.Conserved L (∑ i, ξ i * R.momentum L i - F) := by
  rw [Conserved, totalDeriv_noetherCharge hL ξ h]
  exact neg_mem (sum_mul_euler_mem L ξ)

/-- A strict symmetry, `pr ξ(L) = 0`, conserves `Σᵢ ξᵢ pᵢ`. -/
theorem conserved_of_prolong_eq_zero {L : J} (hL : R.OrderLE L 1) (ξ : ι → J)
    (h : R.prolong ξ L = 0) : R.Conserved L (∑ i, ξ i * R.momentum L i) := by
  have h0 : R.prolong ξ L = R.totalDeriv 0 := by rw [h, map_zero]
  simpa only [sub_zero] using conserved_noetherCharge hL ξ h0

/-- The energy is conserved when the Lagrangian does not depend explicitly on time. -/
theorem conserved_energy {L : J} (hL : R.OrderLE L 1) (ht : R.dt L = 0) :
    R.Conserved L (R.energy L) := by
  rw [Conserved, totalDeriv_energy hL, ht, sub_zero]
  exact neg_mem (sum_mul_euler_mem L fun i => R.q i 1)

end ProjectAInos.Mechanics.JetRing
