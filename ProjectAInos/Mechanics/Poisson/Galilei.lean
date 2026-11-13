/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.AngularMomentum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The Galilei algebra of a free particle

On the canonical phase space of one particle of mass `m`, the generators of the
Galilei group are the momentum `p`, the angular momentum `M = q × p`, the free
Hamiltonian `H₀ = |p|² / 2m` and, at time `t`, the boost generator
`K = m q − t p` (Landau–Lifshitz §§3, 8). Their brackets are

`{Kₐ, p_b} = m δₐ_b`, `{Kₐ, K_b} = 0`, `{Mₐ, K_b} = εₐ_bc K_c`,
`{Mₐ, H₀} = 0`, `{pₐ, H₀} = 0`, `{Kₐ, H₀} = pₐ` for `m ≠ 0`.

The mass appears as a central term in `{K, p}`. The boost generator depends on
time through `K_t − K_s = −(t − s) p`, and this cancels `{K, H₀} = p`: the
centre-of-mass integral is conserved by the free motion.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Galilei

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix AngularMomentum

/-- The boost generator `K = m q − t p` of a particle of mass `m` at time `t`. -/
def K (m t : ℝ) : Fin 3 → Space :=
  fun a => algebraMap ℝ Space m * q a - algebraMap ℝ Space t * p a

/-- The free Hamiltonian `|p|² / 2m`. -/
def freeHamiltonian (m : ℝ) : Space := algebraMap ℝ Space (m⁻¹ / 2) * (p ⬝ᵥ p)

/-- `{Kₐ, p_b} = m δₐ_b`: the mass is a central term. -/
theorem canonical_K_p (m t : ℝ) (a b : Fin 3) :
    canonical.bracket (K m t a) (p b) = if a = b then algebraMap ℝ Space m else 0 := by
  rw [K, AlmostPoissonStructure.bracket_sub_left, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_left, canonical_q_p, canonical_p_p]
  split_ifs <;> simp

/-- `{Kₐ, q_b} = t δₐ_b`. -/
theorem canonical_K_q (m t : ℝ) (a b : Fin 3) :
    canonical.bracket (K m t a) (q b) = if a = b then algebraMap ℝ Space t else 0 := by
  rw [K, AlmostPoissonStructure.bracket_sub_left, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_left, canonical_q_q, canonical_p_q]
  split_ifs <;> simp
  ring

/-- Boosts commute: `{Kₐ, K_b} = 0`. -/
theorem canonical_K_K (m t : ℝ) (a b : Fin 3) :
    canonical.bracket (K m t a) (K m t b) = 0 := by
  have h : canonical.bracket (K m t a) (K m t b) =
      canonical.bracket (K m t a) (algebraMap ℝ Space m * q b - algebraMap ℝ Space t * p b) :=
    rfl
  rw [h, AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_K_q, canonical_K_p]
  split_ifs <;> simp [mul_comm]

/-- Boosts transform as a vector under rotations: `{Mₐ, K_b} = εₐ_bc K_c`. -/
theorem canonical_M_K (m t : ℝ) (a b : Fin 3) :
    canonical.bracket (M a) (K m t b) = epsilon (K m t) a b := by
  have h : canonical.bracket (M a) (K m t b) =
      canonical.bracket (M a) (algebraMap ℝ Space m * q b - algebraMap ℝ Space t * p b) := rfl
  rw [h, AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_M_q, canonical_M_p]
  fin_cases a <;> fin_cases b <;> simp [epsilon, K] <;> ring

/-- The free Hamiltonian is invariant under rotations. -/
theorem canonical_M_freeHamiltonian (m : ℝ) (a : Fin 3) :
    canonical.bracket (M a) (freeHamiltonian m) = 0 := by
  rw [freeHamiltonian, AlmostPoissonStructure.bracket_mul_right, canonical_M_p_sq,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, mul_zero, add_zero]

/-- `{qₐ, H₀} = pₐ / m`. -/
theorem canonical_q_freeHamiltonian (m : ℝ) (a : Fin 3) :
    canonical.bracket (q a) (freeHamiltonian m) = algebraMap ℝ Space m⁻¹ * p a := by
  have h2 : (2 : Space) = algebraMap ℝ Space 2 := (map_ofNat _ 2).symm
  have hm : m⁻¹ / 2 * 2 = m⁻¹ := by ring
  rw [freeHamiltonian, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero]
  simp only [dotProduct, Fin.sum_univ_three, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_mul_right, canonical_q_p]
  fin_cases a <;> simp <;> rw [← two_mul, h2, ← mul_assoc, ← map_mul, hm]

/-- The momentum is conserved by the free motion. -/
theorem canonical_p_freeHamiltonian (m : ℝ) (a : Fin 3) :
    canonical.bracket (p a) (freeHamiltonian m) = 0 := by
  rw [freeHamiltonian, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero]
  simp only [dotProduct, Fin.sum_univ_three, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_mul_right, canonical_p_p, mul_zero, add_zero]

/-- `{Kₐ, H₀} = pₐ` for a nonzero mass. -/
theorem canonical_K_freeHamiltonian {m : ℝ} (hm : m ≠ 0) (t : ℝ) (a : Fin 3) :
    canonical.bracket (K m t a) (freeHamiltonian m) = p a := by
  rw [K, AlmostPoissonStructure.bracket_sub_left, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_left, canonical_q_freeHamiltonian,
    canonical_p_freeHamiltonian]
  simp only [mul_zero, add_zero, sub_zero]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hm, map_one, one_mul]

/-- The explicit time dependence of the boost generator:
`K_t − K_s = −(t − s) p`. -/
theorem K_sub_K (m t s : ℝ) (a : Fin 3) :
    K m t a - K m s a = -(algebraMap ℝ Space (t - s) * p a) := by
  rw [K, K, map_sub]
  ring

end ProjectAInos.Mechanics.Galilei
