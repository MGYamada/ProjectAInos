/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Separation.Stackel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spherical, parabolic and elliptic co-ordinates

Landau–Lifshitz §48. For each of the three systems of co-ordinates:

* the kinetic energy of a particle in the co-ordinates, from the Cartesian
  co-ordinates of a curve (`spherical_kinetic`, `parabolic_kinetic`,
  `elliptic_kinetic`);
* the system of Stäckel on the box of the co-ordinates (`spherical`,
  `parabolic`, `elliptic`), whose Hamiltonian is that of the particle in a
  field of the separable form (`hamiltonian_spherical`,
  `hamiltonian_parabolic`, `hamiltonian_elliptic`; Landau–Lifshitz (48.8),
  (48.15), (48.20));
* the determinant of the matrix of Stäckel (`det_spherical`, `det_parabolic`,
  `det_elliptic`), which is different from zero on the box, so that the
  separated integral is complete and Jacobi's theorem applies.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Real

namespace ProjectAInos.Mechanics.Stackel

/-! ### The kinetic energy in the co-ordinates -/

namespace System

variable {ι : Type} [Fintype ι] [DecidableEq ι] (s : System ι)

/-- The kinetic energy `Σᵢ q̇ᵢ²/(2 Ψᵢ gᵢ)` whose Legendre transform is the
kinetic part of the Hamiltonian. -/
def kinetic (q v : ι → ℝ) : ℝ := ∑ i, v i ^ 2 / (2 * (s.Ψ i q * s.g i (q i)))

/-- The potential energy `Σᵢ Ψᵢ uᵢ`. -/
def potential (q : ι → ℝ) : ℝ := ∑ i, s.Ψ i q * s.u i (q i)

/-- The Hamiltonian is the Legendre transform of `kinetic − potential`, with the
momenta `pᵢ = q̇ᵢ/(Ψᵢ gᵢ)`. -/
theorem hamiltonian_eq_legendre {q v : ι → ℝ} (hΨ : ∀ i, s.Ψ i q ≠ 0)
    (hg : ∀ i, s.g i (q i) ≠ 0) :
    s.hamiltonian q (fun i => v i / (s.Ψ i q * s.g i (q i))) =
      ∑ i, v i / (s.Ψ i q * s.g i (q i)) * v i - (s.kinetic q v - s.potential q) := by
  rw [hamiltonian, kinetic, potential, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hΨ i
  have h2 := hg i
  field_simp
  ring

end System

/-- The velocity in cylindrical co-ordinates: for `x = ρ cos φ`, `y = ρ sin φ`
the square of the velocity is `ρ̇² + ρ² φ̇² + ż²`. -/
theorem cylindrical_speed_sq {ρ φ : ℝ → ℝ} {ρ' φ' t : ℝ} (hρ : HasDerivAt ρ ρ' t)
    (hφ : HasDerivAt φ φ' t) :
    ∃ x' y' : ℝ, HasDerivAt (fun s => ρ s * Real.cos (φ s)) x' t ∧
      HasDerivAt (fun s => ρ s * Real.sin (φ s)) y' t ∧
      x' ^ 2 + y' ^ 2 = ρ' ^ 2 + ρ t ^ 2 * φ' ^ 2 := by
  have hc : HasDerivAt (fun s => Real.cos (φ s)) (-Real.sin (φ t) * φ') t :=
    HasDerivAt.comp t (Real.hasDerivAt_cos (φ t)) hφ
  have hs : HasDerivAt (fun s => Real.sin (φ s)) (Real.cos (φ t) * φ') t :=
    HasDerivAt.comp t (Real.hasDerivAt_sin (φ t)) hφ
  have hx : HasDerivAt (fun s => ρ s * Real.cos (φ s))
      (ρ' * Real.cos (φ t) + ρ t * (-Real.sin (φ t) * φ')) t := hρ.mul hc
  have hy : HasDerivAt (fun s => ρ s * Real.sin (φ s))
      (ρ' * Real.sin (φ t) + ρ t * (Real.cos (φ t) * φ')) t := hρ.mul hs
  refine ⟨_, _, hx, hy, ?_⟩
  have h := Real.sin_sq_add_cos_sq (φ t)
  linear_combination (ρ' ^ 2 + ρ t ^ 2 * φ' ^ 2) * h

section Kinetic

variable {r θ φ ξ η : ℝ → ℝ} {r' θ' φ' ξ' η' t : ℝ}

/-- Spherical co-ordinates: `ρ = r sin θ`, `z = r cos θ`. -/
theorem spherical_kinetic (hr : HasDerivAt r r' t) (hθ : HasDerivAt θ θ' t) :
    ∃ ρ' z' : ℝ, HasDerivAt (fun s => r s * Real.sin (θ s)) ρ' t ∧
      HasDerivAt (fun s => r s * Real.cos (θ s)) z' t ∧
      ρ' ^ 2 + z' ^ 2 = r' ^ 2 + r t ^ 2 * θ' ^ 2 := by
  have hc : HasDerivAt (fun s => Real.cos (θ s)) (-Real.sin (θ t) * θ') t :=
    HasDerivAt.comp t (Real.hasDerivAt_cos (θ t)) hθ
  have hs : HasDerivAt (fun s => Real.sin (θ s)) (Real.cos (θ t) * θ') t :=
    HasDerivAt.comp t (Real.hasDerivAt_sin (θ t)) hθ
  have hρ : HasDerivAt (fun s => r s * Real.sin (θ s))
      (r' * Real.sin (θ t) + r t * (Real.cos (θ t) * θ')) t := hr.mul hs
  have hz : HasDerivAt (fun s => r s * Real.cos (θ s))
      (r' * Real.cos (θ t) + r t * (-Real.sin (θ t) * θ')) t := hr.mul hc
  refine ⟨_, _, hρ, hz, ?_⟩
  have h := Real.sin_sq_add_cos_sq (θ t)
  linear_combination (r' ^ 2 + r t ^ 2 * θ' ^ 2) * h

/-- Parabolic co-ordinates: `ρ = √(ξ η)`, `z = (ξ − η)/2`
(Landau–Lifshitz (48.11), (48.13)). -/
theorem parabolic_kinetic (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t) (hξ0 : 0 < ξ t)
    (hη0 : 0 < η t) :
    ∃ ρ' z' : ℝ, HasDerivAt (fun s => √(ξ s * η s)) ρ' t ∧
      HasDerivAt (fun s => (ξ s - η s) / 2) z' t ∧
      ρ' ^ 2 + z' ^ 2 = (ξ t + η t) / (4 * ξ t) * ξ' ^ 2 + (ξ t + η t) / (4 * η t) * η' ^ 2 := by
  have hpos : 0 < ξ t * η t := mul_pos hξ0 hη0
  have hprod : HasDerivAt (fun s => ξ s * η s) (ξ' * η t + ξ t * η') t := hξ.mul hη
  have hρ : HasDerivAt (fun s => √(ξ s * η s))
      ((ξ' * η t + ξ t * η') / (2 * √(ξ t * η t))) t := hprod.sqrt hpos.ne'
  have hz : HasDerivAt (fun s => (ξ s - η s) / 2) ((ξ' - η') / 2) t := (hξ.sub hη).div_const 2
  refine ⟨_, _, hρ, hz, ?_⟩
  have hsq : √(ξ t * η t) ^ 2 = ξ t * η t := Real.sq_sqrt hpos.le
  have hs : 0 < √(ξ t * η t) := Real.sqrt_pos.mpr hpos
  rw [div_pow, mul_pow, hsq]
  field_simp
  ring

/-- Elliptic co-ordinates: `ρ = σ √((ξ² − 1)(1 − η²))`, `z = σ ξ η`
(Landau–Lifshitz (48.16), (48.18)). -/
theorem elliptic_kinetic (σ : ℝ) (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t)
    (hξ1 : 1 < ξ t) (hη1 : η t ∈ Ioo (-1 : ℝ) 1) :
    ∃ ρ' z' : ℝ, HasDerivAt (fun s => σ * √((ξ s ^ 2 - 1) * (1 - η s ^ 2))) ρ' t ∧
      HasDerivAt (fun s => σ * (ξ s * η s)) z' t ∧
      ρ' ^ 2 + z' ^ 2 = σ ^ 2 * (ξ t ^ 2 - η t ^ 2) / (ξ t ^ 2 - 1) * ξ' ^ 2 +
        σ ^ 2 * (ξ t ^ 2 - η t ^ 2) / (1 - η t ^ 2) * η' ^ 2 := by
  have hA : 0 < ξ t ^ 2 - 1 := by nlinarith
  have hB : 0 < 1 - η t ^ 2 := by nlinarith [hη1.1, hη1.2]
  have hpos : 0 < (ξ t ^ 2 - 1) * (1 - η t ^ 2) := mul_pos hA hB
  have hξ2 : HasDerivAt (fun s => ξ s ^ 2 - 1) (2 * ξ t * ξ') t := by
    have h := (hξ.pow 2).sub_const 1
    simpa using h
  have hη2 : HasDerivAt (fun s => 1 - η s ^ 2) (-(2 * η t * η')) t := by
    have h := (hη.pow 2).const_sub 1
    simpa using h
  have hprod : HasDerivAt (fun s => (ξ s ^ 2 - 1) * (1 - η s ^ 2))
      (2 * ξ t * ξ' * (1 - η t ^ 2) + (ξ t ^ 2 - 1) * -(2 * η t * η')) t := hξ2.mul hη2
  have hρ : HasDerivAt (fun s => σ * √((ξ s ^ 2 - 1) * (1 - η s ^ 2)))
      (σ * ((2 * ξ t * ξ' * (1 - η t ^ 2) + (ξ t ^ 2 - 1) * -(2 * η t * η')) /
        (2 * √((ξ t ^ 2 - 1) * (1 - η t ^ 2))))) t := (hprod.sqrt hpos.ne').const_mul σ
  have hz : HasDerivAt (fun s => σ * (ξ s * η s)) (σ * (ξ' * η t + ξ t * η')) t :=
    (hξ.mul hη).const_mul σ
  refine ⟨_, _, hρ, hz, ?_⟩
  have hsq : √((ξ t ^ 2 - 1) * (1 - η t ^ 2)) ^ 2 = (ξ t ^ 2 - 1) * (1 - η t ^ 2) :=
    Real.sq_sqrt hpos.le
  have hs : 0 < √((ξ t ^ 2 - 1) * (1 - η t ^ 2)) := Real.sqrt_pos.mpr hpos
  rw [mul_pow, div_pow, mul_pow, hsq]
  field_simp
  ring

end Kinetic

/-! ### Spherical co-ordinates -/

section Systems

variable {m : ℝ} {a b c : ℝ → ℝ}

/-- Spherical co-ordinates `(r, θ, φ)` on `r > 0`, `0 < θ < π`, for the field
`a(r) + b(θ)/r² + c(φ)/(r² sin² θ)`. The parameters are the energy, and the
separation constants of `θ` and of `φ`. -/
def spherical (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0)) (hb : ContDiffOn ℝ 1 b (Ioo 0 π))
    (hc : ContDiffOn ℝ 1 c univ) : System (Fin 3) where
  φ := ![![fun _ => 1, fun r => -1 / r ^ 2, fun _ => 0],
    ![fun _ => 0, fun _ => 1, fun θ => -1 / Real.sin θ ^ 2],
    ![fun _ => 0, fun _ => 0, fun _ => 1]]
  g := fun _ _ => 1 / m
  u := ![a, b, c]
  Ψ := ![fun _ => 1, fun q => 1 / q 0 ^ 2, fun q => 1 / (q 0 ^ 2 * Real.sin (q 1) ^ 2)]
  j₀ := 0
  I := ![Ioi 0, Ioo 0 π, univ]
  isOpen i := by
    fin_cases i
    · exact isOpen_Ioi
    · exact isOpen_Ioo
    · exact isOpen_univ
  ordConnected i := by
    fin_cases i
    · exact ordConnected_Ioi
    · exact ordConnected_Ioo
    · exact ordConnected_univ
  contDiffOn_φ i j := by
    have h1 : ContDiffOn ℝ 1 (fun r : ℝ => -1 / r ^ 2) (Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun x hx => pow_ne_zero 2 (ne_of_gt hx)
    have h2 : ContDiffOn ℝ 1 (fun θ : ℝ => -1 / Real.sin θ ^ 2) (Ioo 0 π) :=
      contDiffOn_const.div (Real.contDiff_sin.contDiffOn.pow 2) fun x hx =>
        pow_ne_zero 2 (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
    fin_cases i <;> fin_cases j <;>
      first | exact contDiffOn_const | exact h1 | exact h2
  contDiffOn_g _ := contDiffOn_const
  contDiffOn_u i := by
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  g_pos _ _ _ := one_div_pos.mpr hm
  sum_Ψ q hq j := by
    fin_cases j <;> simp [Fin.sum_univ_three] <;> ring
  differentiableAt_Ψ q hq i := by
    have h0 : (0 : ℝ) < q 0 := hq 0
    have h1 : q 1 ∈ Ioo (0 : ℝ) π := hq 1
    have hs := Real.sin_pos_of_pos_of_lt_pi h1.1 h1.2
    have e0 : q 0 ^ 2 ≠ 0 := pow_ne_zero 2 h0.ne'
    have e1 : q 0 ^ 2 * Real.sin (q 1) ^ 2 ≠ 0 := mul_ne_zero e0 (pow_ne_zero 2 hs.ne')
    fin_cases i
    · exact differentiableAt_const _
    · have h : DifferentiableAt ℝ (fun q : Fin 3 → ℝ => 1 / q 0 ^ 2) q := by
        fun_prop (disch := assumption)
      exact h
    · have h : DifferentiableAt ℝ
          (fun q : Fin 3 → ℝ => 1 / (q 0 ^ 2 * Real.sin (q 1) ^ 2)) q := by
        fun_prop (disch := assumption)
      exact h

theorem hamiltonian_spherical (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q p : Fin 3 → ℝ) :
    (spherical hm ha hb hc).hamiltonian q p =
      p 0 ^ 2 / (2 * m) + a (q 0) + (p 1 ^ 2 / (2 * m) + b (q 1)) / q 0 ^ 2 +
        (p 2 ^ 2 / (2 * m) + c (q 2)) / (q 0 ^ 2 * Real.sin (q 1) ^ 2) := by
  simp [System.hamiltonian, spherical, Fin.sum_univ_three]
  ring

theorem kinetic_spherical (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q v : Fin 3 → ℝ) :
    (spherical hm ha hb hc).kinetic q v =
      m / 2 * (v 0 ^ 2 + q 0 ^ 2 * v 1 ^ 2 + q 0 ^ 2 * Real.sin (q 1) ^ 2 * v 2 ^ 2) := by
  have hm' := hm.ne'
  simp [System.kinetic, spherical, Fin.sum_univ_three]
  field_simp

theorem det_spherical (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (spherical hm ha hb hc).φ i j (q i)).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [spherical]

/-! ### Parabolic co-ordinates -/

/-- Parabolic co-ordinates `(ξ, η, φ)` on `ξ, η > 0`, for the field
`(a(ξ) + b(η))/(ξ + η) + c(φ)/(ξ η)`. -/
def parabolic (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0)) (hb : ContDiffOn ℝ 1 b (Ioi 0))
    (hc : ContDiffOn ℝ 1 c univ) : System (Fin 3) where
  φ := ![![fun x => x, fun _ => 1, fun x => -1 / x],
    ![fun x => x, fun _ => -1, fun x => -1 / x],
    ![fun _ => 0, fun _ => 0, fun _ => 1]]
  g := ![fun x => 4 * x / m, fun x => 4 * x / m, fun _ => 1 / m]
  u := ![a, b, c]
  Ψ := ![fun q => 1 / (q 0 + q 1), fun q => 1 / (q 0 + q 1), fun q => 1 / (q 0 * q 1)]
  j₀ := 0
  I := ![Ioi 0, Ioi 0, univ]
  isOpen i := by
    fin_cases i
    · exact isOpen_Ioi
    · exact isOpen_Ioi
    · exact isOpen_univ
  ordConnected i := by
    fin_cases i
    · exact ordConnected_Ioi
    · exact ordConnected_Ioi
    · exact ordConnected_univ
  contDiffOn_φ i j := by
    have h1 : ContDiffOn ℝ 1 (fun x : ℝ => -1 / x) (Ioi 0) :=
      contDiffOn_const.div contDiffOn_id fun x hx => ne_of_gt hx
    fin_cases i <;> fin_cases j <;>
      first | exact contDiffOn_const | exact contDiffOn_id | exact h1
  contDiffOn_g i := by
    have h1 : ContDiffOn ℝ 1 (fun x : ℝ => 4 * x / m) (Ioi 0) :=
      (contDiffOn_const.mul contDiffOn_id).div_const m
    fin_cases i
    · exact h1
    · exact h1
    · exact contDiffOn_const
  contDiffOn_u i := by
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  g_pos i := by
    fin_cases i
    · intro x hx
      have hx' : (0 : ℝ) < x := hx
      change 0 < 4 * x / m
      positivity
    · intro x hx
      have hx' : (0 : ℝ) < x := hx
      change 0 < 4 * x / m
      positivity
    · intro x _
      exact one_div_pos.mpr hm
  sum_Ψ q hq j := by
    have h0 : (0 : ℝ) < q 0 := hq 0
    have h1 : (0 : ℝ) < q 1 := hq 1
    have hs : q 0 + q 1 ≠ 0 := (add_pos h0 h1).ne'
    have h0' := h0.ne'
    have h1' := h1.ne'
    fin_cases j
    · simp [Fin.sum_univ_three]
      field_simp
    · simp [Fin.sum_univ_three]
    · simp [Fin.sum_univ_three]
      field_simp
      ring
  differentiableAt_Ψ q hq i := by
    have h0 : (0 : ℝ) < q 0 := hq 0
    have h1 : (0 : ℝ) < q 1 := hq 1
    have e0 : q 0 + q 1 ≠ 0 := (add_pos h0 h1).ne'
    have e1 : q 0 * q 1 ≠ 0 := (mul_pos h0 h1).ne'
    have hA : DifferentiableAt ℝ (fun q : Fin 3 → ℝ => 1 / (q 0 + q 1)) q := by
      fun_prop (disch := assumption)
    have hB : DifferentiableAt ℝ (fun q : Fin 3 → ℝ => 1 / (q 0 * q 1)) q := by
      fun_prop (disch := assumption)
    fin_cases i
    · exact hA
    · exact hA
    · exact hB

theorem hamiltonian_parabolic (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) (q p : Fin 3 → ℝ) :
    (parabolic hm ha hb hc).hamiltonian q p =
      (2 * q 0 * p 0 ^ 2 / m + a (q 0) + (2 * q 1 * p 1 ^ 2 / m + b (q 1))) / (q 0 + q 1) +
        (p 2 ^ 2 / (2 * m) + c (q 2)) / (q 0 * q 1) := by
  simp [System.hamiltonian, parabolic, Fin.sum_univ_three]
  ring

theorem kinetic_parabolic (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (h0 : 0 < q 0) (h1 : 0 < q 1) (v : Fin 3 → ℝ) :
    (parabolic hm ha hb hc).kinetic q v =
      m / 2 * ((q 0 + q 1) / (4 * q 0) * v 0 ^ 2 + (q 0 + q 1) / (4 * q 1) * v 1 ^ 2 +
        q 0 * q 1 * v 2 ^ 2) := by
  have hm' := hm.ne'
  have hs : q 0 + q 1 ≠ 0 := (add_pos h0 h1).ne'
  have h0' := h0.ne'
  have h1' := h1.ne'
  simp [System.kinetic, parabolic, Fin.sum_univ_three]
  field_simp

theorem det_parabolic (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (parabolic hm ha hb hc).φ i j (q i)).det = -(q 0 + q 1) := by
  rw [Matrix.det_fin_three]
  simp [parabolic]
  ring

/-! ### Elliptic co-ordinates -/

/-- Elliptic co-ordinates `(ξ, η, φ)` on `ξ > 1`, `−1 < η < 1`, with the foci at
the distance `2σ`, for the field
`(a(ξ) + b(η))/(ξ² − η²) + c(φ)/(σ² (ξ² − 1)(1 − η²))`. -/
def elliptic {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) : System (Fin 3) where
  φ := ![![fun x => x ^ 2, fun _ => 1, fun x => -1 / (σ ^ 2 * (x ^ 2 - 1))],
    ![fun x => -x ^ 2, fun _ => -1, fun x => -1 / (σ ^ 2 * (1 - x ^ 2))],
    ![fun _ => 0, fun _ => 0, fun _ => 1]]
  g := ![fun x => (x ^ 2 - 1) / (m * σ ^ 2), fun x => (1 - x ^ 2) / (m * σ ^ 2),
    fun _ => 1 / m]
  u := ![a, b, c]
  Ψ := ![fun q => 1 / (q 0 ^ 2 - q 1 ^ 2), fun q => 1 / (q 0 ^ 2 - q 1 ^ 2),
    fun q => 1 / (σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2))]
  j₀ := 0
  I := ![Ioi 1, Ioo (-1) 1, univ]
  isOpen i := by
    fin_cases i
    · exact isOpen_Ioi
    · exact isOpen_Ioo
    · exact isOpen_univ
  ordConnected i := by
    fin_cases i
    · exact ordConnected_Ioi
    · exact ordConnected_Ioo
    · exact ordConnected_univ
  contDiffOn_φ i j := by
    have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ.ne'
    have h1 : ContDiffOn ℝ 1 (fun x : ℝ => x ^ 2) (Ioi 1) := contDiffOn_id.pow 2
    have h2 : ContDiffOn ℝ 1 (fun x : ℝ => -1 / (σ ^ 2 * (x ^ 2 - 1))) (Ioi 1) :=
      contDiffOn_const.div (contDiffOn_const.mul ((contDiffOn_id.pow 2).sub contDiffOn_const))
        fun x hx => by
          have hx' : (1 : ℝ) < x := hx
          exact mul_ne_zero hσ2 (by nlinarith)
    have h3 : ContDiffOn ℝ 1 (fun x : ℝ => -x ^ 2) (Ioo (-1) 1) := (contDiffOn_id.pow 2).neg
    have h4 : ContDiffOn ℝ 1 (fun x : ℝ => -1 / (σ ^ 2 * (1 - x ^ 2))) (Ioo (-1) 1) :=
      contDiffOn_const.div (contDiffOn_const.mul (contDiffOn_const.sub (contDiffOn_id.pow 2)))
        fun x hx => by
          have hx' : x ∈ Ioo (-1 : ℝ) 1 := hx
          exact mul_ne_zero hσ2 (by nlinarith [hx'.1, hx'.2])
    fin_cases i <;> fin_cases j <;>
      first | exact contDiffOn_const | exact h1 | exact h2 | exact h3 | exact h4
  contDiffOn_g i := by
    have h1 : ContDiffOn ℝ 1 (fun x : ℝ => (x ^ 2 - 1) / (m * σ ^ 2)) (Ioi 1) :=
      ((contDiffOn_id.pow 2).sub contDiffOn_const).div_const _
    have h2 : ContDiffOn ℝ 1 (fun x : ℝ => (1 - x ^ 2) / (m * σ ^ 2)) (Ioo (-1) 1) :=
      (contDiffOn_const.sub (contDiffOn_id.pow 2)).div_const _
    fin_cases i
    · exact h1
    · exact h2
    · exact contDiffOn_const
  contDiffOn_u i := by
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  g_pos i := by
    fin_cases i
    · intro x hx
      have hx' : (1 : ℝ) < x := hx
      have h : 0 < x ^ 2 - 1 := by nlinarith
      change 0 < (x ^ 2 - 1) / (m * σ ^ 2)
      positivity
    · intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := hx
      have h : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      change 0 < (1 - x ^ 2) / (m * σ ^ 2)
      positivity
    · intro x _
      exact one_div_pos.mpr hm
  sum_Ψ q hq j := by
    have h0 : (1 : ℝ) < q 0 := hq 0
    have h1 : q 1 ∈ Ioo (-1 : ℝ) 1 := hq 1
    have hA : q 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
    have hB : 1 - q 1 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [h1.1, h1.2])
    have hC : q 0 ^ 2 - q 1 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [h1.1, h1.2])
    have hσ' := hσ.ne'
    fin_cases j
    · simp [Fin.sum_univ_three]
      field_simp
      ring
    · simp [Fin.sum_univ_three]
    · simp [Fin.sum_univ_three]
      field_simp
      ring
  differentiableAt_Ψ q hq i := by
    have h0 : (1 : ℝ) < q 0 := hq 0
    have h1 : q 1 ∈ Ioo (-1 : ℝ) 1 := hq 1
    have hA : q 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
    have hB : 1 - q 1 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [h1.1, h1.2])
    have e0 : q 0 ^ 2 - q 1 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [h1.1, h1.2])
    have e1 : σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hσ.ne') hA) hB
    have hΨ₀ : DifferentiableAt ℝ (fun q : Fin 3 → ℝ => 1 / (q 0 ^ 2 - q 1 ^ 2)) q := by
      fun_prop (disch := assumption)
    have hΨ₂ : DifferentiableAt ℝ
        (fun q : Fin 3 → ℝ => 1 / (σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2))) q := by
      fun_prop (disch := assumption)
    fin_cases i
    · exact hΨ₀
    · exact hΨ₀
    · exact hΨ₂

theorem hamiltonian_elliptic {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) (q p : Fin 3 → ℝ) :
    (elliptic hm hσ ha hb hc).hamiltonian q p =
      ((q 0 ^ 2 - 1) * p 0 ^ 2 / (2 * m * σ ^ 2) + a (q 0) +
          ((1 - q 1 ^ 2) * p 1 ^ 2 / (2 * m * σ ^ 2) + b (q 1))) / (q 0 ^ 2 - q 1 ^ 2) +
        (p 2 ^ 2 / (2 * m) + c (q 2)) / (σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2)) := by
  simp [System.hamiltonian, elliptic, Fin.sum_univ_three]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem kinetic_elliptic {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (h0 : 1 < q 0) (h1 : q 1 ∈ Ioo (-1 : ℝ) 1) (v : Fin 3 → ℝ) :
    (elliptic hm hσ ha hb hc).kinetic q v =
      m / 2 * (σ ^ 2 * (q 0 ^ 2 - q 1 ^ 2) / (q 0 ^ 2 - 1) * v 0 ^ 2 +
        σ ^ 2 * (q 0 ^ 2 - q 1 ^ 2) / (1 - q 1 ^ 2) * v 1 ^ 2 +
        σ ^ 2 * (q 0 ^ 2 - 1) * (1 - q 1 ^ 2) * v 2 ^ 2) := by
  have hm' := hm.ne'
  have hσ' := hσ.ne'
  have hA : q 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
  have hB : 1 - q 1 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [h1.1, h1.2])
  have hC : q 0 ^ 2 - q 1 ^ 2 ≠ 0 := ne_of_gt (by nlinarith [h1.1, h1.2])
  simp [System.kinetic, elliptic, Fin.sum_univ_three]
  field_simp

theorem det_elliptic {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ) (ha : ContDiffOn ℝ 1 a (Ioi 1))
    (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (elliptic hm hσ ha hb hc).φ i j (q i)).det =
      -(q 0 ^ 2 - q 1 ^ 2) := by
  rw [Matrix.det_fin_three]
  simp [elliptic]
  ring

/-! ### The matrix of Stäckel is non-degenerate on the box -/

theorem det_ne_zero_spherical (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioo 0 π)) (hc : ContDiffOn ℝ 1 c univ) (q : Fin 3 → ℝ) :
    (Matrix.of fun i j => (spherical hm ha hb hc).φ i j (q i)).det ≠ 0 := by
  rw [det_spherical]
  exact one_ne_zero

theorem det_ne_zero_parabolic (hm : 0 < m) (ha : ContDiffOn ℝ 1 a (Ioi 0))
    (hb : ContDiffOn ℝ 1 b (Ioi 0)) (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (hq : q ∈ (parabolic hm ha hb hc).domain) :
    (Matrix.of fun i j => (parabolic hm ha hb hc).φ i j (q i)).det ≠ 0 := by
  have h0 : (0 : ℝ) < q 0 := hq 0
  have h1 : (0 : ℝ) < q 1 := hq 1
  rw [det_parabolic]
  exact ne_of_lt (by linarith)

theorem det_ne_zero_elliptic {σ : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (ha : ContDiffOn ℝ 1 a (Ioi 1)) (hb : ContDiffOn ℝ 1 b (Ioo (-1) 1))
    (hc : ContDiffOn ℝ 1 c univ) {q : Fin 3 → ℝ}
    (hq : q ∈ (elliptic hm hσ ha hb hc).domain) :
    (Matrix.of fun i j => (elliptic hm hσ ha hb hc).φ i j (q i)).det ≠ 0 := by
  have h0 : (1 : ℝ) < q 0 := hq 0
  have h1 : q 1 ∈ Ioo (-1 : ℝ) 1 := hq 1
  rw [det_elliptic]
  exact ne_of_lt (by nlinarith [h1.1, h1.2])

/-! ### An instance: a free particle in parabolic co-ordinates -/

/-- For a free particle in parabolic co-ordinates with the energy `1`, the
separation constant `0` and `p_φ²/2m = 1`, the separated momenta are real and
different from zero on the box `ξ > 1`, `η > 1`: the hypotheses of the theorems
on the separated action hold on this box. -/
theorem radicand_pos_parabolic_free (hm : 0 < m) (i : Fin 3) (x : ℝ)
    (hx : x ∈ (![Ioi 1, Ioi 1, univ] : Fin 3 → Set ℝ) i) :
    0 < (parabolic (a := fun _ => 0) (b := fun _ => 0) (c := fun _ => 0) hm contDiffOn_const
      contDiffOn_const contDiffOn_const).radicand i x ![1, 0, 1] := by
  fin_cases i
  · have hx' : (1 : ℝ) < x := hx
    have h1 : 0 < x - 1 / x := by
      rw [sub_pos, div_lt_iff₀ (by linarith)]
      nlinarith
    simp [System.radicand, parabolic, Fin.sum_univ_three]
    have e : 2 * (x + -1 / x) / (4 * x / m) = (x - 1 / x) * m / (2 * x) := by
      field_simp
      ring
    rw [e]
    positivity
  · have hx' : (1 : ℝ) < x := hx
    have h1 : 0 < x - 1 / x := by
      rw [sub_pos, div_lt_iff₀ (by linarith)]
      nlinarith
    simp [System.radicand, parabolic, Fin.sum_univ_three]
    have e : 2 * (x + -1 / x) / (4 * x / m) = (x - 1 / x) * m / (2 * x) := by
      field_simp
      ring
    rw [e]
    positivity
  · simp [System.radicand, parabolic, Fin.sum_univ_three]
    exact hm

end Systems

end ProjectAInos.Mechanics.Stackel
