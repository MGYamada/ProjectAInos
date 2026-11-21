/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalCompleteness
import Mathlib.Tactic

/-! # Solid zonal harmonics

Homogenize Bonnet's recurrence in the squared radius and the linear coordinate along the axis.
Multiplication by the degree factorial clears its denominators. Differentiating along the unit
axis lowers degree, and the commutator of the Laplacian with the squared radius then gives
harmonicity. On the unit sphere the normalized solid harmonic is the Legendre polynomial.
-/

@[expose] public section
noncomputable section

open MvPolynomial Metric
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

private abbrev Poly := MvPolynomial (Fin 3) ℝ
private abbrev E := EuclideanSpace ℝ (Fin 3)

private def coord (v : E) : Poly := ∑ i, C (v i) * X i
private def along (v : E) : Poly →ₗ[ℝ] Poly := ∑ i, v i • (pderiv i).toLinearMap

private theorem partial_coord (v : E) (i : Fin 3) : pderiv i (coord v) = C (v i) := by
  classical
  simp [coord, Pi.single_apply]

private theorem along_apply (v : E) (p : Poly) : along v p = ∑ i, C (v i) * pderiv i p := by
  simp [along, LinearMap.sum_apply, smul_eq_C_mul]

private theorem along_mul (v : E) (p q : Poly) :
    along v (p * q) = along v p * q + p * along v q := by
  simp only [along_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_mul]
  ring

private theorem along_coord (v : UnitSphere 3) : along v.val (coord v.val) = 1 := by
  have h : ∑ i, v.val i ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, norm_eq_of_mem_sphere, one_pow]
  simpa only [along_apply, partial_coord, ← sq, map_sum, map_pow, map_one] using congrArg
    (C (σ := Fin 3) (R := ℝ)) h

private theorem along_radius (v : E) : along v (radiusSq 3) = 2 * coord v := by
  classical
  have h (i : Fin 3) : pderiv i (radiusSq 3) = 2 * X i := by
    simp [radiusSq, Pi.single_apply]
  simp only [along_apply, h, coord, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem lap_coord_mul (v : E) (p : Poly) :
    laplacian 3 (coord v * p) = 2 * along v p + coord v * laplacian 3 p := by
  simp only [laplacian, along_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change pderiv i (pderiv i (coord v * p)) = _
  simp [partial_coord]
  ring

private def solid (v : E) : ℕ → Poly
  | 0 => 1
  | 1 => coord v
  | n + 2 => (2 * n + 3 : ℝ) • (coord v * solid v (n + 1)) -
      ((n + 1 : ℝ) ^ 2) • (radiusSq 3 * solid v n)

private theorem homogeneous_solid (v : E) (n : ℕ) : (solid v n).IsHomogeneous n := by
  have hc : (coord v).IsHomogeneous 1 := IsHomogeneous.sum _ _ _ (fun i _ =>
    (isHomogeneous_X ℝ i).C_mul _)
  have hr : (radiusSq 3).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 2)
  induction n using Nat.twoStepInduction with
  | zero => exact isHomogeneous_one _ _
  | one => exact hc
  | more n h₀ h₁ =>
    simp only [solid, smul_eq_C_mul]
    exact ((by convert hc.mul h₁ using 1; omega :
      (coord v * solid v (n + 1)).IsHomogeneous (n + 2)).C_mul _).sub
      ((by simpa [Nat.add_comm] using hr.mul h₀ :
        (radiusSq 3 * solid v n).IsHomogeneous (n + 2)).C_mul _)

private theorem along_solid (v : UnitSphere 3) (n : ℕ) :
    along v.val (solid v.val (n + 1)) = ((n + 1 : ℝ) ^ 2) • solid v.val n := by
  have hzero : along v.val 1 = 0 := by simp [along_apply]
  induction n using Nat.twoStepInduction with
  | zero => simpa [solid] using along_coord v
  | one =>
    rw [solid.eq_3, map_sub, map_smul, map_smul, along_mul, along_mul]
    simp only [solid, along_coord, along_radius, hzero, smul_eq_C_mul, map_ofNat, map_one,
      map_zero, map_add, map_mul, map_pow, Nat.cast_one, Nat.cast_zero, one_mul]
    norm_num [map_ofNat]
    ring
  | more n h₀ h₁ =>
    rw [show solid v.val (n + 2 + 1) = _ from solid.eq_3 v.val (n + 1), map_sub, map_smul,
      map_smul, along_mul, along_mul, along_coord, along_radius, h₁, h₀]
    rw [solid.eq_3 v.val n]
    simp [smul_eq_C_mul, map_ofNat]
    ring

private theorem harmonic_solid (v : UnitSphere 3) (n : ℕ) : laplacian 3 (solid v.val n) = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact laplacian_eq_zero_of_degree_le_one (homogeneous_solid _ 0) (by decide)
  | one => exact laplacian_eq_zero_of_degree_le_one (homogeneous_solid _ 1) (by decide)
  | more n h₀ h₁ =>
    rw [solid.eq_3, map_sub, map_smul, map_smul, lap_coord_mul, laplacian_radiusSq_mul
      (homogeneous_solid _ _), h₀, h₁, along_solid]
    simp [smul_eq_C_mul, map_ofNat]
    ring

private theorem eval_solid (v u : UnitSphere 3) (n : ℕ) :
    eval u.val (solid v.val n) =
      n.factorial * (Legendre.polynomial n).eval (inner ℝ u.val v.val) := by
  have hc : eval u.val (coord v.val) = inner ℝ u.val v.val := by
    simp [coord, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have hr : eval u.val (radiusSq 3) = 1 := by
    simp [radiusSq, ← EuclideanSpace.real_norm_sq_eq, norm_eq_of_mem_sphere u]
  induction n using Nat.twoStepInduction with
  | zero => simp [solid]
  | one => simpa [solid] using hc
  | more n h₀ h₁ =>
    have h := congrArg (Polynomial.eval (inner ℝ u.val v.val)) (Legendre.recurrence n)
    simp at h
    rw [solid.eq_3, map_sub]
    simp only [smul_eq_C_mul, map_mul, eval_C, hc, hr, h₀, h₁, one_mul]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    linear_combination -((n + 1 : ℝ) * n.factorial) * h

/-- Every normalized Legendre zonal function is the restriction of a solid harmonic
of the same degree, including at the pole and antipode. -/
theorem exists_solidZonal (v : UnitSphere 3) (n : ℕ) :
    ∃ p : harmonics 3 n, ∀ u : UnitSphere 3,
      restrict 3 n p.val u = (Legendre.polynomial n).eval (inner ℝ u.val v.val) := by
  refine ⟨⟨⟨(n.factorial : ℝ)⁻¹ • solid v.val n, ?_⟩, ?_⟩, ?_⟩
  · exact (homogeneousSubmodule (Fin 3) ℝ n).smul_mem _ (homogeneous_solid _ n)
  · change laplacian 3 ((n.factorial : ℝ)⁻¹ • solid v.val n) = 0
    rw [map_smul, harmonic_solid, smul_zero]
  · intro u
    change eval u.val ((n.factorial : ℝ)⁻¹ • solid v.val n) = _
    rw [smul_eq_C_mul, map_mul, eval_C, eval_solid]
    field_simp

end ProjectAinos.SpecialFunctions.SphericalHarmonics
