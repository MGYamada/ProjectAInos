/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HarmonicPolynomial
public import ProjectAinos.SpecialFunctions.LegendreOrthogonality
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

/-! # Restrictions of harmonic homogeneous polynomials to the Euclidean unit sphere -/

@[expose] public section
noncomputable section

open MvPolynomial Metric
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

/-- The unit sphere of the ambient real Euclidean space of dimension `d`. -/
abbrev UnitSphere (d : ℕ) := sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- Restriction of a homogeneous polynomial to the unit sphere. -/
def restrict (d k : ℕ) : homogeneousSubmodule (Fin d) ℝ k →ₗ[ℝ] (UnitSphere d → ℝ) where
  toFun p u := eval (u.val) p.val
  map_add' p q := by ext u; simp
  map_smul' a p := by ext u; simp [smul_eq_C_mul]

/-- A homogeneous polynomial evaluated along a ray scales by its degree. -/
theorem eval_smul {d k : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k)
    (a : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    eval (a • u) p = a ^ k * eval u p := by
  classical
  simp only [eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hs]
  ring

/-- Positive ambient dimension ensures that every ray meets the unit sphere. -/
theorem restrict_injective {d : ℕ} (hd : 0 < d) (k : ℕ) : Function.Injective (restrict d k) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  apply Subtype.ext
  apply MvPolynomial.funext
  intro v
  let x := WithLp.toLp 2 v
  obtain ⟨u, hu, hxu⟩ : ∃ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 ∧ ‖x‖ • u = x := by
    by_cases hz : x = 0
    · exact ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp [PiLp.norm_single], by simp [hz]⟩
    · exact ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.mpr hz],
        by simp [smul_smul, norm_ne_zero_iff.mpr hz]⟩
  have he := congrFun hp (⟨u, by simpa using hu⟩ : UnitSphere d)
  change eval u p.val = 0 at he
  change eval x p.val = 0
  rw [← hxu, eval_smul p.property, he, mul_zero]

/-- The degree-`k` real spherical harmonics as a subspace of functions on the sphere. -/
def space (d k : ℕ) : Submodule ℝ (UnitSphere d → ℝ) := (harmonics d k).map (restrict d k)

/-- Restriction preserves the dimension of each harmonic subspace. -/
theorem finrank_space {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (space d k) = Module.finrank ℝ (harmonics d k) :=
  ((harmonics d k).equivMapOfInjective _ (restrict_injective hd k)).finrank_eq.symm

theorem finrank_space_three (k : ℕ) : Module.finrank ℝ (space 3 k) = 2 * k + 1 :=
  (finrank_space (by decide) k).trans (finrank_harmonics_three k)

/-- Evaluate the angular eigenvalue equation on the sphere, using a harmonic representative. -/
theorem angular_eigenvalue {d k : ℕ} (p : harmonics d k) (u : UnitSphere d) :
    eval u.val (angularLaplacian d p.val.val) =
      -((k : ℝ) * (k + d - 2 : ℝ)) * restrict d k p.val u := by
  rw [angularLaplacian_harmonic p.val.property p.property, smul_eq_C_mul, map_mul, eval_C]
  rfl

/-- With the Laplacian sign convention, the degree-`k` eigenvalue on S³ is `−k(k + 2)`. -/
theorem angular_eigenvalue_three_sphere {k : ℕ} (p : harmonics 4 k) (u : UnitSphere 4) :
    eval u.val (angularLaplacian 4 p.val.val) = -((k : ℝ) * (k + 2)) * restrict 4 k p.val u := by
  rw [angular_eigenvalue]
  push_cast
  ring

/-- The Gram matrix of the zonal Legendre functions about any fixed unit axis on S².
The surface measure is the project measure of total mass 4π. -/
theorem integral_zonal_mul (n m : ℕ) {e : EuclideanSpace ℝ (Fin 3)} (he : ‖e‖ = 1) :
    (∫ u : UnitSphere 3, (Legendre.polynomial n).eval (inner ℝ u.val e) *
      (Legendre.polynomial m).eval (inner ℝ u.val e) ∂SmoothGeometry.Sphere.sphereMeasure) =
      if n = m then 4 * Real.pi / (2 * (n : ℝ) + 1) else 0 := by
  have h := SmoothGeometry.Sphere.integral_comp_inner he
    (((Legendre.polynomial n).continuous.mul (Legendre.polynomial m).continuous).continuousOn)
  simp only [Pi.mul_apply] at h
  rw [Legendre.integral_mul] at h
  split_ifs with hn
  · subst m
    simp only [ite_true] at h
    rw [h]
    ring
  · simpa [hn] using h

end ProjectAinos.SpecialFunctions.SphericalHarmonics
