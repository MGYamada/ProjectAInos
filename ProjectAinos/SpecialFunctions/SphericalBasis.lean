/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.HarmonicExtension
public import ProjectAinos.SpecialFunctions.SphericalCompleteness
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic

/-! # An explicit real basis of the spherical harmonics on S²

In degree `n` use the `n+1` homogeneous planar monomials as values on the equatorial
plane and the `n` monomials of degree `n−1` as normal derivatives there. Harmonic extension
is a finite polynomial recurrence. Reading the two initial coefficients recovers each
coordinate separately. Normalized Gram–Schmidt in this order gives an orthonormal basis
for surface measure, including the constant mode in degree zero.
-/

@[expose] public section
noncomputable section

open MvPolynomial InnerProductSpace
open ProjectAinos.SpecialFunctions.HarmonicPolynomial
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

/-- The normal power and planar exponents of the `i`-th Cauchy monomial in degree `n`.
First take the value data in order of increasing first planar exponent, then the derivative data. -/
def cauchyExponents (n : ℕ) (i : Fin (2 * n + 1)) : ℕ × (Fin 2 →₀ ℕ) :=
  let b := if i.val ≤ n then 0 else 1
  let a := if i.val ≤ n then i.val else i.val - (n + 1)
  (b, Finsupp.single 0 a + Finsupp.single 1 (n - b - a))

private theorem degree_data (n : ℕ) (i : Fin (2 * n + 1)) :
    (cauchyExponents n i).2.degree = n - (cauchyExponents n i).1 := by
  simp only [cauchyExponents, map_add, Finsupp.degree_single]
  split <;> omega

private theorem normal_le (n : ℕ) (i : Fin (2 * n + 1)) : (cauchyExponents n i).1 ≤ 1 := by
  simp [cauchyExponents]
  split <;> decide

private theorem normal_le_degree (n : ℕ) (i : Fin (2 * n + 1)) :
    (cauchyExponents n i).1 ≤ n := by
  simp [cauchyExponents]
  split <;> omega

private theorem injective_data (n : ℕ) : Function.Injective (cauchyExponents n) := by
  intro i j h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg (fun p : ℕ × (Fin 2 →₀ ℕ) => p.2 0) h
  apply Fin.ext
  simp only [cauchyExponents, Finsupp.add_apply, Finsupp.single_eq_same] at h₁ h₂
  norm_num [Finsupp.single_apply] at h₂
  split_ifs at h₁ h₂ <;> omega

theorem cauchyExponents_spec (n : ℕ) (i : Fin (2 * n + 1)) :
    (cauchyExponents n i).1 ≤ min 1 n ∧
      (cauchyExponents n i).2.degree = n - (cauchyExponents n i).1 :=
  ⟨le_min (normal_le n i) (normal_le_degree n i), degree_data n i⟩

/-- A degree-`n` harmonic solid polynomial computed from the two planar monomial lists. -/
def solidBasisVector (n : ℕ) (i : Fin (2 * n + 1)) : harmonics 3 n := by
  let b := (cauchyExponents n i).1
  let p := monomial (cauchyExponents n i).2 (1 : ℝ)
  have hp : p.IsHomogeneous (n - b) := isHomogeneous_monomial _ (cauchyExponents_spec n i).2
  refine ⟨⟨extension (n - b) b p, ?_⟩,
    harmonic_extension _ ((cauchyExponents_spec n i).1.trans (min_le_left ..)) hp⟩
  have he : b ≤ n := (cauchyExponents_spec n i).1.trans (min_le_right ..)
  change (extension (n - b) b p).IsHomogeneous n
  simpa only [Nat.add_sub_of_le he] using homogeneous_extension _ b hp

private def readCoeff (n : ℕ) (i : Fin (2 * n + 1)) : harmonics 3 n →ₗ[ℝ] ℝ :=
  (lcoeff ℝ (cauchyExponents n i).2).comp ((normalCoeff (cauchyExponents n i).1).comp
    ((homogeneousSubmodule (Fin 3) ℝ n).subtype.comp (harmonics 3 n).subtype))

private theorem read_vector (n : ℕ) (i j : Fin (2 * n + 1)) :
    readCoeff n i (solidBasisVector n j) = if j = i then 1 else 0 := by
  let a := cauchyExponents n i
  let b := cauchyExponents n j
  change (normalCoeff a.1 (extension (n - b.1) b.1 (monomial b.2 1))).coeff a.2 = _
  dsimp only [a, b]
  rw [normalCoeff_extension _ _ _ _ (by have := normal_le n i; omega)]
  by_cases h : (cauchyExponents n j).1 = (cauchyExponents n i).1
  · simp only [h, ↓reduceIte, coeff_monomial]
    have hh : (cauchyExponents n j).2 = (cauchyExponents n i).2 ↔ j = i :=
      ⟨fun he => injective_data n (Prod.ext h he), fun he => he ▸ rfl⟩
    simp [hh, eq_comm]
  · have hji : j ≠ i := fun he => h (he ▸ rfl)
    simp [h, hji]

theorem linearIndependent_solidBasisVector (n : ℕ) : LinearIndependent ℝ (solidBasisVector n) := by
  apply (Fintype.linearIndependent_iffₛ (R := ℝ) (v := solidBasisVector n)).mpr
  intro c e h i
  have he := congrArg (readCoeff n i) h
  simpa [map_sum, read_vector] using he

/-- The Cartesian harmonic basis, in the order of the two planar Cauchy data. -/
def solidBasis (n : ℕ) : Module.Basis (Fin (2 * n + 1)) ℝ (harmonics 3 n) :=
  basisOfLinearIndependentOfCardEqFinrank (K := ℝ) (V := harmonics 3 n)
    (linearIndependent_solidBasisVector n) (by simp [finrank_harmonics_three])

@[simp] theorem solidBasis_apply (n : ℕ) (i : Fin (2 * n + 1)) :
    solidBasis n i = solidBasisVector n i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) i

/-- Orthonormalize the explicit Cartesian basis for Euclidean surface measure. -/
def realBasis (n : ℕ) : OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n) :=
  gramSchmidtOrthonormalBasis (𝕜 := ℝ)
    (by simp [finrank_l2Space (by decide : 0 < 3), finrank_harmonics_three])
    (fun i => harmonicsEquivL2 (by decide : 0 < 3) n (solidBasisVector n i))

/-- Every vector of the surface-orthonormal basis is given by the normalized Gram–Schmidt
recursion on the indicated polynomials. -/
theorem realBasis_apply (n : ℕ) (i : Fin (2 * n + 1)) :
    realBasis n i = gramSchmidtNormed ℝ
      (fun j => harmonicsEquivL2 (by decide : 0 < 3) n (solidBasisVector n j)) i := by
  apply gramSchmidtOrthonormalBasis_apply
  apply (gramSchmidtNormed_linearIndependent _).ne_zero i
  exact (linearIndependent_solidBasisVector n).map_injOn
    (harmonicsEquivL2 (by decide : 0 < 3) n).toLinearMap
    (harmonicsEquivL2 (by decide : 0 < 3) n).injective.injOn

end ProjectAinos.SpecialFunctions.SphericalHarmonics
