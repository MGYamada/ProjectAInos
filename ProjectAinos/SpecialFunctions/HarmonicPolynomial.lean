/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Fischer decomposition of homogeneous real polynomials

On degree `k` polynomials the commutator of the Laplacian with multiplication by
`r²` is the scalar `2d + 4k`. Successive applications of the Laplacian lower the
degree by two. This proves injectivity, hence bijectivity, of `q ↦ Δ(r²q)` on each
homogeneous piece. Solving `Δ(r²q) = Δp` gives the Fischer decomposition.
-/

@[expose] public section
noncomputable section

open MvPolynomial
namespace ProjectAinos.SpecialFunctions.HarmonicPolynomial

variable {d k : ℕ}
private abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ

/-- The squared Euclidean radius as a polynomial. -/
def radiusSq (d : ℕ) : MvPolynomial (Fin d) ℝ := ∑ i, X i ^ 2

/-- The sum of the unmixed second formal partial derivatives. -/
def laplacian (d : ℕ) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] MvPolynomial (Fin d) ℝ :=
  ∑ i, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

private theorem lap_apply (p : Poly d) : laplacian d p = ∑ i, pderiv i (pderiv i p) := by
  simp [laplacian, LinearMap.sum_apply]

private theorem radius_homogeneous (d : ℕ) : (radiusSq d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 2)

private theorem lap_homogeneous {p : Poly d} (hp : p.IsHomogeneous (k + 2)) :
    (laplacian d p).IsHomogeneous k := by
  rw [lap_apply]
  exact IsHomogeneous.sum _ _ _ (fun i _ => hp.pderiv.pderiv)

private theorem pderiv_radius (i : Fin d) : pderiv i (radiusSq d) = 2 * X i := by
  classical
  simp [radiusSq, map_sum, Pi.single_apply]

/-- Euler's identity makes the commutator with the squared radius scalar in each degree. -/
theorem laplacian_radiusSq_mul {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k) :
    laplacian d (radiusSq d * p) =
      (2 * (d : ℝ) + 4 * k) • p + radiusSq d * laplacian d p := by
  have h (i : Fin d) : pderiv i (pderiv i (radiusSq d * p)) =
      2 * p + 4 * (X i * pderiv i p) + radiusSq d * pderiv i (pderiv i p) := by
    have htwo : pderiv i (2 : Poly d) = 0 := by
      simpa only [map_ofNat] using (pderiv_C (i := i) (a := (2 : ℝ)))
    simp [pderiv_radius, htwo]
    ring
  simp only [lap_apply, h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.mul_sum, hp.sum_X_mul_pderiv, nsmul_eq_mul, smul_eq_C_mul,
    map_add, map_mul, map_ofNat, map_natCast]
  ring

/-- The two initial degrees of the Fischer decomposition consist entirely of harmonics. -/
theorem laplacian_eq_zero_of_degree_le_one {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k)
    (hk : k ≤ 1) :
    laplacian d p = 0 := by
  rw [lap_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi := hp.pderiv (i := i)
  rw [show k - 1 = 0 by omega, ← totalDegree_zero_iff_isHomogeneous,
    totalDegree_eq_zero_iff_eq_C] at hi
  rw [hi, pderiv_C]

private theorem eq_zero_of_radial_relation (k : ℕ) {p : Poly d} (hp : p.IsHomogeneous k)
    {a : ℝ} (ha : 0 < a) (h : a • p + radiusSq d * laplacian d p = 0) : p = 0 := by
  induction k using Nat.strong_induction_on generalizing a p with
  | h k ih =>
    suffices hz : laplacian d p = 0 by
      rw [hz, mul_zero, add_zero, smul_eq_zero] at h
      exact h.resolve_left ha.ne'
    by_cases hk : k ≤ 1
    · exact laplacian_eq_zero_of_degree_le_one hp hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hq := lap_homogeneous hp
    apply ih j (by omega) hq (a := a + (2 * d + 4 * j))
      (by positivity)
    have hd := congrArg (laplacian d) h
    rw [map_add, map_smul, laplacian_radiusSq_mul hq, map_zero] at hd
    simpa [add_smul, add_assoc] using hd

private abbrev Hom (d k : ℕ) := homogeneousSubmodule (Fin d) ℝ k

private def radialMap (d k : ℕ) : Hom d k →ₗ[ℝ] Hom d k where
  toFun p := ⟨laplacian d (radiusSq d * p.val), lap_homogeneous
    (by simpa [add_comm] using (radius_homogeneous d).mul p.property)⟩
  map_add' p q := by ext1; simp [mul_add]
  map_smul' a p := by ext1; simp

private theorem radial_bijective (hd : 0 < d) (k : ℕ) : Function.Bijective (radialMap d k) := by
  let : FiniteDimensional ℝ (Hom d k) :=
    (Submodule.fg_iff_finiteDimensional _).mp (homogeneousSubmodule_fg _ _ _)
  suffices hi : Function.Injective (radialMap d k) from ⟨hi, LinearMap.surjective_of_injective hi⟩
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  apply Subtype.ext
  have h := congrArg Subtype.val hp
  change laplacian d (radiusSq d * p.val) = 0 at h
  rw [laplacian_radiusSq_mul p.property] at h
  exact eq_zero_of_radial_relation k p.property (by positivity) h

/-- The Fischer decomposition in positive ambient dimension. Every polynomial of degree
`k + 2` has a unique homogeneous degree-`k` radial coefficient, leaving a harmonic remainder. -/
theorem existsUnique_fischer {d k : ℕ} (hd : 0 < d) {p : MvPolynomial (Fin d) ℝ}
    (hp : p.IsHomogeneous (k + 2)) :
    ∃! q : homogeneousSubmodule (Fin d) ℝ k,
      (p - radiusSq d * q.val).IsHomogeneous (k + 2) ∧
        laplacian d (p - radiusSq d * q.val) = 0 := by
  obtain ⟨q, hq⟩ := (radial_bijective hd k).surjective ⟨laplacian d p, lap_homogeneous hp⟩
  have eqn : laplacian d (radiusSq d * q.val) = laplacian d p := congrArg Subtype.val hq
  refine ⟨q, ⟨hp.sub (by simpa [add_comm] using (radius_homogeneous d).mul q.property),
    by rw [map_sub, eqn, sub_self]⟩, ?_⟩
  intro w hw
  apply (radial_bijective hd k).injective
  apply Subtype.ext
  rw [map_sub, sub_eq_zero] at hw
  exact hw.2.symm.trans eqn.symm

/-- The harmonic subspace inside the degree-`k` homogeneous polynomials. -/
def harmonics (d k : ℕ) : Submodule ℝ (homogeneousSubmodule (Fin d) ℝ k) :=
  LinearMap.ker ((laplacian d).comp (homogeneousSubmodule (Fin d) ℝ k).subtype)

private theorem hom_finrank (d k : ℕ) :
    Module.finrank ℝ (Hom d k) = Nat.multichoose d k := by
  classical
  let s := Finset.finsuppAntidiag (Finset.univ : Finset (Fin d)) k
  have hs : {a : Fin d →₀ ℕ | a.degree = k} = (s : Set (Fin d →₀ ℕ)) := by
    ext a
    simp [s, Finsupp.degree_eq_sum]
  change Module.finrank ℝ (homogeneousSubmodule (Fin d) ℝ k) = _
  rw [homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := ℝ) (S := ℝ) (s : Set (Fin d →₀ ℕ))).finrank_eq,
    Module.finrank_finsupp_self]
  simpa [s] using (Finset.card_finsuppAntidiag_nat_eq_multichoose (s := Finset.univ (α := Fin d)) k)

/-- Rank-nullity for the surjective Laplacian in each degree at least two. -/
theorem finrank_harmonics_add (hd : 0 < d) (k : ℕ) :
    Module.finrank ℝ (harmonics d (k + 2)) + Nat.multichoose d k = Nat.multichoose d (k + 2) := by
  let : FiniteDimensional ℝ (Hom d (k + 2)) :=
    (Submodule.fg_iff_finiteDimensional _).mp (homogeneousSubmodule_fg _ _ _)
  let L := ((laplacian d).comp (Hom d (k + 2)).subtype).codRestrict (Hom d k)
    (fun p => lap_homogeneous p.property)
  have surj : Function.Surjective L := by
    intro p
    obtain ⟨q, hq⟩ := (radial_bijective hd k).surjective p
    exact ⟨⟨radiusSq d * q.val, by simpa [add_comm] using (radius_homogeneous d).mul q.property⟩,
      hq⟩
  have h := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj, finrank_top, hom_finrank, hom_finrank] at h
  rw [add_comm]
  have hker : LinearMap.ker L = harmonics d (k + 2) := LinearMap.ker_codRestrict ..
  rwa [hker] at h

/-- There are `2k + 1` independent real harmonic homogeneous polynomials in three variables. -/
theorem finrank_harmonics_three (k : ℕ) : Module.finrank ℝ (harmonics 3 k) = 2 * k + 1 := by
  by_cases hk : k ≤ 1
  · have ht : harmonics 3 k = ⊤ := Submodule.eq_top_iff'.mpr
      fun p => laplacian_eq_zero_of_degree_le_one p.property hk
    rw [ht, finrank_top, hom_finrank]
    interval_cases k <;> norm_num
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h := finrank_harmonics_add (d := 3) (by decide) j
  rw [Nat.multichoose_succ_succ 2 (j + 1), Nat.multichoose_succ_succ 2 j] at h
  norm_num only [Nat.multichoose_two, Nat.reduceAdd] at h
  omega

/-- Infinitesimal rotation in the coordinate plane indexed by `i,j`. -/
def rotation {d : ℕ} (i j : Fin d) (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  X i * pderiv j p - X j * pderiv i p

/-- The spherical Laplacian on polynomial representatives is the sum of squares of the
infinitesimal rotations. Each unordered plane occurs twice in the double sum. -/
def angularLaplacian (d : ℕ) (p : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  (1 / 2 : ℝ) • ∑ i, ∑ j, rotation i j (rotation i j p)

private theorem sum_mixed {p : Poly d} (hp : p.IsHomogeneous k) :
    ∑ i, ∑ j, X i * X j * pderiv j (pderiv i p) = (k * (k - 1) : ℕ) • p := by
  calc
    _ = ∑ i, X i * ∑ j, X j * pderiv j (pderiv i p) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i, (k - 1) • (X i * pderiv i p) := by
      simp only [hp.pderiv.sum_X_mul_pderiv, mul_smul_comm]
    _ = _ := by
      rw [← Finset.smul_sum, hp.sum_X_mul_pderiv, smul_smul, Nat.mul_comm]

/-- The angular Laplacian on harmonic polynomials of degree `k` has the
eigenvalue `−k(k + d − 2)` of the unit sphere in ambient dimension `d`. -/
theorem angularLaplacian_harmonic {p : MvPolynomial (Fin d) ℝ} (hp : p.IsHomogeneous k)
    (hh : laplacian d p = 0) :
    angularLaplacian d p = (-((k : ℝ) * (k + d - 2 : ℝ))) • p := by
  classical
  have h (i j : Fin d) : rotation i j (rotation i j p) =
      (X i ^ 2 * pderiv j (pderiv j p) + X j ^ 2 * pderiv i (pderiv i p)) -
      2 * (X i * X j * pderiv j (pderiv i p)) -
      (X i * pderiv i p + X j * pderiv j p) + (if i = j then 2 * (X i * pderiv i p) else 0) := by
    by_cases he : i = j
    · subst j
      simp [rotation]
      ring
    · simp [rotation, pderiv_comm j i p, he, Ne.symm he]
      ring
  have hrad : ∑ i : Fin d, ∑ j, (X i : Poly d) ^ 2 * pderiv j (pderiv j p) = 0 := by
    simp only [← Finset.mul_sum, ← lap_apply, hh, mul_zero, Finset.sum_const_zero]
  have hrad' : ∑ i : Fin d, ∑ j, (X j : Poly d) ^ 2 * pderiv i (pderiv i p) = 0 := by
    rw [Finset.sum_comm]
    exact hrad
  simp only [angularLaplacian, h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hrad, hrad']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.smul_sum]
  simp only [← Finset.mul_sum, sum_mixed hp, hp.sum_X_mul_pderiv, add_zero]
  simp only [smul_eq_C_mul, map_neg, map_sub, map_mul, map_add, map_natCast, map_ofNat,
    nsmul_eq_mul]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.add_one_sub_one, Nat.cast_succ, Nat.cast_mul]
    have hhalf : (C (1 / 2 : ℝ) : Poly d) * 2 = 1 := by rw [← map_ofNat C 2, ← C_mul]; norm_num
    linear_combination -((k + 1 : Poly d) * ((k : Poly d) + d - 1) * p) * hhalf

end ProjectAinos.SpecialFunctions.HarmonicPolynomial
