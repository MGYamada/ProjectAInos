/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalBasis
public import ProjectAinos.SpecialFunctions.SphericalAddition
import Mathlib.Tactic

/-! # Complex spherical harmonics on the two-sphere

Complex coefficients in the Cartesian orthonormal basis give continuous spherical harmonics.
Their surface pairing is the Hermitian pairing of their coefficients, and the addition
kernel is independent of any unitary change of modes.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProjectAinos.SmoothGeometry.Sphere
open scoped ComplexConjugate
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

private abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin (2 * n + 1))
private abbrev Y (n : ℕ) (i : Fin (2 * n + 1)) := representative 3 n (realBasis n i)

/-- Synthesize a complex spherical harmonic from its coefficients in the real Cartesian basis. -/
def complexMode {n : ℕ} (c : EuclideanSpace ℂ (Fin (2 * n + 1))) : C(UnitSphere 3, ℂ) where
  toFun u := ∑ i, c i * (representative 3 n (realBasis n i) u : ℂ)
  continuous_toFun := by fun_prop

private theorem gram (n : ℕ) (i j : Fin (2 * n + 1)) :
    ∫ u, Y n i u * Y n j u ∂sphereMeasure = if i = j then 1 else 0 := by
  have hr k := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (surfaceMeasure 3) (Y n k)
  simp only [Y, toLp_representative] at hr
  rw [← orthonormal_iff_ite.mp (realBasis n).orthonormal i j]
  change _ = inner ℝ (realBasis n i).val (realBasis n j).val
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hr i, hr j] with u hi hj
  simp [Y, hi, hj]
  exact mul_comm ..

/-- The integral Hermitian pairing on the sphere agrees with the Euclidean coefficient pairing. -/
theorem integral_complexMode {n : ℕ} (c d : EuclideanSpace ℂ (Fin (2 * n + 1))) :
    ∫ u, conj (complexMode c u) * complexMode d u ∂sphereMeasure = inner ℂ c d := by
  let F (i j : Fin (2 * n + 1)) (u : UnitSphere 3) :=
    (conj (c i) * d j) * ((Y n i u * Y n j u : ℝ) : ℂ)
  have h (u : UnitSphere 3) : conj (complexMode c u) * complexMode d u =
      ∑ i, ∑ j, F i j u := by
    simp only [complexMode, ContinuousMap.coe_mk, map_sum, map_mul, Complex.conj_ofReal,
      F, Complex.ofReal_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hi i j : Integrable (F i j) sphereMeasure :=
    (show Continuous (F i j) by unfold F; fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [h, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)),
    integral_finsetSum _ (fun j _ => hi _ j)]
  simp only [F, integral_const_mul, integral_complex_ofReal, gram, PiLp.inner_apply,
    RCLike.inner_apply']
  simp [apply_ite]

private def values (n : ℕ) (u : UnitSphere 3) : V n := WithLp.toLp 2 fun i => (Y n i u : ℂ)

private theorem mode_inner {n : ℕ} (c : V n) (u : UnitSphere 3) :
    complexMode c u = inner ℂ (values n u) c := by
  simp [complexMode, PiLp.inner_apply, values, RCLike.inner_apply]

/-- The addition theorem with conjugation for every unitary choice of degree-`n` modes. -/
theorem addition_complex {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n + 1)) ℂ (EuclideanSpace ℂ (Fin (2 * n + 1))))
    (u v : UnitSphere 3) :
    ∑ i, complexMode (b i) u * conj (complexMode (b i) v) =
      (((2 * (n : ℝ) + 1) / (4 * Real.pi) *
        (Legendre.polynomial n).eval (inner ℝ u.val v.val) : ℝ) : ℂ) := by
  simp_rw [mode_inner, inner_conj_symm]
  rw [b.sum_inner_mul_inner, ← addition (realBasis n) u v, Complex.ofReal_sum]
  simp [PiLp.inner_apply, values, Y]
  exact Finset.sum_congr rfl fun _ _ => mul_comm ..

end ProjectAinos.SpecialFunctions.SphericalHarmonics
