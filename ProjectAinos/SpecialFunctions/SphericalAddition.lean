/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.ZonalHarmonics
import Mathlib.Tactic

/-! # The spherical harmonic addition theorem

The evaluation kernel of an orthonormal basis has trace `2n+1`. At each pole the normalized
zonal harmonic has value one and squared norm `4π/(2n+1)`. It gives a pointwise lower bound on
the kernel diagonal. The integral of the bound already equals the trace, so equality holds
at every pole and the evaluation kernel is the corresponding multiple of the zonal harmonic.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric
open ProjectAinos.SmoothGeometry.Sphere
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

private theorem integral_rep_sq {n : ℕ} (f : l2Space 3 n) :
    ∫ u, (representative 3 n f u) ^ 2 ∂sphereMeasure = ‖f‖ ^ 2 := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (surfaceMeasure 3)
    (representative 3 n f)
  rw [toLp_representative] at h
  rw [← real_inner_self_eq_norm_sq]
  change _ = inner ℝ f.val f.val
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h] with u hu using by simp [hu, sq]

private theorem exists_zonal_mode (n : ℕ) (v : UnitSphere 3) :
    ∃ z : l2Space 3 n,
      (∀ u, representative 3 n z u = (Legendre.polynomial n).eval (inner ℝ u.val v.val)) ∧
      ‖z‖ ^ 2 = 4 * Real.pi / (2 * (n : ℝ) + 1) := by
  obtain ⟨p, hp⟩ := exists_solidZonal v n
  let f := onSphere 3 p.val.val
  let z : l2Space 3 n := ⟨ContinuousMap.toLp 2 (surfaceMeasure 3) ℝ f,
    f, ⟨p.val, p.property, rfl⟩, rfl⟩
  have hz : representative 3 n z = f :=
    ContinuousMap.toLp_injective (surfaceMeasure 3) (toLp_representative z)
  have h u : representative 3 n z u = _ := (DFunLike.congr_fun hz u).trans (hp u)
  refine ⟨z, h, ?_⟩
  rw [← integral_rep_sq]
  simp only [h, sq]
  simpa using integral_zonal_mul n n (norm_eq_of_mem_sphere v)

private abbrev Basis (n : ℕ) := OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n)

private def kernel {n : ℕ} (b : Basis n) (v : UnitSphere 3) : l2Space 3 n :=
  ∑ i, representative 3 n (b i) v • b i

private theorem inner_kernel {n : ℕ} (b : Basis n) (v : UnitSphere 3) (f : l2Space 3 n) :
    inner ℝ (kernel b v) f = representative 3 n f v := by
  rw [kernel, sum_inner]
  simp_rw [fun i => real_inner_smul_left (b i) f (representative 3 n (b i) v)]
  have h := congrArg (fun g => representative 3 n g v) (b.sum_repr' f)
  simp only [map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul] at h
  exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans h

private theorem kernel_diag {n : ℕ} (b : Basis n) (v : UnitSphere 3) :
    ‖kernel b v‖ ^ 2 = ∑ i, (representative 3 n (b i) v) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_kernel]
  simp [kernel, ContinuousMap.sum_apply, sq]

private def scale (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) / (4 * Real.pi)

private theorem scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity

private theorem residual {n : ℕ} (b : Basis n) (v : UnitSphere 3) {z : l2Space 3 n}
    (hval : representative 3 n z v = 1)
    (hnorm : ‖z‖ ^ 2 = 4 * Real.pi / (2 * (n : ℝ) + 1)) :
    ‖kernel b v - scale n • z‖ ^ 2 =
      (∑ i, (representative 3 n (b i) v) ^ 2) - scale n := by
  rw [norm_sub_sq_real, real_inner_smul_right (kernel b v) z (scale n), inner_kernel, hval,
    norm_smul, mul_pow,
    Real.norm_of_nonneg (scale_pos n).le, hnorm, kernel_diag]
  unfold scale
  field_simp
  ring

private theorem diagonal {n : ℕ} (b : Basis n) (v : UnitSphere 3) :
    (∑ i, (representative 3 n (b i) v) ^ 2) - scale n = 0 := by
  let F (u : UnitSphere 3) := (∑ i, (representative 3 n (b i) u) ^ 2) - scale n
  have cont : Continuous F := by unfold F; fun_prop
  have pos : 0 ≤ F := by
    intro u
    obtain ⟨z, hz, hnorm⟩ := exists_zonal_mode n u
    have hval : representative 3 n z u = 1 := by
      rw [hz, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow,
        Legendre.polynomial_eval_one]
    exact le_of_le_of_eq (sq_nonneg _) (residual b u hval hnorm)
  have hi : ∫ u, F u ∂sphereMeasure = 0 := by
    unfold F
    rw [integral_sub (integrable_of_continuous (by fun_prop)) (integrable_const _),
      integral_finsetSum _ fun _ _ => integrable_of_continuous (by fun_prop)]
    simp only [integral_rep_sq, b.orthonormal.norm_eq_one, one_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, integral_const,
      sphereMeasure_real_univ, smul_eq_mul]
    unfold scale
    push_cast
    field_simp
    ring
  by_contra hn
  exact (integral_pos_of_integrable_nonneg_nonzero cont (integrable_of_continuous cont) pos hn).ne'
    hi

/-- Addition theorem on S² for any real orthonormal basis, with surface measure of mass `4π`. -/
theorem addition {n : ℕ} (b : OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n))
    (u v : UnitSphere 3) :
    ∑ i, representative 3 n (b i) u * representative 3 n (b i) v =
      (2 * (n : ℝ) + 1) / (4 * Real.pi) * (Legendre.polynomial n).eval (inner ℝ u.val v.val) := by
  obtain ⟨z, hz, hnorm⟩ := exists_zonal_mode n v
  have hval : representative 3 n z v = 1 := by
    rw [hz, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow,
        Legendre.polynomial_eval_one]
  have h := (residual b v hval hnorm).trans (diagonal b v)
  have hk : kernel b v = scale n • z := sub_eq_zero.mp (norm_eq_zero.mp (by simpa using h))
  have he := congrArg (fun f => representative 3 n f u) hk
  simp only [kernel, map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, hz, scale] at he
  exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans he

end ProjectAinos.SpecialFunctions.SphericalHarmonics
