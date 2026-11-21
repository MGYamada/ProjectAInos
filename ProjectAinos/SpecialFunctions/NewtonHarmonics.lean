/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalAddition
public import ProjectAinos.SpecialFunctions.LegendreNewton
public import ProjectAinos.SmoothGeometry.Potential.Multipole
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic

/-! # Newton multipole derivatives in spherical harmonics

Restrict both the analytic Newton kernel and the Legendre generating series to the same
line. Uniqueness of one-variable Taylor coefficients identifies every diagonal derivative.
The spherical addition theorem then separates its observation and source variables.
-/

@[expose] public section
noncomputable section

open Filter Metric MvPolynomial
open scoped Topology
open ProjectAinos.SmoothGeometry.Potential

namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

private abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The diagonal Newton derivative on two unit rays, including the Green function normalization. -/
theorem newtonKernel_unit_derivative (n : ℕ) (u v : UnitSphere 3) :
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel u.val (fun _ => -v.val) =
      (4 * Real.pi)⁻¹ * (Legendre.polynomial n).eval (inner ℝ u.val v.val) := by
  let c := inner ℝ u.val v.val
  let g (t : ℝ) := newtonKernel (u.val + t • -v.val)
  have hc : |c| ≤ 1 := by
    simpa [c, norm_eq_of_mem_sphere] using abs_real_inner_le_norm u.val v.val
  have shape (t : ℝ) : 1 - 2 * c * t + t ^ 2 = ‖u.val + t • -v.val‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, inner_neg_right, norm_smul, norm_neg,
      norm_eq_of_mem_sphere, norm_eq_of_mem_sphere, Real.norm_eq_abs, mul_one, sq_abs]
    dsimp [c]
    ring
  let a (j : ℕ) := (4 * Real.pi)⁻¹ * (Legendre.polynomial j).eval c
  have ha : HasFPowerSeriesAt g (.ofScalars ℝ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
    have h := (Legendre.hasSum_generating hc (by simpa [Real.dist_eq] using ht)).mul_left
      (4 * Real.pi)⁻¹
    rw [shape, Real.sqrt_sq (norm_nonneg _)] at h
    simpa only [a, g, newtonKernel, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add,
      mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hu : u.val ≠ 0 := by intro h; simpa [h] using norm_eq_of_mem_sphere u
  obtain ⟨P, r, hP⟩ := analyticAt_newtonKernel hu
  let b (j : ℕ) := P j (fun _ => -v.val)
  have hb : HasFPowerSeriesAt g (.ofScalars ℝ b) 0 := by
    rw [hasFPowerSeriesAt_iff]
    have hlim : Tendsto (fun t : ℝ => t • -v.val) (𝓝 0) (𝓝 0) := by
      have h : Continuous (fun t : ℝ => t • -v.val) := continuous_id.smul continuous_const
      simpa only [zero_smul] using h.tendsto 0
    filter_upwards [hlim.eventually hP.eventually_hasSum] with t ht
    simpa only [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, zero_add, g, b, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
      using ht
  have he := congrArg (fun s : FormalMultilinearSeries ℝ ℝ ℝ => s.coeff n)
    (hb.eq_formalMultilinearSeries ha)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at he
  rw [← hP.factorial_smul (-v.val), nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]
  exact he

/-- At a nonzero observation point the Legendre coefficient equals the normalized Cartesian
Taylor coefficient for every displacement, even outside the ball of convergence. -/
theorem newtonKernel_derivative_legendre (n : ℕ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0)
    (y : EuclideanSpace ℝ (Fin 3)) :
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel x (fun _ => -y) =
      newtonKernel x * ((Legendre.polynomial n).eval (inner ℝ x y / (‖x‖ * ‖y‖)) *
        (‖y‖ / ‖x‖) ^ n) := by
  by_cases hy : y = 0
  · subst y
    cases n with
    | zero => simp
    | succ n =>
      have he := (iteratedFDeriv ℝ (n + 1) newtonKernel x).map_coord_zero
        (m := fun _ => (0 : E)) (0 : Fin (n + 1)) rfl
      simp [he]
  let u : UnitSphere 3 := ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩
  let v : UnitSphere 3 := ⟨‖y‖⁻¹ • y, by simp [norm_smul, norm_ne_zero_iff.mpr hy]⟩
  have hu : ‖x‖ • u.val = x := smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) _
  have hv : ‖y‖ • v.val = y := smul_inv_smul₀ (norm_ne_zero_iff.mpr hy) _
  have hu0 : u.val ≠ 0 := by intro he; simpa [he] using norm_eq_of_mem_sphere u
  have hc : inner ℝ u.val v.val = inner ℝ x y / (‖x‖ * ‖y‖) := by
    dsimp [u, v]
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  conv_lhs =>
    rw [← hu, iteratedFDeriv_newtonKernel_smul (norm_pos_iff.mpr hx) hu0]
    arg 2; arg 2; ext i; rw [← hv, ← smul_neg]
  simp only [smul_apply, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h := newtonKernel_unit_derivative n u v
  rw [hc] at h
  calc
    _ = (‖y‖ ^ n / ‖x‖ ^ (n + 1)) *
        ((n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel u.val (fun _ => -v.val)) := by ring
    _ = _ := by rw [h]; simp only [newtonKernel, div_pow, pow_succ, mul_inv]; ring

/-- The homogeneous solid polynomial giving a mode away from the unit sphere. -/
def solidRepresentative (n : ℕ) (f : l2Space 3 n) : HarmonicPolynomial.harmonics 3 n :=
  (harmonicsEquivL2 (by decide) n).symm f

private theorem solid_on_sphere {n : ℕ} (f : l2Space 3 n) (u : UnitSphere 3) :
    eval u.val (solidRepresentative n f).val.val = representative 3 n f u := by
  have h := representative_harmonicsEquivL2 (by decide : 0 < 3) n (solidRepresentative n f)
  rw [solidRepresentative, LinearEquiv.apply_symm_apply] at h
  exact (DFunLike.congr_fun h u).symm

/-- Separation of the normalized Taylor coefficient in any real surface-orthonormal basis.
The observation radius is positive; the source displacement is arbitrary, including zero. -/
theorem newtonKernel_derivative_addition {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n + 1)) ℝ (l2Space 3 n)) (u : UnitSphere 3)
    {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin 3)) :
    (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n newtonKernel (r • u.val) (fun _ => -y) =
      ((2 * (n : ℝ) + 1) * r ^ (n + 1))⁻¹ *
        ∑ i, representative 3 n (b i) u * eval y (solidRepresentative n (b i)).val.val := by
  have hu : u.val ≠ 0 := by intro h; simpa [h] using norm_eq_of_mem_sphere u
  obtain ⟨v, hy⟩ : ∃ v : UnitSphere 3, y = ‖y‖ • v.val := by
    by_cases he : y = 0
    · exact ⟨u, by simp [he]⟩
    · exact ⟨⟨‖y‖⁻¹ • y, by simp [norm_smul, norm_ne_zero_iff.mpr he]⟩,
        (smul_inv_smul₀ (norm_ne_zero_iff.mpr he) y).symm⟩
  have hev (i) := eval_smul (solidRepresentative n (b i)).val.property ‖y‖ v.val
  conv_lhs => arg 2; arg 2; ext i; rw [hy, ← smul_neg]
  simp_rw [show ∀ i, eval y (solidRepresentative n (b i)).val.val =
      ‖y‖ ^ n * representative 3 n (b i) v from fun i =>
    (congrArg (fun w : E => eval w (solidRepresentative n (b i)).val.val) hy).trans
      ((hev i).trans (congrArg _ (solid_on_sphere (b i) v)))]
  rw [iteratedFDeriv_newtonKernel_smul hr hu]
  simp only [smul_apply, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  simp_rw [mul_left_comm (representative 3 n _ u) (‖y‖ ^ n), ← Finset.mul_sum]
  rw [addition]
  have h := newtonKernel_unit_derivative n u v
  field_simp at h ⊢
  linear_combination ‖y‖ ^ n * h

end ProjectAinos.SpecialFunctions.SphericalHarmonics
