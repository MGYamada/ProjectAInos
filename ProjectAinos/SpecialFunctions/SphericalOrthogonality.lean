/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalHarmonics
public import ProjectAinos.SmoothGeometry.Potential.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # Orthogonality of spherical harmonics

Test Green's first identity twice with the same radial cutoff. The terms pairing the two
gradients cancel, and Euler's homogeneous identity leaves the difference of the degrees
multiplying the angular integral. The radial integral is strictly positive.
-/

@[expose] public section
noncomputable section

open MvPolynomial MeasureTheory Metric Set
open ProjectAinos.SmoothGeometry.Potential ProjectAinos.SpecialFunctions.HarmonicPolynomial
namespace ProjectAinos.SpecialFunctions.SphericalHarmonics

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
private abbrev P (d : ℕ) := MvPolynomial (Fin d) ℝ
variable {d : ℕ}

private def value (p : P d) (x : E d) := eval x p
private abbrev axis (i : Fin d) : E d := EuclideanSpace.single i 1

private theorem value_C (a : ℝ) : value (C a : P d) = fun _ => a := by funext x; simp [value]

private theorem value_add (p q : P d) : value (p + q) = fun x => value p x + value q x := by
  funext x; simp [value]

private theorem value_mul_X (p : P d) (i : Fin d) :
    value (p * X i) = value p * ⇑(EuclideanSpace.proj (𝕜 := ℝ) i) := by
  funext x; simp [value]

private theorem smooth_value (p : P d) {n : WithTop ℕ∞} : ContDiff ℝ n (value p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [value_C]; exact contDiff_const
  | add p q hp hq => rw [value_add]; exact hp.add hq
  | mul_X p i hp => rw [value_mul_X]; exact hp.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

private theorem diff_value (p : P d) (i : Fin d) (x : E d) :
    fderiv ℝ (value p) x (axis i) = value (pderiv i p) x := by
  classical
  have diff (q : P d) : DifferentiableAt ℝ (value q) x :=
    (smooth_value q (n := 1)).differentiable (by norm_num) x
  induction p using MvPolynomial.induction_on with
  | C a => rw [value_C]; simp [value]
  | add p q hp hq =>
    rw [value_add, fderiv_fun_add (diff p) (diff q), add_apply, hp, hq]
    simp [value]
  | mul_X p j hp =>
    let pr := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin d) j
    rw [value_mul_X, ((diff p).hasFDerivAt.mul pr.hasFDerivAt).fderiv]
    simp [pr, hp, value, axis, Pi.single_apply, eq_comm, mul_comm]
    split <;> simp_all

private theorem lap_value (p : P d) (x : E d) :
    coordLaplacian (value p) x = value (laplacian d p) x := by
  unfold coordLaplacian
  simp_rw [diff_value]
  simp [value, laplacian, LinearMap.sum_apply]

private def profile (s : ℝ) : ℝ := max (1 - s) 0
private def primitive (s : ℝ) : ℝ := ∫ t in s..1, profile t
private def cutoff (x : E d) := primitive (‖x‖ ^ 2)

private theorem continuous_profile : Continuous profile := by unfold profile; fun_prop

private theorem deriv_primitive (s : ℝ) : HasDerivAt primitive (-profile s) s :=
  intervalIntegral.integral_hasDerivAt_left (continuous_profile.intervalIntegrable ..)
    continuous_profile.stronglyMeasurable.stronglyMeasurableAtFilter continuous_profile.continuousAt

private theorem smooth_cutoff : ContDiff ℝ 1 (cutoff (d := d)) := by
  have hc : ContDiff ℝ 1 primitive := contDiff_one_iff_deriv.mpr
    ⟨fun s => (deriv_primitive s).differentiableAt, by
      rw [show deriv primitive = fun s => -profile s from
        funext fun s => (deriv_primitive s).deriv]
      exact continuous_profile.neg⟩
  exact hc.comp (contDiff_norm_sq ℝ)

private theorem compact_cutoff : HasCompactSupport (cutoff (d := d)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E d) 1)
  intro x hx
  by_contra hout
  have h : 1 < ‖x‖ := by simpa using hout
  apply hx
  change (∫ t in ‖x‖ ^ 2..1, profile t) = 0
  calc
    _ = ∫ _ in ‖x‖ ^ 2..1, (0 : ℝ) := intervalIntegral.integral_congr (by
      intro t ht
      have h1 : 1 ≤ ‖x‖ ^ 2 := by nlinarith
      rw [uIcc_comm, uIcc_of_le h1] at ht
      exact max_eq_right (sub_nonpos.mpr ht.1))
    _ = 0 := by simp

private theorem diff_cutoff (i : Fin d) (x : E d) :
    fderiv ℝ cutoff x (axis i) = -2 * profile (‖x‖ ^ 2) * x i := by
  unfold cutoff
  rw [(hasFDerivAt_comp_normSq (deriv_primitive (‖x‖ ^ 2))).fderiv]
  simp [axis, EuclideanSpace.inner_single_right]

private def pairing (p q : P d) (x : E d) : ℝ :=
  ∑ i, fderiv ℝ (cutoff * value p) x (axis i) * value (pderiv i q) x

private theorem integrable_pairing (p q : P d) : Integrable (pairing p q) := by
  have ht : ContDiff ℝ 1 (cutoff * value p) := smooth_cutoff.mul (smooth_value p)
  have hc : HasCompactSupport (cutoff * value p) := compact_cutoff.mul_right
  apply integrable_finsetSum
  intro i _
  exact (((ht.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
    (smooth_value (pderiv i q) (n := 1)).continuous).integrable_of_hasCompactSupport
    ((hc.fderiv_apply (𝕜 := ℝ) (axis i)).mul_right)

private theorem integral_pairing_eq_zero (p q : P d) (hq : laplacian d q = 0) :
    ∫ x, pairing p q x = 0 := by
  have h := integral_mul_coordLaplacian_eq_neg_sum
    (smooth_cutoff.mul (smooth_value p) : ContDiff ℝ 1 (cutoff * value p))
    compact_cutoff.mul_right (smooth_value q)
  simp_rw [lap_value, hq, diff_value q] at h
  change (∫ x : E d, (cutoff x * value p x) * value 0 x) = -(∫ x, pairing p q x) at h
  simpa [value] using h.symm

private theorem euler_value {p : P d} {k : ℕ} (hp : p.IsHomogeneous k) (x : E d) :
    ∑ i, x i * value (pderiv i p) x = k * value p x := by
  simpa [value, nsmul_eq_mul] using congrArg (eval x) hp.sum_X_mul_pderiv

private theorem pairing_sub {k m : ℕ} {p q : P d} (hp : p.IsHomogeneous k)
    (hq : q.IsHomogeneous m) (x : E d) :
    pairing p q x - pairing q p x =
      (2 * ((k : ℝ) - m)) * (profile (‖x‖ ^ 2) * (value p x * value q x)) := by
  have deriv_mul (s : P d) (i : Fin d) :
      fderiv ℝ (cutoff * value s) x (axis i) =
        (-2 * profile (‖x‖ ^ 2) * x i) * value s x + cutoff x * value (pderiv i s) x := by
    have h := ((smooth_cutoff.differentiable (by norm_num) x).hasFDerivAt.mul
      (((smooth_value s (n := 1)).differentiable (by norm_num) x).hasFDerivAt)).fderiv
    rw [h]
    simp [diff_value, diff_cutoff, mul_comm, add_comm]
  unfold pairing
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, ((2 * profile (‖x‖ ^ 2) * value q x) * (x i * value (pderiv i p) x) -
             (2 * profile (‖x‖ ^ 2) * value p x) * (x i * value (pderiv i q) x)) :=
      Finset.sum_congr rfl fun i _ => by rw [deriv_mul, deriv_mul]; ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
                    euler_value hp, euler_value hq]; ring

private theorem weighted_orthogonal {k m : ℕ} (hne : k ≠ m) (p : harmonics d k)
    (q : harmonics d m) :
    ∫ x : E d, profile (‖x‖ ^ 2) * (value p.val.val x * value q.val.val x) = 0 := by
  have h : ∫ x, pairing p.val.val q.val.val x - pairing q.val.val p.val.val x = 0 := by
    rw [integral_sub (integrable_pairing _ _) (integrable_pairing _ _),
      integral_pairing_eq_zero p.val.val q.val.val q.property,
      integral_pairing_eq_zero q.val.val p.val.val p.property, sub_zero]
  simp_rw [pairing_sub p.val.property q.val.property] at h
  rw [integral_const_mul, mul_eq_zero] at h
  exact h.resolve_left (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (by exact_mod_cast hne)))

private theorem radial_pos (n : ℕ) : 0 < ∫ r in Ioi (0 : ℝ), r ^ n * profile (r ^ 2) := by
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from fun r hr => hr.1) (by
      rintro r ⟨hr, h⟩
      have ht : 1 < r := lt_of_not_ge (fun h1 => h ⟨hr, h1⟩)
      simp [profile, max_eq_right (show 1 - r ^ 2 ≤ 0 by nlinarith)])]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  apply intervalIntegral.integral_pos zero_lt_one
  · exact (continuous_id.pow n |>.mul (continuous_profile.comp (continuous_id.pow 2))).continuousOn
  · exact fun r hr => mul_nonneg (pow_nonneg hr.1.le _) (le_max_right ..)
  · exact ⟨1 / 2, by norm_num, mul_pos (by positivity) (by norm_num [profile])⟩

/-- Spherical harmonics of distinct degrees are orthogonal for the surface measure.
The result holds in every positive ambient dimension, including the two-point sphere. -/
theorem integral_mul_eq_zero {k m : ℕ} (hd : 0 < d) (hne : k ≠ m)
    {f g : UnitSphere d → ℝ} (hf : f ∈ space d k) (hg : g ∈ space d m) :
    ∫ u, f u * g u ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere = 0 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨p, hp, rfl⟩ := hf
  obtain ⟨q, hq, rfl⟩ := hg
  have h := SmoothGeometry.Sphere.integral_polar_mul (volume : Measure (E d))
    (fun x => profile (‖x‖ ^ 2) * (value p.val x * value q.val x))
    (fun u => restrict d k p u * restrict d m q u) (fun r => r ^ (k + m) * profile (r ^ 2))
    (by
      intro u r hr
      simp only [norm_smul, Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere, mul_one, value,
        eval_smul p.property, eval_smul q.property, pow_add]
      change _ = eval u.val p.val * eval u.val q.val * _
      ring)
  rw [weighted_orthogonal hne ⟨p, hp⟩ ⟨q, hq⟩] at h
  have he : (∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ (E d) - 1) *
      (r ^ (k + m) * profile (r ^ 2))) ≠ 0 := by
    simpa only [pow_add, mul_assoc] using (radial_pos ((Module.finrank ℝ (E d) - 1) + (k + m))).ne'
  exact (mul_eq_zero.mp h.symm).resolve_right he

end ProjectAinos.SpecialFunctions.SphericalHarmonics
