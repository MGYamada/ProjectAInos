/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.Fresnel
public import ProjectAinos.SpecialFunctions.Fresnel
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Fresnel diffraction by a straight edge

Place the observation point at the transverse origin. At signed distance `L u` behind the
edge the illuminated aperture starts at `−L u`. Rectangular truncations give ordinary
integrable aperture fields. Their limit as the remote sides recede gives the half-plane
pattern, in Fresnel length units `L = √(πz/k)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology Real
namespace ProjectAinos.Electrodynamics.Diffraction
open ProjectAinos.SpecialFunctions

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A uniformly illuminated straight edge truncated at distance `L R` in both coordinates. -/
def edgeAperture (L u R : ℝ) (x : E2) : ℂ :=
  (Ioc (-(L * u)) (L * R)).indicator (fun _ => (1 : ℂ)) (x 0) *
    (Ioc (-(L * R)) (L * R)).indicator (fun _ => (1 : ℂ)) (x 1)

/-- Field relative to the unobstructed wave, in units of the Fresnel length. -/
def edgeAmplitude (u : ℝ) : ℂ := (1 - I) / 2 * ((1 + I) / 2 + Fresnel.integral u)

private def phase (t : ℝ) := Complex.exp (((π / 2 * t ^ 2 : ℝ) : ℂ) * I)

private theorem scaled_integral {L : ℝ} (hL : 0 < L) (a b : ℝ) (hab : a ≤ b) :
    (∫ x : ℝ, (Ioc (L*a) (L*b)).indicator (fun x => phase (x / L)) x) =
      (L : ℂ) * (Fresnel.integral b - Fresnel.integral a) := by
  rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le
    (mul_le_mul_of_nonneg_left hab hL.le)]
  have h := intervalIntegral.smul_integral_comp_mul_left (a := a) (b := b)
    (fun x : ℝ => phase (x / L)) L
  simp only [mul_div_cancel_left₀ _ hL.ne', Complex.real_smul] at h
  rw [← h, Fresnel.integral, Fresnel.integral]
  congr 1
  exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    (a := 0) (b := a) (c := b) (f := phase)
    (Continuous.intervalIntegrable (by unfold phase; fun_prop) ..)
    (Continuous.intervalIntegrable (by unfold phase; fun_prop) ..))

private theorem rectangle {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (u R : ℝ)
    (h₁ : -u ≤ R) (h₂ : 0 ≤ R) :
    fresnelField (π * z / L ^ 2) (edgeAperture L u R) 0 z =
      Complex.exp (I * (π * z / L ^ 2 : ℝ) * z) / (2 * I) *
        ((Fresnel.integral R + Fresnel.integral u) * (2 * Fresnel.integral R)) := by
  let a : Fin 2 → ℝ := ![-u,-R]
  let g (j : Fin 2) := (Ioc (L * a j) (L * R)).indicator (fun x => phase (x / L))
  have hphase (y : E2) : Complex.exp (I * (π * z / L ^ 2 : ℝ) * ‖(0 : E2) - y‖ ^ 2 /
      (2 * z)) = phase (y 0 / L) * phase (y 1 / L) := by
    rw [zero_sub, norm_neg, ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two, phase, phase, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hz.ne', Complex.ofReal_ne_zero.mpr hL.ne']
  have he (y : E2) : edgeAperture L u R y *
      Complex.exp (I * (π * z / L ^ 2 : ℝ) * ‖(0 : E2) - y‖ ^ 2 / (2 * z)) =
      ∏ j, g j (y j) := by
    rw [hphase, Fin.prod_univ_two]
    simp only [edgeAperture, g, a, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg]
    simp only [Set.indicator]
    split_ifs <;> ring
  unfold fresnelField
  simp_rw [he]
  have ht := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp'
    (fun x : Fin 2 → ℝ => ∏ i, g i (x i))
  rw [show (∫ x : E2, ∏ i, g i (x i)) = _ from ht,
    integral_fintype_prod_volume_eq_prod, Fin.prod_univ_two]
  change _ * ((∫ t, (Ioc (L * -u) (L * R)).indicator _ t) *
    (∫ t, (Ioc (L * -R) (L * R)).indicator _ t)) = _
  rw [scaled_integral hL _ _ h₁, scaled_integral hL _ _ (by linarith : -R ≤ R),
    Fresnel.integral_neg, Fresnel.integral_neg]
  push_cast
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr hL.ne',
    Complex.ofReal_ne_zero.mpr hz.ne']
  ring

/-- The half-plane amplitude is the actual large-aperture limit of the project's Fresnel field. -/
theorem tendsto_fresnelField_edge {L z : ℝ} (hL : 0 < L) (hz : 0 < z) (u : ℝ) :
    Tendsto (fun R => fresnelField (π * z / L ^ 2) (edgeAperture L u R) 0 z) atTop
      (𝓝 (Complex.exp (I * (π * z / L ^ 2 : ℝ) * z) * edgeAmplitude u)) := by
  let w := Complex.exp (I * (π * z / L ^ 2 : ℝ) * z)
  have h := (((Fresnel.tendsto_integral_atTop.add_const (Fresnel.integral u)).mul
    (Fresnel.tendsto_integral_atTop.const_mul 2)).const_mul (w / (2 * I)))
  apply Tendsto.congr' (f₁ := fun R => w / (2 * I) *
    ((Fresnel.integral R + Fresnel.integral u) * (2 * Fresnel.integral R))) ?_ _
  · filter_upwards [eventually_ge_atTop (-u), eventually_ge_atTop 0] with R h₁ h₂
    exact (rectangle hL hz u R h₁ h₂).symm
  · convert h using 2
    change w * edgeAmplitude u = _
    unfold edgeAmplitude
    have hi : (1 - I) / 2 = (1 + I) / (2 * I) := by
      field_simp
      linear_combination -I_sq
    rw [hi]
    ring

/-- The intensity pattern is the squared distance to the endpoint of the Cornu spiral, divided by
two. It gives a quarter of the unobstructed intensity on the geometric shadow boundary. -/
theorem normSq_edgeAmplitude (u : ℝ) : Complex.normSq (edgeAmplitude u) =
    ((1 / 2 + Fresnel.cosine u) ^ 2 + (1 / 2 + Fresnel.sine u) ^ 2) / 2 := by
  rw [edgeAmplitude, Complex.normSq_mul]
  simp [Complex.normSq_apply, Fresnel.cosine, Fresnel.sine, Complex.div_ofNat_re,
    Complex.div_ofNat_im]
  ring

@[simp] theorem normSq_edgeAmplitude_zero : Complex.normSq (edgeAmplitude 0) = 1 / 4 := by
  norm_num [normSq_edgeAmplitude, Fresnel.cosine, Fresnel.sine]

end ProjectAinos.Electrodynamics.Diffraction
