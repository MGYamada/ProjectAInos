/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.Aperture
import Mathlib.Tactic

/-!
# Fresnel diffraction

The aperture field `apertureField k u₀` of `ProjectAinos.Electrodynamics.Diffraction.Aperture`
at the height `z` over the point `x` of the plane, compared with the integral of the quadratic
phase (Landau–Lifshitz, *The Classical Theory of Fields*, §60).

* `fresnelField k u₀ x z = (k/2πiz) e^{ikz} ∫ u₀(y) e^{ik|x−y|²/2z} dy`, **the Fresnel
  integral**: the distance `R = (|x − y|² + z²)^{1/2}` is replaced by `z + |x − y|²/2z` in the
  phase and by `z` in the amplitude, and the near-field term of the kernel is dropped.
* `norm_rayleighKernel_sub_fresnelKernel_le`: for the offset `s = |w|`,
  `|K(w, z) − F(w, z)| ≤ (k/2πz)(ks⁴/8z³ + s²/z² + 1/kz)`. The three terms are the error of the
  quadratic phase, `0 ≤ z + s²/2z − R ≤ s⁴/8z³`; the error of the amplitude,
  `1/z − z/R² ≤ s²/z³`; and the near-field term `z e^{ikR}/2πR³` of the kernel, the `−1/R` part
  of `∂_z G_k`.
* `norm_apertureField_sub_fresnelField_le`: **the Fresnel approximation with an explicit
  remainder**, `|u − u_F| ≤ (k/2πz)(kρ⁴/8z³ + ρ²/z² + 1/kz) ‖u₀‖₁` when the aperture is seen
  from `x` within the radius `ρ`, `|x − y| ≤ ρ` on the support. It is small when the Fresnel
  number `kρ²/z` is of order one and `kρ⁴/z³ ≪ 1`, `ρ ≪ z`, `kz ≫ 1`.
* `norm_apertureField_sub_fresnelField_apertureBump_le`: the instance of the smooth aperture.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Fresnel kernel `F(w, z) = (k/2πiz) e^{ikz} e^{ik|w|²/2z}`. -/
def fresnelKernel (k : ℝ) (w : E2) (z : ℝ) : ℂ :=
  k / (2 * π * I * z) * cexp (I * k * z) * cexp (I * k * ‖w‖ ^ 2 / (2 * z))

/-- **The Fresnel integral** `u_F(x, z) = (k/2πiz) e^{ikz} ∫ u₀(y) e^{ik|x−y|²/2z} dy`. -/
def fresnelField (k : ℝ) (u₀ : E2 → ℂ) (x : E2) (z : ℝ) : ℂ :=
  k / (2 * π * I * z) * cexp (I * k * z) * ∫ y, u₀ y * cexp (I * k * ‖x - y‖ ^ 2 / (2 * z))

/-- The Fresnel field as the integral of the data against the Fresnel kernel. -/
theorem fresnelField_eq (k : ℝ) (u₀ : E2 → ℂ) (x : E2) (z : ℝ) :
    fresnelField k u₀ x z = ∫ y, u₀ y * fresnelKernel k (x - y) z := by
  unfold fresnelField fresnelKernel
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- The quadratic phase: `0 ≤ z + s²/2z − (s² + z²)^{1/2} ≤ s⁴/8z³`. -/
theorem phase_sub_sqrt_le {z : ℝ} (hz : 0 < z) (s : ℝ) :
    0 ≤ z + s ^ 2 / (2 * z) - √(s ^ 2 + z ^ 2) ∧
      z + s ^ 2 / (2 * z) - √(s ^ 2 + z ^ 2) ≤ s ^ 4 / (8 * z ^ 3) := by
  set R := √(s ^ 2 + z ^ 2) with hR
  set Φ := z + s ^ 2 / (2 * z) with hΦ
  have hR2 : R ^ 2 = s ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hRz : z ≤ R := by
    rw [hR]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hΦz : z ≤ Φ := by
    have : 0 ≤ s ^ 2 / (2 * z) := by positivity
    linarith
  have hprod : (Φ - R) * (Φ + R) = s ^ 4 / (4 * z ^ 2) := by
    have : (Φ - R) * (Φ + R) = Φ ^ 2 - R ^ 2 := by ring
    rw [this, hR2, hΦ]
    field_simp
    ring
  have h0 : 0 ≤ Φ - R := by
    by_contra h
    have h1 : (Φ - R) * (Φ + R) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have h2 : 0 ≤ s ^ 4 / (4 * z ^ 2) := by positivity
    linarith
  refine ⟨h0, ?_⟩
  have h3 : (Φ - R) * (2 * z) ≤ s ^ 4 / (4 * z ^ 2) := by
    rw [← hprod]
    exact mul_le_mul_of_nonneg_left (by linarith) h0
  rw [le_div_iff₀ (by positivity)]
  have h4 : (Φ - R) * (2 * z) * (4 * z ^ 2) ≤ s ^ 4 := by
    have := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 4 * z ^ 2)
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  nlinarith

/-- **The Fresnel kernel approximates the Rayleigh–Sommerfeld kernel**:
`|K(w, z) − F(w, z)| ≤ (k/2πz)(k|w|⁴/8z³ + |w|²/z² + 1/kz)`. -/
theorem norm_rayleighKernel_sub_fresnelKernel_le {k : ℝ} (hk : 0 < k) {z : ℝ} (hz : 0 < z)
    (w : E2) :
    ‖rayleighKernel k (spacePoint w z) - fresnelKernel k w z‖ ≤
      k / (2 * π * z) * (k * ‖w‖ ^ 4 / (8 * z ^ 3) + ‖w‖ ^ 2 / z ^ 2 + 1 / (k * z)) := by
  set s := ‖w‖ with hs
  set R := √(s ^ 2 + z ^ 2) with hR
  set Φ := z + s ^ 2 / (2 * z) with hΦ
  have hR2 : R ^ 2 = s ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
  have hRz : z ≤ R := by
    rw [hR]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hR0 : 0 < R := hz.trans_le hRz
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨hΦ0, hΦ1⟩ := phase_sub_sqrt_le hz s
  -- the decomposition into the near-field, phase and amplitude errors
  have hF : fresnelKernel k w z = k / (2 * π * I * z) * cexp (I * ((k * Φ : ℝ) : ℂ)) := by
    unfold fresnelKernel
    rw [mul_assoc, ← Complex.exp_add, hΦ]
    congr 2
    push_cast
    ring
  have hK : rayleighKernel k (spacePoint w z) =
      z * (cexp (I * ((k * R : ℝ) : ℂ)) * (1 - I * k * R) / (2 * π * R ^ 3)) := by
    rw [rayleighKernel, spacePoint_apply_two, norm_spacePoint, kernelProfile, ← hs, ← hR]
    push_cast
    ring_nf
  have hdec : rayleighKernel k (spacePoint w z) - fresnelKernel k w z =
      z * cexp (I * ((k * R : ℝ) : ℂ)) / (2 * π * R ^ 3) +
        I * k / (2 * π * z) * (cexp (I * ((k * Φ : ℝ) : ℂ)) - cexp (I * ((k * R : ℝ) : ℂ))) +
        I * k / (2 * π) * cexp (I * ((k * R : ℝ) : ℂ)) * ((1 / z - z / R ^ 2 : ℝ) : ℂ) := by
    rw [hK, hF]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hdec]
  -- the three norms
  have h1 : ‖z * cexp (I * ((k * R : ℝ) : ℂ)) / (2 * π * R ^ 3)‖ = z / (2 * π * R ^ 3) := by
    rw [norm_div, norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_real, mul_one,
      Real.norm_eq_abs, abs_of_pos hz,
      show (2 * π * (R : ℂ) ^ 3) = ((2 * π * R ^ 3 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : ‖I * k / (2 * π * z) * (cexp (I * ((k * Φ : ℝ) : ℂ)) -
      cexp (I * ((k * R : ℝ) : ℂ)))‖ ≤ k / (2 * π * z) * (k * (s ^ 4 / (8 * z ^ 3))) := by
    rw [norm_mul, show I * (k : ℂ) / (2 * π * z) = I * ((k / (2 * π * z) : ℝ) : ℂ) by
      push_cast; ring, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    gcongr
    refine (norm_cexp_I_mul_sub_le _ _).trans ?_
    rw [← mul_sub, abs_mul, abs_of_pos hk, abs_of_nonneg hΦ0]
    gcongr
  have hamp : 0 ≤ 1 / z - z / R ^ 2 ∧ 1 / z - z / R ^ 2 ≤ s ^ 2 / z ^ 3 := by
    have he : 1 / z - z / R ^ 2 = s ^ 2 / (z * R ^ 2) := by
      rw [hR2]
      field_simp
      ring
    rw [he]
    refine ⟨by positivity, ?_⟩
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have h3 : ‖I * k / (2 * π) * cexp (I * ((k * R : ℝ) : ℂ)) * ((1 / z - z / R ^ 2 : ℝ) : ℂ)‖ ≤
      k / (2 * π) * (s ^ 2 / z ^ 3) := by
    rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one,
      show I * (k : ℂ) / (2 * π) = I * ((k / (2 * π) : ℝ) : ℂ) by push_cast; ring, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_nonneg hamp.1]
    gcongr
    exact hamp.2
  have h1' : z / (2 * π * R ^ 3) ≤ 1 / (2 * π * z ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : z ^ 3 ≤ R ^ 3 := by gcongr
    nlinarith [Real.pi_pos]
  calc _ ≤ ‖z * cexp (I * ((k * R : ℝ) : ℂ)) / (2 * π * R ^ 3)‖ +
        ‖I * k / (2 * π * z) * (cexp (I * ((k * Φ : ℝ) : ℂ)) -
          cexp (I * ((k * R : ℝ) : ℂ)))‖ +
        ‖I * k / (2 * π) * cexp (I * ((k * R : ℝ) : ℂ)) * ((1 / z - z / R ^ 2 : ℝ) : ℂ)‖ :=
        norm_add₃_le
    _ ≤ 1 / (2 * π * z ^ 2) + k / (2 * π * z) * (k * (s ^ 4 / (8 * z ^ 3))) +
        k / (2 * π) * (s ^ 2 / z ^ 3) := by
        rw [h1]
        gcongr
    _ = _ := by
        field_simp
        ring

/-- **The Fresnel approximation with an explicit remainder**: if `|x − y| ≤ ρ` on the support of
the aperture data, then at the height `z > 0`
`|u(x, z) − u_F(x, z)| ≤ (k/2πz)(kρ⁴/8z³ + ρ²/z² + 1/kz) ∫ |u₀|`. -/
theorem norm_apertureField_sub_fresnelField_le {k : ℝ} (hk : 0 < k) {u₀ : E2 → ℂ}
    (hc : Continuous u₀) (hs : HasCompactSupport u₀) {x : E2} {z ρ : ℝ} (hz : 0 < z)
    (hρ : ∀ y ∈ tsupport u₀, ‖x - y‖ ≤ ρ) :
    ‖apertureField k u₀ (spacePoint x z) - fresnelField k u₀ x z‖ ≤
      k / (2 * π * z) * (k * ρ ^ 4 / (8 * z ^ 3) + ρ ^ 2 / z ^ 2 + 1 / (k * z)) *
        ∫ y, ‖u₀ y‖ := by
  have hu : Integrable u₀ := hc.integrable_of_hasCompactSupport hs
  have hK : Continuous fun y => rayleighKernel k (spacePoint x z - planePoint y) :=
    (contDiffOn_rayleighKernel k (n := 0)).continuousOn.comp_continuous
      (continuous_const.sub continuous_planePoint)
      (fun y => by simpa [upperHalfSpace] using hz)
  have hF : Continuous fun y => fresnelKernel k (x - y) z := by
    unfold fresnelKernel
    fun_prop
  have hdiff : apertureField k u₀ (spacePoint x z) - fresnelField k u₀ x z =
      ∫ y, u₀ y * (rayleighKernel k (spacePoint (x - y) z) - fresnelKernel k (x - y) z) := by
    rw [fresnelField_eq, apertureField, ← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [spacePoint_sub_planePoint]
      ring
    · exact (hc.mul hK).integrable_of_hasCompactSupport hs.mul_right
    · exact (hc.mul hF).integrable_of_hasCompactSupport hs.mul_right
  set B := k / (2 * π * z) * (k * ρ ^ 4 / (8 * z ^ 3) + ρ ^ 2 / z ^ 2 + 1 / (k * z)) with hB
  rw [hdiff]
  have h : ‖∫ y, u₀ y * (rayleighKernel k (spacePoint (x - y) z) - fresnelKernel k (x - y) z)‖ ≤
      ∫ y, ‖u₀ y‖ * B := by
    refine norm_integral_le_of_norm_le (hu.norm.mul_const _) (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport u₀
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_rayleighKernel_sub_fresnelKernel_le hk hz (x - y)).trans ?_
      have h0 : 0 ≤ ‖x - y‖ := norm_nonneg _
      have hxy := hρ y hy
      rw [hB]
      gcongr
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [integral_mul_const] at h
  linarith

/-- The Fresnel approximation for the smooth aperture: on its support `|x − y| ≤ |x| + 1`. -/
theorem norm_apertureField_sub_fresnelField_apertureBump_le {k : ℝ} (hk : 0 < k) (x : E2)
    {z : ℝ} (hz : 0 < z) :
    ‖apertureField k apertureBump (spacePoint x z) - fresnelField k apertureBump x z‖ ≤
      k / (2 * π * z) * (k * (‖x‖ + 1) ^ 4 / (8 * z ^ 3) + (‖x‖ + 1) ^ 2 / z ^ 2 + 1 / (k * z)) *
        ∫ y, ‖apertureBump y‖ :=
  norm_apertureField_sub_fresnelField_le hk continuous_apertureBump
    hasCompactSupport_apertureBump hz fun y hy =>
      (norm_sub_le x y).trans (by linarith [norm_le_one_of_mem_tsupport_apertureBump hy])

end ProjectAinos.Electrodynamics.Diffraction
