/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Diffraction.Aperture
import Mathlib.Tactic

/-!
# Fraunhofer diffraction

The aperture field `apertureField k u₀` of `ProjectAinos.Electrodynamics.Diffraction.Aperture`
far from the aperture, in a fixed direction `n` (Landau–Lifshitz, *The Classical Theory of
Fields*, §61).

* `fraunhoferAmplitude k u₀ n = (k n_z/2πi) ∫ u₀(y) e^{−ik n·y} dy`: the Fourier transform of
  the aperture data at the transverse wave vector `k n_⊥`, with the obliquity factor `n_z` of
  the Rayleigh–Sommerfeld kernel.
* `norm_fraunhoferKernel_sub_le`: for `|y| ≤ a ≤ D/2`,
  `|D e^{−ikD} K(Dn − (y, 0)) − (kn_z/2πi) e^{−ik n·y}| ≤ (k/2π)(2ka²/D + 10a/D + 8/kD)`. The
  three terms are the error of the phase, `0 ≤ R − D + n·y ≤ 2a²/D`; the error of the
  amplitude, `|D²/R² − 1| ≤ 10a/D`; and the near-field term of the kernel.
* `norm_fraunhofer_sub_le`: **the far-field limit with an explicit rate**,
  `|D e^{−ikD} u(Dn) − fraunhoferAmplitude k u₀ n| ≤ (k/2π)(2ka²/D + 10a/D + 8/kD) ‖u₀‖₁`
  for data supported in `|y| ≤ a` and `D ≥ 2a`; `tendsto_fraunhofer`: the limit as `D → ∞`.
  The near-field term `8/kD` is not of the form `O(ka²/D + a/D)`: it remains for a point
  aperture.
* `babinet`, `babinet_fraunhoferAmplitude`: **Babinet's principle**, complementary aperture
  data `u₀ + u₀′ = U` that are integrable give fields and far-field amplitudes that add to those
  of the unobstructed data `U`; `babinet_disc`: the instance of a disc and the complementary
  screen in the smooth beam `apertureBump`, data with a sharp edge.
* `tendsto_babinet_planeWave`: Babinet's principle for the unobstructed plane wave of normal
  incidence, whose data `1` are not integrable: the integral of the complementary data `1 − u₀`
  over the discs `|y − x| < L` tends to `e^{ikz} − u(x, z)` (with
  `tendsto_integral_ball_rayleighKernel`); `tendsto_babinet_planeWave_apertureBump` is its
  instance.
* `tendsto_fraunhofer_apertureBump`, `norm_fraunhofer_sub_apertureBump_le`: the instances of the
  smooth aperture in the normal direction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The Fraunhofer amplitude** `(k n_z/2πi) ∫ u₀(y) e^{−ik n·y} dy` of the aperture in the
direction `n`. -/
def fraunhoferAmplitude (k : ℝ) (u₀ : E2 → ℂ) (n : E3) : ℂ :=
  k * n 2 / (2 * π * I) * ∫ y, u₀ y * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))

/-- The amplitude as the integral of the data against the plane wave `e^{−ik n·y}`. -/
theorem fraunhoferAmplitude_eq (k : ℝ) (u₀ : E2 → ℂ) (n : E3) :
    fraunhoferAmplitude k u₀ n =
      ∫ y, u₀ y * (k * n 2 / (2 * π * I) * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))) := by
  unfold fraunhoferAmplitude
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- The far-field phase: for `|n| = 1`, `|y| ≤ a ≤ D/2` and `R = |Dn − (y, 0)|`,
`0 ≤ R − D + n·y ≤ 2a²/D`, `|D² − R²| ≤ 2Da + a²` and `R ≥ D/2`. -/
theorem farField_geometry {a : ℝ} {n : E3} (hn : ‖n‖ = 1) {D : ℝ} (hD : 0 < D) {y : E2}
    (hy : ‖y‖ ≤ a) (hDa : 2 * a ≤ D) :
    D / 2 ≤ ‖D • n - planePoint y‖ ∧
      |D ^ 2 - ‖D • n - planePoint y‖ ^ 2| ≤ 2 * D * a + a ^ 2 ∧
      0 ≤ ‖D • n - planePoint y‖ - D + ⟪n, planePoint y⟫_ℝ ∧
      ‖D • n - planePoint y‖ - D + ⟪n, planePoint y⟫_ℝ ≤ 2 * a ^ 2 / D := by
  set R := ‖D • n - planePoint y‖ with hR
  set c := ⟪n, planePoint y⟫_ℝ with hc
  have hDn : ‖D • n‖ = D := by rw [norm_smul, hn, mul_one, Real.norm_eq_abs, abs_of_pos hD]
  have ha0 : 0 ≤ a := (norm_nonneg y).trans hy
  have hca : |c| ≤ ‖y‖ := by
    have := abs_real_inner_le_norm n (planePoint y)
    rwa [hn, one_mul, norm_planePoint] at this
  have hRD : D / 2 ≤ R := by
    have := half_le_norm_sub_planePoint (p := D • n) hy (by rwa [hDn])
    rwa [hDn] at this
  have hR2 : R ^ 2 = D ^ 2 - 2 * D * c + ‖y‖ ^ 2 := by
    rw [hR, norm_sub_sq_real, hDn, norm_planePoint, real_inner_smul_left]
    ring
  have hy2 : ‖y‖ ^ 2 ≤ a ^ 2 := by gcongr
  have hc2 : c ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [← sq_abs]
    gcongr
  refine ⟨hRD, ?_, ?_⟩
  · rw [hR2, show D ^ 2 - (D ^ 2 - 2 * D * c + ‖y‖ ^ 2) = 2 * D * c - ‖y‖ ^ 2 by ring]
    calc |2 * D * c - ‖y‖ ^ 2| ≤ |2 * D * c| + |‖y‖ ^ 2| := abs_sub _ _
      _ = 2 * D * |c| + ‖y‖ ^ 2 := by
        rw [abs_mul, abs_mul, abs_two, abs_of_pos hD, abs_sq]
      _ ≤ 2 * D * a + a ^ 2 := by
        gcongr
        exact hca.trans hy
  · have hsum : 0 < R + D - c := by
      have : c ≤ a := (le_abs_self c).trans (hca.trans hy)
      linarith
    have hprod : (R - D + c) * (R + D - c) = ‖y‖ ^ 2 - c ^ 2 := by
      have : (R - D + c) * (R + D - c) = R ^ 2 - (D - c) ^ 2 := by ring
      rw [this, hR2]
      ring
    have h0 : 0 ≤ R - D + c := by
      by_contra h
      have : (R - D + c) * (R + D - c) < 0 := mul_neg_of_neg_of_pos (by linarith) hsum
      linarith
    refine ⟨h0, ?_⟩
    have hD2 : D / 2 ≤ R + D - c := by
      have : c ≤ a := (le_abs_self c).trans (hca.trans hy)
      linarith
    rw [le_div_iff₀ hD]
    have h1 : (R - D + c) * (D / 2) ≤ (R - D + c) * (R + D - c) :=
      mul_le_mul_of_nonneg_left hD2 h0
    nlinarith

/-- **The kernel in the far zone**: for `|n| = 1`, `n_z > 0`, `|y| ≤ a` and `2a ≤ D`,
`|D e^{−ikD} K(Dn − (y, 0)) − (kn_z/2πi) e^{−ik n·y}| ≤ (k/2π)(2ka²/D + 10a/D + 8/kD)`. -/
theorem norm_fraunhoferKernel_sub_le {k a : ℝ} (hk : 0 < k) {n : E3} (hn : ‖n‖ = 1)
    (hnz : 0 < n 2) {D : ℝ} (hD : 0 < D) {y : E2} (hy : ‖y‖ ≤ a) (hDa : 2 * a ≤ D) :
    ‖D * cexp (-(I * k * D)) * rayleighKernel k (D • n - planePoint y) -
        k * n 2 / (2 * π * I) * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))‖ ≤
      k / (2 * π) * (2 * k * a ^ 2 / D + 10 * a / D + 8 / (k * D)) := by
  obtain ⟨hRD, hDR, hph0, hph1⟩ := farField_geometry hn hD hy hDa
  set R := ‖D • n - planePoint y‖ with hR
  set c := ⟪n, planePoint y⟫_ℝ with hc
  have ha0 : 0 ≤ a := (norm_nonneg y).trans hy
  have hR0 : 0 < R := by linarith
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn2 : n 2 ≤ 1 := by
    have := (le_abs_self _).trans (abs_apply_two_le n)
    rwa [hn] at this
  set E₁ := cexp (I * ((k * (R - D) : ℝ) : ℂ)) with hE₁
  set E₂ := cexp (I * ((-(k * c) : ℝ) : ℂ)) with hE₂
  have hK : rayleighKernel k (D • n - planePoint y) = D * n 2 * kernelProfile k R := by
    rw [rayleighKernel, sub_planePoint_apply_two, PiLp.smul_apply, smul_eq_mul, ← hR]
    push_cast
    ring
  have hdec : D * cexp (-(I * k * D)) * rayleighKernel k (D • n - planePoint y) -
        k * n 2 / (2 * π * I) * cexp (-(I * k * c)) =
      D ^ 2 * n 2 * E₁ / (2 * π * R ^ 3) -
        I * ((k * n 2 / (2 * π) : ℝ) : ℂ) * (((D ^ 2 / R ^ 2 - 1 : ℝ) : ℂ) * E₁ + (E₁ - E₂)) := by
    have h1 : cexp (-(I * k * D)) * cexp (I * k * R) = E₁ := by
      rw [hE₁, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h2 : cexp (-(I * k * c)) = E₂ := by
      rw [hE₂]
      congr 1
      push_cast
      ring
    rw [hK, kernelProfile, h2, ← h1]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [hdec]
  have hn1 : ‖E₁‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have h1 : ‖(D : ℂ) ^ 2 * n 2 * E₁ / (2 * π * R ^ 3)‖ ≤ 4 / (π * D) := by
    rw [norm_div, norm_mul, norm_mul, hn1, mul_one, norm_pow, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hD, abs_of_pos hnz,
      show (2 * π * (R : ℂ) ^ 3) = ((2 * π * R ^ 3 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc D ^ 2 * n 2 / (2 * π * R ^ 3) ≤ D ^ 2 * 1 / (2 * π * (D / 2) ^ 3) := by
          gcongr
      _ = 4 / (π * D) := by
          field_simp
          ring
  have hamp : |D ^ 2 / R ^ 2 - 1| ≤ 10 * a / D := by
    have he : D ^ 2 / R ^ 2 - 1 = (D ^ 2 - R ^ 2) / R ^ 2 := by
      field_simp
    rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < R ^ 2)]
    calc |D ^ 2 - R ^ 2| / R ^ 2 ≤ (2 * D * a + a ^ 2) / (D / 2) ^ 2 := by
          gcongr
      _ = 8 * a / D + 4 * a ^ 2 / D ^ 2 := by
          field_simp
          ring
      _ ≤ 8 * a / D + 2 * a / D := by
          have : 4 * a ^ 2 / D ^ 2 ≤ 2 * a / D := by
            rw [div_le_div_iff₀ (by positivity) hD]
            nlinarith [mul_nonneg (mul_nonneg ha0 hD.le) (sub_nonneg.mpr hDa)]
          linarith
      _ = 10 * a / D := by ring
  have hphase : ‖E₁ - E₂‖ ≤ k * (2 * a ^ 2 / D) := by
    refine (norm_cexp_I_mul_sub_le _ _).trans ?_
    rw [show k * (R - D) - -(k * c) = k * (R - D + c) by ring, abs_mul, abs_of_pos hk,
      abs_of_nonneg hph0]
    gcongr
  have h2 : ‖I * ((k * n 2 / (2 * π) : ℝ) : ℂ) * (((D ^ 2 / R ^ 2 - 1 : ℝ) : ℂ) * E₁ +
      (E₁ - E₂))‖ ≤ k / (2 * π) * (10 * a / D + k * (2 * a ^ 2 / D)) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    calc k * n 2 / (2 * π) * ‖((D ^ 2 / R ^ 2 - 1 : ℝ) : ℂ) * E₁ + (E₁ - E₂)‖
        ≤ k * 1 / (2 * π) * (‖((D ^ 2 / R ^ 2 - 1 : ℝ) : ℂ) * E₁‖ + ‖E₁ - E₂‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ k / (2 * π) * (10 * a / D + k * (2 * a ^ 2 / D)) := by
          rw [norm_mul, hn1, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_one]
          gcongr
  calc _ ≤ ‖(D : ℂ) ^ 2 * n 2 * E₁ / (2 * π * R ^ 3)‖ +
        ‖I * ((k * n 2 / (2 * π) : ℝ) : ℂ) * (((D ^ 2 / R ^ 2 - 1 : ℝ) : ℂ) * E₁ + (E₁ - E₂))‖ :=
        norm_sub_le _ _
    _ ≤ 4 / (π * D) + k / (2 * π) * (10 * a / D + k * (2 * a ^ 2 / D)) := add_le_add h1 h2
    _ = _ := by
        field_simp
        ring

/-- **The far-field limit with an explicit rate**: for data supported in `|y| ≤ a`, a unit
direction `n` with `n_z > 0` and `D ≥ 2a`,
`|D e^{−ikD} u(Dn) − fraunhoferAmplitude k u₀ n| ≤ (k/2π)(2ka²/D + 10a/D + 8/kD) ∫ |u₀|`. -/
theorem norm_fraunhofer_sub_le {k a : ℝ} (hk : 0 < k) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) (ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a) {n : E3} (hn : ‖n‖ = 1)
    (hnz : 0 < n 2) {D : ℝ} (hD : 0 < D) (hDa : 2 * a ≤ D) :
    ‖D * cexp (-(I * k * D)) * apertureField k u₀ (D • n) - fraunhoferAmplitude k u₀ n‖ ≤
      k / (2 * π) * (2 * k * a ^ 2 / D + 10 * a / D + 8 / (k * D)) * ∫ y, ‖u₀ y‖ := by
  have hu : Integrable u₀ := hc.integrable_of_hasCompactSupport hs
  have hpz : 0 < (D • n) 2 := by
    rw [PiLp.smul_apply, smul_eq_mul]
    positivity
  have hK : Continuous fun y => rayleighKernel k (D • n - planePoint y) :=
    (contDiffOn_rayleighKernel k (n := 0)).continuousOn.comp_continuous
      (continuous_const.sub continuous_planePoint)
      (fun y => by simpa [upperHalfSpace] using hpz)
  have hE : Continuous fun y => cexp (-(I * k * ⟪n, planePoint y⟫_ℝ)) := by
    have : Continuous fun y : E2 => ⟪n, planePoint y⟫_ℝ :=
      continuous_const.inner continuous_planePoint
    fun_prop
  have hdiff : D * cexp (-(I * k * D)) * apertureField k u₀ (D • n) -
        fraunhoferAmplitude k u₀ n =
      ∫ y, u₀ y * (D * cexp (-(I * k * D)) * rayleighKernel k (D • n - planePoint y) -
        k * n 2 / (2 * π * I) * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))) := by
    rw [fraunhoferAmplitude_eq, apertureField, ← integral_const_mul, ← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      ring
    · exact ((hc.mul hK).integrable_of_hasCompactSupport hs.mul_right).const_mul _
    · exact (hc.mul (continuous_const.mul hE)).integrable_of_hasCompactSupport hs.mul_right
  set B := k / (2 * π) * (2 * k * a ^ 2 / D + 10 * a / D + 8 / (k * D)) with hB
  rw [hdiff]
  have h : ‖∫ y, u₀ y * (D * cexp (-(I * k * D)) * rayleighKernel k (D • n - planePoint y) -
      k * n 2 / (2 * π * I) * cexp (-(I * k * ⟪n, planePoint y⟫_ℝ)))‖ ≤ ∫ y, ‖u₀ y‖ * B := by
    refine norm_integral_le_of_norm_le (hu.norm.mul_const _) (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport u₀
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_fraunhoferKernel_sub_le hk hn hnz hD (ha y hy) hDa) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [integral_mul_const] at h
  linarith

/-- **Fraunhofer diffraction**: in a direction `n` with `n_z > 0`, the field far from the
aperture is an outgoing spherical wave with the amplitude given by the Fourier transform of the
aperture data, `D e^{−ikD} u(Dn) → (kn_z/2πi) ∫ u₀(y) e^{−ik n·y} dy` as `D → ∞`. -/
theorem tendsto_fraunhofer {k : ℝ} (hk : 0 < k) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) {n : E3} (hn : ‖n‖ = 1) (hnz : 0 < n 2) :
    Tendsto (fun D : ℝ => D * cexp (-(I * k * D)) * apertureField k u₀ (D • n)) atTop
      (𝓝 (fraunhoferAmplitude k u₀ n)) := by
  obtain ⟨a₀, ha₀⟩ := hs.isBounded.subset_closedBall 0
  set a := max a₀ 0 with ha_def
  have ha0 : 0 ≤ a := le_max_right _ _
  have ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a := fun y hy => by
    have := ha₀ hy
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set L := ∫ y, ‖u₀ y‖ with hL
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hT : Tendsto (fun D : ℝ => k / (2 * π) * (2 * k * a ^ 2 / D + 10 * a / D +
      8 / (k * D)) * L) atTop (𝓝 0) := by
    have h1 : Tendsto (fun D : ℝ => 2 * k * a ^ 2 / D) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun D : ℝ => 10 * a / D) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h3 : Tendsto (fun D : ℝ => 8 / (k * D)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hk)
    simpa using ((h1.add h2).add h3).const_mul (k / (2 * π)) |>.mul_const L
  refine squeeze_zero' (Eventually.of_forall fun D => norm_nonneg _) ?_ hT
  filter_upwards [eventually_ge_atTop (max (2 * a) 1)] with D hD
  have hD0 : 0 < D := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hD)
  exact norm_fraunhofer_sub_le hk hc hs ha hn hnz hD0 ((le_max_left _ _).trans hD)

/-! ### Babinet's principle -/

/-- For `z > 0` the kernel is bounded on the screen, so the aperture integral converges for
integrable data. -/
theorem integrable_mul_rayleighKernel (k : ℝ) {u₀ : E2 → ℂ} (hu : Integrable u₀) {p : E3}
    (hp : 0 < p 2) : Integrable fun y => u₀ y * rayleighKernel k (p - planePoint y) := by
  have hK : Continuous fun y => rayleighKernel k (p - planePoint y) :=
    (contDiffOn_rayleighKernel k (n := 0)).continuousOn.comp_continuous
      (continuous_const.sub continuous_planePoint)
      (fun y => by simpa [upperHalfSpace] using hp)
  refine hu.mul_bdd hK.aestronglyMeasurable (c := 1 / (2 * π * p 2 ^ 2) + |k| / (2 * π * p 2))
    (Eventually.of_forall fun y => ?_)
  set q := p - planePoint y with hq
  have hq2 : q 2 = p 2 := sub_planePoint_apply_two p y
  have hz : p 2 ≤ ‖q‖ := by
    rw [← hq2]
    exact (le_abs_self _).trans (abs_apply_two_le q)
  have hR0 : 0 < ‖q‖ := hp.trans_le hz
  have hψ := norm_kernelProfile_le k hR0
  rw [rayleighKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, hq2, abs_of_pos hp]
  calc p 2 * ‖kernelProfile k ‖q‖‖ ≤ p 2 * ((1 + |k| * ‖q‖) / (2 * π * ‖q‖ ^ 3)) := by gcongr
    _ = p 2 / (2 * π * ‖q‖ ^ 3) + |k| * p 2 / (2 * π * ‖q‖ ^ 2) := by
        field_simp
    _ ≤ p 2 / (2 * π * p 2 ^ 3) + |k| * p 2 / (2 * π * p 2 ^ 2) := by gcongr
    _ = 1 / (2 * π * p 2 ^ 2) + |k| / (2 * π * p 2) := by
        field_simp

/-- **Babinet's principle**: complementary aperture data `u₀ + u₀′ = U` give fields that add to
the field of the unobstructed data `U`. -/
theorem babinet (k : ℝ) {u₀ u₀' U : E2 → ℂ} (h : ∀ y, u₀ y + u₀' y = U y) (h₁ : Integrable u₀)
    (h₂ : Integrable u₀') {p : E3} (hp : 0 < p 2) :
    apertureField k u₀ p + apertureField k u₀' p = apertureField k U p := by
  unfold apertureField
  rw [← integral_add (integrable_mul_rayleighKernel k h₁ hp)
    (integrable_mul_rayleighKernel k h₂ hp)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [← h y]
  ring

/-- Translation of an integral over a disc: `∫_{|y − x| < L} h(x − y) dy = ∫_{|w| < L} h(w) dw`. -/
theorem setIntegral_ball_sub (h : E2 → ℂ) (x : E2) (L : ℝ) :
    ∫ y in ball x L, h (x - y) = ∫ w in ball (0 : E2) L, h w := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  conv_rhs => rw [← integral_sub_left_eq_self _ volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hiff : y ∈ ball x L ↔ x - y ∈ ball (0 : E2) L := by
    rw [mem_ball, dist_eq_norm, mem_ball_zero_iff, norm_sub_rev]
  by_cases hy : y ∈ ball x L
  · simp [indicator_of_mem hy, indicator_of_mem (hiff.mp hy)]
  · simp [indicator_of_notMem hy, indicator_of_notMem (fun h => hy (hiff.mpr h))]

/-- **Babinet's principle for the unobstructed plane wave** of normal incidence: the screen
complementary to the aperture `u₀` has the data `1 − u₀`, which are not integrable; their
integral over the discs `|y − x| < L` converges to `e^{ikz} − u(x, z)`, the incident wave minus
the field of the aperture. -/
theorem tendsto_babinet_planeWave (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) (x : E2) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L => ∫ y in ball x L,
        (1 - u₀ y) * rayleighKernel k (spacePoint x z - planePoint y)) atTop
      (𝓝 (cexp (I * k * z) - apertureField k u₀ (spacePoint x z))) := by
  obtain ⟨a₀, ha₀⟩ := hs.isBounded.subset_closedBall 0
  have hK : Continuous fun y => rayleighKernel k (spacePoint x z - planePoint y) :=
    (contDiffOn_rayleighKernel k (n := 0)).continuousOn.comp_continuous
      (continuous_const.sub continuous_planePoint)
      (fun y => by simpa [upperHalfSpace] using hz)
  have hint (L : ℝ) : IntegrableOn
      (fun y => rayleighKernel k (spacePoint x z - planePoint y)) (ball x L) :=
    (hK.continuousOn.integrableOn_compact (isCompact_closedBall x L)).mono_set
      ball_subset_closedBall
  have hu : Integrable fun y => u₀ y * rayleighKernel k (spacePoint x z - planePoint y) :=
    (hc.mul hK).integrable_of_hasCompactSupport hs.mul_right
  have h1 : Tendsto (fun L => ∫ y in ball x L,
      rayleighKernel k (spacePoint x z - planePoint y)) atTop (𝓝 (cexp (I * k * z))) := by
    refine (tendsto_integral_ball_rayleighKernel k hz).congr fun L => ?_
    rw [← setIntegral_ball_sub (fun w => rayleighKernel k (spacePoint w z)) x L]
    simp only [spacePoint_sub_planePoint]
  have h2 : ∀ᶠ L in atTop, ∫ y in ball x L,
      u₀ y * rayleighKernel k (spacePoint x z - planePoint y) =
        apertureField k u₀ (spacePoint x z) := by
    filter_upwards [eventually_gt_atTop (‖x‖ + a₀)] with L hL
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro y hy
      have h0 : u₀ y = 0 := by
        by_contra h
        have h' := ha₀ (subset_tsupport _ h)
        rw [mem_closedBall, dist_zero_right] at h'
        apply hy
        rw [mem_ball, dist_eq_norm]
        calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
          _ < L := by linarith
      simp [h0]
  have h3 (L : ℝ) : ∫ y in ball x L,
      (1 - u₀ y) * rayleighKernel k (spacePoint x z - planePoint y) =
        (∫ y in ball x L, rayleighKernel k (spacePoint x z - planePoint y)) -
          ∫ y in ball x L, u₀ y * rayleighKernel k (spacePoint x z - planePoint y) := by
    rw [← integral_sub (hint L) hu.integrableOn]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  refine (h1.sub tendsto_const_nhds).congr' ?_
  filter_upwards [h2] with L hL
  rw [h3, hL]

/-- Babinet's principle for the far-field amplitudes: in a direction in which the unobstructed
amplitude vanishes, complementary apertures have opposite amplitudes, hence equal intensities. -/
theorem babinet_fraunhoferAmplitude (k : ℝ) {u₀ u₀' U : E2 → ℂ} (h : ∀ y, u₀ y + u₀' y = U y)
    (h₁ : Integrable u₀) (h₂ : Integrable u₀') (n : E3) :
    fraunhoferAmplitude k u₀ n + fraunhoferAmplitude k u₀' n = fraunhoferAmplitude k U n := by
  have hE : Continuous fun y => cexp (-(I * k * ⟪n, planePoint y⟫_ℝ)) := by
    have : Continuous fun y : E2 => ⟪n, planePoint y⟫_ℝ :=
      continuous_const.inner continuous_planePoint
    fun_prop
  have hb : ∀ y, ‖cexp (-(I * k * ⟪n, planePoint y⟫_ℝ))‖ ≤ 1 := fun y => by
    rw [show -(I * (k : ℂ) * (⟪n, planePoint y⟫_ℝ : ℂ)) =
      I * ((-(k * ⟪n, planePoint y⟫_ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_I_mul_ofReal]
  unfold fraunhoferAmplitude
  rw [← mul_add, ← integral_add (h₁.mul_bdd hE.aestronglyMeasurable
    (Eventually.of_forall hb)) (h₂.mul_bdd hE.aestronglyMeasurable (Eventually.of_forall hb))]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [← h y]
  ring

/-- Babinet's principle for a disc of radius `1/2` and the complementary screen in the smooth
beam `apertureBump`: data with a sharp edge. -/
theorem babinet_disc (k : ℝ) {p : E3} (hp : 0 < p 2) :
    apertureField k ((ball (0 : E2) (1 / 2)).indicator apertureBump) p +
        apertureField k ((ball (0 : E2) (1 / 2))ᶜ.indicator apertureBump) p =
      apertureField k apertureBump p := by
  have hχ : Integrable apertureBump :=
    continuous_apertureBump.integrable_of_hasCompactSupport hasCompactSupport_apertureBump
  exact babinet k (fun y => indicator_self_add_compl_apply _ _ y)
    (hχ.indicator measurableSet_ball) (hχ.indicator measurableSet_ball.compl) hp

/-- Babinet's principle for the plane wave and the smooth aperture: the field behind the
complementary screen `1 − χ`, at the centre, is the incident wave minus the field of `χ`. -/
theorem tendsto_babinet_planeWave_apertureBump (k : ℝ) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L => ∫ y in ball (0 : E2) L,
        (1 - apertureBump y) * rayleighKernel k (spacePoint 0 z - planePoint y)) atTop
      (𝓝 (cexp (I * k * z) - apertureField k apertureBump (spacePoint 0 z))) :=
  tendsto_babinet_planeWave k continuous_apertureBump hasCompactSupport_apertureBump 0 hz

/-! ### The smooth aperture -/

/-- The normal `e_z` is a unit vector. -/
theorem norm_single_two : ‖(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : E3)‖ = 1 := by
  simp

/-- The far field of the smooth aperture in the normal direction. -/
theorem tendsto_fraunhofer_apertureBump {k : ℝ} (hk : 0 < k) :
    Tendsto (fun D : ℝ => D * cexp (-(I * k * D)) *
        apertureField k apertureBump (D • EuclideanSpace.single 2 1)) atTop
      (𝓝 (fraunhoferAmplitude k apertureBump (EuclideanSpace.single 2 1))) :=
  tendsto_fraunhofer hk continuous_apertureBump hasCompactSupport_apertureBump norm_single_two
    (by simp)

/-- The rate of the far-field limit for the smooth aperture in the normal direction, `D ≥ 2`. -/
theorem norm_fraunhofer_sub_apertureBump_le {k : ℝ} (hk : 0 < k) {D : ℝ} (hD : 2 ≤ D) :
    ‖D * cexp (-(I * k * D)) * apertureField k apertureBump (D • EuclideanSpace.single 2 1) -
        fraunhoferAmplitude k apertureBump (EuclideanSpace.single 2 1)‖ ≤
      k / (2 * π) * (2 * k * 1 ^ 2 / D + 10 * 1 / D + 8 / (k * D)) *
        ∫ y, ‖apertureBump y‖ :=
  norm_fraunhofer_sub_le hk continuous_apertureBump hasCompactSupport_apertureBump
    (fun _ hy => norm_le_one_of_mem_tsupport_apertureBump hy) norm_single_two (by simp)
    (by linarith) (by linarith)

end ProjectAinos.Electrodynamics.Diffraction
