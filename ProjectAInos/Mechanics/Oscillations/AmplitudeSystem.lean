/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.PropagatorDeformation
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The amplitude system of an oscillator with a slowly varying frequency

In the slow phase `s = ε ∫ ω dt` the complex amplitude `B` of an oscillator
whose frequency is `exp q(s)` satisfies `dB/ds = g(s) e^{2is/ε} conj B`, with
`g = q′/2`. With the conjugate as a second unknown this is the linear system

`u′ = g(z) e^{2iz/ε} w`, `w′ = g(z) e^{−2iz/ε} u`

on `ℂ × ℂ`, whose coefficient `coeff g ε z` is holomorphic in `z` where `g` is.

* `offDiag a b`: the map `(u, w) ↦ (a w, b u)`; `mulI`: the multiplication by
  `i`, which commutes with it.
* `path σ (p, s) = s + i σ ρ(p)` with a smooth step `ρ` from `0` to `1`: the
  lines parallel to the real axis between the heights `0` and `σ`.
* `contDiff_family`, `fderiv_family_one_zero`: the coefficient along the
  path is smooth and satisfies the Cauchy–Riemann equation
  `∂A/∂p = σ ρ′(p) · i ∂A/∂s`, the hypothesis of
  `SmoothGeometry.LinearODE.hasDerivAt_propagator_apply_param`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.Mechanics.AdiabaticAmplitude

open Complex (I)
open SmoothGeometry.LinearODE

/-! ### The operators -/

/-- The map `(u, w) ↦ (a w, b u)` of `ℂ × ℂ`. -/
def offDiag (a b : ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ a).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)).prod
    ((ContinuousLinearMap.mul ℝ ℂ b).comp (ContinuousLinearMap.fst ℝ ℂ ℂ))

theorem offDiag_apply (a b : ℂ) (y : ℂ × ℂ) : offDiag a b y = (a * y.2, b * y.1) := rfl

theorem norm_offDiag_le (a b : ℂ) {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖offDiag a b‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun y => ?_
  rw [offDiag_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · change ‖a * y.2‖ ≤ M * ‖y‖
    rw [norm_mul]
    exact mul_le_mul ha (norm_snd_le y) (norm_nonneg _) hM
  · change ‖b * y.1‖ ≤ M * ‖y‖
    rw [norm_mul]
    exact mul_le_mul hb (norm_fst_le y) (norm_nonneg _) hM

/-- The multiplication by `i` on `ℂ × ℂ`. -/
def mulI : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ I).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod
    ((ContinuousLinearMap.mul ℝ ℂ I).comp (ContinuousLinearMap.snd ℝ ℂ ℂ))

theorem mulI_apply (y : ℂ × ℂ) : mulI y = (I * y.1, I * y.2) := rfl

theorem norm_mulI_le (y : ℂ × ℂ) : ‖mulI y‖ ≤ ‖y‖ := by
  rw [mulI_apply, Prod.norm_def, Prod.norm_def]
  change max ‖I * y.1‖ ‖I * y.2‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]

theorem offDiag_mulI (a b : ℂ) (y : ℂ × ℂ) : offDiag a b (mulI y) = mulI (offDiag a b y) := by
  rw [offDiag_apply, mulI_apply, mulI_apply, offDiag_apply]
  exact Prod.ext (by ring) (by ring)

/-! ### The coefficient -/

/-- The coefficient `g(z) e^{2iz/ε}`. -/
def coeffPlus (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  g z * Complex.exp (((2 / ε : ℝ) : ℂ) * (I * z))

/-- The coefficient `g(z) e^{−2iz/ε}`. -/
def coeffMinus (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  g z * Complex.exp (-(((2 / ε : ℝ) : ℂ) * (I * z)))

/-- The coefficient of the amplitude system at the complex phase `z`. -/
def coeff (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  offDiag (coeffPlus g ε z) (coeffMinus g ε z)

theorem norm_coeffPlus (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    ‖coeffPlus g ε z‖ = ‖g z‖ * Real.exp (-(2 / ε * z.im)) := by
  rw [coeffPlus, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul, Complex.I_mul_re,
    mul_neg]

theorem norm_coeffMinus (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) :
    ‖coeffMinus g ε z‖ = ‖g z‖ * Real.exp (2 / ε * z.im) := by
  rw [coeffMinus, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.I_mul_re, mul_neg, neg_neg]

/-- On the strip `0 ≤ Im z ≤ σ` the coefficient is bounded by `|g(z)| e^{2σ/ε}`. -/
theorem norm_coeff_le (g : ℂ → ℂ) {ε σ : ℝ} (hε : 0 < ε) {z : ℂ} (h0 : 0 ≤ z.im)
    (hσ : z.im ≤ σ) : ‖coeff g ε z‖ ≤ ‖g z‖ * Real.exp (2 / ε * σ) := by
  have h2 : 0 < 2 / ε := by positivity
  refine norm_offDiag_le _ _ ?_ ?_
  · rw [norm_coeffPlus]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : 0 ≤ 2 / ε * z.im := mul_nonneg h2.le h0
    have h3 : 0 ≤ 2 / ε * σ := mul_nonneg h2.le (h0.trans hσ)
    linarith
  · rw [norm_coeffMinus]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ h2.le)) (norm_nonneg _)

theorem coeff_mulI (g : ℂ → ℂ) (ε : ℝ) (z : ℂ) (y : ℂ × ℂ) :
    coeff g ε z (mulI y) = mulI (coeff g ε z y) :=
  offDiag_mulI _ _ y

/-! ### The lines parallel to the real axis -/

/-- The point `s + i σ ρ(p)`, with a smooth step `ρ` from `0` to `1`. -/
def path (σ : ℝ) (q : ℝ × ℝ) : ℂ :=
  (q.2 : ℂ) + ((σ * Real.smoothTransition q.1 : ℝ) : ℂ) * I

theorem path_re (σ : ℝ) (q : ℝ × ℝ) : (path σ q).re = q.2 := by
  simp [path]

theorem path_im (σ : ℝ) (q : ℝ × ℝ) : (path σ q).im = σ * Real.smoothTransition q.1 := by
  simp [path]

theorem path_zero (σ s : ℝ) : path σ (0, s) = (s : ℂ) := by
  simp [path, Real.smoothTransition.zero_of_nonpos le_rfl]

theorem path_one (σ s : ℝ) : path σ (1, s) = (s : ℂ) + (σ : ℂ) * I := by
  simp [path, Real.smoothTransition.one_of_one_le le_rfl]

theorem path_im_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (q : ℝ × ℝ) : 0 ≤ (path σ q).im := by
  rw [path_im]
  exact mul_nonneg hσ (Real.smoothTransition.nonneg _)

theorem path_im_le {σ : ℝ} (hσ : 0 ≤ σ) (q : ℝ × ℝ) : (path σ q).im ≤ σ := by
  rw [path_im]
  exact (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) hσ).trans (mul_one σ).le

theorem contDiff_path (σ : ℝ) : ContDiff ℝ ∞ (path σ) := by
  have h1 : ContDiff ℝ ∞ fun q : ℝ × ℝ => (q.2 : ℂ) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  have h2 : ContDiff ℝ ∞ fun q : ℝ × ℝ => ((σ * Real.smoothTransition q.1 : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (Real.smoothTransition.contDiff.comp contDiff_fst))
  exact h1.add (h2.mul contDiff_const)

/-- The velocity of the path in the parameter. -/
def pathSpeed (σ p : ℝ) : ℝ := σ * deriv Real.smoothTransition p

theorem hasDerivAt_path_fst (σ p s : ℝ) :
    HasDerivAt (fun p' => path σ (p', s)) ((pathSpeed σ p : ℂ) * I) p := by
  have h0 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition p) p :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) p).hasDerivAt
  have h1 : HasDerivAt (fun p' => ((σ * Real.smoothTransition p' : ℝ) : ℂ))
      ((σ * deriv Real.smoothTransition p : ℝ) : ℂ) p := (h0.const_mul σ).ofReal_comp
  have e : (fun p' => path σ (p', s)) =
      fun p' : ℝ => (s : ℂ) + ((σ * Real.smoothTransition p' : ℝ) : ℂ) * I := rfl
  rw [e]
  exact (h1.mul_const I).const_add (s : ℂ)

theorem hasDerivAt_path_snd (σ p s : ℝ) : HasDerivAt (fun s' => path σ (p, s')) 1 s := by
  have h1 : HasDerivAt (fun s' : ℝ => (s' : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  have e : (fun s' => path σ (p, s')) =
      fun s' : ℝ => (s' : ℂ) + ((σ * Real.smoothTransition p : ℝ) : ℂ) * I := rfl
  rw [e]
  exact h1.add_const _

/-! ### The coefficient along the lines -/

section Family

variable {g : ℂ → ℂ} {U : Set ℂ} {σ : ℝ}

/-- The coefficient of the amplitude system along the lines parallel to the
real axis. -/
def family (g : ℂ → ℂ) (ε σ : ℝ) (q : ℝ × ℝ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  coeff g ε (path σ q)

theorem differentiableOn_coeffPlus (hg : DifferentiableOn ℂ g U) (ε : ℝ) :
    DifferentiableOn ℂ (coeffPlus g ε) U :=
  hg.mul ((differentiable_id.const_mul I).const_mul ((2 / ε : ℝ) : ℂ)).cexp.differentiableOn

theorem differentiableOn_coeffMinus (hg : DifferentiableOn ℂ g U) (ε : ℝ) :
    DifferentiableOn ℂ (coeffMinus g ε) U :=
  hg.mul ((differentiable_id.const_mul I).const_mul
    ((2 / ε : ℝ) : ℂ)).neg.cexp.differentiableOn

theorem contDiff_comp_path {c : ℂ → ℂ} (hU : IsOpen U) (hc : DifferentiableOn ℂ c U)
    (hmem : ∀ q, path σ q ∈ U) : ContDiff ℝ ∞ fun q => c (path σ q) :=
  ((hc.contDiffOn hU).restrict_scalars ℝ).comp_contDiff (contDiff_path σ) hmem

theorem contDiff_family (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hmem : ∀ q, path σ q ∈ U) (ε : ℝ) : ContDiff ℝ ∞ (family g ε σ) := by
  rw [contDiff_clm_apply_iff]
  intro y
  exact ((contDiff_comp_path hU (differentiableOn_coeffPlus hg ε) hmem).mul
    contDiff_const).prodMk
    ((contDiff_comp_path hU (differentiableOn_coeffMinus hg ε) hmem).mul contDiff_const)

/-- The Cauchy–Riemann equation of a holomorphic function along the path. -/
theorem fderiv_comp_path_one_zero {c : ℂ → ℂ} (hU : IsOpen U) (hc : DifferentiableOn ℂ c U)
    (hmem : ∀ q, path σ q ∈ U) (q : ℝ × ℝ) :
    fderiv ℝ (fun q => c (path σ q)) q (1, 0) =
      (pathSpeed σ q.1 : ℂ) * (I * fderiv ℝ (fun q => c (path σ q)) q (0, 1)) := by
  obtain ⟨p, s⟩ := q
  have hcz : HasDerivAt c (deriv c (path σ (p, s))) (path σ (p, s)) :=
    (hc.differentiableAt (hU.mem_nhds (hmem (p, s)))).hasDerivAt
  have hsm : DifferentiableAt ℝ (fun q => c (path σ q)) (p, s) :=
    (contDiff_comp_path hU hc hmem).differentiable (by simp) (p, s)
  have h1 := HasDerivAt.scomp p (g₁ := c) (h := fun p' => path σ (p', s)) hcz
    (hasDerivAt_path_fst σ p s)
  have h2 := HasDerivAt.scomp s (g₁ := c) (h := fun s' => path σ (p, s')) hcz
    (hasDerivAt_path_snd σ p s)
  rw [(hasDerivAt_fst_line hsm).unique h1, (hasDerivAt_snd_line hsm).unique h2]
  simp only [smul_eq_mul, one_mul]
  ring

/-- The derivative of the coefficient along the lines, on a vector. -/
theorem fderiv_family_apply (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hmem : ∀ q, path σ q ∈ U) (ε : ℝ) (q w : ℝ × ℝ) (y : ℂ × ℂ) :
    fderiv ℝ (family g ε σ) q w y =
      (fderiv ℝ (fun q => coeffPlus g ε (path σ q)) q w * y.2,
        fderiv ℝ (fun q => coeffMinus g ε (path σ q)) q w * y.1) := by
  have hA := ((contDiff_family hU hg hmem ε).differentiable (by simp) q).hasFDerivAt
  have h1 := (ContinuousLinearMap.apply ℝ (ℂ × ℂ) y).hasFDerivAt.comp q hA
  have hp := ((contDiff_comp_path hU (differentiableOn_coeffPlus hg ε) hmem).differentiable
    (by simp) q).hasFDerivAt
  have hm := ((contDiff_comp_path hU (differentiableOn_coeffMinus hg ε) hmem).differentiable
    (by simp) q).hasFDerivAt
  have h2 : HasFDerivAt
      (fun q => (coeffPlus g ε (path σ q) * y.2, coeffMinus g ε (path σ q) * y.1))
      (((fderiv ℝ (fun q => coeffPlus g ε (path σ q)) q).smulRight y.2).prod
        ((fderiv ℝ (fun q => coeffMinus g ε (path σ q)) q).smulRight y.1)) q :=
    (hp.mul_const' y.2).prodMk (hm.mul_const' y.1)
  exact congrArg (fun T : ℝ × ℝ →L[ℝ] ℂ × ℂ => T w) (h1.unique h2)

/-- The Cauchy–Riemann equation of the coefficient along the lines. -/
theorem fderiv_family_one_zero (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hmem : ∀ q, path σ q ∈ U) (ε : ℝ) (q : ℝ × ℝ) (y : ℂ × ℂ) :
    fderiv ℝ (family g ε σ) q (1, 0) y =
      pathSpeed σ q.1 • mulI (fderiv ℝ (family g ε σ) q (0, 1) y) := by
  rw [fderiv_family_apply hU hg hmem, fderiv_family_apply hU hg hmem,
    fderiv_comp_path_one_zero hU (differentiableOn_coeffPlus hg ε) hmem,
    fderiv_comp_path_one_zero hU (differentiableOn_coeffMinus hg ε) hmem, mulI_apply,
    Prod.smul_mk, Complex.real_smul, Complex.real_smul, Prod.mk.injEq]
  constructor <;> ring

theorem family_mulI (g : ℂ → ℂ) (ε σ : ℝ) (q : ℝ × ℝ) (y : ℂ × ℂ) :
    family g ε σ q (mulI y) = mulI (family g ε σ q y) :=
  coeff_mulI g ε _ y

/-- The speed of the path is bounded for the parameters between `0` and `1`. -/
theorem exists_abs_pathSpeed_le (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc (0 : ℝ) 1, |pathSpeed σ p| ≤ C := by
  have hcont : Continuous fun p => pathSpeed σ p :=
    continuous_const.mul ((Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  exact ⟨C, (norm_nonneg _).trans (hC 0 (left_mem_Icc.mpr zero_le_one)), fun p hp => hC p hp⟩

end Family

end ProjectAInos.Mechanics.AdiabaticAmplitude
