/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.KernelFourier
public import ProjectAinos.SmoothGeometry.Potential.NewtonPotential
public import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Tactic

/-!
# The Fourier resolution of the electrostatic field

Landau–Lifshitz, *The Classical Theory of Fields*, §51. The potential of a charge density `ρ`
solves `−Δφ = ρ`; in Fourier components this reads `‖2πξ‖² 𝓕φ = 𝓕ρ`, so
`𝓕φ(ξ) = 𝓕ρ(ξ)/(4π²‖ξ‖²)` in Mathlib's normalization `𝓕 f ξ = ∫ e^{−2πi⟨x, ξ⟩} f x dx`
(Landau–Lifshitz write `φ_k = 4πρ_k/k²` with `k = 2πξ` in Gaussian units). Space is
`EuclideanSpace ℝ (Fin 3)`, and `ρ` is smooth with compact support.

The symbol `1/(4π²‖ξ‖²)` has no temperate growth at the origin, so the transform of `φ` is stated
in pairing form, as the tempered distribution `χ ↦ ∫ φ 𝓕χ`:

* `fourier_newtonPotential_apply`: for every Schwartz function `χ`,
  `∫ φ(x) 𝓕χ(x) dx = ∫ 𝓕ρ(ξ) χ(ξ)/(4π²‖ξ‖²) dξ`. The proof writes `φ = K ⋆ ρ`, moves the
  translation onto the test function by Fubini's theorem, and applies the transform of the Newton
  kernel `integral_newtonKernel_mul_fourier` of `SmoothGeometry.Potential` to the Schwartz
  function `𝓕ρ · χ`.
* `fourier_boundedTempered_newtonPotential_apply`: the same statement for the tempered
  distribution `boundedTempered φ` of the bounded function `φ`.
* `fourier_fderiv_newtonPotential_apply`: `𝓕(∂ᵥφ) = 2πi⟨ξ, v⟩ 𝓕φ`, by integration by parts
  against the test function; `fourier_electricField_apply`: the field `E = −∇φ` has the transform
  `𝓕E = −2πiξ 𝓕φ`, component by component.

**The prescription at `ξ = 0`.** The function `𝓕ρ/(4π²‖ξ‖²)` fixes the transform only away from
the origin; the potentials `φ + c` solve the same equation `−Δu = ρ`
(`neg_laplacian_newtonPotential_add_const`), and their transforms differ by a distribution
supported at `ξ = 0`:

* `fourier_newtonPotential_add_const`: `∫ (φ + c) 𝓕χ = ∫ 𝓕ρ χ/(4π²‖ξ‖²) + c χ(0)`, and in
  `𝓢′`, `fourier_boundedTempered_newtonPotential_add_const`: the transform of `φ + c` is that of
  `φ` plus `c δ₀`.
* `tendsto_newtonPotential_add_const_iff_fourier`: `φ + c` tends to `0` at infinity exactly when
  its transform has no part at `ξ = 0`, i.e. equals `𝓕ρ/(4π²‖ξ‖²)` as a distribution; both hold
  exactly when `c = 0`.
* `fourier_eq_of_tendsto`: with the uniqueness of the decaying solution of §36, every `C²`
  solution of `−Δu = ρ` that tends to `0` at infinity has the transform `𝓕ρ/(4π²‖ξ‖²)` with no
  part at `ξ = 0`.

`exists_density` and `exists_decaying_solution` show that the hypotheses are satisfiable with a
nonzero density.

Not claimed: the classification of all tempered solutions of `−Δu = ρ`. They differ from `φ` by
harmonic polynomials, whose transforms are combinations of derivatives of `δ₀`; this needs the
structure of distributions supported at a point, which Mathlib lacks. The prescription is
identified here against the constants only.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology FourierTransform SchwartzMap ContDiff Laplacian

namespace ProjectAinos.Electrodynamics.CoulombFourier

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The density and the potential as complex functions -/

/-- A smooth real density of compact support, as a complex function, is a Schwartz function. -/
theorem exists_schwartzMap_eq_ofReal {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) : ∃ ρc : 𝓢(E3, ℂ), ∀ x, ρc x = ρ x :=
  ⟨(hcρ.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hρ),
    fun _ => rfl⟩

/-- The potential of a continuous density of compact support is bounded. -/
theorem exists_abs_newtonPotential_le_const {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) : ∃ A, ∀ x, |newtonPotential ρ x| ≤ A := by
  obtain ⟨A, hA⟩ := exists_abs_newtonPotential_le hρ hcρ
  have hA0 : 0 ≤ A := by simpa using (abs_nonneg _).trans (hA 0)
  refine ⟨A, fun x => (hA x).trans ?_⟩
  exact mul_le_of_le_one_right hA0 (inv_le_one_of_one_le₀ (by simp))

/-- The potential of a continuous density of compact support is continuous. -/
theorem continuous_newtonPotential {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) : Continuous (newtonPotential ρ) :=
  (contDiff_newtonPotential (n := 0) hcρ (contDiff_zero.mpr hρ)).continuous

/-- The potential times an integrable real function is integrable. -/
theorem integrable_newtonPotential_mul {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {g : E3 → ℝ} (hg : Integrable g) :
    Integrable fun x => newtonPotential ρ x * g x := by
  obtain ⟨A, hA⟩ := exists_abs_newtonPotential_le_const hρ hcρ
  exact hg.bdd_mul (continuous_newtonPotential hρ hcρ).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hA x)

/-- The potential, as a complex function, times an integrable function is integrable. -/
theorem integrable_newtonPotential_mul_complex {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {g : E3 → ℂ} (hg : Integrable g) :
    Integrable fun x => (newtonPotential ρ x : ℂ) * g x := by
  obtain ⟨A, hA⟩ := exists_abs_newtonPotential_le_const hρ hcρ
  exact hg.bdd_mul (Complex.continuous_ofReal.comp
    (continuous_newtonPotential hρ hcρ)).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hA x)

/-! ### The transform of the potential -/

/-- **The Fourier resolution of the potential** in pairing form: for a smooth charge density `ρ`
of compact support and every Schwartz function `χ`,
`∫ φ(x) 𝓕χ(x) dx = ∫ 𝓕ρ(ξ) χ(ξ)/(4π²‖ξ‖²) dξ`. As tempered distributions,
`𝓕φ = 𝓕ρ/(4π²‖ξ‖²)`. -/
theorem fourier_newtonPotential_apply {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (newtonPotential ρ x : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) := by
  obtain ⟨ρc, hρc⟩ := exists_schwartzMap_eq_ofReal hρ hcρ
  have hρc' : (⇑ρc : E3 → ℂ) = fun x => (ρ x : ℂ) := funext hρc
  have hρ0 : Continuous ρ := hρ.continuous
  set ψ : 𝓢(E3, ℂ) := SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 ρc) χ with hψ
  have hψapply : ∀ ξ, ψ ξ = 𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ := by
    intro ξ
    rw [hψ, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply',
      SchwartzMap.fourier_coe, hρc']
  have htr : ∀ y, ∫ x, (ρ (x - y) : ℂ) * 𝓕 χ x = 𝓕 ψ y := by
    intro y
    have hint : Integrable fun x => (ρ x : ℂ) := by rw [← hρc']; exact ρc.integrable
    have hψ' : (fun ξ => 𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) = ⇑ψ := funext fun ξ => (hψapply ξ).symm
    rw [kernelFourier_integral_comp_sub_mul_fourier hint χ y, SchwartzMap.fourier_coe, hψ']
  set H : E3 → E3 → ℂ := fun x y => ((newtonKernel y * ρ (x - y) : ℝ) : ℂ) * 𝓕 χ x with hH
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hKm : Measurable newtonKernel := (measurable_norm.const_mul _).inv
    have hm : AEStronglyMeasurable (Function.uncurry H) (volume.prod volume) := by
      apply Measurable.aestronglyMeasurable
      have := hρ0.measurable
      have := (𝓕 χ).continuous.measurable
      rw [hH]
      fun_prop
    rw [integrable_prod_iff hm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simpa only [Function.uncurry_apply_pair, hH, Complex.ofRealCLM_apply] using
        (Complex.ofRealCLM.integrable_comp (integrable_newtonKernel_mul hcρ hρ0 x)).mul_const
          ((𝓕 χ) x)
    · refine (integrable_newtonPotential_mul hρ0.abs hcρ.abs (𝓕 χ).integrable.norm).congr
        (Eventually.of_forall fun x => ?_)
      simp only [Function.uncurry_apply_pair, hH, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (newtonKernel_nonneg _)]
      rw [integral_mul_const, newtonPotential_apply]
  calc ∫ x, (newtonPotential ρ x : ℂ) * 𝓕 χ x = ∫ x, ∫ y, H x y := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hH]
        rw [integral_mul_const, integral_complex_ofReal, newtonPotential_apply]
    _ = ∫ y, ∫ x, H x y := integral_integral_swap hint
    _ = ∫ y, (newtonKernel y : ℂ) * 𝓕 ψ y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hH]
        rw [← htr y, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        push_cast
        ring
    _ = ∫ ξ, (newtonSymbol ξ : ℂ) * ψ ξ := integral_newtonKernel_mul_fourier ψ
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only [hψapply]

/-! ### The transform of the field -/

open LineDeriv in
/-- **The transform of a derivative of the potential** in pairing form: for every direction `v`,
`∫ ∂ᵥφ(x) 𝓕χ(x) dx = ∫ 2πi⟨ξ, v⟩ 𝓕ρ(ξ) χ(ξ)/(4π²‖ξ‖²) dξ`, i.e. `𝓕(∂ᵥφ) = 2πi⟨ξ, v⟩ 𝓕φ`.
The proof integrates by parts against the test function, whose derivative is the transform of
`−2πi⟨ξ, v⟩χ`. -/
theorem fourier_fderiv_newtonPotential_apply {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (v : E3) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (fderiv ℝ (newtonPotential ρ) x v : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) *
        (𝓕 (fun x => (ρ x : ℂ)) ξ * (2 * π * Complex.I * inner ℝ ξ v * χ ξ)) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hφ1 : ContDiff ℝ 1 (newtonPotential ρ) := by
    have h := contDiff_newtonPotential (n := 1) hcρ (by exact_mod_cast hρ1)
    exact_mod_cast h
  have hinner : (fun ξ : E3 => inner ℝ ξ v).HasTemperateGrowth := by fun_prop
  set ψ : 𝓢(E3, ℂ) := -(2 * π * Complex.I) • SchwartzMap.smulLeftCLM ℂ (inner ℝ · v) χ with hψ
  have hψapply : ∀ ξ, ψ ξ = -(2 * π * Complex.I * inner ℝ ξ v * χ ξ) := by
    intro ξ
    rw [hψ, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hinner, smul_eq_mul,
      Complex.real_smul]
    ring
  have hD : ∀ x, fderiv ℝ (𝓕 χ : 𝓢(E3, ℂ)) x v = 𝓕 ψ x := by
    intro x
    rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_fourier_eq]
  obtain ⟨B, hB⟩ := exists_norm_fderiv_newtonPotential_le hρ1 hcρ
  have hDφc : Continuous fun x => fderiv ℝ (newtonPotential ρ) x v :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbd : ∀ x, ‖(fderiv ℝ (newtonPotential ρ) x v : ℂ)‖ ≤ B * ‖v‖ := by
    intro x
    rw [Complex.norm_real]
    refine ((fderiv ℝ (newtonPotential ρ) x).le_opNorm v).trans ?_
    gcongr
    have hB0 : 0 ≤ B := by simpa using (norm_nonneg _).trans (hB 0)
    refine (hB x).trans (mul_le_of_le_one_right hB0 ?_)
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by simp))
  have hf'g : Integrable fun x => fderiv ℝ (newtonPotential ρ) x v • 𝓕 χ x := by
    have h := ((𝓕 χ).integrable (μ := volume)).bdd_mul
      (Complex.continuous_ofReal.comp hDφc).aestronglyMeasurable (Eventually.of_forall hbd)
    simpa only [Complex.real_smul, Function.comp_def] using h
  have hfg' : Integrable fun x => newtonPotential ρ x • fderiv ℝ (𝓕 χ : 𝓢(E3, ℂ)) x v := by
    simpa only [Complex.real_smul, hD] using
      integrable_newtonPotential_mul_complex hρ.continuous hcρ (𝓕 ψ).integrable
  have hfg : Integrable fun x => newtonPotential ρ x • 𝓕 χ x := by
    simpa only [Complex.real_smul] using
      integrable_newtonPotential_mul_complex hρ.continuous hcρ (𝓕 χ).integrable
  have hparts := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hf'g hfg' hfg
    (fun x _ => hφ1.differentiable one_ne_zero x) (fun x _ => (𝓕 χ).differentiableAt)
  simp only [Complex.real_smul, hD] at hparts
  rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero] at hparts
  rw [hparts, fourier_newtonPotential_apply hρ hcρ ψ, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hψapply]
  ring

/-- **The transform of the field** `E = −∇φ` in pairing form: for every component `i`,
`∫ Eᵢ(x) 𝓕χ(x) dx = ∫ −2πiξᵢ 𝓕ρ(ξ) χ(ξ)/(4π²‖ξ‖²) dξ`, i.e. `𝓕E = −2πiξ 𝓕φ`. -/
theorem fourier_electricField_apply {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (i : Fin 3) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (-fderiv ℝ (newtonPotential ρ) x (EuclideanSpace.single i 1) : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) *
        (𝓕 (fun x => (ρ x : ℂ)) ξ * (-(2 * π * Complex.I) * ξ i * χ ξ)) := by
  have h := fourier_fderiv_newtonPotential_apply hρ hcρ (EuclideanSpace.single i 1) χ
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at h
  calc ∫ x, (-fderiv ℝ (newtonPotential ρ) x (EuclideanSpace.single i 1) : ℂ) * 𝓕 χ x
      = -∫ x, (fderiv ℝ (newtonPotential ρ) x (EuclideanSpace.single i 1) : ℂ) * 𝓕 χ x := by
        rw [← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        push_cast
        ring
    _ = _ := by
        rw [h, ← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        ring

/-! ### The prescription at `ξ = 0` -/

/-- The potentials `φ + c` solve the same equation `−Δu = ρ`. -/
theorem neg_laplacian_newtonPotential_add_const {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (c : ℝ) (x : E3) :
    -Δ (fun y => newtonPotential ρ y + c) x = ρ x := by
  have h := (contDiff_two_newtonPotential hcρ hρ).contDiffAt (x := x)
  have hc : ContDiffAt ℝ 2 (fun _ : E3 => c) x := contDiffAt_const
  rw [show (fun y => newtonPotential ρ y + c) = newtonPotential ρ + fun _ => c from rfl,
    h.laplacian_add hc, InnerProductSpace.laplacian_const, Pi.zero_apply, add_zero,
    laplacian_newtonPotential hcρ hρ, neg_neg]

/-- **A constant adds `c δ₀` to the transform**: `∫ (φ + c) 𝓕χ = ∫ 𝓕ρ χ/(4π²‖ξ‖²) + c χ(0)`. -/
theorem fourier_newtonPotential_add_const {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (c : ℝ) (χ : 𝓢(E3, ℂ)) :
    ∫ x, ((newtonPotential ρ x + c : ℝ) : ℂ) * 𝓕 χ x =
      (∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ)) + c * χ 0 := by
  have h1 := integrable_newtonPotential_mul_complex hρ.continuous hcρ (𝓕 χ).integrable
  have h2 : Integrable fun x => (c : ℂ) * 𝓕 χ x := (𝓕 χ).integrable.const_mul _
  simp only [Complex.ofReal_add, add_mul]
  rw [integral_add h1 h2, fourier_newtonPotential_apply hρ hcρ, integral_const_mul,
    integral_fourier_eq_apply_zero]

/-- The transform of `φ + c` has no part at `ξ = 0`, i.e. equals `𝓕ρ/(4π²‖ξ‖²)` as a
distribution, exactly when `c = 0`. -/
theorem fourier_newtonPotential_add_const_eq_iff {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (c : ℝ) :
    (∀ χ : 𝓢(E3, ℂ), ∫ x, ((newtonPotential ρ x + c : ℝ) : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ)) ↔ c = 0 := by
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := exists_schwartzMap_apply_zero_eq_one
    have := h χ
    rw [fourier_newtonPotential_add_const hρ hcρ, hχ, mul_one, add_eq_left] at this
    exact_mod_cast this
  · rintro rfl χ
    simpa using fourier_newtonPotential_apply hρ hcρ χ

/-- `φ + c` tends to `0` at infinity exactly when `c = 0`. -/
theorem tendsto_newtonPotential_add_const_iff {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (c : ℝ) :
    Tendsto (fun x => newtonPotential ρ x + c) (cocompact E3) (𝓝 0) ↔ c = 0 := by
  have hφ := tendsto_newtonPotential_cocompact hρ hcρ
  constructor
  · intro h
    have h2 : Tendsto (fun x => newtonPotential ρ x + c) (cocompact E3) (𝓝 (0 + c)) :=
      hφ.add_const c
    rw [zero_add] at h2
    exact tendsto_nhds_unique h2 h
  · rintro rfl
    simpa using hφ

/-- **The prescription at `ξ = 0`**: among the solutions `φ + c` of `−Δu = ρ`, the one that
tends to `0` at infinity is the one whose transform has no part at `ξ = 0`. -/
theorem tendsto_newtonPotential_add_const_iff_fourier {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (c : ℝ) :
    Tendsto (fun x => newtonPotential ρ x + c) (cocompact E3) (𝓝 0) ↔
      ∀ χ : 𝓢(E3, ℂ), ∫ x, ((newtonPotential ρ x + c : ℝ) : ℂ) * 𝓕 χ x =
        ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) := by
  rw [tendsto_newtonPotential_add_const_iff hρ.continuous hcρ,
    fourier_newtonPotential_add_const_eq_iff hρ hcρ]

/-- **The decaying solution has no part at `ξ = 0`**: a `C²` solution of `−Δu = ρ` that tends to
`0` at infinity is the Newton potential (§36), so its transform is `𝓕ρ/(4π²‖ξ‖²)`. -/
theorem fourier_eq_of_tendsto {ρ u : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hu : ContDiff ℝ 2 u) (hΔ : ∀ x, -Δ u x = ρ x) (hlim : Tendsto u (cocompact E3) (𝓝 0))
    (χ : 𝓢(E3, ℂ)) :
    ∫ x, (u x : ℂ) * 𝓕 χ x = ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) := by
  rw [eq_newtonPotential_of_tendsto hcρ (hρ.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)) hu hΔ hlim]
  exact fourier_newtonPotential_apply hρ hcρ χ

/-! ### As tempered distributions -/

open Classical in
/-- The tempered distribution `χ ↦ ∫ u χ` of an essentially bounded real function `u`, and `0`
if `u` is not essentially bounded. -/
def boundedTempered (u : E3 → ℝ) : 𝓢'(E3, ℂ) :=
  if h : MemLp (fun x => (u x : ℂ)) ⊤ then Lp.toTemperedDistribution (h.toLp _) else 0

/-- The pairing of the tempered distribution of a bounded function. -/
theorem boundedTempered_apply {u : E3 → ℝ} (hu : MemLp (fun x => (u x : ℂ)) ⊤)
    (χ : 𝓢(E3, ℂ)) : boundedTempered u χ = ∫ x, (u x : ℂ) * χ x := by
  simp only [boundedTempered, hu, ↓reduceDIte, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, smul_eq_mul, mul_comm]

/-- The potential of a continuous density of compact support is essentially bounded. -/
theorem memLp_top_newtonPotential {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) : MemLp (fun x => (newtonPotential ρ x : ℂ)) ⊤ := by
  obtain ⟨A, hA⟩ := exists_abs_newtonPotential_le_const hρ hcρ
  exact memLp_top_of_bound (Complex.continuous_ofReal.comp
    (continuous_newtonPotential hρ hcρ)).aestronglyMeasurable A
    (Eventually.of_forall fun x => by simpa using hA x)

/-- **The Fourier resolution of the potential** in `𝓢′`: the transform of the tempered
distribution of `φ` is `𝓕ρ/(4π²‖ξ‖²)`, `𝓕φ(χ) = ∫ 𝓕ρ(ξ) χ(ξ)/(4π²‖ξ‖²) dξ`. -/
theorem fourier_boundedTempered_newtonPotential_apply {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (χ : 𝓢(E3, ℂ)) :
    𝓕 (boundedTempered (newtonPotential ρ)) χ =
      ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) := by
  rw [TemperedDistribution.fourier_apply,
    boundedTempered_apply (memLp_top_newtonPotential hρ.continuous hcρ),
    fourier_newtonPotential_apply hρ hcρ]

/-- **A constant adds `c δ₀`** in `𝓢′`: the transform of `φ + c` is that of `φ` plus `c δ₀`. -/
theorem fourier_boundedTempered_newtonPotential_add_const {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (c : ℝ) :
    𝓕 (boundedTempered fun x => newtonPotential ρ x + c) =
      𝓕 (boundedTempered (newtonPotential ρ)) + (c : ℂ) • TemperedDistribution.delta 0 := by
  have hc : MemLp (fun x => ((newtonPotential ρ x + c : ℝ) : ℂ)) ⊤ := by
    simpa only [Complex.ofReal_add, Pi.add_def] using
      (memLp_top_newtonPotential hρ.continuous hcρ).add (memLp_top_const (c : ℂ))
  ext χ
  rw [TemperedDistribution.fourier_apply, boundedTempered_apply hc,
    fourier_newtonPotential_add_const hρ hcρ, add_apply,
    fourier_boundedTempered_newtonPotential_apply hρ hcρ, smul_apply,
    TemperedDistribution.delta_apply, smul_eq_mul]

/-! ### An instance -/

/-- The hypotheses are satisfiable: a smooth bump density of compact support, with value `1` at
the origin. -/
theorem exists_density : ∃ ρ : E3 → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ ρ 0 = 1 :=
  ⟨kernelFourier_bump, kernelFourier_bump.contDiff, kernelFourier_bump.hasCompactSupport,
    kernelFourier_bump.one_of_mem_closedBall (mem_closedBall_self kernelFourier_bump.rIn_pos.le)⟩

/-- The hypotheses of `fourier_eq_of_tendsto` are satisfiable with a nonzero density: the bump
density and its Newton potential, which is a decaying `C²` solution of `−Δu = ρ`. -/
theorem exists_decaying_solution : ∃ ρ u : E3 → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
    ρ 0 = 1 ∧ ContDiff ℝ 2 u ∧ (∀ x, -Δ u x = ρ x) ∧ Tendsto u (cocompact E3) (𝓝 0) := by
  obtain ⟨ρ, hρ, hcρ, hρ0⟩ := exists_density
  have hρ2 : ContDiff ℝ 2 ρ := hρ.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  exact ⟨ρ, newtonPotential ρ, hρ, hcρ, hρ0, contDiff_two_newtonPotential hcρ hρ2,
    fun x => by rw [laplacian_newtonPotential hcρ hρ2, neg_neg],
    tendsto_newtonPotential_cocompact hρ.continuous hcρ⟩

end ProjectAinos.Electrodynamics.CoulombFourier
