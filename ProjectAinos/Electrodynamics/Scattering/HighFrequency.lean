/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Scattering.LowFrequency
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

/-!
# Scattering of high-frequency waves

Landau–Lifshitz, *The Classical Theory of Fields*, §80, in units with `c = 1` and `div E = k⁰`.

**Free charges at high frequencies.** At frequencies large compared with those of the motion in
the system the charges scatter as free ones:

* `abs_crossSection_sub_thomson_le`: for `ω ≥ 2|ω₀|` the cross section of the bound charge of §79
  satisfies `|σ(ω) − σ_T| ≤ σ_T · 4(ω₀² + 2γ²)/ω²`, and `crossSection_tendsto_thomson`:
  `σ(ω) → σ_T` as `ω → ∞`.

**Coherent and incoherent scattering.** For `N` identical scatterers at the positions `rₐ` the
scattered amplitudes add with the phases `e^{i q·rₐ}`, `q` the change of the wave vector, so the
cross section of the system is that of one scatterer times `|Σₐ e^{i q·rₐ}|²`. For a fixed angle of
scattering `θ ≠ 0`, `|q| = 2ω sin(θ/2)` grows with the frequency.

* `coherentFactor P q` is the mean of `|Σₐ e^{i q·rₐ}|²` over a joint distribution `P` of the
  positions; `coherentFactor_eq`: it is `Σₐ Σ_b ⟨cos⟨q, rₐ − r_b⟩⟩` (`norm_sum_exp_sq`), and
  `coherentFactor_zero`: in the forward direction it is `N²` (coherent scattering).
* `tendsto_coherentFactor`: if the relative positions of the pairs have densities
  (`HasPairDensities`), the mean factor tends to `N` as `|q| → ∞`: the scattering at short
  wavelengths is incoherent, the cross section `N` times that of one scatterer. The interference
  terms vanish by the lemma of Riemann–Lebesgue (`tendsto_integral_cos_inner`, from
  `tendsto_integral_exp_inner_smul_cocompact` applied to the density of Radon–Nikodym).
* A distribution with a density on the space of configurations has pair densities
  (`hasPairDensities_of_absolutelyContinuous`); the uniform distribution in a ball is an instance
  (`uniformConfiguration`, `tendsto_coherentFactor_uniformConfiguration`).

The scope is the classical model. When `ħω` is comparable with `mc²` the recoil of the electron
(the effect of Compton) and the quantum corrections change the cross section; they lie outside the
classical theory and are not stated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter ProbabilityTheory
open scoped Topology RealInnerProductSpace

namespace ProjectAinos.Electrodynamics.Scattering.HighFrequency

open SmoothGeometry Thomson LowFrequency
open ProjectAinos.Mechanics (responseDenominator)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The free-charge limit -/

/-- **The free-charge limit with a rate** (Landau–Lifshitz §80): for `ω ≥ 2|ω₀|` the cross section
of the bound charge differs from Thomson's by at most `σ_T · 4(ω₀² + 2γ²)/ω²`. -/
theorem abs_crossSection_sub_thomson_le (e m : ℝ) {γ ω₀ ω : ℝ} (hω : ω ≠ 0)
    (h : 4 * ω₀ ^ 2 ≤ ω ^ 2) :
    |oscillatorCrossSection e m γ ω₀ ω - thomsonCrossSection e m| ≤
      thomsonCrossSection e m * (4 * (ω₀ ^ 2 + 2 * γ ^ 2) / ω ^ 2) := by
  have hT : 0 ≤ thomsonCrossSection e m := by
    unfold thomsonCrossSection
    have : 0 < π := pi_pos
    positivity
  have hu : 0 < ω ^ 2 := by positivity
  have hw : 0 ≤ ω₀ ^ 2 := sq_nonneg ω₀
  have hc : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hD : responseDenominator γ ω₀ ω = (ω₀ ^ 2 - ω ^ 2) ^ 2 + 4 * γ ^ 2 * ω ^ 2 := rfl
  have hDlow : 9 * (ω ^ 2) ^ 2 / 16 ≤ responseDenominator γ ω₀ ω := by
    rw [hD]
    nlinarith [mul_nonneg hc hu.le]
  have hDpos : 0 < responseDenominator γ ω₀ ω := lt_of_lt_of_le (by positivity) hDlow
  have key : oscillatorCrossSection e m γ ω₀ ω - thomsonCrossSection e m =
      thomsonCrossSection e m * (((ω ^ 2) ^ 2 - responseDenominator γ ω₀ ω) /
        responseDenominator γ ω₀ ω) := by
    rw [oscillatorCrossSection]
    field_simp
  set u := ω ^ 2
  set w := ω₀ ^ 2
  set D := responseDenominator γ ω₀ ω
  have hnum : |u ^ 2 - D| ≤ (9 / 4 * w + 4 * γ ^ 2) * u := by
    rw [hD, abs_le]
    constructor <;> nlinarith [mul_nonneg hc hu.le, mul_nonneg hw hu.le]
  rw [key, abs_mul, abs_of_nonneg hT, abs_div, abs_of_pos hDpos]
  refine mul_le_mul_of_nonneg_left ?_ hT
  rw [div_le_div_iff₀ hDpos hu]
  calc |u ^ 2 - D| * u ≤ (9 / 4 * w + 4 * γ ^ 2) * u * u := by gcongr
    _ ≤ 4 * (w + 2 * γ ^ 2) * D := by
      have h1 : (9 / 4 * w + 4 * γ ^ 2) * u * u ≤ 4 * (w + 2 * γ ^ 2) * (9 * u ^ 2 / 16) := by
        nlinarith [mul_nonneg hw (sq_nonneg u), mul_nonneg hc (sq_nonneg u)]
      have h2 : 4 * (w + 2 * γ ^ 2) * (9 * u ^ 2 / 16) ≤ 4 * (w + 2 * γ ^ 2) * D :=
        mul_le_mul_of_nonneg_left hDlow (by positivity)
      linarith

/-- **At high frequencies the bound charge scatters as a free one** (Landau–Lifshitz §80):
`σ(ω) → σ_T` as `ω → ∞`, for any `γ` and `ω₀`. -/
theorem crossSection_tendsto_thomson (e m γ ω₀ : ℝ) :
    Tendsto (fun ω => oscillatorCrossSection e m γ ω₀ ω) atTop (𝓝 (thomsonCrossSection e m)) := by
  have hb : Tendsto (fun ω : ℝ => thomsonCrossSection e m * (4 * (ω₀ ^ 2 + 2 * γ ^ 2) / ω ^ 2))
      atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := 4 * (ω₀ ^ 2 + 2 * γ ^ 2))).div_atTop
      (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0))
    simpa using this.const_mul (thomsonCrossSection e m)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun ω => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop (2 * |ω₀| + 1)] with ω hω
  rw [Real.norm_eq_abs]
  have h0 := abs_nonneg ω₀
  refine abs_crossSection_sub_thomson_le e m (lt_of_lt_of_le (by positivity) hω).ne' ?_
  nlinarith [sq_abs ω₀]

/-! ### Coherent and incoherent scattering -/

/-- `|Σₐ e^{iθₐ}|² = Σₐ Σ_b cos(θₐ − θ_b)`. -/
theorem norm_sum_exp_sq {ι : Type*} (s : Finset ι) (θ : ι → ℝ) :
    ‖∑ a ∈ s, Complex.exp (θ a * Complex.I)‖ ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, Real.cos (θ a - θ b) := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_sub]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]

/-- The mean coherence factor `⟨|Σₐ e^{i q·rₐ}|²⟩` of `N` scatterers whose positions
`r = (r₁, …, r_N)` have the joint distribution `P`, for the change `q = k − k′` of the wave
vector. The scattered amplitudes of identical scatterers add with the phases `e^{i q·rₐ}`, so the
mean cross section of the system is this factor times that of one scatterer. -/
def coherentFactor {N : ℕ} (P : Measure (Fin N → E3)) (q : E3) : ℝ :=
  ∫ r, ‖∑ a, Complex.exp ((⟪q, r a⟫ : ℝ) * Complex.I)‖ ^ 2 ∂P

/-- The relative positions of the pairs have densities: for `a ≠ b` the law of `rₐ − r_b` is
absolutely continuous, so that it has an integrable density. -/
def HasPairDensities {N : ℕ} (P : Measure (Fin N → E3)) : Prop :=
  ∀ a b : Fin N, a ≠ b → P.map (fun r => r a - r b) ≪ volume

/-- **Riemann–Lebesgue** for an absolutely continuous finite measure on `ℝ³`:
`∫ cos⟨q, u⟩ dμ(u) → 0` as `|q| → ∞` (`tendsto_integral_exp_inner_smul_cocompact` for the
density of `μ`). -/
theorem tendsto_integral_cos_inner (μ : Measure E3) [IsFiniteMeasure μ] (hμ : μ ≪ volume) :
    Tendsto (fun q : E3 => ∫ u, Real.cos ⟪q, u⟫ ∂μ) (cocompact E3) (𝓝 0) := by
  set f : E3 → ℝ := fun u => (μ.rnDeriv volume u).toReal
  have hf : Integrable f volume := Measure.integrable_toReal_rnDeriv
  have hg : Integrable (fun u => (f u : ℂ)) volume := hf.ofReal
  have hRL := tendsto_integral_exp_inner_smul_cocompact (V := E3) (fun u => (f u : ℂ))
  have hne : (-(2 * π)⁻¹ : ℝ) ≠ 0 := by
    have : 0 < π := pi_pos
    simp only [ne_eq, neg_eq_zero, inv_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact this.ne'
  have hc : Tendsto (fun q : E3 => (-(2 * π)⁻¹ : ℝ) • q) (cocompact E3) (cocompact E3) :=
    (Homeomorph.smulOfNeZero _ hne).isClosedEmbedding.tendsto_cocompact
  have h2 := (Complex.continuous_re.tendsto 0).comp (hRL.comp hc)
  rw [Complex.zero_re] at h2
  refine h2.congr fun q => ?_
  simp only [Function.comp_apply]
  rw [← RCLike.re_to_complex, ← integral_re ((Real.fourierIntegral_convergent_iff _).2 hg),
    ← integral_toReal_rnDeriv_mul hμ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hp : 2 * π * -⟪u, (-(2 * π)⁻¹ : ℝ) • q⟫ = ⟪q, u⟫ := by
    rw [real_inner_smul_right, real_inner_comm]
    field_simp
  simp only [Circle.smul_def, Real.fourierChar_apply, hp, smul_eq_mul, RCLike.re_to_complex,
    Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- `cos⟨q, u⟩` is integrable for a finite measure. -/
theorem integrable_cos_inner {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → E3} (hg : Measurable g) (q : E3) :
    Integrable (fun x => Real.cos ⟪q, g x⟫) μ := by
  refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun x => ?_)
  · exact (Real.continuous_cos.comp (continuous_const.inner continuous_id)).measurable.comp hg
      |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _

/-- The coherence factor is `Σₐ Σ_b ⟨cos⟨q, rₐ − r_b⟩⟩`. -/
theorem coherentFactor_eq {N : ℕ} (P : Measure (Fin N → E3)) [IsFiniteMeasure P] (q : E3) :
    coherentFactor P q = ∑ a, ∑ b, ∫ r, Real.cos ⟪q, r a - r b⟫ ∂P := by
  have hm : ∀ a b : Fin N, Measurable fun r : Fin N → E3 => r a - r b := fun a b =>
    (continuous_apply a |>.sub (continuous_apply b)).measurable
  rw [coherentFactor]
  simp_rw [norm_sum_exp_sq, ← inner_sub_right]
  rw [integral_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ => integrable_cos_inner P (hm a b) q]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_cos_inner P (hm a b) q]

/-- In the forward direction, `q = 0`, the scattering is coherent: the factor is `N²`. -/
theorem coherentFactor_zero {N : ℕ} (P : Measure (Fin N → E3)) [IsProbabilityMeasure P] :
    coherentFactor P 0 = N ^ 2 := by
  rw [coherentFactor_eq]
  simp [sq]

/-- **Incoherent scattering at short wavelengths** (Landau–Lifshitz §80): if the relative
positions of the pairs of scatterers have densities, the mean coherence factor
`⟨|Σₐ e^{i q·rₐ}|²⟩` tends to `N` as `|q| → ∞`: the interference terms
`⟨cos⟨q, rₐ − r_b⟩⟩`, `a ≠ b`, vanish by the lemma of Riemann–Lebesgue, and the cross section of the
system is `N` times that of one scatterer. -/
theorem tendsto_coherentFactor {N : ℕ} (P : Measure (Fin N → E3)) [IsProbabilityMeasure P]
    (hP : HasPairDensities P) :
    Tendsto (coherentFactor P) (cocompact E3) (𝓝 N) := by
  have hm : ∀ a b : Fin N, Measurable fun r : Fin N → E3 => r a - r b := fun a b =>
    (continuous_apply a |>.sub (continuous_apply b)).measurable
  have hterm : ∀ a b : Fin N, Tendsto (fun q => ∫ r, Real.cos ⟪q, r a - r b⟫ ∂P)
      (cocompact E3) (𝓝 (if a = b then 1 else 0)) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp only [hab, ↓reduceIte]
      refine (tendsto_integral_cos_inner (P.map fun r => r a - r b) (hP a b hab)).congr
        fun q => ?_
      rw [integral_map (hm a b).aemeasurable (f := fun u => Real.cos ⟪q, u⟫)
        (Real.continuous_cos.comp (continuous_const.inner continuous_id)).aestronglyMeasurable]
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun a _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun b _ => hterm a b
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h.congr fun q => (coherentFactor_eq P q).symm

/-- A distribution of the positions that is absolutely continuous on the space of configurations
has pair densities: the map `r ↦ rₐ − r_b` is linear and onto, so the preimage of a null set is
null (`ae_comp_linearMap_mem_iff`). -/
theorem hasPairDensities_of_absolutelyContinuous {N : ℕ} {P : Measure (Fin N → E3)}
    (hP : P ≪ volume) : HasPairDensities P := by
  intro a b hab
  set L : (Fin N → E3) →ₗ[ℝ] E3 := LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E3) a -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => E3) b with hLdef
  have hL : Function.Surjective L := fun u => ⟨Pi.single a u, by
    simp [hLdef, Ne.symm hab]⟩
  have hmeas : Measurable fun r : Fin N → E3 => r a - r b :=
    ((continuous_apply a).sub (continuous_apply b)).measurable
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply hmeas hs]
  apply hP
  have h := (ae_comp_linearMap_mem_iff L volume volume hL hs.compl).mpr
    (by rw [ae_iff]; simpa using hs0)
  rw [ae_iff] at h
  have h' : volume {x : Fin N → E3 | x a - x b ∈ s} = 0 := by simpa [hLdef] using h
  exact h'

/-- The uniform distribution of the configurations of `N` scatterers in the unit ball of the space
of configurations (the sup norm: each `rₐ` in the unit ball of `ℝ³`). -/
abbrev uniformConfiguration (N : ℕ) : Measure (Fin N → E3) :=
  volume[|closedBall (0 : Fin N → E3) 1]

/-- The uniform distribution is a probability measure. -/
instance (N : ℕ) : IsProbabilityMeasure (uniformConfiguration N) :=
  cond_isProbabilityMeasure_of_finite (measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne

/-- An instance of `HasPairDensities`: the uniform distribution. -/
theorem hasPairDensities_uniformConfiguration (N : ℕ) :
    HasPairDensities (uniformConfiguration N) :=
  hasPairDensities_of_absolutelyContinuous cond_absolutelyContinuous

/-- The incoherence at short wavelengths for scatterers distributed uniformly. -/
theorem tendsto_coherentFactor_uniformConfiguration (N : ℕ) :
    Tendsto (coherentFactor (uniformConfiguration N)) (cocompact E3) (𝓝 N) :=
  tendsto_coherentFactor _ (hasPairDensities_uniformConfiguration N)

end ProjectAinos.Electrodynamics.Scattering.HighFrequency
