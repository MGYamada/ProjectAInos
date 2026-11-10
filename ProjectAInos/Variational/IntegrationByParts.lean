module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Analytic interfaces for integration by parts

These are identities for supplied coefficient functions. The coordinate Euler–Lagrange layer connects them to derivatives of a Lagrangian.
-/

@[expose] public section

open MeasureTheory
open scoped Interval

namespace ProjectAInos.Variational

/-- First variation with covector-valued coefficients and vector-valued
variations. This retains the endpoint pairing for any real normed fibre. -/
theorem interval_firstVariation_pairing
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} {A P P' : ℝ → F →L[ℝ] ℝ} {η η' : ℝ → F}
    (hP : ∀ t ∈ Set.uIcc a b, HasDerivAt P (P' t) t)
    (hη : ∀ t ∈ Set.uIcc a b, HasDerivAt η (η' t) t)
    (hAη : IntervalIntegrable (fun t => A t (η t)) volume a b)
    (hP'η : IntervalIntegrable (fun t => P' t (η t)) volume a b)
    (hPη' : IntervalIntegrable (fun t => P t (η' t)) volume a b) :
    (∫ t in a..b, A t (η t) + P t (η' t)) =
      (P b (η b) - P a (η a)) + ∫ t in a..b, (A t - P' t) (η t) := by
  have hparts := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hP t ht).clm_apply (hη t ht)) (hP'η.add hPη')
  simp only [sub_apply]
  rw [intervalIntegral.integral_add hAη hPη',
    intervalIntegral.integral_sub hAη hP'η]
  rw [intervalIntegral.integral_add hP'η hPη'] at hparts
  linarith

/-- Scalar one-dimensional first-variation identity, including its boundary term.
The supplied derivatives are certified on the full closed interval. -/
theorem interval_firstVariation_identity {a b : ℝ} {A P P' η η' : ℝ → ℝ}
    (hP : ∀ t ∈ Set.uIcc a b, HasDerivAt P (P' t) t)
    (hη : ∀ t ∈ Set.uIcc a b, HasDerivAt η (η' t) t)
    (hP' : IntervalIntegrable P' volume a b)
    (hη' : IntervalIntegrable η' volume a b)
    (hAη : IntervalIntegrable (fun t => A t * η t) volume a b) :
    (∫ t in a..b, A t * η t + P t * η' t) =
      (P b * η b - P a * η a) + ∫ t in a..b, (A t - P' t) * η t := by
  have hPc : ContinuousOn P (Set.uIcc a b) :=
    fun t ht => (hP t ht).continuousAt.continuousWithinAt
  have hηc : ContinuousOn η (Set.uIcc a b) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hPη' := hη'.continuousOn_mul hPc
  have hP'η := hP'.mul_continuousOn hηc
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_add hAη hPη',
    intervalIntegral.integral_sub hAη hP'η,
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hP hη hP' hη']
  ring

/-- Fixed endpoint variations remove precisely the endpoint pairing. -/
theorem interval_firstVariation_fixedEndpoints {a b : ℝ} {A P P' η η' : ℝ → ℝ}
    (hP : ∀ t ∈ Set.uIcc a b, HasDerivAt P (P' t) t)
    (hη : ∀ t ∈ Set.uIcc a b, HasDerivAt η (η' t) t)
    (hP' : IntervalIntegrable P' volume a b)
    (hη' : IntervalIntegrable η' volume a b)
    (hAη : IntervalIntegrable (fun t => A t * η t) volume a b)
    (ha : η a = 0) (hb : η b = 0) :
    (∫ t in a..b, A t * η t + P t * η' t) =
      ∫ t in a..b, (A t - P' t) * η t := by
  simpa only [ha, hb, mul_zero, sub_self, zero_add]
    using interval_firstVariation_identity hP hη hP' hη' hAη

/-- One directional term in arbitrary finite dimension, with no boundary term.
This theorem uses an additive Haar measure on the entire vector space.
It does NOT apply to an arbitrary restricted-domain measure.
Compact support is one way to establish the three product integrability
assumptions; it is not silently assumed here. -/
theorem directional_integrationByParts
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {P η : E → ℝ} {v : E}
    (hP'η : Integrable (fun x => fderiv ℝ P x v * η x) μ)
    (hPη' : Integrable (fun x => P x * fderiv ℝ η x v) μ)
    (hPη : Integrable (fun x => P x * η x) μ)
    (hP : ∀ x ∈ tsupport η, DifferentiableAt ℝ P x)
    (hη : ∀ x ∈ tsupport P, DifferentiableAt ℝ η x) :
    (∫ x, P x * fderiv ℝ η x v ∂μ) =
      - ∫ x, fderiv ℝ P x v * η x ∂μ :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hP'η hPη' hPη hP hη

/-- Finite sum of directional terms: the scalar-field weak-form identity.
Taking `E = Fin n → ℝ` and `v i = Pi.single i 1` gives the usual divergence.
The identification of `A, P` with the partial derivatives of `L` is not part
of this theorem. -/
theorem finite_firstVariation_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {ι : Type*} [Fintype ι] {v : ι → E} {A η : E → ℝ} {P : ι → E → ℝ}
    (hAη : Integrable (fun x => A x * η x) μ)
    (hP'η : ∀ i, Integrable (fun x => fderiv ℝ (P i) x (v i) * η x) μ)
    (hPη' : ∀ i, Integrable (fun x => P i x * fderiv ℝ η x (v i)) μ)
    (hPη : ∀ i, Integrable (fun x => P i x * η x) μ)
    (hP : ∀ i, ∀ x ∈ tsupport η, DifferentiableAt ℝ (P i) x)
    (hη : ∀ i, ∀ x ∈ tsupport (P i), DifferentiableAt ℝ η x) :
    (∫ x, A x * η x + ∑ i, P i x * fderiv ℝ η x (v i) ∂μ) =
      ∫ x, (A x - ∑ i, fderiv ℝ (P i) x (v i)) * η x ∂μ := by
  have hright := integrable_finsetSum Finset.univ (fun i _ => hPη' i)
  have hleft := integrable_finsetSum Finset.univ (fun i _ => hP'η i)
  have hi : (∫ x, ∑ i, P i x * fderiv ℝ η x (v i) ∂μ) =
      - ∫ x, ∑ i, fderiv ℝ (P i) x (v i) * η x ∂μ := by
    rw [integral_finsetSum _ (fun i _ => hPη' i),
      integral_finsetSum _ (fun i _ => hP'η i)]
    simp only [directional_integrationByParts (hP'η _) (hPη' _) (hPη _) (hP _) (hη _),
      Finset.sum_neg_distrib]
  rw [integral_add hAη hright, hi, ← sub_eq_add_neg, ← integral_sub hAη hleft]
  congr 1
  funext x
  rw [sub_mul, Finset.sum_mul]

end ProjectAInos.Variational
