/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.LienardWiechert
public import ProjectAinos.Electrodynamics.RetardedPotential
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# The point charge is the source of its field

The potentials of Liénard and Wiechert (`LienardWiechert.scalarPotential`,
`LienardWiechert.vectorPotential`, `lienardWiechert`) are the retarded potentials of the charge
density `e δ(x − r(t))` and the current density `e ṙ(t) δ(x − r(t))` of a point charge on a
subluminal world line (Landau–Lifshitz, *The Classical Theory of Fields*, §63). Off the world
line they solve the homogeneous wave equation (`box_lienardWiechert_zero`); here the world line is
included, with test functions in place of distributions: for every `C²` function `χ` of compact
support on space-time,

  `∫ φ box χ d⁴v = −e ∫ χ(t, r(t)) dt`,  `∫ aᵢ box χ d⁴v = −e ∫ ṙᵢ(t) χ(t, r(t)) dt`,

that is `box φ = −e δ(x − r(t))` and `box 𝐚 = −e ṙ δ(x − r(t))` with `box = −∂₀² + Δ`, the
equations `box (Rg) = −g` of the retarded potentials (`box_retardedScalar`) with the point source.

* Space-time: `measurePreserving_timeSpaceEquiv`, the splitting `v ↦ (v⁰, 𝐯)` preserves the
  volume (the product Lebesgue measure on `Fin 4 → ℝ` and on `ℝ × Space 3`), so that
  `∫ g d⁴v = ∫ g(t, x) dt d³x` (`integral_spacetime_eq`).
* The light-cone co-ordinates `(τ, y) ↦ (τ + ‖y‖, r(τ) + y)` (`SubluminalWorldline.lightConeEquiv`,
  a bijection by the uniqueness of the retarded time): the world line is a null set
  (`volume_worldline`), the co-ordinates map the complement of the axis `y = 0` onto the
  complement of the world line (`image_lightConeEquiv`), and there they have the derivative
  `(δτ, δy) ↦ (δτ + ŷ · δy, ṙ(τ) δτ + δy)` (`hasFDerivAt_lightConeEquiv`) with the matrix
  `[[1, ŷᵀ], [ṙ, I]]` and the Jacobian determinant `1 − ŷ · ṙ(τ) ≥ 1 − v₀ > 0`
  (`det_lightConeDeriv`, `lightConeJacobian`, `sub_le_lightConeJacobian`).
* **The change of variables** `∫ g(t, x) dt d³x = ∫ (1 − ŷ · ṙ(τ)) g(τ + ‖y‖, r(τ) + y) dτ d³y`
  for every function `g` (`integral_lightCone`; `lintegral_lightCone`,
  `integrable_lightCone_iff`, `integrableOn_lightCone_iff`, and `integral_lightCone_iterated` as
  an iterated integral), from the change of variables of Mathlib on the open set `y ≠ 0`.
* In these co-ordinates `φ dt d³x = e dτ d³y/(4π‖y‖)` and `𝐚 dt d³x = e ṙ(τ) dτ d³y/(4π‖y‖)`
  (`lightConeJacobian_mul_scalarPotential`, `lightConeJacobian_mul_vectorPotential`,
  `integral_scalarPotential_mul`, `integral_vectorPotential_mul`): the factor `1 − ŷ · ṙ` of the
  Jacobian cancels the denominator `R − R·v` of the potentials.
* **Local integrability**: the light-cone co-ordinates of a bounded set of events are bounded
  (`exists_lightConeEquiv_preimage_subset`) and `1/‖y‖` is locally integrable, so the potentials,
  of the order `1/R` near the world line, are locally integrable on space-time
  (`locallyIntegrable_scalarPotential`, `locallyIntegrable_vectorPotential`,
  `locallyIntegrable_potentialComponent`).
* **The advanced identity** `∫ □u(τ + ‖y‖, x + y)/(4π‖y‖) dy = u(τ, x)` for `u` of class `C²`
  with compact support (`integral_wave_div_norm_advanced`), from the retarded identity
  `Wave.integral_wave_div_norm` by the reflection `(t, x) ↦ (−t, −x)`, which leaves
  `□ = ∂ₜ² − Δ` invariant (`waveOperator_comp_neg`).
* **The source identity**: with the theorem of Fubini in the light-cone co-ordinates and the
  advanced identity at the points `(τ, r(τ))` of the world line
  (`integral_mul_newtonKernel_mul_wave`, `integral_mul_box_of_lightCone`),
  `integral_scalarPotential_mul_box`, `integral_vectorPotential_mul_box`, and for the components
  of the potential `integral_potentialComponent_mul_box`: `box A₀ = k⁰` and `box aᵢ = −kⁱ`
  against test functions, with the current `k = e (1, ṙ) δ(x − r(t))` of the point charge (as in
  `box_retardedPotential`). Both sides are well defined
  (`integrable_scalarPotential_mul_box`, `integrable_vectorPotential_mul_box`).
* Instances: with the bump `spacetimeBump` the right side `−e ∫ χ(t, r(t)) dt` does not vanish
  for a nonzero charge whose world line starts in the ball of the radius `2`
  (`integral_spacetimeBump_pos`, `integral_scalarPotential_mul_box_spacetimeBump_ne_zero`), in
  particular for the charge at rest at the origin (`integral_scalarPotential_mul_box_rest`,
  `integral_scalarPotential_mul_box_rest_ne_zero`) and for the uniform circular motion of a radius
  below `2` (`integral_scalarPotential_mul_box_circular_ne_zero`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff ENNReal

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SpecialRelativity
open SmoothGeometry.Minkowski (Space)

/-! ### The volume of space-time -/

/-- The splitting `v ↦ (v⁰, 𝐯)` of space-time into time and space preserves the volume. -/
theorem measurePreserving_timeSpaceEquiv :
    MeasurePreserving (Wave.timeSpaceEquiv : Spacetime → ℝ × Space 3) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin 3))).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)
  convert h using 1
  funext v
  refine Prod.ext rfl ?_
  ext i
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]

/-- The splitting of space-time as a measurable equivalence. -/
def timeSpaceMeasurableEquiv : Spacetime ≃ᵐ ℝ × Space 3 :=
  Wave.timeSpaceEquiv.toHomeomorph.toMeasurableEquiv

/-- The measurable splitting is the splitting `v ↦ (v⁰, 𝐯)`. -/
theorem coe_timeSpaceMeasurableEquiv :
    (timeSpaceMeasurableEquiv : Spacetime → ℝ × Space 3) = Wave.timeSpaceEquiv := rfl

/-- The inverse of the measurable splitting is `(t, x) ↦ Minkowski.vector t x`. -/
@[simp] theorem timeSpaceMeasurableEquiv_symm_apply (p : ℝ × Space 3) :
    timeSpaceMeasurableEquiv.symm p = Minkowski.vector p.1 p.2 := rfl

/-- The inverse of the splitting preserves the volume. -/
theorem measurePreserving_timeSpaceMeasurableEquiv_symm :
    MeasurePreserving (timeSpaceMeasurableEquiv.symm : ℝ × Space 3 → Spacetime) :=
  measurePreserving_timeSpaceEquiv.symm timeSpaceMeasurableEquiv

/-- **Integrals on space-time in time and space**: `∫ g d⁴v = ∫ g(t, x) dt d³x`. -/
theorem integral_spacetime_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Spacetime → F) : ∫ v, g v = ∫ p : ℝ × Space 3, g (Minkowski.vector p.1 p.2) :=
  (measurePreserving_timeSpaceMeasurableEquiv_symm.integral_comp' g).symm

/-- The volume of `ℝ × Space 3` is a Haar measure (the product of two Haar measures). -/
instance isAddHaarMeasure_volume_timeSpace :
    Measure.IsAddHaarMeasure (volume : Measure (ℝ × Space 3)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The axis `y = 0` of `ℝ × Space 3` is a null set. -/
theorem ae_snd_ne_zero : ∀ᵐ q : ℝ × Space 3, q.2 ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [Measure.volume_eq_prod, Measure.measure_prod_null
    (isClosed_eq continuous_snd continuous_const).measurableSet]
  refine Eventually.of_forall fun t => ?_
  have h : Prod.mk t ⁻¹' {q : ℝ × Space 3 | q.2 = 0} = {0} := by
    ext x
    simp
  simp only [h, measure_singleton, Pi.zero_apply]

/-- The complement of the axis `y = 0` is a measurable set. -/
theorem measurableSet_snd_ne_zero : MeasurableSet {q : ℝ × Space 3 | q.2 ≠ 0} :=
  (isOpen_ne_fun continuous_snd continuous_const).measurableSet

/-- The complement of the axis `y = 0` has full measure. -/
theorem restrict_snd_ne_zero :
    (volume : Measure (ℝ × Space 3)).restrict {q | q.2 ≠ 0} = volume :=
  Measure.restrict_eq_self_of_ae_mem ae_snd_ne_zero

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

/-! ### The world line is a null set -/

/-- The world line `{(t, r(t))}` is a closed set of `ℝ × Space 3`. -/
theorem isClosed_worldline : IsClosed {p : ℝ × Space 3 | p.2 = w.r p.1} :=
  isClosed_eq continuous_snd (w.contDiff_r.continuous.comp continuous_fst)

/-- **The world line is a null set**: each time slice of it is a point. -/
theorem volume_worldline : volume {p : ℝ × Space 3 | p.2 = w.r p.1} = 0 := by
  rw [Measure.volume_eq_prod, Measure.measure_prod_null w.isClosed_worldline.measurableSet]
  refine Eventually.of_forall fun t => ?_
  have h : Prod.mk t ⁻¹' {p : ℝ × Space 3 | p.2 = w.r p.1} = {w.r t} := by
    ext x
    simp
  simp only [h, measure_singleton, Pi.zero_apply]

/-- Almost every event is off the world line. -/
theorem ae_offWorldline : ∀ᵐ p : ℝ × Space 3, p.2 ≠ w.r p.1 := by
  rw [ae_iff]
  simpa using w.volume_worldline

/-! ### The light-cone co-ordinates -/

/-- The light-cone co-ordinates are `(τ, y) ↦ (τ + ‖y‖, r(τ) + y)`. -/
theorem lightConeEquiv_apply (q : ℝ × Space 3) :
    w.lightConeEquiv q = (q.1 + ‖q.2‖, w.r q.1 + q.2) := rfl

/-- The inverse of the light-cone co-ordinates is `(t, x) ↦ (τ, R)`. -/
theorem lightConeEquiv_symm_apply (p : ℝ × Space 3) :
    w.lightConeEquiv.symm p = (w.retardedTime p.1 p.2, w.retardedSeparation p.1 p.2) := rfl

/-- The light-cone co-ordinates are continuous. -/
theorem continuous_lightConeEquiv : Continuous w.lightConeEquiv :=
  (continuous_fst.add continuous_snd.norm).prodMk
    ((w.contDiff_r.continuous.comp continuous_fst).add continuous_snd)

/-- The derivative `(δτ, δy) ↦ (δτ + ŷ · δy, ṙ(τ) δτ + δy)` of the light-cone co-ordinates at
`(τ, y)`. -/
def lightConeDeriv (q : ℝ × Space 3) : ℝ × Space 3 →L[ℝ] ℝ × Space 3 :=
  (ContinuousLinearMap.fst ℝ ℝ (Space 3) +
      (‖q.2‖⁻¹ • innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ (Space 3))).prod
    ((ContinuousLinearMap.fst ℝ ℝ (Space 3)).smulRight (deriv w.r q.1) +
      ContinuousLinearMap.snd ℝ ℝ (Space 3))

/-- The light-cone co-ordinates are differentiable off the axis `y = 0`. -/
theorem hasFDerivAt_lightConeEquiv {q : ℝ × Space 3} (hq : q.2 ≠ 0) :
    HasFDerivAt w.lightConeEquiv (w.lightConeDeriv q) q := by
  have h1 : HasFDerivAt (fun q : ℝ × Space 3 => q.1 + ‖q.2‖)
      (ContinuousLinearMap.fst ℝ ℝ (Space 3) +
        (‖q.2‖⁻¹ • innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ (Space 3))) q :=
    hasFDerivAt_fst.add ((Wave.hasFDerivAt_norm_of_ne_zero hq).comp q hasFDerivAt_snd)
  have hr : HasFDerivAt w.r ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv w.r q.1)) q.1 :=
    (w.differentiable_r q.1).hasDerivAt.hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × Space 3 => w.r q.1 + q.2)
      ((ContinuousLinearMap.fst ℝ ℝ (Space 3)).smulRight (deriv w.r q.1) +
        ContinuousLinearMap.snd ℝ ℝ (Space 3)) q := by
    refine ((hr.comp q hasFDerivAt_fst).add hasFDerivAt_snd).congr_fderiv ?_
    ext δ <;> simp
  exact h1.prodMk h2

/-- The Jacobian determinant `1 − ŷ · ṙ(τ)` of the light-cone co-ordinates at `(τ, y)`. -/
def lightConeJacobian (q : ℝ × Space 3) : ℝ := 1 - inner ℝ q.2 (deriv w.r q.1) / ‖q.2‖

/-- **The Jacobian determinant of the light-cone co-ordinates** is `1 − ŷ · ṙ(τ)`: the matrix of
the derivative is `[[1, ŷᵀ], [ṙ, I]]`. -/
theorem det_lightConeDeriv (q : ℝ × Space 3) :
    (w.lightConeDeriv q).det = w.lightConeJacobian q := by
  set b : Module.Basis (Unit ⊕ Fin 3) ℝ (ℝ × Space 3) :=
    (Module.Basis.singleton Unit ℝ).prod (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis with hb
  have hM : LinearMap.toMatrix b b (w.lightConeDeriv q : ℝ × Space 3 →ₗ[ℝ] ℝ × Space 3) =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) (Matrix.of fun _ j => ‖q.2‖⁻¹ * q.2 j)
        (Matrix.of fun i _ => deriv w.r q.1 i) 1 := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix_apply, hb, lightConeDeriv]
    · simp [LinearMap.toMatrix_apply, hb, lightConeDeriv, EuclideanSpace.inner_single_right]
    · simp [LinearMap.toMatrix_apply, hb, lightConeDeriv]
    · simp [LinearMap.toMatrix_apply, hb, lightConeDeriv, Matrix.one_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, hM, Matrix.det_fromBlocks_one₂₂,
    Matrix.det_unique]
  simp [Matrix.mul_apply, lightConeJacobian, PiLp.inner_apply, Finset.mul_sum, div_eq_inv_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The light-cone co-ordinates map the complement of the axis `y = 0` onto the complement of
the world line. -/
theorem image_lightConeEquiv : w.lightConeEquiv '' {q | q.2 ≠ 0} = {p | p.2 ≠ w.r p.1} := by
  rw [Equiv.image_eq_preimage_symm]
  ext p
  simp only [mem_preimage, mem_ofPred_eq, lightConeEquiv_symm_apply]
  refine ⟨fun h hp => h ?_, w.retardedSeparation_ne_zero⟩
  rw [SubluminalWorldline.retardedSeparation, hp, w.retardedTime_self, sub_self]

/-- The Jacobian determinant is at least `1 − v₀`. -/
theorem sub_le_lightConeJacobian (q : ℝ × Space 3) : 1 - w.v₀ ≤ w.lightConeJacobian q := by
  have h1 : inner ℝ q.2 (deriv w.r q.1) ≤ ‖q.2‖ * w.v₀ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (w.norm_deriv_le _) (norm_nonneg _))
  have h2 : inner ℝ q.2 (deriv w.r q.1) / ‖q.2‖ ≤ w.v₀ := by
    rcases eq_or_lt_of_le (norm_nonneg q.2) with h | h
    · rw [← h, div_zero]
      exact w.v₀_nonneg
    · rw [div_le_iff₀ h]
      linarith
  rw [lightConeJacobian]
  linarith

/-- The Jacobian determinant is positive. -/
theorem lightConeJacobian_pos (q : ℝ × Space 3) : 0 < w.lightConeJacobian q := by
  linarith [w.sub_le_lightConeJacobian q, w.v₀_lt_one]

/-- The absolute value of the Jacobian determinant. -/
theorem abs_det_lightConeDeriv (q : ℝ × Space 3) :
    |(w.lightConeDeriv q).det| = w.lightConeJacobian q := by
  rw [det_lightConeDeriv, abs_of_pos (w.lightConeJacobian_pos q)]

/-- The image of the complement of the axis has full measure. -/
theorem restrict_image_lightConeEquiv :
    (volume : Measure (ℝ × Space 3)).restrict (w.lightConeEquiv '' {q | q.2 ≠ 0}) = volume := by
  rw [image_lightConeEquiv]
  exact Measure.restrict_eq_self_of_ae_mem w.ae_offWorldline

/-! ### The change of variables -/

/-- **The change of variables to the light-cone co-ordinates**:
`∫ g(t, x) dt d³x = ∫ (1 − ŷ · ṙ(τ)) g(τ + ‖y‖, r(τ) + y) dτ d³y` for every function `g`
(both sides vanish together when `g` is not integrable, `integrable_lightCone_iff`). -/
theorem integral_lightCone {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × Space 3 → F) :
    ∫ p, g p = ∫ q, w.lightConeJacobian q • g (w.lightConeEquiv q) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_snd_ne_zero
    (fun q hq => (w.hasFDerivAt_lightConeEquiv hq).hasFDerivWithinAt)
    w.lightConeEquiv.injective.injOn g
  rw [w.restrict_image_lightConeEquiv, restrict_snd_ne_zero] at h
  simpa only [abs_det_lightConeDeriv] using h

/-- The change of variables to the light-cone co-ordinates for the Lebesgue integral. -/
theorem lintegral_lightCone (g : ℝ × Space 3 → ℝ≥0∞) :
    ∫⁻ p, g p = ∫⁻ q, ENNReal.ofReal (w.lightConeJacobian q) * g (w.lightConeEquiv q) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_snd_ne_zero
    (fun q hq => (w.hasFDerivAt_lightConeEquiv hq).hasFDerivWithinAt)
    w.lightConeEquiv.injective.injOn g
  rw [w.restrict_image_lightConeEquiv, restrict_snd_ne_zero] at h
  simpa only [abs_det_lightConeDeriv] using h

/-- A function is integrable exactly when its pull-back to the light-cone co-ordinates, times
the Jacobian determinant, is integrable. -/
theorem integrable_lightCone_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × Space 3 → F) :
    Integrable g ↔ Integrable fun q => w.lightConeJacobian q • g (w.lightConeEquiv q) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_snd_ne_zero (fun q hq => (w.hasFDerivAt_lightConeEquiv hq).hasFDerivWithinAt)
    w.lightConeEquiv.injective.injOn g
  rw [IntegrableOn, IntegrableOn, w.restrict_image_lightConeEquiv, restrict_snd_ne_zero] at h
  simpa only [abs_det_lightConeDeriv] using h

/-- Integrability on a measurable set in the light-cone co-ordinates. -/
theorem integrableOn_lightCone_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × Space 3 → F) {s : Set (ℝ × Space 3)} (hs : MeasurableSet s) :
    IntegrableOn g s ↔ IntegrableOn (fun q => w.lightConeJacobian q • g (w.lightConeEquiv q))
      (w.lightConeEquiv ⁻¹' s) := by
  have h : (fun q => w.lightConeJacobian q • s.indicator g (w.lightConeEquiv q)) =
      (w.lightConeEquiv ⁻¹' s).indicator
        fun q => w.lightConeJacobian q • g (w.lightConeEquiv q) := by
    funext q
    by_cases hq : w.lightConeEquiv q ∈ s
    · rw [indicator_of_mem hq, indicator_of_mem (show q ∈ w.lightConeEquiv ⁻¹' s from hq)]
    · rw [indicator_of_notMem hq, indicator_of_notMem (show q ∉ w.lightConeEquiv ⁻¹' s from hq),
        smul_zero]
  rw [← integrable_indicator_iff hs,
    ← integrable_indicator_iff (hs.preimage w.continuous_lightConeEquiv.measurable),
    w.integrable_lightCone_iff, h]

/-- The change of variables as an iterated integral, for an integrable function `g`:
`∫ g(t, x) dt d³x = ∫ (∫ (1 − ŷ · ṙ(τ)) g(τ + ‖y‖, r(τ) + y) d³y) dτ`. -/
theorem integral_lightCone_iterated {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ × Space 3 → F} (hg : Integrable g) :
    ∫ p, g p = ∫ τ, ∫ y : Space 3,
      (1 - inner ℝ y (deriv w.r τ) / ‖y‖) • g (τ + ‖y‖, w.r τ + y) := by
  rw [w.integral_lightCone, Measure.volume_eq_prod,
    integral_prod _ ((w.integrable_lightCone_iff g).mp hg)]
  rfl

/-! ### Bounded regions -/

/-- The light-cone co-ordinates of the events with `|t| ≤ T` and `‖x‖ ≤ ρ` are bounded:
`|τ| ≤ M` and `‖y‖ ≤ T + M` with `M = (T + ρ + ‖r(0)‖)/(1 − v₀)`. -/
theorem lightConeEquiv_preimage_subset (T ρ : ℝ) :
    w.lightConeEquiv ⁻¹' {p | |p.1| ≤ T ∧ ‖p.2‖ ≤ ρ} ⊆
      Icc (-((T + ρ + ‖w.r 0‖) / (1 - w.v₀))) ((T + ρ + ‖w.r 0‖) / (1 - w.v₀)) ×ˢ
        closedBall 0 (T + (T + ρ + ‖w.r 0‖) / (1 - w.v₀)) := by
  rintro ⟨τ, y⟩ ⟨ht, hx⟩
  simp only [lightConeEquiv_apply] at ht hx
  set M := (T + ρ + ‖w.r 0‖) / (1 - w.v₀) with hM
  have hv : 0 < 1 - w.v₀ := by linarith [w.v₀_lt_one]
  have hr : ‖w.r τ - w.r 0‖ ≤ w.v₀ * |τ| := by simpa using w.norm_sub_le 0 τ
  have hy : ‖y‖ ≤ ρ + w.v₀ * |τ| + ‖w.r 0‖ := by
    have he : y = (w.r τ + y) - (w.r τ - w.r 0) - w.r 0 := by abel
    calc ‖y‖ = ‖(w.r τ + y) - (w.r τ - w.r 0) - w.r 0‖ := by rw [← he]
      _ ≤ ‖w.r τ + y‖ + ‖w.r τ - w.r 0‖ + ‖w.r 0‖ :=
        (_root_.norm_sub_le _ _).trans
          (by linarith [_root_.norm_sub_le (w.r τ + y) (w.r τ - w.r 0)])
      _ ≤ _ := by linarith
  have hT := abs_le.mp ht
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hx
  have hτ : |τ| ≤ M := by
    rw [hM, le_div_iff₀ hv]
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg h]
      nlinarith [norm_nonneg y, mul_nonneg h w.v₀_nonneg, norm_nonneg (w.r 0)]
    · rw [abs_of_neg h] at hy ⊢
      nlinarith
  refine ⟨abs_le.mp hτ, ?_⟩
  rw [mem_closedBall_zero_iff]
  linarith [neg_abs_le τ]

/-- The light-cone co-ordinates of a bounded set of events are bounded. -/
theorem exists_lightConeEquiv_preimage_subset {K : Set (ℝ × Space 3)}
    (hK : Bornology.IsBounded K) :
    ∃ M L : ℝ, w.lightConeEquiv ⁻¹' K ⊆ Icc (-M) M ×ˢ closedBall 0 L := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine ⟨_, _, (preimage_mono fun p hp => ?_).trans (w.lightConeEquiv_preimage_subset R R)⟩
  have h := mem_closedBall_zero_iff.mp (hR hp)
  exact ⟨(Real.norm_eq_abs p.1 ▸ norm_fst_le p).trans h, (norm_snd_le p).trans h⟩

end SubluminalWorldline

/-- The kernel `c(τ)/(4π‖y‖)` is integrable on the bounded sets `[−M, M] × B(0, L)`. -/
theorem integrableOn_mul_newtonKernel {c : ℝ → ℝ} (hc : Continuous c) (M L : ℝ) :
    IntegrableOn (fun q : ℝ × Space 3 => c q.1 * SmoothGeometry.Potential.newtonKernel q.2)
      (Icc (-M) M ×ˢ closedBall 0 L) := by
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hc.integrableOn_Icc.mul_prod
    (SmoothGeometry.Potential.locallyIntegrable_newtonKernel.integrableOn_isCompact
      (isCompact_closedBall 0 L))

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

/-! ### The potentials in the light-cone co-ordinates -/

/-- `‖y‖ − y · ṙ(τ) = ‖y‖ (1 − ŷ · ṙ(τ))` is positive for `y ≠ 0`. -/
theorem norm_sub_inner_pos {q : ℝ × Space 3} (hq : q.2 ≠ 0) :
    0 < ‖q.2‖ - inner ℝ q.2 (deriv w.r q.1) := by
  have hn : 0 < ‖q.2‖ := norm_pos_iff.mpr hq
  have h := w.lightConeJacobian_pos q
  rw [lightConeJacobian, sub_pos, div_lt_one hn] at h
  linarith

/-- **The scalar potential in the light-cone co-ordinates**: the Jacobian determinant times
`φ(τ + ‖y‖, r(τ) + y)` is `e/(4π‖y‖)`, that is `φ dt d³x = e dτ d³y/(4π‖y‖)`. -/
theorem lightConeJacobian_mul_scalarPotential (e : ℝ) {q : ℝ × Space 3} (hq : q.2 ≠ 0) :
    w.lightConeJacobian q *
        LienardWiechert.scalarPotential e w (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) =
      e / (4 * Real.pi * ‖q.2‖) := by
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hD := (w.norm_sub_inner_pos hq).ne'
  rw [scalarPotential_add_norm w, lightConeJacobian]
  field_simp

/-- **The vector potential in the light-cone co-ordinates**: the Jacobian determinant times
`𝐚(τ + ‖y‖, r(τ) + y)` is `e ṙ(τ)/(4π‖y‖)`, that is `𝐚 dt d³x = e ṙ(τ) dτ d³y/(4π‖y‖)`. -/
theorem lightConeJacobian_mul_vectorPotential (e : ℝ) {q : ℝ × Space 3} (hq : q.2 ≠ 0)
    (i : Fin 3) :
    w.lightConeJacobian q *
        LienardWiechert.vectorPotential e w (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) i =
      e * deriv w.r q.1 i / (4 * Real.pi * ‖q.2‖) := by
  have hn : ‖q.2‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hD := (w.norm_sub_inner_pos hq).ne'
  rw [vectorPotential_add_norm w, lightConeJacobian]
  field_simp

/-- **The scalar potential in the light-cone co-ordinates** on space-time:
`∫ φ g d⁴v = ∫ e g(τ + ‖y‖, r(τ) + y)/(4π‖y‖) dτ d³y` for every function `g`. -/
theorem integral_scalarPotential_mul (e : ℝ) (g : Spacetime → ℝ) :
    ∫ v, LienardWiechert.scalarPotential e w v * g v =
      ∫ q : ℝ × Space 3, e / (4 * Real.pi * ‖q.2‖) *
        g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) := by
  rw [integral_spacetime_eq, w.integral_lightCone]
  refine integral_congr_ae (ae_snd_ne_zero.mono fun q hq => ?_)
  simp only [lightConeEquiv_apply, smul_eq_mul]
  rw [← mul_assoc, w.lightConeJacobian_mul_scalarPotential e hq]

/-- **The vector potential in the light-cone co-ordinates** on space-time:
`∫ aᵢ g d⁴v = ∫ e ṙᵢ(τ) g(τ + ‖y‖, r(τ) + y)/(4π‖y‖) dτ d³y` for every function `g`. -/
theorem integral_vectorPotential_mul (e : ℝ) (i : Fin 3) (g : Spacetime → ℝ) :
    ∫ v, LienardWiechert.vectorPotential e w v i * g v =
      ∫ q : ℝ × Space 3, e * deriv w.r q.1 i / (4 * Real.pi * ‖q.2‖) *
        g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) := by
  rw [integral_spacetime_eq, w.integral_lightCone]
  refine integral_congr_ae (ae_snd_ne_zero.mono fun q hq => ?_)
  simp only [lightConeEquiv_apply, smul_eq_mul]
  rw [← mul_assoc, w.lightConeJacobian_mul_vectorPotential e hq]

/-! ### Local integrability -/

/-- A function on space-time is locally integrable if in the light-cone co-ordinates, times the
Jacobian determinant, it is `c(τ)/(4π‖y‖)` with a continuous `c`. -/
theorem locallyIntegrable_of_lightCone {g : Spacetime → ℝ} {c : ℝ → ℝ} (hc : Continuous c)
    (hg : ∀ q : ℝ × Space 3, q.2 ≠ 0 →
      w.lightConeJacobian q * g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) =
        c q.1 / (4 * Real.pi * ‖q.2‖)) :
    LocallyIntegrable g := by
  refine locallyIntegrable_iff.mpr fun k hk => ?_
  rw [← measurePreserving_timeSpaceMeasurableEquiv_symm.integrableOn_comp_preimage
    timeSpaceMeasurableEquiv.symm.measurableEmbedding]
  have hk' : IsCompact (timeSpaceMeasurableEquiv.symm ⁻¹' k) :=
    Wave.timeSpaceEquiv.symm.toHomeomorph.isCompact_preimage.mpr hk
  rw [w.integrableOn_lightCone_iff _ hk'.isClosed.measurableSet]
  obtain ⟨M, L, hML⟩ := w.exists_lightConeEquiv_preimage_subset hk'.isBounded
  refine ((integrableOn_mul_newtonKernel hc M L).mono_set hML).congr_fun_ae ?_
  filter_upwards [ae_restrict_of_ae ae_snd_ne_zero] with q hq
  simp only [Function.comp_apply, smul_eq_mul, lightConeEquiv_apply,
    timeSpaceMeasurableEquiv_symm_apply]
  rw [hg q hq, SmoothGeometry.Potential.newtonKernel, div_eq_mul_inv]

/-- **The scalar potential of Liénard and Wiechert is locally integrable** on space-time: near
the world line it is of the order `1/R`. -/
theorem locallyIntegrable_scalarPotential (e : ℝ) :
    LocallyIntegrable (LienardWiechert.scalarPotential e w) :=
  w.locallyIntegrable_of_lightCone (c := fun _ => e) continuous_const fun _ hq =>
    w.lightConeJacobian_mul_scalarPotential e hq

/-- **The vector potential of Liénard and Wiechert is locally integrable** on space-time. -/
theorem locallyIntegrable_vectorPotential (e : ℝ) (i : Fin 3) :
    LocallyIntegrable fun v => LienardWiechert.vectorPotential e w v i :=
  w.locallyIntegrable_of_lightCone (c := fun t => e * deriv w.r t i)
    (continuous_const.mul (LienardWiechert.contDiff_component w.contDiff_deriv i).continuous)
    fun _ hq => w.lightConeJacobian_mul_vectorPotential e hq i

/-- The components of the potential of Liénard and Wiechert are locally integrable. -/
theorem locallyIntegrable_potentialComponent (e : ℝ) (μ : Fin 4) :
    LocallyIntegrable (potentialComponent (lienardWiechert e w) μ) := by
  refine Fin.cases ?_ (fun i => ?_) μ
  · rw [potentialComponent_lienardWiechert_zero]
    exact (w.locallyIntegrable_scalarPotential e).neg
  · rw [potentialComponent_lienardWiechert_succ]
    exact w.locallyIntegrable_vectorPotential e i

end SubluminalWorldline

/-! ### The advanced identity -/

/-- The wave operator commutes with the reflection `p ↦ −p` of time and space. -/
theorem waveOperator_comp_neg (u : ℝ × Space 3 → ℝ) (p : ℝ × Space 3) :
    Wave.waveOperator (fun p => u (-p)) p = Wave.waveOperator u (-p) := by
  have hd : ∀ (f : ℝ × Space 3 → ℝ) (p v : ℝ × Space 3),
      fderiv ℝ (fun p => f (-p)) p v = -fderiv ℝ f (-p) v := by
    intro f p v
    have h := (ContinuousLinearEquiv.neg ℝ (M := ℝ × Space 3)).comp_right_fderiv (f := f) (x := p)
    rw [show (fun p => f (-p)) = f ∘ (ContinuousLinearEquiv.neg ℝ (M := ℝ × Space 3)) from rfl, h]
    simp
  have key : ∀ (f : ℝ × Space 3 → ℝ) (v w : ℝ × Space 3),
      fderiv ℝ (fun p => fderiv ℝ (fun p => f (-p)) p v) p w =
        fderiv ℝ (fun p => fderiv ℝ f p v) (-p) w := by
    intro f v w
    have h1 : (fun p => fderiv ℝ (fun p => f (-p)) p v) = fun p => -fderiv ℝ f (-p) v :=
      funext fun p => hd f p v
    have h2 := hd (fun q => fderiv ℝ f q v) p w
    rw [h1, fderiv_fun_neg, _root_.neg_apply, h2, neg_neg]
  have ht : ∀ f : ℝ × Space 3 → ℝ, Wave.timeDeriv f = fun p => fderiv ℝ f p (1, 0) :=
    fun _ => rfl
  have hs : ∀ (i : Fin 3) (f : ℝ × Space 3 → ℝ),
      Wave.spaceDeriv i f = fun p => fderiv ℝ f p (0, EuclideanSpace.single i 1) := fun _ _ => rfl
  simp only [Wave.waveOperator, ht, hs]
  rw [key u]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => key u _ _)

/-- **The advanced identity**: `∫ □u(τ + ‖y‖, x + y)/(4π‖y‖) dy = u(τ, x)` for a `C²` function `u`
of compact support, with `□ = ∂ₜ² − Δ`. It follows from the retarded identity
`Wave.integral_wave_div_norm` by the reflection `(t, x) ↦ (−t, −x)`, which leaves `□` invariant
(`waveOperator_comp_neg`). -/
theorem integral_wave_div_norm_advanced {u : ℝ × Space 3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hc : HasCompactSupport u) (τ : ℝ) (x : Space 3) :
    ∫ y : Space 3, Wave.waveOperator u (τ + ‖y‖, x + y) / (4 * Real.pi * ‖y‖) = u (τ, x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  have hsupp : tsupport (fun p : ℝ × Space 3 => u (-p)) = Neg.neg ⁻¹' tsupport u :=
    tsupport_comp_eq_preimage u (Homeomorph.neg (ℝ × Space 3))
  have hL : ∀ y : Space 3, R + |τ| + 1 ≤ ‖y‖ →
      (-τ - ‖y‖, -x - y) ∉ tsupport (fun p : ℝ × Space 3 => u (-p)) := by
    intro y hy hmem
    rw [hsupp, mem_preimage] at hmem
    have h := mem_closedBall_zero_iff.mp (hR hmem)
    have h1 := (norm_fst_le (-((-τ - ‖y‖, -x - y) : ℝ × Space 3))).trans h
    simp only [Prod.fst_neg, Real.norm_eq_abs] at h1
    have h2 := le_abs_self (-(-τ - ‖y‖))
    have h3 := neg_abs_le τ
    linarith
  have h := Wave.integral_wave_div_norm (f := fun p => u (-p)) (hu.comp contDiff_neg) (-τ) (-x) hL
  have hfun : (fun y : Space 3 =>
      Wave.waveOperator (fun p => u (-p)) (-τ - ‖y‖, -x - y) / (4 * Real.pi * ‖y‖)) =
      fun y => Wave.waveOperator u (τ + ‖y‖, x + y) / (4 * Real.pi * ‖y‖) := by
    funext y
    rw [waveOperator_comp_neg]
    congr 2
    ext
    · simp only [Prod.fst_neg]
      ring
    · rw [Prod.snd_neg, neg_sub, sub_neg_eq_add, add_comm]
  rw [hfun] at h
  rw [h]
  simp

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

/-! ### The source identity -/

/-- The integral of `c(τ) □u(τ + ‖y‖, r(τ) + y)/(4π‖y‖)` over the light-cone co-ordinates is
`∫ c(τ) u(τ, r(τ)) dτ`, by the theorem of Fubini and the advanced identity. -/
theorem integral_mul_newtonKernel_mul_wave {c : ℝ → ℝ} (hc : Continuous c)
    {u : ℝ × Space 3 → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    ∫ q : ℝ × Space 3, c q.1 * SmoothGeometry.Potential.newtonKernel q.2 *
        Wave.waveOperator u (w.lightConeEquiv q) =
      ∫ τ, c τ * u (τ, w.r τ) := by
  set F := fun q : ℝ × Space 3 => c q.1 * SmoothGeometry.Potential.newtonKernel q.2 *
    Wave.waveOperator u (w.lightConeEquiv q) with hF
  have hint : Integrable F := by
    have hK : IsCompact (tsupport u) := hcs
    obtain ⟨M, L, hML⟩ := w.exists_lightConeEquiv_preimage_subset hK.isBounded
    have hsupp : Function.support F ⊆ w.lightConeEquiv ⁻¹' tsupport u := by
      intro q hq
      by_contra h
      exact hq (by simp [F, Wave.waveOperator_eq_zero_of_notMem h])
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    have hwc : Continuous (Wave.waveOperator u) := Wave.continuous_waveOperator hu
    have hwcs : HasCompactSupport (Wave.waveOperator u) := by
      refine hcs.mono' fun p hp => ?_
      by_contra h
      exact hp (Wave.waveOperator_eq_zero_of_notMem h)
    obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support hwcs
    exact ((integrableOn_mul_newtonKernel hc M L).mono_set hML).mul_bdd
      (hwc.comp w.continuous_lightConeEquiv).aestronglyMeasurable
      (Eventually.of_forall fun q => hC _)
  rw [Measure.volume_eq_prod, integral_prod F hint]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [F, lightConeEquiv_apply]
  rw [← integral_wave_div_norm_advanced hu hcs τ (w.r τ), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [SmoothGeometry.Potential.newtonKernel]
  ring

end SubluminalWorldline

/-! ### Test functions on space-time -/

/-- The wave operator of a `C²` function on space-time in time and space:
`box χ (v) = −□u(v⁰, 𝐯)` with `u(t, x) = χ(t, x)`. -/
theorem box_eq_neg_waveOperator {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) :
    box χ = fun v => -Wave.waveOperator (fun p => χ (Wave.timeSpaceEquiv.symm p))
      (Wave.timeSpaceEquiv v) := by
  funext v
  have h := box_comp_timeSpaceEquiv (hχ.comp Wave.timeSpaceEquiv.symm.contDiff) v
  have hχu : (fun z => (χ ∘ Wave.timeSpaceEquiv.symm) (Wave.timeSpaceEquiv z)) = χ := by
    funext z
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [hχu] at h
  exact h

/-- The wave operator of a `C²` function on space-time is continuous. -/
theorem continuous_box {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) : Continuous (box χ) := by
  rw [box_eq_neg_waveOperator hχ]
  exact ((Wave.continuous_waveOperator (hχ.comp Wave.timeSpaceEquiv.symm.contDiff)).comp
    Wave.timeSpaceEquiv.continuous).neg

/-- The wave operator of a function of compact support has compact support. -/
theorem hasCompactSupport_box {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) : HasCompactSupport (box χ) := by
  refine hc.mono' fun v hv => ?_
  by_contra h
  apply hv
  rw [box_eq_neg_waveOperator hχ, neg_eq_zero]
  refine Wave.waveOperator_eq_zero_of_notMem fun hmem => h ?_
  rw [show (fun p => χ (Wave.timeSpaceEquiv.symm p)) =
      χ ∘ Wave.timeSpaceEquiv.symm.toHomeomorph from rfl,
    tsupport_comp_eq_preimage χ Wave.timeSpaceEquiv.symm.toHomeomorph, mem_preimage] at hmem
  exact (Wave.timeSpaceEquiv.symm_apply_apply v) ▸ hmem

namespace SubluminalWorldline

variable (w : SubluminalWorldline)

/-- **The pairing with the wave operator of a test function**: if in the light-cone
co-ordinates, times the Jacobian determinant, `g` is `c(τ)/(4π‖y‖)` with a continuous `c`, then
`∫ g box χ d⁴v = −∫ c(t) χ(t, r(t)) dt` for every `C²` function `χ` of compact support. -/
theorem integral_mul_box_of_lightCone {g : Spacetime → ℝ} {c : ℝ → ℝ} (hc : Continuous c)
    (hg : ∀ q : ℝ × Space 3, q.2 ≠ 0 →
      w.lightConeJacobian q * g (Minkowski.vector (q.1 + ‖q.2‖) (w.r q.1 + q.2)) =
        c q.1 / (4 * Real.pi * ‖q.2‖))
    {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) :
    ∫ v, g v * box χ v = -∫ t, c t * χ (Minkowski.vector t (w.r t)) := by
  set u : ℝ × Space 3 → ℝ := fun p => χ (Wave.timeSpaceEquiv.symm p) with hu_def
  have hu : ContDiff ℝ 2 u := hχ.comp Wave.timeSpaceEquiv.symm.contDiff
  have hcu : HasCompactSupport u := hχc.comp_homeomorph Wave.timeSpaceEquiv.symm.toHomeomorph
  have hbox : ∀ (a : ℝ) (b : Space 3),
      box χ (Minkowski.vector a b) = -Wave.waveOperator u (a, b) := by
    intro a b
    rw [box_eq_neg_waveOperator hχ]
    simp [u]
  calc ∫ v, g v * box χ v
      = ∫ q : ℝ × Space 3, -(c q.1 * SmoothGeometry.Potential.newtonKernel q.2 *
          Wave.waveOperator u (w.lightConeEquiv q)) := by
        rw [integral_spacetime_eq, w.integral_lightCone]
        refine integral_congr_ae (ae_snd_ne_zero.mono fun q hq => ?_)
        simp only [lightConeEquiv_apply, smul_eq_mul]
        rw [hbox, SmoothGeometry.Potential.newtonKernel]
        linear_combination (-Wave.waveOperator u (q.1 + ‖q.2‖, w.r q.1 + q.2)) * hg q hq
    _ = -∫ t, c t * χ (Minkowski.vector t (w.r t)) := by
        rw [integral_neg, w.integral_mul_newtonKernel_mul_wave hc hu hcu]
        simp [u]

/-- **The point charge is the source of its scalar potential** (Landau–Lifshitz §63): for every
`C²` function `χ` of compact support on space-time, `∫ φ box χ d⁴v = −e ∫ χ(t, r(t)) dt`. In the
sense of distributions `box φ = −e δ(x − r(t))`, the equation `box φ = −ρ` of the retarded
potential (`box_retardedScalar`) with the density `ρ = e δ(x − r(t))` of the point charge. -/
theorem integral_scalarPotential_mul_box (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) :
    ∫ v, LienardWiechert.scalarPotential e w v * box χ v =
      -(e * ∫ t, χ (Minkowski.vector t (w.r t))) := by
  rw [w.integral_mul_box_of_lightCone (c := fun _ => e) continuous_const
    (fun _ hq => w.lightConeJacobian_mul_scalarPotential e hq) hχ hc, integral_const_mul]

/-- **The point charge is the source of its vector potential**: for every `C²` function `χ` of
compact support on space-time, `∫ aᵢ box χ d⁴v = −e ∫ ṙᵢ(t) χ(t, r(t)) dt`, that is
`box 𝐚 = −e ṙ(t) δ(x − r(t))`, the current density of the point charge. -/
theorem integral_vectorPotential_mul_box (e : ℝ) (i : Fin 3) {χ : Spacetime → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    ∫ v, LienardWiechert.vectorPotential e w v i * box χ v =
      -(e * ∫ t, deriv w.r t i * χ (Minkowski.vector t (w.r t))) := by
  rw [w.integral_mul_box_of_lightCone (c := fun t => e * deriv w.r t i)
    (continuous_const.mul (LienardWiechert.contDiff_component w.contDiff_deriv i).continuous)
    (fun _ hq => w.lightConeJacobian_mul_vectorPotential e hq i) hχ hc, ← integral_const_mul]
  simp only [mul_assoc]

/-- **The equations of the potentials with the current of the point charge**: the components of
the potential of Liénard and Wiechert satisfy `box A₀ = k⁰` and `box aᵢ = −kⁱ` against test
functions, with the current `k = e (1, ṙ(t)) δ(x − r(t))` of the point charge, that is
`∫ A₀ box χ = e ∫ χ(t, r(t)) dt` and `∫ aᵢ box χ = −e ∫ ṙᵢ(t) χ(t, r(t)) dt`
(compare `box_retardedPotential`). -/
theorem integral_potentialComponent_mul_box (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) :
    ∫ v, potentialComponent (lienardWiechert e w) 0 v * box χ v =
        e * ∫ t, χ (Minkowski.vector t (w.r t)) ∧
      ∀ i : Fin 3, ∫ v, potentialComponent (lienardWiechert e w) i.succ v * box χ v =
        -(e * ∫ t, deriv w.r t i * χ (Minkowski.vector t (w.r t))) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [potentialComponent_lienardWiechert_zero]
    simp only [neg_mul, integral_neg]
    rw [w.integral_scalarPotential_mul_box e hχ hc, neg_neg]
  · rw [potentialComponent_lienardWiechert_succ]
    exact w.integral_vectorPotential_mul_box e i hχ hc

/-- Both sides of the source identity are well defined: the product of the scalar potential and
the wave operator of a test function is integrable. -/
theorem integrable_scalarPotential_mul_box (e : ℝ) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ) :
    Integrable fun v => LienardWiechert.scalarPotential e w v * box χ v :=
  (w.locallyIntegrable_scalarPotential e).integrable_smul_right_of_hasCompactSupport
    (continuous_box hχ) (hasCompactSupport_box hχ hc)

/-- The product of a component of the vector potential and the wave operator of a test function
is integrable. -/
theorem integrable_vectorPotential_mul_box (e : ℝ) (i : Fin 3) {χ : Spacetime → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    Integrable fun v => LienardWiechert.vectorPotential e w v i * box χ v :=
  (w.locallyIntegrable_vectorPotential e i).integrable_smul_right_of_hasCompactSupport
    (continuous_box hχ) (hasCompactSupport_box hχ hc)

/-! ### Instances -/

/-- The bump `spacetimeBump` (equal to `1` on the ball of the radius `1` about the origin and
supported in the ball of the radius `2`, for the sup norm) has a positive integral along a world
line that starts in the ball of the radius `2`. -/
theorem integral_spacetimeBump_pos (h : ‖w.r 0‖ < 2) :
    0 < ∫ t, spacetimeBump (Minkowski.vector t (w.r t)) := by
  have hcont : Continuous fun t => spacetimeBump (Minkowski.vector t (w.r t)) :=
    spacetimeBump.continuous.comp
      (Wave.timeSpaceEquiv.symm.continuous.comp (continuous_id.prodMk w.contDiff_r.continuous))
  have hcs : HasCompactSupport fun t => spacetimeBump (Minkowski.vector t (w.r t)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun t ht => ?_
    refine spacetimeBump.zero_of_le_dist ?_
    have h1 : |t| ≤ ‖Minkowski.vector t (w.r t)‖ := by
      simpa using norm_le_pi_norm (Minkowski.vector t (w.r t)) 0
    have h2 : 2 < |t| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with ht | ht
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        exact ht
    rw [dist_zero_right]
    exact le_trans (by norm_num [spacetimeBump]) (h2.le.trans h1)
  have hR : spacetimeBump.rOut = 2 := rfl
  have h0 : spacetimeBump (Minkowski.vector 0 (w.r 0)) ≠ 0 := by
    refine (spacetimeBump.pos_of_mem_ball ?_).ne'
    rw [mem_ball_zero_iff, hR, pi_norm_lt_iff (by norm_num)]
    intro μ
    refine Fin.cases ?_ (fun i => ?_) μ
    · simp
    · simp only [Minkowski.vector_succ]
      exact (PiLp.norm_apply_le (w.r 0) i).trans_lt h
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun t => spacetimeBump.nonneg) h0

/-- **An instance of the source identity** with the bump `spacetimeBump`: for a nonzero charge
on a world line that starts in the ball of the radius `2`, `∫ φ box χ` does not vanish. -/
theorem integral_scalarPotential_mul_box_spacetimeBump_ne_zero {e : ℝ} (he : e ≠ 0)
    (h : ‖w.r 0‖ < 2) :
    ∫ v, LienardWiechert.scalarPotential e w v * box spacetimeBump v ≠ 0 := by
  rw [w.integral_scalarPotential_mul_box e (spacetimeBump.contDiff (n := 2))
    spacetimeBump.hasCompactSupport]
  exact neg_ne_zero.mpr (mul_ne_zero he (w.integral_spacetimeBump_pos h).ne')

/-- The source identity for the charge at rest at the origin. -/
theorem integral_scalarPotential_mul_box_rest (e : ℝ) {χ : Spacetime → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) :
    ∫ v, LienardWiechert.scalarPotential e (rest 0) v * box χ v =
      -(e * ∫ t, χ (Minkowski.vector t 0)) := by
  rw [(rest 0).integral_scalarPotential_mul_box e hχ hc]
  simp [rest, uniform]

/-- **An instance**: the charge at rest at the origin is a nonzero source, tested against the
bump `spacetimeBump`. -/
theorem integral_scalarPotential_mul_box_rest_ne_zero {e : ℝ} (he : e ≠ 0) :
    ∫ v, LienardWiechert.scalarPotential e (rest 0) v * box spacetimeBump v ≠ 0 :=
  (rest 0).integral_scalarPotential_mul_box_spacetimeBump_ne_zero he (by simp [rest, uniform])

/-- **An instance**: the charge in uniform circular motion of a radius `|ρ| < 2` is a nonzero
source, tested against the bump `spacetimeBump`. -/
theorem integral_scalarPotential_mul_box_circular_ne_zero {e ρ Ω : ℝ} (he : e ≠ 0)
    (h : |ρ * Ω| < 1) (hρ : |ρ| < 2) :
    ∫ v, LienardWiechert.scalarPotential e (circular ρ Ω h) v * box spacetimeBump v ≠ 0 :=
  (circular ρ Ω h).integral_scalarPotential_mul_box_spacetimeBump_ne_zero he
    (by simpa [circular, circularPath, norm_smul, PiLp.norm_single] using hρ)

end SubluminalWorldline

end ProjectAinos.Electrodynamics
