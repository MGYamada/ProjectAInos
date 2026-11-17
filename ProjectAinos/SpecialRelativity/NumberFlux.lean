/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.ShellMeasure
public import ProjectAinos.SpecialRelativity.ObserverEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The distribution function and the number of particles

A distribution of particles of mass `m` in the momenta is a function `f` of the space momenta
`π`, in the chart of the future mass shell (Landau–Lifshitz, *The Classical Theory of Fields*,
§10).

* `numberCurrent m f = ∫ f(π) p(π) dᵈπ/E` is the number current, a vector of space-time.
* `transformDistribution m L f` is the distribution in the frame transformed by `L`: it has at
  the momentum `L p` the value of `f` at `p`. `numberCurrent_transform` shows that the number
  current is a vector: the current of the transformed distribution is `L` of the current.
* `numberDensity u f = pair u N` is the density of the number of particles for the observer
  `u`. It does not change if the observer and the distribution are transformed together
  (`numberDensity_transform`), and `time_numberCurrent` shows that in the frame of the
  co-ordinates it is `∫ f(π) dᵈπ`.
* `numberFlux m σ n f = ∫ pair (n x) N[f(x, ·)] dσ(x)` is the number of particles that cross
  a hypersurface with the surface measure `σ` and the field `n` of its normals, for a
  distribution that depends on the event. `numberFlux_transform`: it does not change if the
  measure, the normals and the distribution are transformed together. For the hyperplane
  `x⁰ = τ` of the co-ordinates with the measure `dᵈx` and the constant normal it is
  `∫∫ f dᵈπ dᵈx` (`numberFlux_hyperplane`).

The surface measure and the normals of a hypersurface are given: a measure on the events and
a field of vectors. Only those of the hyperplanes of the co-ordinates are constructed.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace ProjectAinos.SpecialRelativity.FutureShell

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ} {m : ℝ}

/-- The number current `N = ∫ f(π) p(π) dᵈπ/E` of a distribution on the shell. -/
def numberCurrent (m : ℝ) (f : (Fin d → ℝ) → ℝ) : MinkowskiModel d :=
  ∫ π, f π • point m π ∂(measure d m)

/-- The distribution in the frame transformed by `L`: its value at `L p` is the value of `f`
at `p`. -/
def transformDistribution (m : ℝ) (L : orthochronousLorentzGroup d) (f : (Fin d → ℝ) → ℝ) :
    (Fin d → ℝ) → ℝ :=
  fun π => f (action m L⁻¹ π)

/-- A Lorentz transformation, as a continuous linear map of space-time. -/
def lorentzCLM (L : orthochronousLorentzGroup d) : MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap

theorem lorentzCLM_apply (L : orthochronousLorentzGroup d) (v : MinkowskiModel d) :
    lorentzCLM L v = L.val.val v := rfl

theorem point_action_inv (L : orthochronousLorentzGroup d) {π : Fin d → ℝ}
    (hπ : π ∈ domain d m) : L.val.val (point m (action m L⁻¹ π)) = point m π := by
  rw [← point_action L (action_mem L⁻¹ hπ), ← action_mul L L⁻¹ hπ, mul_inv_cancel, action_one]

/-- The number current is a vector: the current of the transformed distribution is the
transformed current. -/
theorem numberCurrent_transform (L : orthochronousLorentzGroup d) (f : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    numberCurrent m (transformDistribution m L f) = L.val.val (numberCurrent m f) := by
  have hae : (fun π => transformDistribution m L f π • point m π) =ᵐ[measure d m]
      fun π => lorentzCLM L (f (action m L⁻¹ π) • point m (action m L⁻¹ π)) := by
    filter_upwards [ae_mem_domain] with π hπ
    rw [lorentzCLM_apply, map_smul, point_action_inv L hπ, transformDistribution]
  have hcomp : Integrable ((fun π => f π • point m π) ∘ action m L⁻¹) (measure d m) :=
    (measurePreserving_action L⁻¹).integrable_comp_of_integrable hf
  have hcomm := ContinuousLinearMap.integral_comp_comm (lorentzCLM L) hcomp
  simp only [Function.comp_apply] at hcomm
  have hinv := integral_comp_action L⁻¹ (fun π => f π • point m π) hf.aestronglyMeasurable
  unfold numberCurrent
  rw [integral_congr_ae hae, hcomm, hinv, lorentzCLM_apply]

/-- The density of the number of particles for the observer `u`. -/
def numberDensity (m : ℝ) (u : Observer d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  pair u.velocity (numberCurrent m f)

/-- The density is the integral of the distribution with the energy measured by the
observer. -/
theorem numberDensity_eq (u : Observer d) (f : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    numberDensity m u f = ∫ π, f π * observerEnergy u (point m π) ∂(measure d m) := by
  have h := ContinuousLinearMap.integral_comp_comm (pair u.velocity) hf
  rw [numberDensity, numberCurrent, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun π => ?_)
  change pair u.velocity (f π • point m π) = f π * pair u.velocity (point m π)
  rw [map_smul, smul_eq_mul]

/-- The density does not change if the observer and the distribution are transformed
together. -/
theorem numberDensity_transform (L : orthochronousLorentzGroup d) (u : Observer d)
    (f : (Fin d → ℝ) → ℝ) (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    numberDensity m (u.transform L) (transformDistribution m L f) = numberDensity m u f := by
  rw [numberDensity, numberCurrent_transform L f hf]
  exact LorentzGroup.preserves_pair L.val u.velocity (numberCurrent m f)

/-- For a distribution that is not negative the density is not negative for every observer. -/
theorem numberDensity_nonneg (u : Observer d) {f : (Fin d → ℝ) → ℝ} (hf0 : ∀ π, 0 ≤ f π)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) : 0 ≤ numberDensity m u f := by
  rw [numberDensity_eq u f hf]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_mem_domain] with π hπ
  exact mul_nonneg (hf0 π) (pair_nonneg_of_futureCausal u.futureTimelike.futureCausal
    (futureCausal_of_mem (point_mem hπ)))

/-- In the frame of the co-ordinates the density of the number of particles is
`∫ f(π) dᵈπ`. -/
theorem time_numberCurrent (f : (Fin d → ℝ) → ℝ)
    (hf : Integrable (fun π => f π • point m π) (measure d m)) :
    time (numberCurrent m f) = ∫ π in domain d m, f π := by
  have h := ContinuousLinearMap.integral_comp_comm (time : MinkowskiModel d →L[ℝ] ℝ) hf
  rw [numberCurrent, ← h, measure, integral_withDensity_eq_integral_toReal_smul
    measurable_density (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_domain fun π hπ => ?_
  have hE := energy_pos hπ
  change (ENNReal.ofReal (energy m π)⁻¹).toReal • time (f π • point m π) = f π
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hE.le), map_smul, time_point, smul_eq_mul,
    smul_eq_mul]
  field_simp

/-- The number of particles that cross a hypersurface with the surface measure `σ` and the
normal `n x` at the event `x`, for a distribution `f x` that depends on the event. -/
def numberFlux (m : ℝ) (σ : Measure (MinkowskiModel d))
    (n : MinkowskiModel d → MinkowskiModel d) (f : MinkowskiModel d → (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ x, pair (n x) (numberCurrent m (f x)) ∂σ

/-- The number of particles does not change if the surface measure, the normals and the
distribution are transformed together. -/
theorem numberFlux_transform (L : orthochronousLorentzGroup d)
    (σ : Measure (MinkowskiModel d)) (n : MinkowskiModel d → MinkowskiModel d)
    (f : MinkowskiModel d → (Fin d → ℝ) → ℝ)
    (hf : ∀ x, Integrable (fun π => f x π • point m π) (measure d m)) :
    numberFlux m (Measure.map L.val.val σ) (fun y => L.val.val (n (L.val.val.symm y)))
        (fun y => transformDistribution m L (f (L.val.val.symm y))) =
      numberFlux m σ n f := by
  have hemb : MeasurableEmbedding (L.val.val : MinkowskiModel d → MinkowskiModel d) :=
    (LorentzGroup.toContinuousLinearEquiv L.val).toHomeomorph.measurableEmbedding
  rw [numberFlux, hemb.integral_map, numberFlux]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change pair (L.val.val (n (L.val.val.symm (L.val.val x)))) (numberCurrent m
    (transformDistribution m L (f (L.val.val.symm (L.val.val x))))) = _
  rw [LinearEquiv.symm_apply_apply, numberCurrent_transform L (f x) (hf x)]
  exact LorentzGroup.preserves_pair L.val (n x) (numberCurrent m (f x))

/-! ### The hyperplanes of the co-ordinates -/

theorem measurableEmbedding_cons (τ : ℝ) :
    MeasurableEmbedding fun x : Fin d → ℝ => (Fin.cons τ x : MinkowskiModel d) := by
  have hleft : Function.LeftInverse (spaceMomentum (d := d))
      fun x : Fin d → ℝ => (Fin.cons τ x : MinkowskiModel d) := fun _ => rfl
  have hcont : Continuous fun x : Fin d → ℝ => (Fin.cons τ x : MinkowskiModel d) := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_const
    · exact continuous_apply j
  exact (hleft.isClosedEmbedding contDiff_spaceMomentum.continuous hcont).measurableEmbedding

/-- The surface measure `dᵈx` of the hyperplane `x⁰ = τ` of the co-ordinates. -/
def hyperplaneMeasure (d : ℕ) (τ : ℝ) : Measure (MinkowskiModel d) :=
  Measure.map (fun x : Fin d → ℝ => (Fin.cons τ x : MinkowskiModel d)) volume

/-- Through the hyperplane `x⁰ = τ` the number of particles is `∫∫ f dᵈπ dᵈx`. -/
theorem numberFlux_hyperplane (τ : ℝ) (f : MinkowskiModel d → (Fin d → ℝ) → ℝ)
    (hf : ∀ x, Integrable (fun π => f x π • point m π) (measure d m)) :
    numberFlux m (hyperplaneMeasure d τ) (fun _ => timeAxis d) f =
      ∫ x : Fin d → ℝ, ∫ π in domain d m, f (Fin.cons τ x) π := by
  rw [numberFlux, hyperplaneMeasure, (measurableEmbedding_cons τ).integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change pair (timeAxis d) (numberCurrent m (f (Fin.cons τ x))) = _
  rw [pair_timeAxis, time_numberCurrent _ (hf _)]

end ProjectAinos.SpecialRelativity.FutureShell
