/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.ProperTime
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric

/-!
# The clocks of observers in co-ordinates

An observer reads time intervals from the proper time of its worldline (Landau–Lifshitz, §84).
For a metric given by coefficients on an open set `U` of the model space:

* `properTime_coordinate`: the proper time of a smooth curve of `U` is
  `∫ √(−g_{μν} ẋ^μ ẋ^ν) dt`.
* `properTime_atRest`: an observer at rest in the co-ordinates on `[a, b]`, `x(t) = x₀ + t e₀`,
  has the proper time `∫ √(−g₀₀) dt` there.

The distances that an observer measures are the spatial form of
`SmoothGeometry.Minkowski.spatialForm`, with its positivity at every event
(`SmoothGeometry.LorentzMetric.spatialForm_pos`) and the spatial metric of the observer at rest
(`SmoothGeometry.CoordinateMetric.spatialMetric_pos`).
-/

@[expose] public section

noncomputable section

open Bundle MeasureTheory Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry LorentzMetric CoordinateMetric

variable {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- The proper time of a smooth curve of the open set `U` in its co-ordinates. -/
theorem properTime_coordinate (g : CoordinateMetric .timeNegative d U) {γ : ℝ → U}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : MinkowskiModel d)) (a b : ℝ) :
    properTime g.toLorentzMetric γ a b =
      ∫ t in a..b, Real.sqrt (-g.form (γ t) (deriv (fun s => (γ s : MinkowskiModel d)) t)
        (deriv (fun s => (γ s : MinkowskiModel d)) t)) := by
  have hm : ContMDiff 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) ∞ γ :=
    (ContMDiff.subtypeVal_comp_iff U γ).mp hγ.contMDiff
  rw [properTime_chart g.toLorentzMetric (physicalChart_mem (γ a)) γ a b (fun t _ => by simp)
    (fun t _ => (hm t).mdifferentiableAt (by simp))]
  have he : (physicalChart (γ a) ∘ γ) = fun s => (γ s : MinkowskiModel d) :=
    funext fun s => physicalChart_apply (γ a) (γ s)
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [he, toLorentzMetric_chartMetric]

/-- **The clock of an observer at rest.** A smooth curve that is at rest in the co-ordinates on
`[a, b]`, `x(t) = x₀ + t e₀`, has the proper time `∫ √(−g₀₀) dt` from `a` to `b`. -/
theorem properTime_atRest (g : CoordinateMetric .timeNegative d U) {γ : ℝ → U}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : MinkowskiModel d)) {x₀ : MinkowskiModel d} {a b : ℝ}
    (hrest : ∀ t ∈ uIcc a b, (γ t : MinkowskiModel d) = x₀ + t • Pi.single 0 1) :
    properTime g.toLorentzMetric γ a b =
      ∫ t in a..b, Real.sqrt (-g.form (γ t) (Pi.single 0 1) (Pi.single 0 1)) := by
  rw [properTime_coordinate g hγ]
  refine intervalIntegral.integral_congr_ae ?_
  have hmax : ∀ᵐ t ∂volume, t ∉ ({max a b} : Set ℝ) :=
    (Set.countable_singleton (max a b)).ae_notMem volume
  filter_upwards [hmax] with t ht hmem
  have htI : t ∈ Ioo (min a b) (max a b) := by
    rw [uIoc, mem_Ioc] at hmem
    exact ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using ht)⟩
  have hnear : (fun s => (γ s : MinkowskiModel d)) =ᶠ[𝓝 t]
      fun s => x₀ + s • Pi.single 0 1 :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds htI) fun s hs =>
      hrest s (by rw [uIcc]; exact Ioo_subset_Icc_self hs)
  have hd : deriv (fun s => (γ s : MinkowskiModel d)) t = Pi.single 0 1 := by
    rw [hnear.deriv_eq]
    exact (((hasDerivAt_id t).smul_const (Pi.single 0 1 : MinkowskiModel d)).const_add
      x₀).deriv.trans (one_smul _ _)
  simp only [hd]

end ProjectAinos.GeneralRelativity
