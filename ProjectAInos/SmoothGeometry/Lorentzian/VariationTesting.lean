/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LocalizedVariation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Detecting tangent residuals by actual manifold variations

The fundamental lemma is applied inside a local time patch in one chart.
Every test field used in the argument is realized by an actual C² family.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open Variational

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Zero pairing against every actual fixed-endpoint variation forces a
residual to vanish. Continuity is required only for its scalar chart pairings. -/
theorem eq_zero_of_variation_pairing (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (R : AlongField (d := d) γ)
    (hR : ∀ (e : OpenPartialHomeomorph M E), e ∈ IsManifold.maximalAtlas I ∞ M →
      ∀ (w : E) (t : ℝ), t ∈ Ioo a b → γ t ∈ e.source →
        ContinuousAt (fun s => g.form (γ s) (chartField e w (γ s)) (R s)) t)
    (hz : ∀ V : ManifoldCurveVariation («E» := E) γ a b,
      (∫ t in a..b, g.form (γ t) (variationField V t) (R t)) = 0) :
    ∀ t ∈ Ioo a b, R t = 0 := by
  intro t ht
  have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact ⟨ht.1.le, ht.2.le⟩
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  obtain ⟨U, hUsub, hU, htU⟩ := mem_nhds_iff.mp
    (inter_mem (isOpen_Ioo.mem_nhds ht)
      ((hγ t ht').continuousAt (e.open_source.mem_nhds hx)))
  have hUI : U ⊆ Ioo a b := fun _ hs => (hUsub hs).1
  have hstay : MapsTo γ U e.source := fun _ hs => (hUsub hs).2
  have hpair (w : E) : g.form (γ t) (chartField e w (γ t)) (R t) = 0 := by
    let f : ℝ → ℝ := fun s => g.form (γ s) (chartField e w (γ s)) (R s)
    have hf : ContinuousOn f U := fun s hs => (hR e he w s (hUI hs) (hstay hs)).continuousWithinAt
    have ha := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn (μ := volume) hU.measurableSet)
      (fun θ hθ _hcompact hsupp => by
        let η : ℝ → E := fun s => θ s • w
        have hη : ContDiff ℝ 2 η := (hθ.of_le (by simp)).smul contDiff_const
        have hηsupp : tsupport η ⊆ U :=
          (tsupport_comp_subset (g := fun c : ℝ => c • w) (zero_smul ℝ w) θ).trans hsupp
        let V := chartCurveVariation he hU hUI hstay hηsupp hγ hη
        have hidentity : (∫ s in a..b, g.form (γ s) (variationField V s) (R s)) =
            ∫ s, θ s • f s := by
          calc
            _ = ∫ s in a..b, θ s • f s := by
              apply intervalIntegral.integral_congr
              intro s hs
              dsimp only [V]
              rw [variationField_chart he hU hUI hstay hηsupp hγ hη hs]
              simp only [η, chartField_smul, map_smul, smul_apply,
                smul_eq_mul, f]
            _ = _ := by
              rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
              exact setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
                rw [image_eq_zero_of_notMem_tsupport (fun h => hs (hUI (hsupp h))), zero_smul]
        exact hidentity.symm.trans (hz V))
    have hae : f =ᵐ[volume.restrict U] (fun _ => 0) :=
      (ae_restrict_iff' hU.measurableSet).2 ha
    exact Measure.eqOn_open_of_ae_eq hae hU hf continuous_const.continuousOn htU
  apply g.nondegenerate (γ t) (R t)
  intro v
  rw [g.symmetric]
  simpa only [chartField_tangentMap he hx] using hpair (chartTangentMap e (γ t) v)

end ProjectAInos.SmoothGeometry.LorentzMetric
