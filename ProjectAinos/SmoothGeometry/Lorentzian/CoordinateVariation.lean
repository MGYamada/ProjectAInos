/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.SignatureStability

/-!
# Variations of a coordinate metric with compact support

A variation of a coordinate metric `g` on an open set `U` of the model space is a family of
symmetric forms `h`. The sum `g + ε h` is again a coordinate metric when it has the signature of
the convention at every point of `U` (`CoordinateMetric.IsAdmissible`).

* `CoordinateMetric.eventually_isAdmissible`: if `h` is continuous, symmetric, and has compact
  support inside `U`, then `g + ε h` is admissible for all `ε` near `0`. The signature is stable
  at each point of the support (`Minkowski.exists_lorentzFrame_of_near`), uniformly on the
  compact support by the tube lemma, and outside the support `g + ε h = g`.
* `CoordinateMetric.addVariation`: the coordinate metric `g + ε h` for an admissible `ε`.
-/

@[expose] public section

noncomputable section

open Bundle ContinuousLinearMap Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry

variable {σ : LorentzConvention} {d : ℕ}

namespace CoordinateMetric

variable {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U)

/-- `g + ε h` has the signature of the convention at every point of `U`. -/
def IsAdmissible
    (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ U, ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
    ∀ v w, (g.form x + ε • h x) v w = minkowskiForm σ d (e v) (e w)

theorem isAdmissible_zero
    (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) :
    g.IsAdmissible h 0 := fun x hx => by
  obtain ⟨e, he⟩ := g.signature x hx
  exact ⟨e, fun v w => by simpa using he v w⟩

theorem form_symmetric {x : MinkowskiModel d} (hx : x ∈ U) (v w : MinkowskiModel d) :
    g.form x v w = g.form x w v := by
  obtain ⟨e, he⟩ := g.signature x hx
  rw [he, he, minkowskiForm_symmetric]

/-- **Admissibility of small variations with compact support.** -/
theorem eventually_isAdmissible
    {h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}
    (hc : Continuous h) (hK : HasCompactSupport h) (hKU : tsupport h ⊆ U)
    (hs : ∀ x v w, h x v w = h x w v) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), g.IsAdmissible h ε := by
  have hP : ∀ x ∈ tsupport h, ∀ᶠ z : ℝ × MinkowskiModel d in 𝓝 ((0 : ℝ), x),
      ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
        ∀ v w, (g.form z.2 + z.1 • h z.2) v w = minkowskiForm σ d (e v) (e w) := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    obtain ⟨e, he⟩ := g.signature x hxU
    set c := ‖(e.symm : MinkowskiModel d →L[ℝ] MinkowskiModel d)‖ ^ 2
    set δ := 1 / (2 * (c + 1))
    have hδ0 : 0 < δ := by positivity
    have hterm (i j : Fin (d + 1)) : Filter.Tendsto (fun z : ℝ × MinkowskiModel d =>
        |g.form z.2 (Pi.single i 1) (Pi.single j 1) + z.1 * h z.2 (Pi.single i 1) (Pi.single j 1)
          - g.form x (Pi.single i 1) (Pi.single j 1)|) (𝓝 ((0 : ℝ), x)) (𝓝 0) := by
      have h1 : ContinuousAt (fun y => g.form y (Pi.single i 1) (Pi.single j 1)) x :=
        ((g.smooth.clm_apply contDiffOn_const).clm_apply contDiffOn_const).continuousOn
          |>.continuousAt (U.isOpen.mem_nhds hxU)
      have h2 : Continuous (fun y => h y (Pi.single i 1) (Pi.single j 1)) :=
        (hc.clm_apply continuous_const).clm_apply continuous_const
      have hcont : ContinuousAt (fun z : ℝ × MinkowskiModel d =>
          |g.form z.2 (Pi.single i 1) (Pi.single j 1) +
            z.1 * h z.2 (Pi.single i 1) (Pi.single j 1) -
              g.form x (Pi.single i 1) (Pi.single j 1)|) ((0 : ℝ), x) :=
        (((h1.comp_of_eq continuousAt_snd rfl).add (continuousAt_fst.mul
          (h2.continuousAt.comp continuousAt_snd))).sub continuousAt_const).abs
      have := hcont.tendsto
      simpa using this
    have hN : ∀ᶠ z : ℝ × MinkowskiModel d in 𝓝 ((0 : ℝ), x),
        (∑ i, ∑ j, |g.form z.2 (Pi.single i 1) (Pi.single j 1) +
          z.1 * h z.2 (Pi.single i 1) (Pi.single j 1) -
            g.form x (Pi.single i 1) (Pi.single j 1)|) < δ := by
      have ht := tendsto_finsetSum (Finset.univ : Finset (Fin (d + 1))) fun i _ =>
        tendsto_finsetSum (Finset.univ : Finset (Fin (d + 1))) fun j _ => hterm i j
      simp only [Finset.sum_const_zero] at ht
      exact ht.eventually (gt_mem_nhds hδ0)
    have hU : ∀ᶠ z : ℝ × MinkowskiModel d in 𝓝 ((0 : ℝ), x), z.2 ∈ U :=
      continuousAt_snd.eventually (U.isOpen.mem_nhds hxU)
    filter_upwards [hN, hU] with z hz hzU
    refine Minkowski.exists_lorentzFrame_of_near σ e he
      (fun v w => by simp only [add_apply, smul_apply, g.form_symmetric hzU v w, hs])
      hδ0.le (fun u => ?_) ?_
    · have hb := Minkowski.abs_apply_self_le (g.form z.2 + z.1 • h z.2 - g.form x) u
      simp only [sub_apply, add_apply, smul_apply, smul_eq_mul] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hz.le (sq_nonneg _))
    · have hc0 : 0 ≤ c := by positivity
      simp only [δ]
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
  have hKc : IsCompact (tsupport h) := hK
  filter_upwards [hKc.eventually_forall_of_forall_eventually
    (P := fun ε y => ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, (g.form y + ε • h y) v w = minkowskiForm σ d (e v) (e w)) hP] with ε hε x hx
  by_cases hxK : x ∈ tsupport h
  · exact hε x hxK
  · obtain ⟨e, he⟩ := g.signature x hx
    refine ⟨e, fun v w => ?_⟩
    rw [← he v w, image_eq_zero_of_notMem_tsupport hxK]
    simp

/-- The coordinate metric `g + ε h` for an admissible `ε`. -/
def addVariation (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hh : ContDiffOn ℝ ∞ h U) (ε : ℝ) (hε : g.IsAdmissible h ε) : CoordinateMetric σ d U where
  form x := g.form x + ε • h x
  smooth := g.smooth.add (hh.const_smul ε)
  signature := hε

@[simp] theorem addVariation_form
    (h : MinkowskiModel d → MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (hh : ContDiffOn ℝ ∞ h U) (ε : ℝ) (hε : g.IsAdmissible h ε) (x : MinkowskiModel d) :
    (g.addVariation h hh ε hε).form x = g.form x + ε • h x := rfl

end CoordinateMetric

end ProjectAinos.SmoothGeometry
