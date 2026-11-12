/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ChartConnection

/-! # Differentiation in manifold chart directions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

omit [IsManifold I ∞ M] in
/-- Local equality suffices for equality of vector-space-valued manifold derivatives. -/
theorem mvfderiv_congr_of_eventuallyEq {f h : M → F} {x : M}
    (hfh : f =ᶠ[𝓝 x] h) : mvfderiv I f x = mvfderiv I h x := by
  simp only [mvfderiv, hfh.mfderiv_eq]
  rfl

omit [IsManifold I ∞ M] in
/-- Differentiation along a pulled-back constant chart direction is
ordinary differentiation of the coordinate representative. -/
theorem mvfderiv_chartField {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    {f : M → F} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (v : E) :
    mvfderiv I f x (chartField e v x) = fderiv ℝ (f ∘ e.symm) (e x) v := by
  have hF : MDifferentiableAt I 𝓘(ℝ, F) (f ∘ e.symm) (e x) :=
    hf.comp_of_eq (e x) ((contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).mdifferentiableAt
      (by simp)) (e.left_inv hx)
  have heq : (f ∘ e.symm) ∘ e =ᶠ[𝓝 x] f := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hd := mvfderiv_congr_of_eventuallyEq (d := d) heq
  have h := congrArg (fun L => L (chartField e v x))
    (mvfderiv_comp x hF ((contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp)))
  rw [hd, mvfderiv_eq_fderiv] at h
  change mvfderiv I f x (chartField e v x) =
    fderiv ℝ (f ∘ e.symm) (e x) (chartTangentMap e x (chartField e v x)) at h
  simpa only [chartTangentMap_field he hx] using h

/-- Mixed scalar derivatives commute in constant chart directions under
local `C²` regularity. This is Schwarz's theorem transported through the chart. -/
theorem mvfderiv_chartField_commute {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (u v : E) :
    mvfderiv I (fun y => mvfderiv I f y (chartField e v y)) x (chartField e u x) =
      mvfderiv I (fun y => mvfderiv I f y (chartField e u y)) x (chartField e v x) := by
  let D (w : E) : M → ℝ := fun y => mvfderiv I f y (chartField e w y)
  have hD (w : E) : MDifferentiableAt I 𝓘(ℝ) (D w) x :=
    (contMDiffAt_directionalDerivative (n := 1) hf
      ((chartField_contMDiffAt he hx w).of_le (by simp))).mdifferentiableAt (by norm_num)
  have hF : ContDiffAt ℝ 2 (f ∘ e.symm) (e x) :=
    (hf.comp_of_eq ((contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).of_le (by simp))
      (e.left_inv hx)).contDiffAt
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hf.of_le (by norm_num))
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    simpa only [ContinuousAt, e.left_inv hx] using
      (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).continuousAt
  have heq (w : E) : D w ∘ e.symm =ᶠ[𝓝 (e x)] (fun z => fderiv ℝ (f ∘ e.symm) z w) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx), ht.eventually hn] with z hz hfz
    simpa only [D, Function.comp_apply, e.right_inv hz] using
      mvfderiv_chartField he (e.map_target hz) (hfz.mdifferentiableAt (by norm_num)) w
  rw [mvfderiv_chartField he hx (hD v), mvfderiv_chartField he hx (hD u),
    (heq v).fderiv_eq, (heq u).fderiv_eq]
  have h := fderiv_apply_lieBracket (V := fun _ => u) (W := fun _ => v) hF
    (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
    (differentiableAt_const v) (differentiableAt_const u)
  simp only [lieBracket, fderiv_const_apply, zero_apply, sub_self, map_zero] at h
  exact sub_eq_zero.mp h.symm

end ProjectAInos.SmoothGeometry.LorentzMetric
