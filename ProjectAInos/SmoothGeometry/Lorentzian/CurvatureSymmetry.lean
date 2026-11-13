/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Curvature
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartDerivatives

/-! # Metric symmetries of Lorentz curvature

Metric compatibility and commuting scalar chart derivatives imply skew
adjointness of curvature. The proof uses local charts, without normal
coordinates, positive definiteness or a globally chosen frame.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

private theorem eventually_mdiff_field {Z : ∀ x, TM x} {x : M}
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I ((I).prod I) (T% Z) y :=
  ((contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hZ.of_le (by norm_num))).mono (fun _ hy => hy.mdifferentiableAt (by norm_num))

/-- Differentiate metric compatibility once more, keeping all four terms. -/
theorem pairing_second_derivative {X Y Z W : ∀ x, TM x} {x : M}
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x)
    (hW : ContMDiffAt I ((I).prod I) 2 (T% W) x) :
    mvfderiv I (fun y => mvfderiv I (fun z => g.form z (Z z) (W z)) y (Y y)) x (X x) =
      g.form x (g.covariantField X (g.covariantField Y Z) x) (W x) +
      g.form x (g.covariantField Y Z x) (g.covariantField X W x) +
      (g.form x (g.covariantField X Z x) (g.covariantField Y W x) +
        g.form x (Z x) (g.covariantField X (g.covariantField Y W) x)) := by
  have hYZ := (g.contMDiffAt_covariantField (n := 1) (hY.of_le (by norm_num)) hZ).mdifferentiableAt
    (by norm_num)
  have hYW := (g.contMDiffAt_covariantField (n := 1) (hY.of_le (by norm_num)) hW).mdifferentiableAt
    (by norm_num)
  have hZd := hZ.mdifferentiableAt (by norm_num)
  have hWd := hW.mdifferentiableAt (by norm_num)
  have heq : (fun y => mvfderiv I (fun z => g.form z (Z z) (W z)) y (Y y)) =ᶠ[𝓝 x]
      (fun y => g.form y (g.covariantField Y Z y) (W y) +
        g.form y (Z y) (g.covariantField Y W y)) := by
    filter_upwards [eventually_mdiff_field hZ, eventually_mdiff_field hW] with y hyZ hyW
    exact g.leviCivita_metricCompatible (Y y) hyZ hyW
  have hmv := mvfderiv_congr_of_eventuallyEq (d := d) heq
  rw [hmv, mvfderiv_fun_add (g.mdifferentiableAt_pairing hYZ hWd)
    (g.mdifferentiableAt_pairing hZd hYW), add_apply,
    g.leviCivita_metricCompatible (X x) hYZ hWd,
    g.leviCivita_metricCompatible (X x) hZd hYW]
  rfl

private theorem curvatureField_chart_skew (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) {Z W : ∀ x, TM x}
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x)
    (hW : ContMDiffAt I ((I).prod I) 2 (T% W) x) (u v : E) :
    g.form x (g.curvatureField (chartField e u) (chartField e v) Z x) (W x) +
      g.form x (Z x) (g.curvatureField (chartField e u) (chartField e v) W x) = 0 := by
  have hcomm := mvfderiv_chartField_commute he hx (g.contMDiffAt_pairing hZ hW) u v
  rw [g.pairing_second_derivative ((chartField_contMDiffAt he hx v).of_le (by simp)) hZ hW,
    g.pairing_second_derivative ((chartField_contMDiffAt he hx u).of_le (by simp)) hZ hW] at hcomm
  have hz (V : ∀ y, TM y) :
      g.covariantField (mlieBracket I (chartField e u) (chartField e v)) V x = 0 := by
    simp only [covariantField, chartField_bracket he hx, map_zero]
  simp only [curvatureField, hz, sub_zero, map_sub, sub_apply]
  linarith only [hcomm]

/-- Curvature is skew-adjoint with respect to the Lorentz metric. -/
theorem curvature_skewAdjoint (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z + g.form x w (g.curvature x u v z) = 0 := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source E x
  have hU := (chartField_contMDiffAt he hx (chartTangentMap e x u)).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hV := (chartField_contMDiffAt he hx (chartTangentMap e x v)).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have h := curvatureField_chart_skew g he hx (contMDiffAt_extend I E w)
    (contMDiffAt_extend I E z) (chartTangentMap e x u) (chartTangentMap e x v)
  rw [← g.curvature_apply hU hV (contMDiffAt_extend I E w),
    ← g.curvature_apply hU hV (contMDiffAt_extend I E z)] at h
  simpa only [chartField_tangentMap he hx, extend_apply_self] using h

/-- Antisymmetry in the last two arguments of the lowered Riemann tensor. -/
theorem curvature_pair_swap (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z = -g.form x (g.curvature x u v z) w := by
  have h := g.curvature_skewAdjoint x u v w z
  rw [g.symmetric x w] at h
  linarith only [h]

/-- First Bianchi after lowering the output index. -/
theorem curvature_pair_bianchi (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z + g.form x (g.curvature x v w u) z +
      g.form x (g.curvature x w u v) z = 0 := by
  simpa using congrArg (fun a => g.form x a z) (g.curvature_first_bianchi x u v w)

/-- Interchanging the two argument pairs preserves the lowered curvature. -/
theorem curvature_pair_interchange (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z = g.form x (g.curvature x w z u) v := by
  have h₁ := g.curvature_pair_bianchi x u v w z
  have h₂ := g.curvature_pair_bianchi x u v z w
  have h₃ := g.curvature_pair_bianchi x u w z v
  have h₄ := g.curvature_pair_bianchi x v w z u
  simp only [g.curvature_swap x w u v, map_neg, neg_apply] at h₁
  simp only [g.curvature_swap x z u v, map_neg, neg_apply] at h₂
  rw [g.curvature_pair_swap x u v z w] at h₂
  simp only [g.curvature_swap x z u w, map_neg, neg_apply] at h₃
  rw [g.curvature_pair_swap x u w z v, g.curvature_pair_swap x u z w v] at h₃
  simp only [g.curvature_swap x z v w, map_neg, neg_apply] at h₄
  rw [g.curvature_pair_swap x v w z u, g.curvature_pair_swap x w z v u,
    g.curvature_pair_swap x v z w u] at h₄
  linarith only [h₁, h₂, h₃, h₄]

end ProjectAInos.SmoothGeometry.LorentzMetric
