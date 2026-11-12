/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.RadialFrame
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartCurvature
public import ProjectAInos.SmoothGeometry.ODE.CoordinateCurvature

/-! # Native curvature and the coordinate flatness condition

The bundled coefficient curvature is evaluated on the coordinate basis and
identified with the native Christoffel curvature formula. Thus native zero
curvature supplies exactly the compatibility hypothesis required by the
radial parallel-frame construction.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Set Filter
open scoped ContDiff Manifold Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

open LinearODE

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

theorem chartChristoffelBilinear_basis (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (x : M) (k i j : Fin (d + 1)) :
    g.chartChristoffelBilinear e x (Pi.single i 1) (Pi.single j 1) k =
      g.chartChristoffel e x k i j := by
  simp [g.chartChristoffelBilinear_apply, Pi.single_apply]

/-- Evaluating the derivative of the bundled coefficients agrees with the
ordinary derivative of each scalar Christoffel coefficient. -/
theorem chartChristoffelBilinear_fderiv_basis (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : E} (hq : q ∈ e.target) (u : E) (k i j : Fin (d + 1)) :
    fderiv ℝ (fun z => g.chartChristoffelBilinear e (e.symm z)) q u
      (Pi.single i 1) (Pi.single j 1) k =
        fderiv ℝ (fun z => g.chartChristoffel e (e.symm z) k i j) q u := by
  have hΓ := ((g.chartChristoffelBilinear_contDiffOn he).contDiffAt
    (e.open_target.mem_nhds hq)).differentiableAt (by simp)
  have hd := (proj k : E →L[ℝ] ℝ).hasFDerivAt.comp q
    ((hΓ.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i 1) q)).clm_apply
      (hasFDerivAt_const (Pi.single j 1) q))
  have h := congrArg (fun A : E →L[ℝ] ℝ => A u) hd.fderiv
  simpa [Function.comp_def, chartChristoffelBilinear_basis] using h.symm

/-- The coordinate trilinear curvature has exactly the native components,
with the established `R(∂ᵢ,∂ⱼ)∂ₖ` index order. -/
theorem coefficientCurvature_basis (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : E} (hq : q ∈ e.target) (l i j k : Fin (d + 1)) :
    coefficientCurvature (fun z => g.chartChristoffelBilinear e (e.symm z)) q
      (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) l =
        g.chartCurvature e (e.symm q) l i j k := by
  rw [coefficientCurvature_apply]
  simp only [Pi.sub_apply, Pi.add_apply,
    g.chartChristoffelBilinear_fderiv_basis he hq]
  rw [g.chartCurvature_eq_fderiv he (e.map_target hq), e.right_inv hq]
  have hprod (a b c : Fin (d + 1)) :
      g.chartChristoffelBilinear e (e.symm q) (Pi.single a 1)
        (g.chartChristoffelBilinear e (e.symm q) (Pi.single b 1) (Pi.single c 1)) l =
          ∑ s, g.chartChristoffel e (e.symm q) l a s *
            g.chartChristoffel e (e.symm q) s b c := by
    simp [g.chartChristoffelBilinear_apply, Pi.single_apply]
  rw [hprod, hprod, Finset.sum_sub_distrib]
  ring

/-- Vanishing of the native tensor at a point gives vanishing of the full
coordinate trilinear map at its coordinate representative. -/
theorem coefficientCurvature_eq_zero (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : E} (hq : q ∈ e.target) (hR : g.curvature (e.symm q) = 0) :
    coefficientCurvature (fun z => g.chartChristoffelBilinear e (e.symm z)) q = 0 := by
  apply coefficientCurvature_eq_zero_of_basis
  intro i j k
  ext l
  rw [g.coefficientCurvature_basis he hq]
  simp [chartCurvature, hR]

/-- Native zero curvature implies the full bundled coordinate flatness
condition on the chart target, rather than only its basis components. -/
theorem isFlatConnectionOn_of_curvature_eq_zero (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hR : ∀ x ∈ e.source, g.curvature x = 0) :
    IsFlatConnectionOn (fun q => g.chartChristoffelBilinear e (e.symm q)) e.target := by
  rw [isFlatConnectionOn_iff]
  intro q hq
  exact g.coefficientCurvature_eq_zero he hq (hR _ (e.map_target hq))

end ProjectAInos.SmoothGeometry.LorentzMetric
