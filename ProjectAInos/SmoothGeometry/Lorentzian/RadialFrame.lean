/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LocalInertial
public import ProjectAInos.SmoothGeometry.Manifold.SmoothExtension
public import ProjectAInos.SmoothGeometry.ODE.Radial
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Local coordinate coefficients for radial transport

The native Levi-Civita connection supplies smooth bundled chart coefficients.
A cutoff extends them without changing their germ. Consequently the radial
ODE construction does not require a globally defined chart or connection
coefficients that are smooth outside the chart target.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open ContinuousLinearMap Set
open scoped ContDiff Manifold Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The bundled native connection coefficients are smooth on the coordinate
domain of any smooth maximal-atlas chart. -/
theorem chartChristoffelBilinear_contDiffOn (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (fun q => g.chartChristoffelBilinear e (e.symm q)) e.target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  apply contDiffOn_pi.mpr
  intro k
  have heq : (fun q => g.chartChristoffelBilinear e (e.symm q) v w k) =
      (fun q => ∑ i, ∑ j, g.chartChristoffel e (e.symm q) k i j * v i * w j) := by
    funext q
    exact g.chartChristoffelBilinear_apply e (e.symm q) v w k
  rw [heq]
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hc := (g.chartChristoffel_contMDiffAt he (e.map_target hq) k i j).comp q
    (contMDiffAt_symm_of_mem_maximalAtlas he hq)
  exact (hc.contDiffAt.mul contDiffAt_const).mul contDiffAt_const

/-- Smooth global coordinate coefficients can be chosen without changing the
connection near a chosen point of the original chart. -/
theorem exists_smooth_chartChristoffel_extension (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {p : M} (hp : p ∈ e.source) :
    ∃ Γ : E → E →L[ℝ] E →L[ℝ] E, ContDiff ℝ ∞ Γ ∧
      ∃ V : Set E, IsOpen V ∧ e p ∈ V ∧ V ⊆ e.target ∧
        EqOn Γ (fun q => g.chartChristoffelBilinear e (e.symm q)) V := by
  obtain ⟨Γ, hΓ, V, hV, hpV, hsub, hEq⟩ :=
    Manifold.exists_contDiff_extension_near_compact (K := {e p})
      isCompact_singleton e.open_target (singleton_subset_iff.mpr (e.map_source hp))
      (g.chartChristoffelBilinear_contDiffOn he)
  exact ⟨Γ, hΓ, V, hV, hpV (mem_singleton _), hsub, hEq⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
