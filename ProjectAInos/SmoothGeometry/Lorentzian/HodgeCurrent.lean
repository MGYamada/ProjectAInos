/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeSquare
public import ProjectAInos.SmoothGeometry.Minkowski.HodgeCurrent

/-! # Metric-dual current and contraction of the Lorentz volume

Pointwise Lorentz signature witnesses transport the coordinate identity.
No global Lorentz frame or flatness assumption is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel 3) M] [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]

/-- In four dimensions, `⋆(v♭) = ιᵥ vol`, in either metric signature. -/
theorem hodge_flat_one (g : LorentzMetric σ 3 M) (o : OrientedAtlas 4 M) (x : M)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel 3) x) :
    g.hodgeFiber o x (by decide : 1 + 3 = 3 + 1) (oneFormEquiv (g.flat x v)) =
      interior v (g.volumeForm o x) := by
  obtain ⟨L, hL⟩ := g.signature x
  have hα : oneFormEquiv (g.flat x v) =
      (oneFormEquiv (Minkowski.flat σ (L v))).compContinuousLinearMap L.toContinuousLinearMap := by
    ext w
    exact hL v (w 0)
  rw [hα, g.hodgeFiber_frame o x L hL, Minkowski.hodge_flat_one,
    ← g.frameVolume_form o x L, DifferentialForm.interior_smul, interior_comp]
  rfl

end ProjectAInos.SmoothGeometry.LorentzMetric
