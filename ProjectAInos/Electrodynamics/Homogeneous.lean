/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Curved
public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormExterior

/-! # The homogeneous Maxwell equation in covariant components -/

@[expose] public section
noncomputable section
open scoped Manifold ContDiff

namespace ProjectAInos.Electrodynamics.Curved
open SmoothGeometry SmoothGeometry.DifferentialForm SmoothGeometry.LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)

/-- Maxwell's homogeneous equation is the cyclic covariant tensor identity. -/
theorem Maxwell.homogeneous_covariant {F : Field (M := M)} {j : CurrentVector (M := M)}
    (h : Maxwell g o F j) (x : M) (u v w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) x) :
    g.twoFormDerivative F x v w u + g.twoFormDerivative F x w u v +
      g.twoFormDerivative F x u v w = 0 :=
  (g.exteriorDerivative_zero_iff_covariant F).mp h.1 x u v w

/-- The cyclic component equation holds in every smooth chart, with the actual connection. -/
theorem Maxwell.homogeneous_components {F : Field (M := M)} {j : CurrentVector (M := M)}
    (h : Maxwell g o F j) {e : OpenPartialHomeomorph M (MinkowskiModel 3)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M)
    {x : M} (hx : x ∈ e.source) (i j k : Fin 4) :
    g.twoFormCovariantComponent F e x i j k + g.twoFormCovariantComponent F e x j k i +
      g.twoFormCovariantComponent F e x k i j = 0 :=
  (g.exteriorDerivative_zero_iff_components F).mp h.1 e he x hx i j k

end ProjectAInos.Electrodynamics.Curved
