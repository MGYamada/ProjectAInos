/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# The tangent spaces of a manifold are normable

Mathlib defines `TangentSpace I x` as the model vector space `E` and derives its instances from
those of `E`. The derived instance `IsNormableSpace 𝕜 (TangentSpace I x)` is stated with the
module structure of `E` in place of the module structure of the tangent space. The two agree
after `TangentSpace` is unfolded, and instance search does not unfold it, so the derived instance
is not found.

`tangentSpace_isNormableSpace` states the instance for the module structure of the tangent space.
Operations on continuous linear maps that need a normable space, such as
`ContinuousLinearMap.flip`, then apply to maps between tangent spaces. No norm is chosen on a
tangent space.
-/

@[expose] public section

namespace ProjectAinos.SmoothGeometry

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M)

/-- The topology of a tangent space is the topology of a norm. -/
instance tangentSpace_isNormableSpace : IsNormableSpace 𝕜 (TangentSpace I x) :=
  inferInstanceAs (IsNormableSpace 𝕜 E)

end ProjectAinos.SmoothGeometry
