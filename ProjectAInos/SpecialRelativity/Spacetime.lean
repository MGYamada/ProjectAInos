/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Affine
public import ProjectAInos.SmoothGeometry.Minkowski.Observer

/-! # Special relativity in natural units with signature (-+++) -/
@[expose] public section
noncomputable section
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry

abbrev Spacetime := MinkowskiModel 3
abbrev FourVector := MinkowskiModel 3
abbrev FourCovector := FourVector →L[ℝ] ℝ
def metric := minkowskiForm .timeNegative 3
def spacetimeManifold := minkowski .timeNegative 3

theorem metric_time_negative : metric (Pi.single 0 1) (Pi.single 0 1) = -1 := by
  norm_num [metric, minkowskiForm_apply, lorentzSign, Pi.single_apply]

end ProjectAInos.SpecialRelativity
