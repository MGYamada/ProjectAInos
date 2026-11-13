/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Homogeneous
public import ProjectAInos.Electrodynamics.CurvedExamples

/-! # Closed and nonclosed examples of the covariant Maxwell cyclic sum -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.Electrodynamics.Curved.Examples
open SmoothGeometry SmoothGeometry.DifferentialForm SmoothGeometry.LorentzMetric

local notation "E" => SpecialRelativity.Spacetime
local notation "g" => minkowskiMetric LorentzConvention.timeNegative 3
local notation "o" => OrientedAtlas.standard 4

theorem electric_covariant_cyclic (x : E) (u v w : TangentSpace 𝓘(ℝ, E) x) :
    (g).twoFormDerivative electric x v w u + (g).twoFormDerivative electric x w u v +
      (g).twoFormDerivative electric x u v w = 0 :=
  electric_maxwell.homogeneous_covariant g o x u v w

/-- A nonclosed two-form has a nonzero cyclic sum; the equation is not automatic. -/
theorem magneticExcitation_covariant_cyclic (x : E) :
    (g).twoFormDerivative magneticExcitation x (Pi.single 2 1) (Pi.single 3 1) (Pi.single 0 1) +
      (g).twoFormDerivative magneticExcitation x (Pi.single 3 1) (Pi.single 0 1) (Pi.single 2 1) +
      (g).twoFormDerivative magneticExcitation x (Pi.single 0 1) (Pi.single 2 1) (Pi.single 3 1) = 1 := by
  have h := (g).exteriorDerivative_eq_covariant magneticExcitation x
    (Pi.single 0 1) (Pi.single 2 1) (Pi.single 3 1)
  rw [(g).twoFormDerivative_skew magneticExcitation x (Pi.single 0 1) (Pi.single 3 1),
    sub_neg_eq_add, magneticExcitation_derivative] at h
  rw [← h]
  change coordinateForm ![0, 2, 3] ![(Pi.single 0 1 : E), Pi.single 2 1, Pi.single 3 1] = 1
  norm_num [coordinateForm_apply, Matrix.det_fin_three, Pi.single_apply]

end ProjectAInos.Electrodynamics.Curved.Examples
