/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Current
public import ProjectAInos.Electrodynamics.CurvedExamples

/-! # The nonzero Maxwell source as an actual vector field -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.Electrodynamics.Curved.Examples
open SmoothGeometry SmoothGeometry.DifferentialForm SmoothGeometry.LorentzMetric

local notation "E" => SpecialRelativity.Spacetime
local notation "g" => minkowskiMetric LorentzConvention.timeNegative 3
local notation "o" => OrientedAtlas.standard 4

/-- The vector current `-∂x`, as a smooth actual tangent section. -/
def negativeSpatial : CurrentVector (M := E) :=
  ⟨modelField (-(Pi.single 1 1 : E)), fun x => modelField_contMDiff _ x⟩

theorem negativeSpatial_currentForm : currentForm g o negativeSpatial = spatialCurrent := by
  ext x w
  rw [currentForm_volume, LorentzianVolumeExamples.minkowski_volume]
  change interior (-(Pi.single 1 1 : E)) (coordinateForm id) w = coordinateForm ![0, 2, 3] w
  rw [Minkowski.interior_coordinate_volume]
  simp [Fin.sum_univ_succ, Pi.single_apply, Fin.succAbove]
  congr 1
  ext i j
  fin_cases j <;> rfl

/-- The field `F=t dt∧dx` has the vector source `j=-∂x`, fixing the physical sign. -/
theorem electric_source : source g o electric = negativeSpatial := by
  apply (currentEquiv g o).injective
  change currentForm g o (source g o electric) = currentForm g o negativeSpatial
  rw [electric_current, negativeSpatial_currentForm]

theorem electric_source_divergence (x : E) : (g).divergence (source g o electric) x = 0 :=
  electric_maxwell.divergence_zero g o x

end ProjectAInos.Electrodynamics.Curved.Examples
