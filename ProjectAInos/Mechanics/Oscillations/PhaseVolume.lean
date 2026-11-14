/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Oscillator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The phase volume of the oscillator

Liouville's theorem for the oscillator (Landau–Lifshitz §46): the flow of
`p²/2m + ½ m ω² q²` is a linear map of determinant one, so it preserves the
Lebesgue measure of the phase plane.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Oscillator

open MeasureTheory

/-- Liouville's theorem for the oscillator: the flow at every time preserves
the Lebesgue measure of the phase plane. -/
theorem map_flowMatrix_volume {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (t : ℝ) :
    Measure.map (Matrix.toLin' (flowMatrix m ω t)) (volume : Measure (Fin 2 → ℝ)) = volume := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (by rw [det_flowMatrix hm hω]; exact one_ne_zero), det_flowMatrix hm hω, inv_one, abs_one,
    ENNReal.ofReal_one, one_smul]

theorem measurePreserving_flowMatrix {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (t : ℝ) :
    MeasurePreserving (Matrix.toLin' (flowMatrix m ω t)) (volume : Measure (Fin 2 → ℝ)) volume :=
  ⟨(Matrix.toLin' (flowMatrix m ω t)).continuous_of_finiteDimensional.measurable,
    map_flowMatrix_volume hm hω t⟩

end ProjectAInos.Mechanics.Oscillator
