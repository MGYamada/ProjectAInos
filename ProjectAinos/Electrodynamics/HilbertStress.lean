/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.StressTensor
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMatter

/-!
# The stress tensor of the field from the variation of the metric

The Hilbert tensor of a fixed electromagnetic field, `CoordinateMetric.maxwellStress`, is the
first variation of `−¼ F_{ab} F^{ab} √|g|` with respect to the metric
(`CoordinateMetric.hasDerivAt_integral_maxwellDensity`). In Minkowski space, for the field
`F_{ab} = G(e_a, e_b)` of a two-form `G`, it is the stress tensor `stressForm G` of §33
(`maxwellStress_minkowski`): the variation of the metric characterizes the tensor
`T_{μν} = F_{μα} F_ν{}^α − ¼ g_{μν} F²` (Landau–Lifshitz, §94, applied to §33).
-/

@[expose] public section

noncomputable section

open TopologicalSpace

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

theorem sum_diagonal_mul {n : ℕ} (s : Fin n → ℝ) (b : Fin n) (f : Fin n → ℝ) :
    ∑ e, Matrix.diagonal s b e * f e = s b * f b := by
  simp [Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq]

/-- The components `F_{ab} = G(e_a, e_b)` of a field of two-forms. -/
def componentMatrix (G : Spacetime → TwoForm) (x : Spacetime) :
    Matrix (Fin (3 + 1)) (Fin (3 + 1)) ℝ :=
  Matrix.of fun a b => component (G x) a b

theorem componentMatrix_antisymm (G : Spacetime → TwoForm) (x : Spacetime) (a b : Fin (3 + 1)) :
    componentMatrix G x a b = -componentMatrix G x b a := by
  simp only [componentMatrix, Matrix.of_apply, component]
  exact twoForm_swap _ _ _

/-- **The Hilbert tensor of the field in Minkowski space is the stress tensor of §33.** -/
theorem maxwellStress_minkowski {U : Opens Spacetime} (G : Spacetime → TwoForm) (x : Spacetime)
    (i k : Fin (3 + 1)) :
    (CoordinateMetric.minkowski .timeNegative 3 U).maxwellStress (componentMatrix G) x i k =
      stressForm (G x) (Pi.single i 1) (Pi.single k 1) := by
  have hinv : (Matrix.diagonal (lorentzSign (d := 3) .timeNegative))⁻¹ =
      Matrix.diagonal (lorentzSign (d := 3) .timeNegative) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp only [SmoothGeometry.lorentzSign_sq, Matrix.diagonal_one]
  have hprod : (CoordinateMetric.minkowski .timeNegative 3 U).maxwellProduct (componentMatrix G)
      x i k = covectorPairing ((G x).curryLeft (Pi.single i 1))
        ((G x).curryLeft (Pi.single k 1)) := by
    rw [CoordinateMetric.maxwellProduct, CoordinateMetric.minkowski_coefficient, hinv,
      covectorPairing]
    simp only [sum_diagonal_mul, oneCovector_curryLeft_single, componentMatrix, Matrix.of_apply,
      component]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hinvt : (CoordinateMetric.minkowski .timeNegative 3 U).maxwellInvariant
      (componentMatrix G) x = tensorContraction (G x) (G x) := by
    rw [CoordinateMetric.maxwellInvariant, CoordinateMetric.minkowski_coefficient, hinv,
      tensorContraction]
    simp only [mul_assoc, ← Finset.mul_sum, sum_diagonal_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [componentMatrix, Matrix.of_apply, raisedComponent]
    ring
  rw [CoordinateMetric.maxwellStress, hprod, hinvt, CoordinateMetric.minkowski_coefficient,
    stressForm, minkowskiForm_single, Matrix.diagonal_apply]
  ring

end ProjectAinos.Electrodynamics
