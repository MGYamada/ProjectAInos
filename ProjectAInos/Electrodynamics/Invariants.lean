module
public import ProjectAInos.Electrodynamics.Field

/-! # Electromagnetic scalar and pseudoscalar

Both indices are raised with (-+++). Contraction of two antisymmetric tensors
counts each unordered pair twice. Rest-space norms are computed with the
inverse Lorentz metric on the observer-annihilating covectors.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

def raisedComponent (F : TwoForm) (i j : Fin 4) : ℝ :=
  lorentzSign .timeNegative i * lorentzSign .timeNegative j * component F i j

def tensorContraction (F G : TwoForm) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, component F i j * raisedComponent G i j

def scalarInvariant (F : TwoForm) : ℝ := (1 / 2 : ℝ) * tensorContraction F F
def pseudoscalarInvariant (F : TwoForm) : ℝ := (1 / 4 : ℝ) * tensorContraction F (star F)

def covectorPairing (a b : OneForm) : ℝ :=
  ∑ i : Fin 4, lorentzSign .timeNegative i *
    oneCovector a (Pi.single i 1) * oneCovector b (Pi.single i 1)

theorem covectorPairing_eq_metric (a b : OneForm) :
    covectorPairing a b = minkowskiForm .timeNegative 3
      (sharp .timeNegative (oneCovector a)) (sharp .timeNegative (oneCovector b)) := by
  rw [minkowskiForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [sharp_apply, sharp_apply]
  by_cases hi : i = 0 <;> simp [lorentzSign, hi]

/-- The observer-annihilating covectors carry a nonnegative Euclidean rest norm. -/
theorem covectorPairing_nonneg (u : Observer 3) (a : OneForm)
    (ha : oneCovector a u.velocity = 0) : 0 ≤ covectorPairing a a := by
  let v : u.restSpace := ⟨sharp .timeNegative (oneCovector a), by
    change pair u.velocity (sharp .timeNegative (oneCovector a)) = 0
    have h : minkowskiForm .timeNegative 3 (sharp .timeNegative (oneCovector a)) u.velocity = 0 := by
      change flat .timeNegative (sharp .timeNegative (oneCovector a)) u.velocity = 0
      rw [sharp, (flat .timeNegative).apply_symm_apply]
      exact ha
    rw [minkowskiForm_symmetric, metric_eq] at h
    simpa using h⟩
  rw [covectorPairing_eq_metric]
  have hr := u.restForm_convention .timeNegative v v
  norm_num at hr
  change 0 ≤ minkowskiForm .timeNegative 3 (v : Spacetime) (v : Spacetime)
  rw [← hr]
  by_cases hv : v = 0
  · simp [hv]
  · exact le_of_lt (u.restForm_posDef v hv)

theorem electric_apply (u : Observer 3) (F : TwoForm) (w : Spacetime) :
    oneCovector (electric u F) w = -F ![u.velocity, w] := by
  change oneCovector (-(F.curryLeft u.velocity)) w = _
  rw [map_neg]
  change -(oneCovector (F.curryLeft u.velocity) w) = _
  rw [oneCovector_curryLeft]

theorem magnetic_apply (u : Observer 3) (F : TwoForm) (w : Spacetime) :
    oneCovector (magnetic u F) w = star F ![u.velocity, w] :=
  oneCovector_curryLeft _ _ _

theorem tensorContraction_coordinates (F G : TwoForm) :
    tensorContraction F G = 2 *
      (-component F 0 1 * component G 0 1 - component F 0 2 * component G 0 2 -
        component F 0 3 * component G 0 3 + component F 1 2 * component G 1 2 +
        component F 1 3 * component G 1 3 + component F 2 3 * component G 2 3) := by
  rw [twoForm_expansion F, twoForm_expansion G]
  simp [tensorContraction, raisedComponent, component, twoFormExpansion,
    coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply, Fin.sum_univ_succ, lorentzSign]
  ring

theorem scalarInvariant_observer (u : Observer 3) (F : TwoForm) :
    scalarInvariant F = covectorPairing (magnetic u F) (magnetic u F) -
      covectorPairing (electric u F) (electric u F) := by
  have hscaled : covectorPairing (magnetic u F) (magnetic u F) -
      covectorPairing (electric u F) (electric u F) = intervalQuadratic u.velocity * scalarInvariant F := by
    simp only [covectorPairing, electric_apply, magnetic_apply]
    rw [twoForm_expansion F]
    simp [star, hodgeTwo_apply,
      scalarInvariant, tensorContraction_coordinates, component, twoFormExpansion,
      coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply, Fin.sum_univ_succ,
      lorentzSign, intervalQuadratic_apply, pair_four]
    ring
  rw [u.unit, one_mul] at hscaled
  exact hscaled.symm

theorem pseudoscalarInvariant_observer (u : Observer 3) (F : TwoForm) :
    pseudoscalarInvariant F = covectorPairing (electric u F) (magnetic u F) := by
  have hscaled : covectorPairing (electric u F) (magnetic u F) =
      intervalQuadratic u.velocity * pseudoscalarInvariant F := by
    simp only [covectorPairing, electric_apply, magnetic_apply]
    rw [twoForm_expansion F]
    simp [star, hodgeTwo_apply,
      pseudoscalarInvariant, tensorContraction_coordinates, component, twoFormExpansion,
      coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply, Fin.sum_univ_succ,
      lorentzSign, intervalQuadratic_apply, pair_four]
    ring
  rw [u.unit, one_mul] at hscaled
  exact hscaled.symm

theorem pseudoscalar_reverse_orientation (F : TwoForm) :
    (1 / 4 : ℝ) * tensorContraction F (hodgeFiber .timeNegative .reversed (by decide) F) =
      -pseudoscalarInvariant F := by
  rw [hodgeFiber_reverse]
  simp [pseudoscalarInvariant, tensorContraction, raisedComponent, component, star,
    Finset.sum_neg_distrib]

end ProjectAInos.Electrodynamics
