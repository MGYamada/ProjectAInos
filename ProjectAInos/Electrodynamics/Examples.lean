module
public import ProjectAInos.Electrodynamics.LorentzForce
public import ProjectAInos.Electrodynamics.GaugeAction
public import ProjectAInos.Electrodynamics.Covariance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Nonzero fields, gauge pairs, and a uniformly accelerated charged particle -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace ProjectAInos.Electrodynamics.Examples
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity Mechanics

def restObserver : Observer 3 where
  velocity := Pi.single 0 1
  unit := by norm_num [intervalQuadratic_apply, pair_four, Pi.single_apply]
  future := by norm_num

def uniformPotential (E B : ℝ) : Spacetime →L[ℝ] OneForm :=
  oneCovector.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).smulRight
      (-E • (ContinuousLinearMap.proj 1 : FourCovector))) +
    ((ContinuousLinearMap.proj 2 : Spacetime →L[ℝ] ℝ).smulRight
      (B • (ContinuousLinearMap.proj 3 : FourCovector))))

def uniformField (E B : ℝ) : TwoForm := -E • coordinateForm ![0, 1] + B • coordinateForm ![2, 3]

theorem uniformPotential_covector (E B : ℝ) (x v : Spacetime) :
    oneCovector (uniformPotential E B x) v = -E * x 0 * v 1 + B * x 2 * v 3 := by
  simp [uniformPotential]
  ring

theorem uniformPotential_field (E B : ℝ) (x : Spacetime) :
    fieldTensor (uniformPotential E B) x = uniformField E B := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, fieldTensor_apply, (uniformPotential E B).fderiv]
  simp only [uniformPotential_covector]
  simp [uniformField, coordinateForm_apply, Matrix.det_fin_two]
  ring

theorem uniformField_electric (E B : ℝ) :
    oneCovector (electric restObserver (uniformField E B)) (Pi.single 1 1) = E := by
  rw [electric_apply]
  simp [uniformField, restObserver, coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

theorem uniformField_magnetic (E B : ℝ) :
    oneCovector (magnetic restObserver (uniformField E B)) (Pi.single 1 1) = B := by
  rw [magnetic_apply]
  simp [uniformField, restObserver, star, hodge_dt_dx, hodge_dy_dz,
    coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

example : uniformField 1 2 ≠ 0 := by
  intro h
  have he := uniformField_electric 1 2
  rw [h] at he
  norm_num [electric] at he

example : scalarInvariant (uniformField 1 2) = 3 := by
  norm_num [scalarInvariant, tensorContraction_coordinates, uniformField, component,
    coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

example : pseudoscalarInvariant (uniformField 1 2) = 2 := by
  norm_num [pseudoscalarInvariant, tensorContraction_coordinates, uniformField, component,
    star, hodge_dt_dx, hodge_dy_dz, coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

example : reconstructTwoForm .timeNegative .standard restObserver
    (-(electric restObserver (uniformField 1 2))) (magnetic restObserver (uniformField 1 2)) =
      uniformField 1 2 := observer_reconstruction _ _

example : (1 / 4 : ℝ) * tensorContraction (uniformField 1 2)
    (hodgeFiber .timeNegative .reversed (by decide) (uniformField 1 2)) = -2 := by
  rw [pseudoscalar_reverse_orientation]
  norm_num [pseudoscalarInvariant, tensorContraction_coordinates, uniformField, component,
    star, hodge_dt_dx, hodge_dy_dz, coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

def gaugeFunction : Spacetime →L[ℝ] ℝ := ContinuousLinearMap.proj 0

/-- An actual Lorentz transformation reversing one spatial coordinate. -/
def spatialReflection : LorentzGroup 3 := reflection (Pi.single 1 1)
  (by norm_num [intervalQuadratic_apply, pair_four, Pi.single_apply])

theorem spatialReflection_det : spatialReflection.val.toLinearMap.det = -1 :=
  reflectionLinear_det _ (by norm_num [intervalQuadratic_apply, pair_four, Pi.single_apply])

example : pseudoscalarInvariant (lorentzPullback spatialReflection (uniformField 1 2)) = -2 := by
  rw [pseudoscalarInvariant_orientationReversing spatialReflection spatialReflection_det]
  norm_num [pseudoscalarInvariant, tensorContraction_coordinates, uniformField, component,
    star, hodge_dt_dx, hodge_dy_dz, coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]

theorem uniform_gauge_equivalent :
    fieldTensor (gaugeShift (uniformPotential 1 2) gaugeFunction) = fieldTensor (uniformPotential 1 2) :=
  fieldTensor_gauge _ _ (uniformPotential 1 2).differentiable gaugeFunction.contDiff

theorem uniform_gauge_distinct : gaugeShift (uniformPotential 1 2) gaugeFunction ≠ uniformPotential 1 2 := by
  intro h
  have he := congrArg (fun A : Potential => oneCovector (A 0) (Pi.single 0 1)) h
  simp only [gaugeShift, Pi.add_apply, map_add, add_apply, scalar_derivative, gaugeFunction.fderiv] at he
  norm_num [gaugeFunction] at he

def hyperbola (τ : ℝ) : Spacetime := ![Real.sinh τ, Real.cosh τ, 0, 0]
def hyperbolaVelocity (τ : ℝ) : Spacetime := ![Real.cosh τ, Real.sinh τ, 0, 0]

theorem hyperbola_smooth : ContDiff ℝ 2 hyperbola := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_sinh
  · exact Real.contDiff_cosh
  · exact contDiff_const
  · exact contDiff_const

theorem hyperbola_deriv (τ : ℝ) : deriv hyperbola τ = hyperbolaVelocity τ := by
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact Real.hasDerivAt_sinh τ
  · exact Real.hasDerivAt_cosh τ
  · exact hasDerivAt_const τ 0
  · exact hasDerivAt_const τ 0

theorem hyperbolaVelocity_deriv (τ : ℝ) : deriv hyperbolaVelocity τ = hyperbola τ := by
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact Real.hasDerivAt_cosh τ
  · exact Real.hasDerivAt_sinh τ
  · exact hasDerivAt_const τ 0
  · exact hasDerivAt_const τ 0

theorem hyperbola_unit (τ : ℝ) : intervalQuadratic (deriv hyperbola τ) = 1 := by
  rw [hyperbola_deriv]
  simp [intervalQuadratic_apply, pair_four, hyperbolaVelocity, ← pow_two]

theorem hyperbola_future (τ : ℝ) : FutureTimelike (deriv hyperbola τ) := by
  rw [futureTimelike_iff]
  constructor
  · change 0 < intervalQuadratic (deriv hyperbola τ)
    rw [hyperbola_unit]
    norm_num
  · rw [hyperbola_deriv]
    exact Real.cosh_pos τ

theorem hyperbola_lorentzForce (τ : ℝ) :
    lorentzForce 1 (uniformField 1 0) (hyperbolaVelocity τ) = hyperbola τ := by
  ext i
  rw [lorentzForce_component]
  fin_cases i <;>
    simp [uniformField, hyperbola, hyperbolaVelocity, raisedComponent, component,
      coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply, Fin.sum_univ_succ,
      flat_apply, minkowskiForm_apply, lorentzSign]

/-- A non-inertial, future-timelike worldline is stationary for m = e = E = 1. -/
theorem hyperbola_stationary {a b : ℝ} (hab : a < b) :
    Stationary a b (chargedLagrangian 1 1 (uniformPotential 1 0)) hyperbola := by
  apply (stationary_iff_lorentzForce 1 1 hab hyperbola_smooth isOpen_univ
    (uniformPotential 1 0).contDiff.contDiffOn (fun _ _ => mem_univ _)
    (fun τ _ => (futureTimelike_iff _).mp (hyperbola_future τ) |>.1)).mpr
  intro τ _
  have hu : (fun s => fourVelocity (deriv hyperbola s)) = hyperbolaVelocity := by
    funext s
    rw [fourVelocity, properSpeed, hyperbola_unit s, Real.sqrt_one, inv_one, one_smul, hyperbola_deriv]
  rw [hu, hyperbolaVelocity_deriv, one_smul, uniformPotential_field, hyperbola_deriv,
    hyperbola_lorentzForce]

end ProjectAInos.Electrodynamics.Examples
