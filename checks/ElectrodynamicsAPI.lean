import ProjectAInos

open ProjectAInos
open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity Electrodynamics

#check Variational.exists_contDiff_extension_near_compact
#check Variational.eventually_mapsTo_open
#check Mechanics.hasDerivAt_action_firstVariation_on
#check Mechanics.stationary_iff_eulerLagrange_on
#check freeAction_eq_action
#check freeLagrangian_contDiffOn
#check fieldTensor_gauge_on
#check bianchi_components
#check fieldTensor_poincare
#check scalarInvariant_observer
#check pseudoscalarInvariant_observer
#check scalarInvariant_lorentz
#check pseudoscalarInvariant_orientationReversing
#check chargedAction_eq
#check stationary_iff_lorentzForce
#check stationary_properTime
#check lorentzForce_component
#check lorentzForce_orthogonal
#check mass_shell
#check zero_charge_acceleration
#check chargedAction_gauge_on
#check stationary_gauge_iff_on
#check Polynomial.fieldTensor_potential
#check Polynomial.radial_formula
#check Polynomial.radial_upstream
#check Polynomial.mapCoefficients_closed
#check Polynomial.radial_map
#check Polynomial.constantJet_nonzero
#check Polynomial.linearJet_nonzero
#check Examples.hyperbola_stationary
#check YM.Maxwell.potential
#check YM.Maxwell.curl_inverse
#check YM.Maxwell.potential_recover

example (u : Observer 3) (F : TwoForm) :
    (1 / 2 : ℝ) * tensorContraction F F =
      covectorPairing (magnetic u F) (magnetic u F) - covectorPairing (electric u F) (electric u F) :=
  scalarInvariant_observer u F

example (u : Observer 3) (F : TwoForm) :
    (1 / 4 : ℝ) * tensorContraction F (star F) = covectorPairing (electric u F) (magnetic u F) :=
  pseudoscalarInvariant_observer u F
