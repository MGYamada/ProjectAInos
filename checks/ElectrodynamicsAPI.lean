import ProjectAInos

noncomputable section

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

section CurvedMaxwell

open scoped Manifold ContDiff
open DifferentialForm

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)

example : SmoothCovector 𝓘(ℝ, MinkowskiModel 3) (M := M) ≃ₗ[ℝ]
    SmoothForm 𝓘(ℝ, MinkowskiModel 3) M 1 := smoothOneFormEquiv _

example (j : Curved.CurrentVector (M := M)) (x : M)
    (v : Fin 1 → TangentSpace 𝓘(ℝ, MinkowskiModel 3) x) :
    Curved.currentOneForm g j x v = g.form x (j x) (v 0) :=
  Curved.currentOneForm_apply g j x v

example (j : Curved.CurrentVector (M := M)) :
    Curved.currentVector g o (Curved.currentForm g o j) = j :=
  Curved.currentVector_currentForm g o j

example (J : Curved.CurrentForm (M := M)) :
    Curved.currentForm g o (Curved.currentVector g o J) = J :=
  Curved.currentForm_currentVector g o J

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M))
    (h : smoothExteriorDerivative (Curved.excitation g o F) = Curved.currentForm g o j) :
    smoothExteriorDerivative (Curved.currentForm g o j) = 0 :=
  Curved.current_closed_of_source g o F j h

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M)) :
    Curved.Maxwell g o F j ↔ smoothExteriorDerivative F = 0 ∧ j = Curved.source g o F :=
  Curved.maxwell_iff g o F j

example (A : Curved.Potential (M := M)) :
    Curved.Maxwell g o (smoothExteriorDerivative A) (Curved.source g o (smoothExteriorDerivative A)) :=
  Curved.potential_maxwell g o A

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M)) :
    Curved.Maxwell g o.reverse F j ↔ Curved.Maxwell g o F j := Curved.maxwell_reverse_iff g o F j

example (F : Electrodynamics.Field) (hF : ContDiff ℝ ∞ F) (x : Spacetime) :
    Curved.excitation (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4)
      (ofFlat F hF) x = -Electrodynamics.star (F x) := Curved.excitation_flat F hF x

example : Curved.currentForm (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4)
    (Curved.source (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4)
      Curved.Examples.electric) = Curved.Examples.spatialCurrent := Curved.Examples.electric_current

example : Curved.source (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4)
    Curved.Examples.electric ≠ 0 := Curved.Examples.electric_source_nonzero

example (j : Curved.CurrentVector (M := M)) (x : M) :
    Curved.currentForm g o j x = DifferentialForm.interior (j x) (g.volumeForm o x) :=
  Curved.currentForm_volume g o j x

example (j : Curved.CurrentVector (M := M)) (x : M) :
    smoothExteriorDerivative (Curved.currentForm g o j) x =
      g.divergence j x • g.volumeForm o x := Curved.exteriorDerivative_currentForm g o j x

example (j : Curved.CurrentVector (M := M)) :
    smoothExteriorDerivative (Curved.currentForm g o j) = 0 ↔ ∀ x, g.divergence j x = 0 :=
  Curved.current_closed_iff_divergence g o j

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M))
    (h : smoothExteriorDerivative (Curved.excitation g o F) = Curved.currentForm g o j) :
    ∀ x, g.divergence j x = 0 := Curved.divergence_zero_of_source g o F j h

example : Curved.source (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4)
    Curved.Examples.electric = Curved.Examples.negativeSpatial := Curved.Examples.electric_source

end CurvedMaxwell

section HomogeneousMaxwell

open scoped Manifold ContDiff
open DifferentialForm LorentzMetric
variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)

example {F : Curved.Field (M := M)} {j : Curved.CurrentVector (M := M)}
    (h : Curved.Maxwell g o F j) {e : OpenPartialHomeomorph M (MinkowskiModel 3)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M)
    {x : M} (hx : x ∈ e.source) (i j k : Fin 4) :
    g.twoFormCovariantComponent F e x i j k + g.twoFormCovariantComponent F e x j k i +
      g.twoFormCovariantComponent F e x k i j = 0 := h.homogeneous_components g o he hx i j k

example (x : Spacetime) :
    (minkowskiMetric .timeNegative 3).twoFormDerivative Curved.Examples.magneticExcitation x
        (Pi.single 2 1) (Pi.single 3 1) (Pi.single 0 1) +
      (minkowskiMetric .timeNegative 3).twoFormDerivative Curved.Examples.magneticExcitation x
        (Pi.single 3 1) (Pi.single 0 1) (Pi.single 2 1) +
      (minkowskiMetric .timeNegative 3).twoFormDerivative Curved.Examples.magneticExcitation x
        (Pi.single 0 1) (Pi.single 2 1) (Pi.single 3 1) = 1 :=
  Curved.Examples.magneticExcitation_covariant_cyclic x

end HomogeneousMaxwell

example : (minkowskiMetric .timeNegative 3).twoFormDivergence Curved.Examples.electric =
    Curved.source (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4)
      Curved.Examples.electric := Curved.Examples.electric_twoFormDivergence_eq_source

section SourcedMaxwell

open scoped Manifold ContDiff
open DifferentialForm LorentzMetric
variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)

example (F : Curved.Field (M := M)) :
    smoothExteriorDerivative (Curved.excitation g o F) =
      Curved.currentForm g o (g.twoFormDivergence F) := Curved.exteriorDerivative_excitation g o F

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M)) :
    smoothExteriorDerivative (Curved.excitation g o F) = Curved.currentForm g o j ↔
      g.twoFormDivergence F = j := Curved.sourced_iff_divergence g o F j

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M)) :
    Curved.Maxwell g o F j ↔
      (∀ x (u v w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) x),
        g.twoFormDerivative F x v w u + g.twoFormDerivative F x w u v +
          g.twoFormDerivative F x u v w = 0) ∧ g.twoFormDivergence F = j :=
  Curved.maxwell_iff_covariant g o F j

example (F : Curved.Field (M := M)) (j : Curved.CurrentVector (M := M)) :
    Curved.Maxwell g o F j ↔
      (∀ (e : OpenPartialHomeomorph M (MinkowskiModel 3)),
        e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M →
        ∀ x ∈ e.source, ∀ i k l : Fin 4,
          g.twoFormCovariantComponent F e x i k l +
          g.twoFormCovariantComponent F e x k l i +
          g.twoFormCovariantComponent F e x l i k = 0) ∧
      (∀ (e : OpenPartialHomeomorph M (MinkowskiModel 3))
          (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M),
        ∀ (x : M) (hx : x ∈ e.source), ∀ k : Fin 4,
          (∑ b, ∑ a, ∑ i, g.twoFormCovariantComponent F e x i a b *
            g.inverseComponent x (chartTangentEquiv he hx) a i *
            g.inverseComponent x (chartTangentEquiv he hx) k b) =
              chartTangentMap e x (j x) k) := Curved.maxwell_iff_components g o F j

example (F : Curved.Field (M := M)) {e : OpenPartialHomeomorph M (MinkowskiModel 3)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel 3) ∞ M)
    {x : M} (hx : x ∈ e.source) (j : Fin 4) :
    chartTangentMap e x (Curved.source g o F x) j = (g.chartDensity e x)⁻¹ *
      ∑ i, mvfderiv 𝓘(ℝ, MinkowskiModel 3)
        (fun y => g.chartDensity e y * g.raisedTwoFormComponent F e y i j) x
        (chartField e (Pi.single i 1) x) := Curved.source_density g o F he hx j

example (F : Curved.Field (M := M)) :
    Curved.source g o.reverse F = Curved.source g o F := Curved.source_reverse g o F

example (F : Curved.Field (M := M)) (x : M) :
    g.divergence (g.twoFormDivergence F) x = 0 := Curved.divergence_twoFormDivergence g o F x

end SourcedMaxwell
