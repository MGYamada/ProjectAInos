/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.SourcedActionExamples

/-! Public consumers of the field with a prescribed current: the action with a current three-form
and its stationarity, the change of the action under a gauge change and the closedness of the
current, the current of the matter with the sign of the source term, the equations of Maxwell
for the electric and the magnetic field, the conservation of the charge in a box, and the
stationary field `t dt ∧ dx` with the current `∂x`.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open MeasureTheory Set
open scoped ContDiff
namespace ProjectAinos.Electrodynamics.SourcedAction

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm

open SpecialRelativity VacuumAction ContinuousLinearMap

example (a : OneForm) (R : ThreeForm) :
    sourcePairing a R = coefficient (wedgeFiber a R) :=
  sourcePairing_apply a R

example : lagrangian 0 = VacuumAction.lagrangian :=
  lagrangian_zero

example (J : Form Spacetime 3) (A : Potential) (x : Spacetime) :
    Variational.density (lagrangian J) A x =
      Variational.density VacuumAction.lagrangian A x - sourcePairing (A x) (J x) :=
  density_eq J A x

example {J : Form Spacetime 3} (hJ : ContDiff ℝ 2 J) :
    ContDiff ℝ 2 (Function.uncurry (lagrangian J)) :=
  lagrangian_contDiff hJ

example {J : Form Spacetime 3} (hJ : ContDiff ℝ 2 J) {A η : Potential}
    {x : Spacetime} (hA : DifferentiableAt ℝ A x) (hη : DifferentiableAt ℝ η x) :
    Variational.firstVariationDensity (lagrangian J) A η x =
      -coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) -
        sourcePairing (η x) (J x) :=
  firstVariationDensity_eq hJ hA hη

example {U : Set Spacetime} {A η : Potential} {J : Form Spacetime 3}
    (hJ : ContDiff ℝ 2 J) (hA : ContDiff ℝ 2 A) (hη : Variational.InteriorVariation U η)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    HasDerivAt (fun ε => Variational.action (volume.restrict U) (lagrangian J)
      (Variational.perturb A η ε))
      (-∫ x in U, (coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) +
        sourcePairing (η x) (J x))) 0 :=
  hasDerivAt_action hJ hA hη hfin

example {U : Set Spacetime} {η : Potential}
    (hη : Variational.InteriorVariation U η) {f : Spacetime → ℝ} (hf : Continuous f)
    (h0 : ∀ x, x ∉ tsupport η → f x = 0) : Integrable f volume :=
  integrable_of_eq_zero_off hη hf h0

example {U : Set Spacetime} {A η : Potential} {J : Form Spacetime 3}
    (hJ : ContDiff ℝ 2 J) (hA : ContDiff ℝ 2 A) (hη : Variational.InteriorVariation U η) :
    (∫ x in U, (coefficient (wedgeFiber (fieldTensor η x) (star (fieldTensor A x))) +
        sourcePairing (η x) (J x))) =
      ∫ x in U, sourcePairing (η x) (residual A x + J x) :=
  weak_form hJ hA hη

example {U : Set Spacetime} {A : Potential} {J : Form Spacetime 3}
    (hU : IsOpen U) (hA : ContDiff ℝ 2 A) (hJ : ContDiff ℝ 2 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian J) A ↔ ∀ x ∈ U, residual A x + J x = 0 :=
  stationary_iff hU hA hJ hfin

example {U : Set Spacetime} {A : Potential} {J : Form Spacetime 3}
    (hU : IsOpen U) (hA : ContDiff ℝ 2 A) (hJ : ContDiff ℝ 2 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian J) A ↔
      ∀ x ∈ U, exteriorDerivative (fun y => -star (fieldTensor A y)) x = J x :=
  stationary_iff_excitation hU hA hJ hfin

example {U : Set Spacetime} {A : Potential} (hU : IsOpen U)
    (hA : ContDiff ℝ 2 A)
    (hfin : Integrable (Variational.density (lagrangian 0) A) (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian 0) A ↔ ∀ x ∈ U, residual A x = 0 :=
  stationary_zero_iff hU hA hfin

example (χ : Spacetime → ℝ) (x : Spacetime) :
    scalarForm χ x = χ x • (coordinateForm ![] : Spacetime [⋀^Fin 0]→L[ℝ] ℝ) :=
  scalarForm_apply_eq χ x

example {χ : Spacetime → ℝ} {x : Spacetime}
    (hx : x ∉ tsupport χ) : exteriorDerivative (scalarForm χ) x = 0 :=
  exteriorDerivative_scalarForm_eq_zero hx

example (R : Spacetime [⋀^Fin (3 + 1)]→L[ℝ] ℝ) :
    coefficient (wedgeFiber (k := 0) (coordinateForm ![] : Spacetime [⋀^Fin 0]→L[ℝ] ℝ) R) =
      coefficient R :=
  coefficient_wedgeFiber_one R

example {χ : Spacetime → ℝ} {J : Form Spacetime 3}
    {x : Spacetime} (hχ : DifferentiableAt ℝ (scalarForm χ) x) (hJ : DifferentiableAt ℝ J x) :
    coefficient (exteriorDerivative (wedge (scalarForm χ) J) x) =
      sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) +
        χ x * coefficient (exteriorDerivative J x) :=
  coefficient_exteriorDerivative_wedge hχ hJ

example {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hK : HasCompactSupport χ) {J : Form Spacetime 3} (hJ : ContDiff ℝ 1 J) :
    ∫ x, sourcePairing (exteriorDerivative (scalarForm χ) x) (J x) =
      -∫ x, χ x * coefficient (exteriorDerivative J x) :=
  integral_sourcePairing_exteriorDerivative hχ hK hJ

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 1 A U) {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hK : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) {J : Form Spacetime 3}
    (hJ : ContDiff ℝ 1 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    Variational.action (volume.restrict U) (lagrangian J) (gaugeShift A χ) =
      Variational.action (volume.restrict U) (lagrangian J) A +
        ∫ x, χ x * coefficient (exteriorDerivative J x) :=
  action_gaugeShift hU hA hχ hK hsub hJ hfin

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiffOn ℝ 1 A U) {J : Form Spacetime 3} (hJ : ContDiff ℝ 1 J)
    (hfin : Integrable (Variational.density (lagrangian J) A) (volume.restrict U)) :
    (∀ χ : Spacetime → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      Variational.action (volume.restrict U) (lagrangian J) (gaugeShift A χ) =
        Variational.action (volume.restrict U) (lagrangian J) A) ↔
      ∀ x ∈ U, exteriorDerivative J x = 0 :=
  action_gaugeShift_eq_iff hU hA hJ hfin

end ProjectAinos.Electrodynamics.SourcedAction

open MeasureTheory
open scoped Manifold ContDiff
namespace ProjectAinos.Electrodynamics.SourcedAction

open Module

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm

open SpecialRelativity VacuumAction ContinuousLinearMap

example (a : OneForm) : a = ofCovectors ![oneCovector a] :=
  oneForm_eq_ofCovectors a

example (a : OneForm) (v : Spacetime) :
    coefficient (wedgeFiber a (interior v (coordinateForm id))) = oneCovector a v :=
  coefficient_wedge_interior_volume a v

example (k : Spacetime → Spacetime) (x : Spacetime)
    (z : Variational.JetFiber Spacetime OneForm) :
    lagrangian (matterCurrentForm k) x z = VacuumAction.lagrangian x z + oneCovector z.1 (k x) :=
  lagrangian_matterCurrentForm k x z

example (k : Spacetime → Spacetime) (A : Potential) (x : Spacetime) :
    Variational.density (lagrangian (matterCurrentForm k)) A x =
      Variational.density VacuumAction.lagrangian A x + oneCovector (A x) (k x) :=
  density_matterCurrentForm k A x

example (j : Curved.CurrentVector (M := Spacetime)) (x : Spacetime) :
    Curved.currentForm (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4) j x =
      interior (j x) (coordinateForm id) :=
  currentForm_minkowski j x

example (j : Spacetime → Spacetime) (x : Spacetime) :
    matterCurrentForm (fun y => -j y) x = interior (j x) (coordinateForm id) :=
  matterCurrentForm_neg j x

example (j : Curved.CurrentVector (M := Spacetime))
    (x : Spacetime) :
    matterCurrentForm (fun y => -(j y : Spacetime)) x =
      Curved.currentForm (minkowskiMetric .timeNegative 3) (OrientedAtlas.standard 4) j x :=
  matterCurrentForm_eq_currentForm j x

example {n : ℕ∞ω} {k : Spacetime → Spacetime} (hk : ContDiff ℝ n k) :
    ContDiff ℝ n (matterCurrentForm k) :=
  contDiff_matterCurrentForm hk

example {U : Set Spacetime} {A : Potential}
    {k : Spacetime → Spacetime} (hU : IsOpen U) (hA : ContDiff ℝ 2 A) (hk : ContDiff ℝ 2 k)
    (hfin : Integrable (Variational.density (lagrangian (matterCurrentForm k)) A)
      (volume.restrict U)) :
    Variational.Stationary volume U (lagrangian (matterCurrentForm k)) A ↔
      ∀ x ∈ U, exteriorDerivative (fun y => -star (fieldTensor A y)) x = matterCurrentForm k x :=
  stationary_iff_matterCurrent hU hA hk hfin

end ProjectAinos.Electrodynamics.SourcedAction

open MeasureTheory
open scoped ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (μ a b : Fin 4) :
    partialAt (fun y => component (G y) a b) μ x =
      fderiv ℝ G x (Pi.single μ 1) ![Pi.single a 1, Pi.single b 1] :=
  partialAt_component hG μ a b

example {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (i : Fin 3) (μ : Fin 4) :
    partialAt (electricField G i) μ x =
      fderiv ℝ G x (Pi.single μ 1) ![Pi.single i.succ 1, Pi.single 0 1] :=
  partialAt_electricField hG i μ

example {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x)
    (μ : Fin 4) :
    partialAt (magneticField G 0) μ x =
        fderiv ℝ G x (Pi.single μ 1) ![Pi.single 2 1, Pi.single 3 1] ∧
      partialAt (magneticField G 1) μ x =
        fderiv ℝ G x (Pi.single μ 1) ![Pi.single 3 1, Pi.single 1 1] ∧
      partialAt (magneticField G 2) μ x =
        fderiv ℝ G x (Pi.single μ 1) ![Pi.single 1 1, Pi.single 2 1] :=
  partialAt_magneticField hG μ

example (G : Field) (x u v w : Spacetime) :
    exteriorDerivative G x ![u, v, w] =
      fderiv ℝ G x u ![v, w] - fderiv ℝ G x v ![u, w] + fderiv ℝ G x w ![u, v] :=
  exteriorDerivative_three G x u v w

example {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x) :
    exteriorDerivative G x ![Pi.single 1 1, Pi.single 2 1, Pi.single 3 1] =
      divergence3 (magneticField G) x :=
  exteriorDerivative_spatial hG

example {G : Field} {x : Spacetime} (hG : DifferentiableAt ℝ G x) :
    exteriorDerivative G x ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1] =
        partialAt (magneticField G 0) 0 x + curl (electricField G) x 0 ∧
      exteriorDerivative G x ![Pi.single 0 1, Pi.single 3 1, Pi.single 1 1] =
        partialAt (magneticField G 1) 0 x + curl (electricField G) x 1 ∧
      exteriorDerivative G x ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] =
        partialAt (magneticField G 2) 0 x + curl (electricField G) x 2 :=
  exteriorDerivative_temporal hG

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    (h : exteriorDerivative F x = 0) :
    divergence3 (magneticField F) x = 0 ∧
      ∀ i, partialAt (magneticField F i) 0 x + curl (electricField F) x i = 0 :=
  homogeneous_of_closed hF h

example {A : Potential} {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : Spacetime} (hx : x ∈ U) :
    divergence3 (magneticField (fieldTensor A)) x = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor A) i) 0 x +
        curl (electricField (fieldTensor A)) x i = 0 :=
  homogeneous_fieldTensor hU hA hx

example (G : TwoForm) : electricVector (-G) = -electricVector G :=
  electricVector_neg G

example (G : TwoForm) : magneticVector (-G) = -magneticVector G :=
  magneticVector_neg G

example (G : TwoForm) : electricVector (star G) = -magneticVector G :=
  electricVector_star G

example (G : TwoForm) : magneticVector (star G) = electricVector G :=
  magneticVector_star G

example (G : TwoForm) : electricVector (-star G) = magneticVector G :=
  electricVector_excitation G

example (G : TwoForm) :
    magneticVector (-star G) = -electricVector G :=
  magneticVector_excitation G

example (f : Spacetime → ℝ) (μ : Fin 4) (x : Spacetime) :
    partialAt (fun y => -f y) μ x = -partialAt f μ x :=
  partialAt_neg f μ x

example (k : Spacetime → Spacetime) (x : Spacetime) :
    SourcedAction.matterCurrentForm k x ![Pi.single 1 1, Pi.single 2 1, Pi.single 3 1] =
      -k x 0 :=
  matterCurrentForm_spatial k x

example (k : Spacetime → Spacetime) (x : Spacetime) :
    SourcedAction.matterCurrentForm k x ![Pi.single 0 1, Pi.single 2 1, Pi.single 3 1] = k x 1 ∧
      SourcedAction.matterCurrentForm k x ![Pi.single 0 1, Pi.single 3 1, Pi.single 1 1] =
        k x 2 ∧
      SourcedAction.matterCurrentForm k x ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1] =
        k x 3 :=
  matterCurrentForm_temporal k x

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x)
    {k : Spacetime → Spacetime}
    (h : exteriorDerivative (fun y => -star (F y)) x = SourcedAction.matterCurrentForm k x) :
    divergence3 (electricField F) x = k x 0 ∧
      ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ :=
  inhomogeneous_of_excitation hF h

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiff ℝ 2 A) {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    (hfin : Integrable (Variational.density
      (SourcedAction.lagrangian (SourcedAction.matterCurrentForm k)) A) (volume.restrict U))
    (hs : Variational.Stationary volume U
      (SourcedAction.lagrangian (SourcedAction.matterCurrentForm k)) A)
    {x : Spacetime} (hx : x ∈ U) :
    (divergence3 (magneticField (fieldTensor A)) x = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor A) i) 0 x +
        curl (electricField (fieldTensor A)) x i = 0) ∧
    (divergence3 (electricField (fieldTensor A)) x = k x 0 ∧
      ∀ i, curl (magneticField (fieldTensor A)) x i -
        partialAt (electricField (fieldTensor A) i) 0 x = k x i.succ) :=
  maxwell_of_stationary hU hA hk hfin hs hx

end ProjectAinos.Electrodynamics

open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

open SourcedAction VacuumAction ContinuousLinearMap

example (v : Spacetime) :
    matterCurrentMap v = -interior v (coordinateForm id) :=
  matterCurrentMap_apply v

example (k : Spacetime → Spacetime) :
    matterCurrentForm k = fun y => matterCurrentMap (k y) :=
  matterCurrentForm_eq_comp k

example (v : Spacetime) (i : Fin 4) :
    coordinateForm (n := 4) id
        (Matrix.vecCons v (Fin.removeNth i (Pi.basisFun ℝ (Fin 4) : Fin 4 → Spacetime))) =
      (-1 : ℝ) ^ (i : ℕ) * v i :=
  volume_cons_removeNth v i

example {k : Spacetime → Spacetime}
    {x : Spacetime} (hk : DifferentiableAt ℝ k x) :
    coefficient (exteriorDerivative (matterCurrentForm k) x) = -divergence4 k x :=
  coefficient_exteriorDerivative_matterCurrentForm hk

example {k : Spacetime → Spacetime}
    {x : Spacetime} (hk : DifferentiableAt ℝ k x) :
    exteriorDerivative (matterCurrentForm k) x = 0 ↔ divergence4 k x = 0 :=
  exteriorDerivative_matterCurrentForm_eq_zero_iff hk

example {U : Set Spacetime} (hU : IsOpen U) {A : Potential}
    (hA : ContDiff ℝ 3 A) {k : Spacetime → Spacetime} (hk : ContDiff ℝ 2 k)
    (hfin : Integrable (Variational.density (lagrangian (matterCurrentForm k)) A)
      (volume.restrict U))
    (hs : Variational.Stationary volume U (lagrangian (matterCurrentForm k)) A)
    {x : Spacetime} (hx : x ∈ U) : divergence4 k x = 0 :=
  divergence4_eq_zero_of_stationary hU hA hk hfin hs hx

example (k : Spacetime → Spacetime) (a b : Spacetime) :
    faceFlux k a b 0 = charge k a b (b 0) - charge k a b (a 0) :=
  faceFlux_zero k a b

example {k : Spacetime → Spacetime} (hk : ContDiff ℝ 1 k) {a b : Spacetime}
    (hle : a ≤ b) (hdiv : ∀ x ∈ Icc a b, divergence4 k x = 0) :
    charge k a b (b 0) - charge k a b (a 0) = -∑ i : Fin 3, faceFlux k a b i.succ :=
  charge_balance hk hle hdiv

end ProjectAinos.Electrodynamics

open MeasureTheory Set
open scoped ContDiff
namespace ProjectAinos.Electrodynamics.SourcedAction.Examples

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

open VacuumAction ContinuousLinearMap

example (x : Spacetime) :
    HasFDerivAt potential
      ((ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).smulRight
        (x 0 • oneCovector.symm (ContinuousLinearMap.proj 1))) x :=
  hasFDerivAt_potential x

example : ContDiff ℝ ∞ potential :=
  contDiff_potential

example (x : Spacetime) :
    fieldTensor potential x = x 0 • coordinateForm ![0, 1] :=
  fieldTensor_potential x

example (x : Spacetime) :
    -star (fieldTensor potential x) = x 0 • coordinateForm ![2, 3] :=
  excitation_potential x

example (x : Spacetime) :
    matterCurrentForm current x = coordinateForm ![0, 2, 3] :=
  matterCurrentForm_current x

example (x : Spacetime) :
    exteriorDerivative (fun y => -star (fieldTensor potential y)) x =
      matterCurrentForm current x :=
  exteriorDerivative_excitation x

example :
    Continuous (Variational.density (lagrangian (matterCurrentForm current)) potential) :=
  continuous_density

example {U : Set Spacetime} (hb : Bornology.IsBounded U) :
    Integrable (Variational.density (lagrangian (matterCurrentForm current)) potential)
      (volume.restrict U) :=
  integrable_density hb

example {U : Set Spacetime} (hU : IsOpen U) (hb : Bornology.IsBounded U) :
    Variational.Stationary volume U (lagrangian (matterCurrentForm current)) potential :=
  stationary_example hU hb

example {x : Spacetime} (hx : x ∈ Metric.ball 0 1) :
    (divergence3 (magneticField (fieldTensor potential)) x = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor potential) i) 0 x +
        curl (electricField (fieldTensor potential)) x i = 0) ∧
    (divergence3 (electricField (fieldTensor potential)) x = 0 ∧
      ∀ i, curl (magneticField (fieldTensor potential)) x i -
        partialAt (electricField (fieldTensor potential) i) 0 x =
          (Pi.single 1 1 : Spacetime) i.succ) :=
  maxwell_example hx

end ProjectAinos.Electrodynamics.SourcedAction.Examples
