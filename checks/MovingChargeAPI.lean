/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.SourceCovariance
import ProjectAinos.Electrodynamics.MovingCharge
import ProjectAinos.Electrodynamics.MovingSource

/-! Public consumers of the field of a moving charge (Landau–Lifshitz §38): the transport of the
current and of the sourced field equation by proper Lorentz maps, the excitation from the 3+1
equations, static solutions and their boost with the moving current, the point charge with the
field (38.8), and the boosted Newton potential of a smooth charge.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section SourceCovariance

open scoped Topology

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (L : Spacetime →L[ℝ] Spacetime) :
    (coordinateForm (n := 4) id).compContinuousLinearMap L =
      LinearMap.det (L : Spacetime →ₗ[ℝ] Spacetime) • coordinateForm (n := 4) id :=
  coordinateVolume_comp L

example (L : LorentzGroup 3) (x : Spacetime) :
    fderiv ℝ L.val x = (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap :=
  fderiv_lorentz L x

example (L : properLorentzGroup 3) :
    LinearMap.det ((LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap :
      Spacetime →ₗ[ℝ] Spacetime) = 1 :=
  det_properLorentz L

example (L : properLorentzGroup 3) (k : Spacetime → Spacetime) :
    pullback L.val.val (SourcedAction.matterCurrentForm k) =
      SourcedAction.matterCurrentForm (fun y => L.val.val.symm (k (L.val.val y))) :=
  matterCurrentForm_lorentz L k

example (F : Field) :
    (fun y => star (F y)) = hodgeForm .timeNegative .standard (by decide) F :=
  star_eq_hodgeForm F

example (L : properLorentzGroup 3) (F : Field) :
    (fun y => -star (pullback L.val.val F y)) =
      pullback L.val.val (fun y => -star (F y)) :=
  neg_star_pullback L F

example (L : properLorentzGroup 3) {F : Field} {J : Form Spacetime 3} {U : Set Spacetime}
    (hF : ∀ x ∈ U, DifferentiableAt ℝ F x)
    (h : ∀ x ∈ U, exteriorDerivative (fun y => -star (F y)) x = J x) :
    ∀ x ∈ L.val.val ⁻¹' U,
      exteriorDerivative (fun y => -star (pullback L.val.val F y)) x = pullback L.val.val J x :=
  excitation_lorentz L hF h

example {A : Potential} {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    {x : Spacetime} (hx : x ∈ U) :
    DifferentiableAt ℝ (fieldTensor A) x :=
  differentiableAt_fieldTensor hU hA hx

example (L : LorentzGroup 3) {A : Potential} {U : Set Spacetime} (hA : ContDiffOn ℝ 2 A U) :
    ContDiffOn ℝ 2 (pullback L.val A) (L.val ⁻¹' U) :=
  contDiffOn_pullback_lorentz L hA

example (L : properLorentzGroup 3) {A : Potential} {k : Spacetime → Spacetime} {U : Set Spacetime}
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (h : ∀ x ∈ U, exteriorDerivative (fun y => -star (fieldTensor A y)) x =
      SourcedAction.matterCurrentForm k x) :
    ∀ x ∈ L.val.val ⁻¹' U,
      exteriorDerivative (fun y => -star (fieldTensor (pullback L.val.val A) y)) x =
        SourcedAction.matterCurrentForm (fun y => L.val.val.symm (k (L.val.val y))) x :=
  excitation_pullback L hU hA h

example (μ : Fin 4) :
    ℝ :=
  raiseSign μ

example :
    TwoForm →L[ℝ] (Fin 4 → Fin 4 → ℝ) :=
  raisedComponents

example (F : TwoForm) (μ ν : Fin 4) :
    raisedComponents F μ ν = raiseSign μ * raiseSign ν * component F μ ν :=
  raisedComponents_apply F μ ν

example (F : TwoForm) :
    -star F = bivectorVolume (raisedComponents F) :=
  neg_star_eq_bivectorVolume F

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x) :
    exteriorDerivative (fun y => -star (F y)) x =
      interior (fun ν => ∑ μ : Fin 4, raisedComponents (fderiv ℝ F x (Pi.single μ 1)) μ ν)
        (coordinateForm id) :=
  exteriorDerivative_neg_star hF

example {F : Field} {x : Spacetime} (hF : DifferentiableAt ℝ F x) {k : Spacetime → Spacetime}
    (hdiv : divergence3 (electricField F) x = k x 0)
    (hcurl : ∀ i, curl (magneticField F) x i - partialAt (electricField F i) 0 x = k x i.succ) :
    exteriorDerivative (fun y => -star (F y)) x = SourcedAction.matterCurrentForm k x :=
  excitation_of_inhomogeneous hF hdiv hcurl

end ProjectAinos.Electrodynamics

end SourceCovariance

section MovingCharge

open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.MovingCharge

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (f : Space 3 → ℝ) (i : Fin 3) (p : Space 3) :
    ℝ :=
  spatialPartial f i p

example (f : Space 3 → ℝ) (p : Space 3) :
    ℝ :=
  spaceLaplacian f p

example (φ : Space 3 → ℝ) :
    Potential :=
  staticScalar φ

example (φ : Space 3 → ℝ) (p : Space 3) :
    Fin 3 → ℝ :=
  staticElectric φ p

example (ρ : Space 3 → ℝ) :
    Spacetime → Spacetime :=
  staticCurrent ρ

example :
    space (Pi.single 0 1 : Spacetime) = 0 :=
  space_single_zero

example (i : Fin 3) :
    space (Pi.single i.succ 1 : Spacetime) = EuclideanSpace.single i 1 :=
  space_single_succ i

example {φ : Space 3 → ℝ} {x : Spacetime} (hφ : DifferentiableAt ℝ φ (space x)) :
    HasFDerivAt (staticScalar φ)
      ((-(fderiv ℝ φ (space x)).comp (space : Spacetime →L[ℝ] Space 3)).smulRight
        (oneCovector.symm (ContinuousLinearMap.proj 0))) x :=
  hasFDerivAt_staticScalar hφ

example {φ : Space 3 → ℝ} {x : Spacetime} (hφ : DifferentiableAt ℝ φ (space x)) (v w : Spacetime) :
    fieldTensor (staticScalar φ) x ![v, w] =
      fderiv ℝ φ (space x) (space w) * v 0 - fderiv ℝ φ (space x) (space v) * w 0 :=
  fieldTensor_staticScalar_apply hφ v w

example {φ : Space 3 → ℝ} {x : Spacetime} (hφ : DifferentiableAt ℝ φ (space x)) :
    electricVector (fieldTensor (staticScalar φ) x) = staticElectric φ (space x) :=
  electricVector_staticScalar hφ

example {φ : Space 3 → ℝ} {x : Spacetime} (hφ : DifferentiableAt ℝ φ (space x)) :
    magneticVector (fieldTensor (staticScalar φ) x) = 0 :=
  magneticVector_staticScalar hφ

example {g : Space 3 → ℝ} {x : Spacetime} (hg : DifferentiableAt ℝ g (space x)) :
    HasFDerivAt (fun y => g (space y))
      ((fderiv ℝ g (space x)).comp (space : Spacetime →L[ℝ] Space 3)) x :=
  hasFDerivAt_comp_space hg

example {f : Space 3 → ℝ} {D : Set (Space 3)} (hD : IsOpen D) (hf : ContDiffOn ℝ 2 f D)
    {p : Space 3} (hp : p ∈ D) (i : Fin 3) :
    DifferentiableAt ℝ (spatialPartial f i) p :=
  differentiableAt_spatialPartial hD hf hp i

example {φ : Space 3 → ℝ} {D : Set (Space 3)} (hφ : ContDiffOn ℝ 2 φ D) :
    ContDiffOn ℝ 2 (staticScalar φ) (space ⁻¹' D) :=
  contDiffOn_staticScalar hφ

namespace StaticSolution

variable (S : StaticSolution)

example :
    Set Spacetime :=
  spacetimeDomain S

example :
    IsOpen S.spacetimeDomain :=
  isOpen_spacetimeDomain S

example {p : Space 3} (hp : p ∈ S.domain) :
    DifferentiableAt ℝ S.potential p :=
  differentiableAt_potential S hp

example {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3) :
    electricField (fieldTensor (staticScalar S.potential)) i =ᶠ[𝓝 x]
      fun y => -spatialPartial S.potential i (space y) :=
  electricField_eventually S hx i

example {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3) :
    magneticField (fieldTensor (staticScalar S.potential)) i =ᶠ[𝓝 x] fun _ => 0 :=
  magneticField_eventually S hx i

example {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3) (μ : Fin 4) :
    partialAt (electricField (fieldTensor (staticScalar S.potential)) i) μ x =
      -fderiv ℝ (spatialPartial S.potential i) (space x) (space (Pi.single μ 1)) :=
  partialAt_electricField S hx i μ

example {x : Spacetime} (hx : space x ∈ S.domain) (i : Fin 3) (μ : Fin 4) :
    partialAt (magneticField (fieldTensor (staticScalar S.potential)) i) μ x = 0 :=
  partialAt_magneticField S hx i μ

example {x : Spacetime} (hx : space x ∈ S.domain) :
    exteriorDerivative (fun y => -star (fieldTensor (staticScalar S.potential) y)) x =
      SourcedAction.matterCurrentForm (staticCurrent S.density) x :=
  excitation S hx

end StaticSolution

section Moving

variable (V : ℝ) (hV : |V| < 1)

example :
    properLorentzGroup 3 :=
  restFrame V hV

example (y : Spacetime) :
    Space 3 :=
  comovingPosition V hV y

example (y : Spacetime) :
    comovingPosition V hV y 0 = (axisVelocity V hV).gamma * (y 1 - V * y 0) :=
  comovingPosition_zero V hV y

example (y : Spacetime) :
    comovingPosition V hV y 1 = y 2 :=
  comovingPosition_one V hV y

example (y : Spacetime) :
    comovingPosition V hV y 2 = y 3 :=
  comovingPosition_two V hV y

example (φ : Space 3 → ℝ) :
    Potential :=
  movingScalar V hV φ

example (φ : Space 3 → ℝ) (y v : Spacetime) :
    oneCovector (movingScalar V hV φ y) v =
      -((axisVelocity V hV).gamma * φ (comovingPosition V hV y)) * (v 0 - V * v 1) :=
  movingScalar_apply V hV φ y v

example (ρ : Space 3 → ℝ) (y : Spacetime) :
    Spacetime :=
  movingCurrent V hV ρ y

example :
    (boost (axisVelocity V hV)).val.symm (Pi.single 0 1) =
      ![(axisVelocity V hV).gamma, (axisVelocity V hV).gamma * V, 0, 0] :=
  boost_symm_single_zero V hV

example (ρ : Space 3 → ℝ) :
    (fun y => (restFrame V hV).val.val.symm (staticCurrent ρ ((restFrame V hV).val.val y))) =
      movingCurrent V hV ρ :=
  transport_staticCurrent V hV ρ

example (S : StaticSolution) {y : Spacetime} (hy : comovingPosition V hV y ∈ S.domain) :
    exteriorDerivative (fun z => -star (fieldTensor (movingScalar V hV S.potential) z)) y =
      SourcedAction.matterCurrentForm (movingCurrent V hV S.density) y :=
  excitation_movingScalar V hV S hy

example (S : StaticSolution) :
    ContDiffOn ℝ 2 (movingScalar V hV S.potential)
      {y | comovingPosition V hV y ∈ S.domain} :=
  contDiffOn_movingScalar V hV S

example (S : StaticSolution) :
    IsOpen {y | comovingPosition V hV y ∈ S.domain} :=
  isOpen_comovingDomain V hV S

example (S : StaticSolution) {y : Spacetime} (hy : comovingPosition V hV y ∈ S.domain) :
    (divergence3 (magneticField (fieldTensor (movingScalar V hV S.potential))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (movingScalar V hV S.potential)) i) 0 y +
        curl (electricField (fieldTensor (movingScalar V hV S.potential))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (movingScalar V hV S.potential))) y =
      (axisVelocity V hV).gamma * S.density (comovingPosition V hV y) ∧
    ∀ i, curl (magneticField (fieldTensor (movingScalar V hV S.potential))) y i -
        partialAt (electricField (fieldTensor (movingScalar V hV S.potential)) i) 0 y =
      (axisVelocity V hV).gamma * S.density (comovingPosition V hV y) * ![V, 0, 0] i :=
  maxwell_movingScalar V hV S hy

example {φ : Space 3 → ℝ} {y : Spacetime} (hφ : DifferentiableAt ℝ φ (comovingPosition V hV y)) :
    fieldTensor (movingScalar V hV φ) y =
      lorentzPullback (boost (axisVelocity V hV))
        (fieldTensor (staticScalar φ) ((boost (axisVelocity V hV)).val y)) :=
  fieldTensor_movingScalar V hV hφ

example {φ : Space 3 → ℝ} {y : Spacetime} (hφ : DifferentiableAt ℝ φ (comovingPosition V hV y)) :
    electricVector (fieldTensor (movingScalar V hV φ) y) =
      ![staticElectric φ (comovingPosition V hV y) 0,
        (axisVelocity V hV).gamma * staticElectric φ (comovingPosition V hV y) 1,
        (axisVelocity V hV).gamma * staticElectric φ (comovingPosition V hV y) 2] :=
  electricField_movingScalar V hV hφ

example {φ : Space 3 → ℝ} {y : Spacetime} (hφ : DifferentiableAt ℝ φ (comovingPosition V hV y)) :
    magneticVector (fieldTensor (movingScalar V hV φ) y) =
      crossProduct ![V, 0, 0] (electricVector (fieldTensor (movingScalar V hV φ) y)) :=
  magneticField_movingScalar V hV hφ

end Moving

example (q : ℝ) (p : Space 3) :
    ℝ :=
  coulombPotential q p

example {p : Space 3} (hp : p ≠ 0) :
    HasFDerivAt (fun r : Space 3 => ‖r‖) (‖p‖⁻¹ • innerSL ℝ p) p :=
  hasFDerivAt_norm_space hp

example (q : ℝ) {p : Space 3} (hp : p ≠ 0) :
    HasFDerivAt (coulombPotential q)
      ((-(q / (4 * Real.pi)) * (‖p‖ ^ 3)⁻¹) • innerSL ℝ p) p :=
  hasFDerivAt_coulombPotential q hp

example (q : ℝ) {p : Space 3} (hp : p ≠ 0) (i : Fin 3) :
    spatialPartial (coulombPotential q) i p = -(q / (4 * Real.pi)) * (p i * (‖p‖ ^ 3)⁻¹) :=
  spatialPartial_coulombPotential q hp i

example (q : ℝ) {p : Space 3} (hp : p ≠ 0) :
    spaceLaplacian (coulombPotential q) p = 0 :=
  spaceLaplacian_coulombPotential q hp

example (q : ℝ) :
    StaticSolution :=
  coulombSolution q

example (ρ₀ : ℝ) (p : Space 3) :
    ℝ :=
  uniformPotential ρ₀ p

example (ρ₀ : ℝ) (i : Fin 3) :
    spatialPartial (uniformPotential ρ₀) i = fun p => -(ρ₀ / 3) * p i :=
  spatialPartial_uniformPotential ρ₀ i

example (ρ₀ : ℝ) (p : Space 3) :
    spaceLaplacian (uniformPotential ρ₀) p = -ρ₀ :=
  spaceLaplacian_uniformPotential ρ₀ p

example (ρ₀ : ℝ) :
    StaticSolution :=
  uniformSolution ρ₀

section MovingPointCharge

variable (V : ℝ) (hV : |V| < 1)

example (q : ℝ) :
    Potential :=
  movingCoulomb V hV q

example (y : Spacetime) :
    Space 3 :=
  presentSeparation V hV y

example (y : Spacetime) :
    presentSeparation V hV y 0 = y 1 - y 0 * V :=
  presentSeparation_zero V hV y

example (y : Spacetime) :
    presentSeparation V hV y 1 = y 2 :=
  presentSeparation_one V hV y

example (y : Spacetime) :
    presentSeparation V hV y 2 = y 3 :=
  presentSeparation_two V hV y

example (y : Spacetime) :
    comovingPosition V hV y 0 = (axisVelocity V hV).gamma * presentSeparation V hV y 0 ∧
      comovingPosition V hV y 1 = presentSeparation V hV y 1 ∧
      comovingPosition V hV y 2 = presentSeparation V hV y 2 :=
  comovingPosition_presentSeparation V hV y

example {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    comovingPosition V hV y ≠ 0 :=
  comovingPosition_ne_zero V hV hy

example (y : Spacetime) :
    SourcedAction.matterCurrentForm (fun _ => 0) y = 0 :=
  matterCurrentForm_zero y

example (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    exteriorDerivative (fun z => -star (fieldTensor (movingCoulomb V hV q) z)) y = 0 :=
  movingCoulomb_vacuum V hV q hy

example (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    (divergence3 (magneticField (fieldTensor (movingCoulomb V hV q))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (movingCoulomb V hV q)) i) 0 y +
        curl (electricField (fieldTensor (movingCoulomb V hV q))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (movingCoulomb V hV q))) y = 0 ∧
    ∀ i, curl (magneticField (fieldTensor (movingCoulomb V hV q))) y i -
        partialAt (electricField (fieldTensor (movingCoulomb V hV q)) i) 0 y = 0 :=
  maxwell_movingCoulomb V hV q hy

example {s : ℝ} (hs : 0 < s) :
    s ^ (3 / 2 : ℝ) = s * √s :=
  rpow_three_halves hs

example (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) (i : Fin 3) :
    electricVector (fieldTensor (movingCoulomb V hV q) y) i =
      q * (1 - V ^ 2) * presentSeparation V hV y i /
        (4 * Real.pi * ‖presentSeparation V hV y‖ ^ 3 *
          (1 - V ^ 2 * Real.sin (InnerProductGeometry.angle (presentSeparation V hV y)
            (EuclideanSpace.single 0 1)) ^ 2) ^ (3 / 2 : ℝ)) :=
  electricField_movingCoulomb V hV q hy i

example (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    magneticVector (fieldTensor (movingCoulomb V hV q) y) =
      crossProduct ![V, 0, 0] (electricVector (fieldTensor (movingCoulomb V hV q) y)) :=
  magneticField_movingCoulomb V hV q hy

example (q : ℝ) {y : Spacetime} (hy : presentSeparation V hV y ≠ 0) :
    exteriorDerivative (fun z => -star (fieldTensor (movingCoulomb V hV q) z)) y = 0 ∧
    (∀ i, electricVector (fieldTensor (movingCoulomb V hV q) y) i =
      q * (1 - V ^ 2) * presentSeparation V hV y i /
        (4 * Real.pi * ‖presentSeparation V hV y‖ ^ 3 *
          (1 - V ^ 2 * Real.sin (InnerProductGeometry.angle (presentSeparation V hV y)
            (EuclideanSpace.single 0 1)) ^ 2) ^ (3 / 2 : ℝ))) ∧
    magneticVector (fieldTensor (movingCoulomb V hV q) y) =
      crossProduct ![V, 0, 0] (electricVector (fieldTensor (movingCoulomb V hV q) y)) :=
  movingCoulomb_field V hV q hy

end MovingPointCharge

end ProjectAinos.Electrodynamics.MovingCharge

end MovingCharge

section MovingSource

open Set

open scoped ContDiff

namespace ProjectAinos.Electrodynamics.MovingCharge

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Potential SpecialRelativity

example (f : Space 3 → ℝ) (p : Space 3) :
    spaceLaplacian f p = coordLaplacian f p :=
  spaceLaplacian_eq_coordLaplacian f p

example (ρ : Space 3 → ℝ) (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    StaticSolution :=
  newtonSolution ρ hcρ hρ

example (V : ℝ) (hV : |V| < 1) (ρ : Space 3 → ℝ) (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (y : Spacetime) :
    (divergence3 (magneticField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y = 0 ∧
      ∀ i, partialAt (magneticField (fieldTensor (movingScalar V hV (newtonPotential ρ))) i) 0 y +
        curl (electricField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y i = 0) ∧
    divergence3 (electricField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y =
      (axisVelocity V hV).gamma * ρ (comovingPosition V hV y) ∧
    ∀ i, curl (magneticField (fieldTensor (movingScalar V hV (newtonPotential ρ)))) y i -
        partialAt (electricField (fieldTensor (movingScalar V hV (newtonPotential ρ))) i) 0 y =
      (axisVelocity V hV).gamma * ρ (comovingPosition V hV y) * ![V, 0, 0] i :=
  maxwell_movingNewton V hV ρ hcρ hρ y

end ProjectAinos.Electrodynamics.MovingCharge

end MovingSource
