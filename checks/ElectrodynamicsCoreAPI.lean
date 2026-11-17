/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Components
import ProjectAinos.Electrodynamics.Examples

/-! Public consumers of the flat core of electrodynamics for a charge in a given field:
potentials and the field tensor, the components, the invariants and their covariance, the
action of a charge and the Lorentz force, the gauge change of the action and the uniform
examples.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open scoped ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (a : OneForm) (v : Spacetime) :
    oneCovector a v = a (fun _ => v) :=
  oneCovector_apply a v

example (F : TwoForm) (v w : Spacetime) :
    oneCovector (F.curryLeft v) w = F ![v, w] :=
  oneCovector_curryLeft F v w

example (A : Potential) (x v w : Spacetime) :
    fieldTensor A x ![v, w] =
      oneCovector (fderiv ℝ A x v) w - oneCovector (fderiv ℝ A x w) v :=
  fieldTensor_apply A x v w

example {n : ℕ∞ω} {χ : Spacetime → ℝ} (hχ : ContDiff ℝ n χ) :
    ContDiff ℝ n (scalarForm χ) :=
  scalarForm_contDiff hχ

example {n : ℕ∞ω} {χ : Spacetime → ℝ} {x : Spacetime}
    (hχ : ContDiffAt ℝ n χ x) : ContDiffAt ℝ n (scalarForm χ) x :=
  scalarForm_contDiffAt hχ

example (χ : Spacetime → ℝ) (x : Spacetime) :
    oneCovector (exteriorDerivative (scalarForm χ) x) = fderiv ℝ χ x :=
  scalar_derivative χ x

example (A : Potential) (χ : Spacetime → ℝ)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    fieldTensor (gaugeShift A χ) = fieldTensor A :=
  fieldTensor_gauge A χ hA hχ

example (A : Potential) (χ : Spacetime → ℝ)
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U)
    (hχ : ContDiffOn ℝ 2 χ U) : Set.EqOn (fieldTensor (gaugeShift A χ)) (fieldTensor A) U :=
  fieldTensor_gauge_on A χ hU hA hχ

example (A : Potential) {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) : Set.EqOn (exteriorDerivative (fieldTensor A)) 0 U :=
  bianchi_on A hU hA

example (f : Spacetime → Spacetime) (A : Potential)
    (hf : ContDiff ℝ 2 f) (hA : Differentiable ℝ A) :
    fieldTensor (pullback f A) = pullback f (fieldTensor A) :=
  fieldTensor_pullback f A hf hA

example (f : Spacetime → Spacetime) (A : Potential)
    {U : Set Spacetime} (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x)
    (hA : ∀ x ∈ U, DifferentiableAt ℝ A (f x)) :
    Set.EqOn (fieldTensor (pullback f A)) (pullback f (fieldTensor A)) U :=
  fieldTensor_pullback_on f A hf hA

example (u : Observer 3) (F : TwoForm) :
    reconstructTwoForm .timeNegative .standard u (-(electric u F)) (magnetic u F) = F :=
  observer_reconstruction u F

example (u : Observer 3) (F : TwoForm) :
    oneCovector (electric u F) u.velocity = 0 :=
  electric_annihilates_observer u F

example (u : Observer 3) (F : TwoForm) :
    oneCovector (magnetic u F) u.velocity = 0 :=
  magnetic_annihilates_observer u F

end ProjectAinos.Electrodynamics

open scoped ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (φ : Spacetime → ℝ) (a : Spacetime → Fin 3 → ℝ)
    (x v : Spacetime) :
    oneCovector (potentialOf φ a x) v = -φ x * v 0 + ∑ i : Fin 3, a x i * v i.succ :=
  potentialOf_apply φ a x v

example {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (ν : Fin 4) (v : Spacetime) :
    fderiv ℝ (potentialComponent A ν) x v = oneCovector (fderiv ℝ A x v) (Pi.single ν 1) :=
  fderiv_potentialComponent hA ν v

example {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) (μ ν : Fin 4) :
    component (fieldTensor A x) μ ν =
      fderiv ℝ (potentialComponent A ν) x (Pi.single μ 1) -
        fderiv ℝ (potentialComponent A μ) x (Pi.single ν 1) :=
  fieldTensor_component hA μ ν

example (A : Potential) {U : Set Spacetime} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : Spacetime} (hx : x ∈ U) (u v w : Spacetime) :
    fderiv ℝ (fieldTensor A) x u ![v, w] + fderiv ℝ (fieldTensor A) x v ![w, u] +
      fderiv ℝ (fieldTensor A) x w ![u, v] = 0 :=
  bianchi_components A hU hA hx u v w

example (L : LorentzGroup 3) (A : Potential) (hA : Differentiable ℝ A) :
    fieldTensor (pullback L.val A) = pullback L.val (fieldTensor A) :=
  fieldTensor_lorentz L A hA

example (P : PoincareGroup 3) (A : Potential) (hA : Differentiable ℝ A) :
    fieldTensor (pullback P.val A) = pullback P.val (fieldTensor A) :=
  fieldTensor_poincare P A hA

end ProjectAinos.Electrodynamics

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (a b : OneForm) :
    covectorPairing a b = minkowskiForm .timeNegative 3
      (sharp .timeNegative (oneCovector a)) (sharp .timeNegative (oneCovector b)) :=
  covectorPairing_eq_metric a b

example (u : Observer 3) (a : OneForm)
    (ha : oneCovector a u.velocity = 0) : 0 ≤ covectorPairing a a :=
  covectorPairing_nonneg u a ha

example (u : Observer 3) (F : TwoForm) (w : Spacetime) :
    oneCovector (electric u F) w = -F ![u.velocity, w] :=
  electric_apply u F w

example (u : Observer 3) (F : TwoForm) (w : Spacetime) :
    oneCovector (magnetic u F) w = star F ![u.velocity, w] :=
  magnetic_apply u F w

example (F G : TwoForm) :
    tensorContraction F G = 2 *
      (-component F 0 1 * component G 0 1 - component F 0 2 * component G 0 2 -
        component F 0 3 * component G 0 3 + component F 1 2 * component G 1 2 +
        component F 1 3 * component G 1 3 + component F 2 3 * component G 2 3) :=
  tensorContraction_coordinates F G

example (u : Observer 3) (F : TwoForm) :
    scalarInvariant F = covectorPairing (magnetic u F) (magnetic u F) -
      covectorPairing (electric u F) (electric u F) :=
  scalarInvariant_observer u F

example (u : Observer 3) (F : TwoForm) :
    pseudoscalarInvariant F = covectorPairing (electric u F) (magnetic u F) :=
  pseudoscalarInvariant_observer u F

example (F : TwoForm) :
    (1 / 4 : ℝ) * tensorContraction F (hodgeFiber .timeNegative .reversed (by decide) F) =
      -pseudoscalarInvariant F :=
  pseudoscalar_reverse_orientation F

end ProjectAinos.Electrodynamics

open Module exteriorPower
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (F G : TwoForm) :
    exteriorPairing F G = (1 / 2 : ℝ) * tensorContraction F G :=
  exteriorPairing_coordinates F G

example (L : LorentzGroup 3) (F G : TwoForm) :
    exteriorPairing (lorentzPullback L F) (lorentzPullback L G) = exteriorPairing F G :=
  exteriorPairing_lorentz L F G

example (L : LorentzGroup 3) (F : TwoForm) :
    scalarInvariant (lorentzPullback L F) = scalarInvariant F :=
  scalarInvariant_lorentz L F

example (L : properLorentzGroup 3) (F : TwoForm) :
    star (lorentzPullback L.val F) = lorentzPullback L.val (star F) :=
  star_properLorentz L F

example (L : properLorentzGroup 3) (F : TwoForm) :
    pseudoscalarInvariant (lorentzPullback L.val F) = pseudoscalarInvariant F :=
  pseudoscalarInvariant_properLorentz L F

example (F : TwoForm) :
    pseudoscalarInvariant F = -(1 / 2 : ℝ) *
      wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel]) (toExterior F)
        (toExterior F) :=
  pseudoscalarInvariant_wedge F

example (L : LorentzGroup 3) (F : TwoForm) :
    pseudoscalarInvariant (lorentzPullback L F) =
      L.val.toLinearMap.det * pseudoscalarInvariant F :=
  pseudoscalarInvariant_lorentz L F

example (L : LorentzGroup 3)
    (hL : L.val.toLinearMap.det = -1) (F : TwoForm) :
    pseudoscalarInvariant (lorentzPullback L F) = -pseudoscalarInvariant F :=
  pseudoscalarInvariant_orientationReversing L hL F

end ProjectAinos.Electrodynamics

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity Mechanics

example {A : Potential} {x : Spacetime}
    (hA : DifferentiableAt ℝ A x) :
    HasFDerivAt (potentialCovector A) (potentialDifferential A x) x :=
  hasFDerivAt_potentialCovector hA

example {U : Set Spacetime} (hU : IsOpen U) :
    IsOpen (admissibleJets U) :=
  isOpen_admissibleJets hU

example (m e : ℝ) {A : Potential}
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U) :
    ContDiffOn ℝ 2 (Function.uncurry (chargedLagrangian m e A)) (admissibleJets U) :=
  chargedLagrangian_contDiffOn m e hU hA

example (m e : ℝ) {A : Potential} {γ : ℝ → Spacetime} (a b : ℝ)
    (hγ : ContDiff ℝ 2 γ) (hA : ContinuousOn A (γ '' uIcc a b)) :
    chargedAction m e A γ a b = freeAction m γ a b +
      e * ∫ t in a..b, potentialCovector A (γ t) (deriv γ t) :=
  chargedAction_eq m e a b hγ hA

example (m e : ℝ) {A : Potential}
    {z : Spacetime × Spacetime} (hA : DifferentiableAt ℝ A z.1)
    (hv : Timelike z.2) (t : ℝ) :
    HasFDerivAt (chargedLagrangian m e A t)
      ((kineticMomentum m z.2).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime) +
        e • ((potentialCovector A z.1).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime) +
          ((potentialDifferential A z.1).comp
            (ContinuousLinearMap.fst ℝ Spacetime Spacetime)).flip z.2)) z :=
  hasFDerivAt_chargedLagrangian m e hA hv t

example (m e : ℝ) {A : Potential} {γ : ℝ → Spacetime} {t : ℝ}
    (hA : DifferentiableAt ℝ A (γ t)) (hv : Timelike (deriv γ t)) :
    force (chargedLagrangian m e A) γ t = e • (potentialDifferential A (γ t)).flip (deriv γ t) :=
  charged_force m e hA hv

example (m e : ℝ) {A : Potential} {γ : ℝ → Spacetime} {t : ℝ}
    (hA : DifferentiableAt ℝ A (γ t)) (hv : Timelike (deriv γ t)) :
    momentum (chargedLagrangian m e A) γ t =
      kineticMomentum m (deriv γ t) + e • potentialCovector A (γ t) :=
  charged_momentum m e hA hv

example (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (chargedLagrangian m e A) γ ↔
      ∀ t ∈ Ioo a b, eulerLagrange (chargedLagrangian m e A) γ t = 0 :=
  charged_stationary_iff m e hab hγ hU hA hγU hv

end ProjectAinos.Electrodynamics

open Set Filter
open scoped Topology ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity Mechanics

example (e : ℝ) (F : TwoForm) (v w : Spacetime) :
    minkowskiForm .timeNegative 3 (lorentzForce e F v) w = -e * F ![v, w] :=
  lorentzForce_lowered e F v w

example (e : ℝ) (F : TwoForm) (v : Spacetime) :
    minkowskiForm .timeNegative 3 (lorentzForce e F v) v = 0 :=
  lorentzForce_orthogonal e F v

example (F : TwoForm) (v : Spacetime) :
    lorentzForce 0 F v = 0 :=
  lorentzForce_zero_charge F v

example (m : ℝ) {v : Spacetime} (hv : Timelike v) :
    minkowskiForm .timeNegative 3 (m • fourVelocity v) (m • fourVelocity v) = -(m ^ 2) :=
  mass_shell m hv

example (m : ℝ) {γ : ℝ → Spacetime} {t : ℝ}
    (hγ : ContDiff ℝ 2 γ) (hv : Timelike (deriv γ t)) :
    HasDerivAt (fun s => kineticMomentum m (deriv γ s))
      (m • flat .timeNegative (deriv (fun s => fourVelocity (deriv γ s)) t)) t :=
  hasDerivAt_kineticMomentum m hγ hv

example (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {t : ℝ} (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U) (ht : γ t ∈ U)
    (hv : Timelike (deriv γ t)) :
    eulerLagrange (chargedLagrangian m e A) γ t =
      flat .timeNegative (lorentzForce e (fieldTensor A (γ t)) (deriv γ t) -
        m • deriv (fun s => fourVelocity (deriv γ s)) t) :=
  eulerLagrange_charged m e hγ hU hA ht hv

example (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (chargedLagrangian m e A) γ ↔
      ∀ t ∈ Ioo a b, m • deriv (fun s => fourVelocity (deriv γ s)) t =
        lorentzForce e (fieldTensor A (γ t)) (deriv γ t) :=
  stationary_iff_lorentzForce m e hab hγ hU hA hγU hv

example {m : ℝ} (hm : 0 < m) {F : TwoForm}
    {v a : Spacetime} (h : m • a = lorentzForce 0 F v) : a = 0 :=
  zero_charge_acceleration hm h

example (e : ℝ) (F : TwoForm) (v : Spacetime) (μ : Fin 4) :
    lorentzForce e F v μ = e * ∑ ν : Fin 4,
      raisedComponent F μ ν * flat .timeNegative v (Pi.single ν 1) :=
  lorentzForce_component e F v μ

example (m e : ℝ) {A : Potential} {U : Set Spacetime}
    {γ : ℝ → Spacetime} {a b : ℝ} (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U) (hγU : ∀ t ∈ Icc a b, γ t ∈ U)
    (hunit : ∀ t ∈ Icc a b, intervalQuadratic (deriv γ t) = 1)
    (hs : Stationary a b (chargedLagrangian m e A) γ) {t : ℝ} (ht : t ∈ Ioo a b) :
    m • deriv (deriv γ) t = lorentzForce e (fieldTensor A (γ t)) (deriv γ t) :=
  stationary_properTime m e hab hγ hU hA hγU hunit hs ht

end ProjectAinos.Electrodynamics

open Set
open scoped ContDiff
namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.DifferentialForm SpecialRelativity Mechanics

example (m e : ℝ) {A : Potential} (hA : Continuous A) :
    Continuous (Function.uncurry (chargedLagrangian m e A)) :=
  continuous_chargedLagrangian m e hA

example (m e : ℝ) (A : Potential) {χ : Spacetime → ℝ}
    (hχ : Differentiable ℝ χ) :
    chargedLagrangian m e (gaugeShift A χ) = chargedLagrangian m e A +
      totalTimeDerivative (fun z : ℝ × Spacetime => e * χ z.2) :=
  chargedLagrangian_gauge m e A hχ

example (m e : ℝ) {A : Potential} (hA : Continuous A)
    {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 1 χ) {γ : ℝ → Spacetime}
    (hγ : ContDiff ℝ 1 γ) (a b : ℝ) :
    chargedAction m e (gaugeShift A χ) γ a b = chargedAction m e A γ a b +
      e * (χ (γ b) - χ (γ a)) :=
  chargedAction_gauge m e hA hχ hγ a b

example (m e : ℝ) {A : Potential} (hA : Continuous A)
    {χ : Spacetime → ℝ} (hχ : ContDiff ℝ 1 χ) {γ : ℝ → Spacetime}
    (hγ : ContDiff ℝ 1 γ) (a b : ℝ) :
    Stationary a b (chargedLagrangian m e (gaugeShift A χ)) γ ↔
      Stationary a b (chargedLagrangian m e A) γ :=
  stationary_gauge_iff m e hA hχ hγ a b

example {A : Potential} {χ : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContDiffOn ℝ 2 A U)
    (hχ : ContDiffOn ℝ 3 χ U) : ContDiffOn ℝ 2 (gaugeShift A χ) U :=
  gaugeShift_contDiffOn hU hA hχ

example (m e : ℝ) {A : Potential} {χ : Spacetime → ℝ}
    {U : Set Spacetime} {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ) (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) (hχ : ContDiffOn ℝ 3 χ U)
    (hγU : ∀ t ∈ Icc a b, γ t ∈ U) (hv : ∀ t ∈ Icc a b, Minkowski.Timelike (deriv γ t)) :
    Stationary a b (chargedLagrangian m e (gaugeShift A χ)) γ ↔
      Stationary a b (chargedLagrangian m e A) γ :=
  stationary_gauge_iff_on m e hab hγ hU hA hχ hγU hv

example (m e : ℝ) {A : Potential} {χ : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U) (hA : ContinuousOn A U)
    (hχ : ContDiffOn ℝ 1 χ U) {γ : ℝ → Spacetime} (hγ : ContDiff ℝ 2 γ)
    (a b : ℝ) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) :
    chargedAction m e (gaugeShift A χ) γ a b = chargedAction m e A γ a b +
      e * (χ (γ b) - χ (γ a)) :=
  chargedAction_gauge_on m e hU hA hχ hγ a b hγU

end ProjectAinos.Electrodynamics

open Set
open scoped ContDiff
namespace ProjectAinos.Electrodynamics.Examples

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open Mechanics

example (E B : ℝ) (x v : Spacetime) :
    oneCovector (uniformPotential E B x) v = -E * x 0 * v 1 + B * x 2 * v 3 :=
  uniformPotential_covector E B x v

example (E B : ℝ) (x : Spacetime) :
    fieldTensor (uniformPotential E B) x = uniformField E B :=
  uniformPotential_field E B x

example (E B : ℝ) :
    oneCovector (electric restObserver (uniformField E B)) (Pi.single 1 1) = E :=
  uniformField_electric E B

example (E B : ℝ) :
    oneCovector (magnetic restObserver (uniformField E B)) (Pi.single 1 1) = B :=
  uniformField_magnetic E B

example : spatialReflection.val.toLinearMap.det = -1 :=
  spatialReflection_det

example :
    fieldTensor (gaugeShift (uniformPotential 1 2) gaugeFunction) =
      fieldTensor (uniformPotential 1 2) :=
  uniform_gauge_equivalent

example : gaugeShift (uniformPotential 1 2) gaugeFunction ≠ uniformPotential 1 2 :=
  uniform_gauge_distinct

example : ContDiff ℝ 2 hyperbola :=
  hyperbola_smooth

example (τ : ℝ) : deriv hyperbola τ = hyperbolaVelocity τ :=
  hyperbola_deriv τ

example (τ : ℝ) : deriv hyperbolaVelocity τ = hyperbola τ :=
  hyperbolaVelocity_deriv τ

example (τ : ℝ) : intervalQuadratic (deriv hyperbola τ) = 1 :=
  hyperbola_unit τ

example (τ : ℝ) : FutureTimelike (deriv hyperbola τ) :=
  hyperbola_future τ

example (τ : ℝ) :
    lorentzForce 1 (uniformField 1 0) (hyperbolaVelocity τ) = hyperbola τ :=
  hyperbola_lorentzForce τ

example {a b : ℝ} (hab : a < b) :
    Stationary a b (chargedLagrangian 1 1 (uniformPotential 1 0)) hyperbola :=
  hyperbola_stationary hab

end ProjectAinos.Electrodynamics.Examples
