/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the §3.1 API. Default elaborator options are intentional:
these checks must not rely on the implementation's transparency settings. -/
noncomputable section
open CategoryTheory
open ProjectAInos ProjectAInos.SmoothGeometry ProjectAInos.SmoothGeometry.Minkowski
open ProjectAInos.SmoothGeometry.DifferentialForm ProjectAInos.SpecialRelativity

example (σ : LorentzConvention) (v : MinkowskiModel 3) :
    σ.timeSign * minkowskiForm σ 3 v v = intervalQuadratic v :=
  intervalQuadratic_convention σ v

example (σ : LorentzConvention) (v : MinkowskiModel 3) :
    sharp σ (flat σ v) = v := (flat σ).symm_apply_apply v

example (σ : LorentzConvention) (X : LorentzManifold σ 3) :
    X.opposite.toScheme = X.toScheme := rfl

example : (minkowskiMetric .timePositive 3).IsLocallyMinkowski :=
  minkowski_isLocallyMinkowski _ _

example : (minkowskiMetric .timeNegative 3).IsLocallyMinkowski :=
  minkowski_isLocallyMinkowski _ _

example (σ : LorentzConvention) (v : MinkowskiModel 3) :
    Timelike v ↔ 0 < σ.timeSign * minkowskiForm σ 3 v v := timelike_convention σ v

example : Convex ℝ {v : MinkowskiModel 3 | FutureCausal v} := futureCausal_convex

example {p q r : Spacetime} (hpq : CausallyPrecedes p q) (hqr : CausallyPrecedes q r) :
    CausallyPrecedes p r := causallyPrecedes_trans hpq hqr

example {p q : Spacetime} (hpq : CausallyPrecedes p q) (hqp : CausallyPrecedes q p) :
    p = q := causallyPrecedes_antisymm hpq hqp

example (σ : LorentzConvention) (L : MinkowskiModel 3 ≃ₗ[ℝ] MinkowskiModel 3) :
    L ∈ LorentzGroup 3 ↔ ∀ v w, minkowskiForm σ 3 (L v) (L w) = minkowskiForm σ 3 v w :=
  mem_lorentzGroup_iff σ L

example (L : LorentzGroup 3) :
    (LorentzGroup.matrix L).det = 1 ∨ (LorentzGroup.matrix L).det = -1 :=
  LorentzGroup.matrix_det_eq_one_or_neg_one L

example (L : LorentzGroup 3) (a v : Spacetime) :
    (PoincareGroup.ofLinearTranslation L a).val v = L.val v + a :=
  PoincareGroup.ofLinearTranslation_apply L a v

example (f : PoincareGroup 3) :
    Manifold.scheme 4 Spacetime ≅ Manifold.scheme 4 Spacetime := PoincareGroup.toSchemeIso f

example (u : Observer 3) : Module.finrank ℝ u.restSpace = 3 := u.restSpace_finrank

example (u : Observer 3) (v : FourVector) :
    u.clock v • u.velocity + u.project v = v := u.decomposition v

example (β : Velocity 3) (v : FourVector) :
    time ((boost β).val v) = β.gamma * (time v - inner ℝ β.val (space v)) := boost_time β v

example (β : Velocity 3) : boost β.neg = (boost β)⁻¹ := boost_neg_inverse β

example (L : orthochronousLorentzGroup 3) (β : Velocity 3) : ‖(L • β).val‖ < 1 :=
  (L • β).property

example (a b : ℝ) (ha : |a| < 1) (hb : |b| < 1) :
    rapidity ((a+b)/(1+a*b)) = rapidity a + rapidity b := rapidity_add a b ha hb

example (γ : ℝ → FourVector) (a b : ℝ) (h : TimelikeSegment γ a b) :
    IntervalIntegrable (fun t => properSpeed (deriv γ t)) MeasureTheory.volume a b :=
  properTime_integrable γ a b h.regular

example (γ : ℝ → FourVector) (f : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t ∈ Set.uIcc a b, ContDiffAt ℝ 1 γ (f t))
    (hf : ∀ t ∈ Set.uIcc a b, ContDiffAt ℝ 1 f t)
    (hp : ∀ t ∈ Set.uIcc a b, 0 ≤ deriv f t) :
    properTime (γ ∘ f) a b = properTime γ (f a) (f b) :=
  properTime_reparametrize γ f a b hγ hf hp

example {v : FourVector} (hv : Timelike v) :
    minkowskiForm .timeNegative 3 (fourVelocity v) (fourVelocity v) = -1 := fourVelocity_metric hv

example (ω : Form FourVector 1) (hω : ContDiff ℝ 2 ω) :
    exteriorDerivative (exteriorDerivative ω) = 0 := exteriorDerivative_squared ω hω

example (ω η : Form FourVector 1) {U : Set FourVector} (hU : IsOpen U)
    (h : Set.EqOn ω η U) : Set.EqOn (exteriorDerivative ω) (exteriorDerivative η) U :=
  exteriorDerivative_local hU h

example (f : FourVector → FourVector) (ω : Form FourVector 1)
    (hf : ContDiff ℝ 2 f) (hω : Differentiable ℝ ω) :
    exteriorDerivative (pullback f ω) = pullback f (exteriorDerivative ω) :=
  exteriorDerivative_pullback f ω hf hω

example : exteriorDerivative coordinatePotential = coordinateField := coordinatePotential_exteriorDerivative
example : coordinateField ≠ 0 := coordinateField_nonzero
example (χ : Form FourVector 0) (hχ : ContDiff ℝ 2 χ) :
    extDeriv (coordinatePotential + extDeriv χ) = coordinateField := coordinatePotential_gauge χ hχ

example (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![0,1]) =
      -coordinateForm ![2,3] := hodge_dt_dx σ

example (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![2,3]) =
      coordinateForm ![0,1] := hodge_dy_dz σ

example (σ : LorentzConvention) (o : SpacetimeOrientation) (F : TwoForm) :
    hodgeFiber σ o (by decide : 2+2=3+1) (hodgeFiber σ o (by decide) F) = -F :=
  hodgeFiber_two_square σ o F

example (σ : LorentzConvention) (o : SpacetimeOrientation) (F : TwoForm) :
    hodgeFiber σ.opposite o (by decide : 2+2=3+1) F = hodgeFiber σ o (by decide) F :=
  hodgeFiber_two_opposite σ o F

example (σ : LorentzConvention) (o : SpacetimeOrientation)
    (L : properLorentzGroup 3) (F : Form FourVector 2) :
    hodgeForm σ o (by decide : 2+2=3+1) (pullback L.val.val F) =
      pullback L.val.val (hodgeForm σ o (by decide) F) := hodgeForm_pullback σ o _ L F

example (σ : LorentzConvention) (o : SpacetimeOrientation) (u : Observer 3) (F : TwoForm) :
    reconstructTwoForm σ o u (F.curryLeft u.velocity)
      ((hodgeFiber σ o (by decide : 2+2=3+1) F).curryLeft u.velocity) = F :=
  reconstructTwoForm_contractions σ o u F

example : properTime
    (fun t : ℝ => (0 : MinkowskiModel 1) + t • vector 1 Examples.beta.val) 0 1 = 4/5 :=
  Examples.time_dilation
