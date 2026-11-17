/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.FieldClassification
import ProjectAinos.Electrodynamics.CurvedPotential

/-! Public consumers of the transformation and the classification of a field: a projection
that commutes with an operator and the operators with `(A² − a²)(A² + b²) = 0`, the electric
and the magnetic components with their transformation under a boost, the identities of the
generator of a constant field with the four kinds of motion, and potentials as one-forms on a
manifold.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set
open scoped ContDiff
namespace ProjectAinos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section Projection

variable {A P : E →L[ℝ] E} {κ κ₁ κ₂ : ℝ}

example (hc : ∀ w, P (A w) = A (P w)) (hi : ∀ w, P (P w) = P w)
    (hκ : ∀ w, A (A (P w)) = κ • P w) (w : E) :
    (A ∘L P) ((A ∘L P) ((A ∘L P) w)) = κ • (A ∘L P) w :=
  comp_projection_cube hc hi hκ w

example (hc : ∀ w, P (A w) = A (P w))
    (hi : ∀ w, P (P w) = P w) (h₁ : ∀ w, A (A (P w)) = κ₁ • P w)
    (h₂ : ∀ w, A (A (w - P w)) = κ₂ • (w - P w)) {s₁ c₁ s₂ c₂ : ℝ → ℝ}
    (hs₁ : ∀ τ, HasDerivAt s₁ (1 + κ₁ * c₁ τ) τ) (hc₁ : ∀ τ, HasDerivAt c₁ (s₁ τ) τ)
    (hs₁0 : s₁ 0 = 0) (hc₁0 : c₁ 0 = 0)
    (hs₂ : ∀ τ, HasDerivAt s₂ (1 + κ₂ * c₂ τ) τ) (hc₂ : ∀ τ, HasDerivAt c₂ (s₂ τ) τ)
    (hs₂0 : s₂ 0 = 0) (hc₂0 : c₂ 0 = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity A u₀ τ = u₀ + s₁ τ • A (P u₀) + c₁ τ • A (A (P u₀)) +
      s₂ τ • A (u₀ - P u₀) + c₂ τ • A (A (u₀ - P u₀)) :=
  linearVelocity_eq_of_projection hc hi h₁ h₂ hs₁ hc₁ hs₁0 hc₁0 hs₂ hc₂ hs₂0 hc₂0 u₀ τ

end Projection

section Quartic

variable {A : E →L[ℝ] E} {a b : ℝ}

omit [CompleteSpace E] in
example (A : E →L[ℝ] E) (a b : ℝ) (w : E) :
    hyperbolicProjection A a b w = (a ^ 2 + b ^ 2)⁻¹ • (A (A w) + b ^ 2 • w) :=
  hyperbolicProjection_apply A a b w

omit [CompleteSpace E] in
example (A : E →L[ℝ] E) (a b : ℝ) (w : E) :
    hyperbolicProjection A a b (A w) = A (hyperbolicProjection A a b w) :=
  hyperbolicProjection_comm A a b w

variable (hA : ∀ v, A (A (A (A v))) = (a ^ 2 - b ^ 2) • A (A v) + (a ^ 2 * b ^ 2) • v)

include hA in
omit [CompleteSpace E] in
example (w : E) :
    A (A (A (A w) + b ^ 2 • w)) = a ^ 2 • (A (A w) + b ^ 2 • w) :=
  sq_apply_add hA w

include hA in
omit [CompleteSpace E] in
example (w : E) :
    A (A (hyperbolicProjection A a b w)) = a ^ 2 • hyperbolicProjection A a b w :=
  sq_hyperbolicProjection hA w

include hA in
omit [CompleteSpace E] in
example (hN : a ^ 2 + b ^ 2 ≠ 0) (w : E) :
    hyperbolicProjection A a b (hyperbolicProjection A a b w) = hyperbolicProjection A a b w :=
  hyperbolicProjection_idem hA hN w

include hA in
omit [CompleteSpace E] in
example (hN : a ^ 2 + b ^ 2 ≠ 0) (w : E) :
    A (A (w - hyperbolicProjection A a b w)) = -b ^ 2 • (w - hyperbolicProjection A a b w) :=
  sq_sub_hyperbolicProjection hA hN w

include hA in
example (hN : a ^ 2 + b ^ 2 ≠ 0) {s₁ c₁ s₂ c₂ : ℝ → ℝ}
    (hs₁ : ∀ τ, HasDerivAt s₁ (1 + a ^ 2 * c₁ τ) τ) (hc₁ : ∀ τ, HasDerivAt c₁ (s₁ τ) τ)
    (hs₁0 : s₁ 0 = 0) (hc₁0 : c₁ 0 = 0)
    (hs₂ : ∀ τ, HasDerivAt s₂ (1 + -b ^ 2 * c₂ τ) τ) (hc₂ : ∀ τ, HasDerivAt c₂ (s₂ τ) τ)
    (hs₂0 : s₂ 0 = 0) (hc₂0 : c₂ 0 = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity A u₀ τ = u₀ + s₁ τ • A (hyperbolicProjection A a b u₀) +
      c₁ τ • A (A (hyperbolicProjection A a b u₀)) +
      s₂ τ • A (u₀ - hyperbolicProjection A a b u₀) +
      c₂ τ • A (A (u₀ - hyperbolicProjection A a b u₀)) :=
  linearVelocity_eq_of_quartic hA hN hs₁ hc₁ hs₁0 hc₁0 hs₂ hc₂ hs₂0 hc₂0 u₀ τ

end Quartic

end ProjectAinos.SmoothGeometry.LinearODE

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example (F : TwoForm) (μ ν : Fin 4) : component F μ ν = -component F ν μ :=
  component_swap F μ ν

example (F : TwoForm) (v w : Spacetime) :
    F ![v, w] = component F 0 1 * (v 0 * w 1 - v 1 * w 0) +
      component F 0 2 * (v 0 * w 2 - v 2 * w 0) + component F 0 3 * (v 0 * w 3 - v 3 * w 0) +
      component F 1 2 * (v 1 * w 2 - v 2 * w 1) + component F 1 3 * (v 1 * w 3 - v 3 * w 1) +
      component F 2 3 * (v 2 * w 3 - v 3 * w 2) :=
  twoForm_apply F v w

example (F : TwoForm) (v w : Spacetime) :
    F ![v, w] = electricVector F 0 * (v 1 * w 0 - v 0 * w 1) +
      electricVector F 1 * (v 2 * w 0 - v 0 * w 2) +
      electricVector F 2 * (v 3 * w 0 - v 0 * w 3) +
      magneticVector F 0 * (v 2 * w 3 - v 3 * w 2) +
      magneticVector F 1 * (v 3 * w 1 - v 1 * w 3) +
      magneticVector F 2 * (v 1 * w 2 - v 2 * w 1) :=
  twoForm_apply_vectors F v w

example (L : LorentzGroup 3) (F : TwoForm) (v w : Spacetime) :
    lorentzPullback L F ![v, w] = F ![L.val v, L.val w] :=
  lorentzPullback_apply L F v w

example (L : LorentzGroup 3) (F : TwoForm) (μ ν : Fin 4) :
    component (lorentzPullback L F) μ ν = F ![L.val (Pi.single μ 1), L.val (Pi.single ν 1)] :=
  component_lorentzPullback L F μ ν

example (V : ℝ) (hV : |V| < 1) :
    (axisVelocity V hV).gamma ^ 2 * (1 - V ^ 2) = 1 :=
  axisVelocity_gamma_identity V hV

example (V : ℝ) (hV : |V| < 1) (v : Spacetime) :
    (boost (axisVelocity V hV)).val v =
      ![(axisVelocity V hV).gamma * (v 0 - V * v 1),
        (axisVelocity V hV).gamma * (v 1 - V * v 0), v 2, v 3] :=
  boost_axisVelocity_apply V hV v

section Boost

variable (V : ℝ) (hV : |V| < 1)

example :
    (boost (axisVelocity V hV)).val (Pi.single 0 1) =
      ![(axisVelocity V hV).gamma, -((axisVelocity V hV).gamma * V), 0, 0] :=
  boost_axisVelocity_single_zero V hV

example :
    (boost (axisVelocity V hV)).val (Pi.single 1 1) =
      ![-((axisVelocity V hV).gamma * V), (axisVelocity V hV).gamma, 0, 0] :=
  boost_axisVelocity_single_one V hV

example :
    (boost (axisVelocity V hV)).val (Pi.single 2 1) = ![0, 0, 1, 0] :=
  boost_axisVelocity_single_two V hV

example :
    (boost (axisVelocity V hV)).val (Pi.single 3 1) = ![0, 0, 0, 1] :=
  boost_axisVelocity_single_three V hV

example (F : TwoForm) :
    electricVector (lorentzPullback (boost (axisVelocity V hV)) F) =
      ![electricVector F 0,
        (axisVelocity V hV).gamma * (electricVector F 1 + V * magneticVector F 2),
        (axisVelocity V hV).gamma * (electricVector F 2 - V * magneticVector F 1)] :=
  electricVector_boost V hV F

example (F : TwoForm) :
    magneticVector (lorentzPullback (boost (axisVelocity V hV)) F) =
      ![magneticVector F 0,
        (axisVelocity V hV).gamma * (magneticVector F 1 - V * electricVector F 2),
        (axisVelocity V hV).gamma * (magneticVector F 2 + V * electricVector F 1)] :=
  magneticVector_boost V hV F

end Boost

example : timeAxis 3 = Pi.single 0 1 :=
  timeAxis_eq_single

example (F : TwoForm) (i : Fin 3) :
    electricVector F i = component F i.succ 0 :=
  electricVector_apply F i

example (F : TwoForm) (μ ν : Fin 4) :
    component (star F) μ ν =
      -component F 0 1 * ((Pi.single μ 1 : Spacetime) 2 * (Pi.single ν 1 : Spacetime) 3 -
          (Pi.single μ 1 : Spacetime) 3 * (Pi.single ν 1 : Spacetime) 2) +
        component F 0 2 * ((Pi.single μ 1 : Spacetime) 1 * (Pi.single ν 1 : Spacetime) 3 -
          (Pi.single μ 1 : Spacetime) 3 * (Pi.single ν 1 : Spacetime) 1) -
        component F 0 3 * ((Pi.single μ 1 : Spacetime) 1 * (Pi.single ν 1 : Spacetime) 2 -
          (Pi.single μ 1 : Spacetime) 2 * (Pi.single ν 1 : Spacetime) 1) +
        component F 1 2 * ((Pi.single μ 1 : Spacetime) 0 * (Pi.single ν 1 : Spacetime) 3 -
          (Pi.single μ 1 : Spacetime) 3 * (Pi.single ν 1 : Spacetime) 0) -
        component F 1 3 * ((Pi.single μ 1 : Spacetime) 0 * (Pi.single ν 1 : Spacetime) 2 -
          (Pi.single μ 1 : Spacetime) 2 * (Pi.single ν 1 : Spacetime) 0) +
        component F 2 3 * ((Pi.single μ 1 : Spacetime) 0 * (Pi.single ν 1 : Spacetime) 1 -
          (Pi.single μ 1 : Spacetime) 1 * (Pi.single ν 1 : Spacetime) 0) :=
  component_star F μ ν

example (F : TwoForm) (i : Fin 3) :
    component (star F) 0 i.succ = magneticVector F i :=
  component_star_zero_succ F i

example (F : TwoForm) (i : Fin 3) :
    oneCovector (electric (restObserver 3) F) (Pi.single i.succ 1) = electricVector F i :=
  electric_restObserver_single F i

example (F : TwoForm) (i : Fin 3) :
    oneCovector (magnetic (restObserver 3) F) (Pi.single i.succ 1) = magneticVector F i :=
  magnetic_restObserver_single F i

example (F : TwoForm) :
    scalarInvariant F = ∑ i, magneticVector F i ^ 2 - ∑ i, electricVector F i ^ 2 :=
  scalarInvariant_vectors F

example (F : TwoForm) :
    pseudoscalarInvariant F = ∑ i, electricVector F i * magneticVector F i :=
  pseudoscalarInvariant_vectors F

example (β : Velocity 3) :
    (boost β.neg).val (Pi.single 0 1) = β.observer.velocity :=
  boost_neg_single_zero β

example (β : Velocity 3) (F : TwoForm) (i : Fin 3) :
    oneCovector (electric β.observer F) ((boost β.neg).val (Pi.single i.succ 1)) =
      electricVector (lorentzPullback (boost β.neg) F) i :=
  electric_observer_apply β F i

example (β : Velocity 3) (F : TwoForm) (i : Fin 3) :
    oneCovector (magnetic β.observer F) ((boost β.neg).val (Pi.single i.succ 1)) =
      magneticVector (lorentzPullback (boost β.neg) F) i :=
  magnetic_observer_apply β F i

section Moving

variable (V : ℝ) (hV : |V| < 1)

example :
    (axisVelocity V hV).neg = axisVelocity (-V) (by rwa [abs_neg]) :=
  axisVelocity_neg V hV

example :
    (axisVelocity (-V) (by rwa [abs_neg])).gamma = (axisVelocity V hV).gamma :=
  gamma_axisVelocity_neg V hV

example (F : TwoForm) :
    electricVector (lorentzPullback (boost (axisVelocity V hV).neg) F) =
      ![electricVector F 0,
        (axisVelocity V hV).gamma * (electricVector F 1 - V * magneticVector F 2),
        (axisVelocity V hV).gamma * (electricVector F 2 + V * magneticVector F 1)] :=
  electricVector_moving V hV F

example (F : TwoForm) :
    magneticVector (lorentzPullback (boost (axisVelocity V hV).neg) F) =
      ![magneticVector F 0,
        (axisVelocity V hV).gamma * (magneticVector F 1 + V * electricVector F 2),
        (axisVelocity V hV).gamma * (magneticVector F 2 - V * electricVector F 1)] :=
  magneticVector_moving V hV F

end Moving

end ProjectAinos.Electrodynamics

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

example : (Pi.single 0 1 : Spacetime) = ![1, 0, 0, 0] :=
  single_zero_eq

example : (Pi.single 1 1 : Spacetime) = ![0, 1, 0, 0] :=
  single_one_eq

example : (Pi.single 2 1 : Spacetime) = ![0, 0, 1, 0] :=
  single_two_eq

example : (Pi.single 3 1 : Spacetime) = ![0, 0, 0, 1] :=
  single_three_eq

example (e : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F v = e •
      ![electricVector F 0 * v 1 + electricVector F 1 * v 2 + electricVector F 2 * v 3,
        v 0 * electricVector F 0 + (v 2 * magneticVector F 2 - v 3 * magneticVector F 1),
        v 0 * electricVector F 1 + (v 3 * magneticVector F 0 - v 1 * magneticVector F 2),
        v 0 * electricVector F 2 + (v 1 * magneticVector F 1 - v 2 * magneticVector F 0)] :=
  lorentzForce_vectors e F v

example (e : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F v = e • forceVector (electricVector F) (magneticVector F) v :=
  lorentzForce_eq_forceVector e F v

example (E B : Fin 3 → ℝ) (v : Spacetime) :
    forceVector E B (forceVector E B (forceVector E B v)) =
      (-(∑ i, B i ^ 2 - ∑ i, E i ^ 2)) • forceVector E B v -
        (∑ i, E i * B i) • forceVector (-B) E v :=
  forceVector_cube E B v

example (E B : Fin 3 → ℝ) (v : Spacetime) :
    forceVector E B (forceVector (-B) E v) = (-(∑ i, E i * B i)) • v :=
  forceVector_dual E B v

example (E B : Fin 3 → ℝ) (c : ℝ) (v : Spacetime) :
    forceVector E B (c • v) = c • forceVector E B v :=
  forceVector_smul E B c v

end ProjectAinos.Electrodynamics

namespace ProjectAinos.Electrodynamics.ConstantField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.LinearODE SpecialRelativity

open SmoothGeometry.DifferentialForm Examples

variable {m e : ℝ} (F : TwoForm)

example (m e : ℝ) (v : Spacetime) :
    generator m e F v = (e / m) • forceVector (electricVector F) (magneticVector F) v :=
  generator_eq_forceVector F m e v

example (m e : ℝ) (v : Spacetime) :
    generator m e F (generator m e F (generator m e F v)) =
      (-((e / m) ^ 2 * scalarInvariant F)) • generator m e F v -
        ((e / m) ^ 3 * pseudoscalarInvariant F) • dualGenerator F v :=
  generator_cube_eq F m e v

example (m e : ℝ) (v : Spacetime) :
    generator m e F (dualGenerator F v) = (-(e / m * pseudoscalarInvariant F)) • v :=
  generator_dualGenerator F m e v

example (m e : ℝ) (v : Spacetime) :
    generator m e F (generator m e F (generator m e F (generator m e F v))) =
      (-((e / m) ^ 2 * scalarInvariant F)) • generator m e F (generator m e F v) +
        ((e / m) ^ 4 * pseudoscalarInvariant F ^ 2) • v :=
  generator_quartic F m e v

example (hI : pseudoscalarInvariant F = 0) (m e : ℝ)
    (v : Spacetime) :
    generator m e F (generator m e F (generator m e F v)) =
      (-((e / m) ^ 2 * scalarInvariant F)) • generator m e F v :=
  generator_cube_of_pseudoscalarInvariant F hI m e v

variable {F}

example {α β : FourCovector} (h : IsSimple F α β) :
    pseudoscalarInvariant F = 0 :=
  pseudoscalarInvariant_of_isSimple h

example (hI : pseudoscalarInvariant F = 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hκ : -((e / m) ^ 2 * scalarInvariant F) = Ω ^ 2) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sinh (Ω * τ) / Ω) • generator m e F u₀ +
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  velocity_of_scalarInvariant_neg hI hΩ hκ u₀ τ

example (hI : pseudoscalarInvariant F = 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hκ : -((e / m) ^ 2 * scalarInvariant F) = -Ω ^ 2) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sin (Ω * τ) / Ω) • generator m e F u₀ +
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  velocity_of_scalarInvariant_pos hI hΩ hκ u₀ τ

example (hI₁ : scalarInvariant F = 0)
    (hI₂ : pseudoscalarInvariant F = 0) (m e : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + τ • generator m e F u₀ +
      (τ ^ 2 / 2) • generator m e F (generator m e F u₀) :=
  velocity_of_invariants_zero hI₁ hI₂ m e u₀ τ

example {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 - b ^ 2 = -((e / m) ^ 2 * scalarInvariant F))
    (hab' : a ^ 2 * b ^ 2 = (e / m) ^ 4 * pseudoscalarInvariant F ^ 2) (u₀ : Spacetime)
    (τ : ℝ) :
    velocity m e F u₀ τ =
      u₀ + (Real.sinh (a * τ) / a) •
          generator m e F (hyperbolicProjection (generator m e F) a b u₀) +
        ((Real.cosh (a * τ) - 1) / a ^ 2) • generator m e F
          (generator m e F (hyperbolicProjection (generator m e F) a b u₀)) +
        (Real.sin (b * τ) / b) •
          generator m e F (u₀ - hyperbolicProjection (generator m e F) a b u₀) +
        ((1 - Real.cos (b * τ)) / b ^ 2) • generator m e F
          (generator m e F (u₀ - hyperbolicProjection (generator m e F) a b u₀)) :=
  velocity_of_quartic ha hb hab hab' u₀ τ

example (p : ℝ) {q : ℝ} (hq : q ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = p ∧ a ^ 2 * b ^ 2 = q ^ 2 :=
  exists_rates p hq

example (E B : ℝ) :
    electricVector (uniformField E B) = ![E, 0, 0] :=
  electricVector_uniformField E B

example (E B : ℝ) :
    magneticVector (uniformField E B) = ![B, 0, 0] :=
  magneticVector_uniformField E B

example (E B : ℝ) :
    scalarInvariant (uniformField E B) = B ^ 2 - E ^ 2 :=
  scalarInvariant_uniformField E B

example (E B : ℝ) :
    pseudoscalarInvariant (uniformField E B) = E * B :=
  pseudoscalarInvariant_uniformField E B

example (E : ℝ) : pseudoscalarInvariant (nullField E) = 0 :=
  pseudoscalarInvariant_nullField E

example (E : ℝ) : scalarInvariant (nullField E) = 0 :=
  scalarInvariant_nullField E

example {m e E B : ℝ} (hE : e * E / m ≠ 0) (hB : e * B / m ≠ 0)
    (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField E B) u₀ τ =
      u₀ + (Real.sinh (e * E / m * τ) / (e * E / m)) • generator m e (uniformField E B)
          (hyperbolicProjection (generator m e (uniformField E B)) (e * E / m) (e * B / m)
            u₀) +
        ((Real.cosh (e * E / m * τ) - 1) / (e * E / m) ^ 2) • generator m e (uniformField E B)
          (generator m e (uniformField E B)
            (hyperbolicProjection (generator m e (uniformField E B)) (e * E / m) (e * B / m)
              u₀)) +
        (Real.sin (e * B / m * τ) / (e * B / m)) • generator m e (uniformField E B)
          (u₀ - hyperbolicProjection (generator m e (uniformField E B)) (e * E / m)
            (e * B / m) u₀) +
        ((1 - Real.cos (e * B / m * τ)) / (e * B / m) ^ 2) • generator m e (uniformField E B)
          (generator m e (uniformField E B)
            (u₀ - hyperbolicProjection (generator m e (uniformField E B)) (e * E / m)
              (e * B / m) u₀)) :=
  velocity_uniformField_closed hE hB u₀ τ

end ProjectAinos.Electrodynamics.ConstantField

open Bundle
open scoped Manifold ContDiff
namespace ProjectAinos.Electrodynamics.Curved

open SmoothGeometry SmoothGeometry.DifferentialForm

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]

example (A : Potential (M := M)) : smoothExteriorDerivative (fieldOf A) = 0 :=
  fieldOf_closed A

example (A : Potential (M := M)) (χ : GaugeFunction (M := M)) :
    fieldOf (gaugeShift A χ) = fieldOf A :=
  fieldOf_gaugeShift A χ

example (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) (χ : GaugeFunction (M := M)) :
    source g o (fieldOf (gaugeShift A χ)) = source g o (fieldOf A) :=
  source_gaugeShift g o A χ

example (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) (χ : GaugeFunction (M := M)) (j : CurrentVector (M := M)) :
    Maxwell g o (fieldOf (gaugeShift A χ)) j ↔ Maxwell g o (fieldOf A) j :=
  maxwell_gaugeShift_iff g o A χ j

example (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)
    (A : Potential (M := M)) : Maxwell g o (fieldOf A) (source g o (fieldOf A)) :=
  maxwell_fieldOf g o A

section Pullback

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel 3) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ N]

example (f : C^∞⟮𝓘(ℝ, MinkowskiModel 3), M; 𝓘(ℝ, MinkowskiModel 3), N⟯)
    (A : Potential (M := N)) :
    fieldOf (smoothPullback 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f A) =
      smoothPullback 𝓘(ℝ, MinkowskiModel 3) 𝓘(ℝ, MinkowskiModel 3) f (fieldOf A) :=
  fieldOf_pullback f A

end Pullback

example (A : Electrodynamics.Potential) (hA : ContDiff ℝ ∞ A)
    (x : SpecialRelativity.Spacetime) :
    fieldOf (ofFlat A hA) x = Electrodynamics.fieldTensor A x :=
  fieldOf_ofFlat A hA x

end ProjectAinos.Electrodynamics.Curved
