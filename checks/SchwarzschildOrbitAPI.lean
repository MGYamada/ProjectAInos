/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.SchwarzschildRotations
import ProjectAinos.GeneralRelativity.SchwarzschildCircular
import ProjectAinos.GeneralRelativity.PerihelionIntegral
import ProjectAinos.GeneralRelativity.DeflectionIntegral
import ProjectAinos.GeneralRelativity.SchwarzschildOrbit
import ProjectAinos.GeneralRelativity.Perihelion
import ProjectAinos.GeneralRelativity.LightDeflection
import ProjectAinos.GeneralRelativity.EquatorialComparison

/-! Public consumers of the motion in the Schwarzschild field (Landau–Lifshitz §101): the rotations
as Killing fields with the conservation of angular momentum and the planarity of the motion, the
effective potential with the circular orbits and the photon sphere, the integral of the perihelion
advance with its explicit bounds, and the deflection of light as a small-angle problem; the
integrals of the motion and the radial equation of a geodesic, the perihelion advance and the
deflection of light along given geodesics, and the comparison of the chart geodesics of the
geodesic Hamiltonian with native geodesics. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section SchwarzschildRotations


open ContinuousLinearMap Set TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

open LorentzMetric (chartField curveVelocity)

open CoordinateMetric (physicalChart vectorFieldOf lieOf)

variable {M : ℝ}

example (A B : ℝ → ℝ) (D : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  sphereField A B D x

example (hM : 0 ≤ M) {A B : ℝ → ℝ} (D : ℝ) (hA : ∀ φ, HasDerivAt A (B φ) φ)
    (hB : ∀ φ, HasDerivAt B (-A φ) φ) :
    ∀ y ∈ domain M, ∀ i j, lieOf (metric hM).coefficient (sphereField A B D) y i j = 0 :=
  lieOf_sphereField hM D hA hB

example {d : ℕ} {U : Opens (MinkowskiModel d)} {ξ : MinkowskiModel d → MinkowskiModel d}
    (hξ : ContDiffOn ℝ ∞ ξ U) (x₀ y : U) :
    MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      ((𝓘(ℝ, MinkowskiModel d)).prod 𝓘(ℝ, MinkowskiModel d)) (T% (vectorFieldOf x₀ ξ)) y :=
  mdifferentiableAt_vectorFieldOf hξ x₀ y

example (a : Fin 3) (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  rotationField a x

example (a : Fin 3) (x : MinkowskiModel 3) :
    rotationField a x 0 = 0 :=
  rotationField_zero a x

example (a : Fin 3) (x : MinkowskiModel 3) :
    rotationField a x 1 = 0 :=
  rotationField_one a x

example {A B : ℝ → ℝ} (D : ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiffOn ℝ ∞ (sphereField A B D) (domain M) :=
  contDiffOn_sphereField D hA hB

example (a : Fin 3) :
    ContDiffOn ℝ ∞ (rotationField a) (domain M) :=
  contDiffOn_rotationField a

example (hM : 0 ≤ M) (a : Fin 3) :
    ∀ y ∈ domain M, ∀ i j, lieOf (metric hM).coefficient (rotationField a) y i j = 0 :=
  lieOf_rotationField hM a

example (hM : 0 ≤ M) (x₀ : domain M) (a : Fin 3) :
    (metric hM).toLorentzMetric.IsKillingField (vectorFieldOf x₀ (rotationField a)) :=
  isKillingField_rotationField hM x₀ a

example (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) (a : Fin 3) :
    ℝ :=
  angularMomentum hM x₀ γ τ a

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (a : Fin 3) :
    angularMomentum hM x₀ γ τ₁ a = angularMomentum hM x₀ γ τ₂ a :=
  angularMomentum_eq hM x₀ hγ hs h₁ h₂ a

example (a : Fin 3) (x v : MinkowskiModel 3) :
    ℝ :=
  angularComponent a x v

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) (a : Fin 3) :
    angularMomentum hM x₀ γ τ a =
      angularComponent a (γ τ) (deriv (fun t => (γ t : MinkowskiModel 3)) τ) :=
  angularMomentum_eq_angularComponent hM x₀ hγ a

example {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0) (v : MinkowskiModel 3) :
    angularComponent 0 x v = x 1 ^ 2 * (-Real.sin (x 3) * v 2 -
      Real.sin (x 2) * Real.cos (x 2) * Real.cos (x 3) * v 3) :=
  angularComponent_zero hs v

example {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0) (v : MinkowskiModel 3) :
    angularComponent 1 x v = x 1 ^ 2 * (Real.cos (x 3) * v 2 -
      Real.sin (x 2) * Real.cos (x 2) * Real.sin (x 3) * v 3) :=
  angularComponent_one hs v

example (x v : MinkowskiModel 3) :
    angularComponent 2 x v = x 1 ^ 2 * (Real.sin (x 2) ^ 2 * v 3) :=
  angularComponent_two x v

example {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0) (v : MinkowskiModel 3) :
    angularComponent 0 x v ^ 2 + angularComponent 1 x v ^ 2 + angularComponent 2 x v ^ 2 =
      x 1 ^ 4 * (v 2 ^ 2 + Real.sin (x 2) ^ 2 * v 3 ^ 2) :=
  sum_angularComponent_sq hs v

example (x : MinkowskiModel 3) :
    Fin 3 → ℝ :=
  radialDirection x

example {x : MinkowskiModel 3} (hs : Real.sin (x 2) ≠ 0) (v : MinkowskiModel 3) :
    radialDirection x 0 * angularComponent 0 x v + radialDirection x 1 * angularComponent 1 x v +
      radialDirection x 2 * angularComponent 2 x v = 0 :=
  direction_angularComponent hs v

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    angularMomentum hM x₀ γ τ 0 ^ 2 + angularMomentum hM x₀ γ τ 1 ^ 2 +
        angularMomentum hM x₀ γ τ 2 ^ 2 =
      (γ τ : MinkowskiModel 3) 1 ^ 4 * (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2) :=
  sum_angularMomentum_sq hM x₀ hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    radialDirection (γ τ) 0 * angularMomentum hM x₀ γ τ 0 +
        radialDirection (γ τ) 1 * angularMomentum hM x₀ γ τ 1 +
      radialDirection (γ τ) 2 * angularMomentum hM x₀ γ τ 2 = 0 :=
  direction_angularMomentum hM x₀ hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) :
    (∀ a, angularMomentum hM x₀ γ τ a = angularMomentum hM x₀ γ τ₀ a) ∧
      radialDirection (γ τ) 0 * angularMomentum hM x₀ γ τ₀ 0 +
          radialDirection (γ τ) 1 * angularMomentum hM x₀ γ τ₀ 1 +
        radialDirection (γ τ) 2 * angularMomentum hM x₀ γ τ₀ 2 = 0 :=
  planar_motion hM x₀ hγ hs h₀ hτ

example {x v : MinkowskiModel 3} (hθ : x 2 = Real.pi / 2) (hv : v 2 = 0) :
    angularComponent 0 x v = 0 ∧ angularComponent 1 x v = 0 ∧
      angularComponent 2 x v = x 1 ^ 2 * v 3 :=
  angularComponent_equatorial hθ hv

example {r : ℝ} (hr : 2 * M < r) (t φ : ℝ) :
    (![t, r, Real.pi / 2, φ] : MinkowskiModel 3) ∈ domain M :=
  equatorial_mem_domain hr t φ

example {r : ℝ} (hr : 2 * M < r) (Ω : ℝ) (t : ℝ) :
    domain M :=
  equatorialCircle hr Ω t

example (hM : 0 ≤ M) (x₀ : domain M) {r : ℝ} (hr : 2 * M < r) (Ω τ : ℝ) :
    angularMomentum hM x₀ (equatorialCircle hr Ω) τ 0 = 0 ∧
      angularMomentum hM x₀ (equatorialCircle hr Ω) τ 1 = 0 ∧
        angularMomentum hM x₀ (equatorialCircle hr Ω) τ 2 = r ^ 2 * Ω :=
  angularMomentum_equatorialCircle hM x₀ hr Ω τ

example (hM : 0 ≤ M) {r : ℝ} (hr : 2 * M < r) {Ω : ℝ} (hΩ : r ^ 3 * Ω ^ 2 = M) :
    (metric hM).toLorentzMetric.IsGeodesicOn univ (equatorialCircle hr Ω) :=
  isGeodesicOn_equatorialCircle hM hr hΩ

example (hM : 0 ≤ M) (x₀ : domain M) {r : ℝ} (hr : 2 * M < r) {Ω : ℝ} (hΩ : r ^ 3 * Ω ^ 2 = M)
    (τ₀ τ : ℝ) :
    (∀ a, angularMomentum hM x₀ (equatorialCircle hr Ω) τ a =
        angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ a) ∧
      radialDirection (equatorialCircle hr Ω τ) 0 *
            angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ 0 +
          radialDirection (equatorialCircle hr Ω τ) 1 *
            angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ 1 +
        radialDirection (equatorialCircle hr Ω τ) 2 *
          angularMomentum hM x₀ (equatorialCircle hr Ω) τ₀ 2 = 0 :=
  planar_motion_equatorialCircle hM x₀ hr hΩ τ₀ τ

end ProjectAinos.GeneralRelativity.SchwarzschildExterior

end SchwarzschildRotations

section SchwarzschildCircular


open ContinuousLinearMap Set Filter TopologicalSpace

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

open CoordinateMetric (christoffelOf physicalChart)

open LorentzMetric (curveVelocity chartField)

variable {M : ℝ}

example (M : ℝ) (y : MinkowskiModel 3) :
    Fin 4 → ℝ :=
  diagonalCoefficients M y

example (hM : 0 ≤ M) (y : MinkowskiModel 3) :
    (metric hM).coefficient y = Matrix.diagonal (diagonalCoefficients M y) :=
  coefficient_eq_diagonal hM y

example (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M) (i : Fin 4) :
    diagonalCoefficients M y i ≠ 0 :=
  diagonalCoefficients_ne_zero hM hy i

example (M : ℝ) (y : MinkowskiModel 3) :
    Fin 4 → Fin 4 → ℝ :=
  coefficientDerivative M y

example {f : ℝ → ℝ} {f' : ℝ} (a : Fin 4) {y : MinkowskiModel 3} (hf : HasDerivAt f f' (y a)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => f (z a))
      (f' • (proj a : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hasFDerivAt_coord a hf

example (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M) (a b : Fin 4) :
    fderiv ℝ (fun z => diagonalCoefficients M z a) y (Pi.single b 1) =
      coefficientDerivative M y a b :=
  fderiv_diagonalCoefficients hM hy a b

example (M : ℝ) (y : MinkowskiModel 3) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel M y

example (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M) (k i j : Fin 4) :
    christoffelOf (metric hM).coefficient y k i j =
      ((if k = j then coefficientDerivative M y k i else 0) +
        (if k = i then coefficientDerivative M y k j else 0) -
        (if i = j then coefficientDerivative M y i k else 0)) /
          (2 * diagonalCoefficients M y k) :=
  christoffelOf_metric_eq_formula hM hy k i j

example (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M) (k i j : Fin 4) :
    christoffelOf (metric hM).coefficient y k i j = christoffel M y k i j :=
  christoffelOf_metric hM hy k i j

example (M κ L r : ℝ) :
    ℝ :=
  effectivePotential M κ L r

example (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (effectivePotential M κ L)
      (2 * (M * κ * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2) / r ^ 4) r :=
  hasDerivAt_effectivePotential M κ L hr

example (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (effectivePotential M κ L) r =
      2 * (M * κ * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2) / r ^ 4 :=
  deriv_effectivePotential M κ L hr

example (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (deriv (effectivePotential M κ L))
      (2 * (-2 * M * κ * r ^ 2 + 3 * L ^ 2 * r - 12 * M * L ^ 2) / r ^ 5) r :=
  hasDerivAt_deriv_effectivePotential M κ L hr

example (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (effectivePotential M κ L)) r =
      2 * (-2 * M * κ * r ^ 2 + 3 * L ^ 2 * r - 12 * M * L ^ 2) / r ^ 5 :=
  deriv_deriv_effectivePotential M κ L hr

example (L : ℝ) {R : ℝ} (hR : R ≠ 0) :
    deriv (effectivePotential M 1 L) R = 0 ↔ L ^ 2 * (R - 3 * M) = M * R ^ 2 :=
  deriv_effectivePotential_eq_zero_iff L hR

example (hM : 0 < M) {L R : ℝ} (hR : R ≠ 0) (h : deriv (effectivePotential M 1 L) R = 0) :
    3 * M < R :=
  three_mul_lt_of_deriv_effectivePotential_eq_zero hM hR h

example (hM : 0 < M) {L R : ℝ} (hR : R ≠ 0) (h : deriv (effectivePotential M 1 L) R = 0) :
    deriv (deriv (effectivePotential M 1 L)) R = 2 * M * (R - 6 * M) / (R ^ 3 * (R - 3 * M)) :=
  deriv_deriv_effectivePotential_of_deriv_eq_zero hM hR h

example (hM : 0 < M) {L R : ℝ} (hR : R ≠ 0) (h : deriv (effectivePotential M 1 L) R = 0) :
    0 < deriv (deriv (effectivePotential M 1 L)) R ↔ 6 * M < R :=
  deriv_deriv_effectivePotential_pos_iff hM hR h

example (M L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (effectivePotential M 0 L) r = 2 * L ^ 2 * (3 * M - r) / r ^ 4 :=
  deriv_effectivePotential_light M L hr

example {L R : ℝ} (hL : L ≠ 0) (hR : R ≠ 0) :
    deriv (effectivePotential M 0 L) R = 0 ↔ R = 3 * M :=
  deriv_effectivePotential_light_eq_zero_iff hL hR

example (hM : 0 < M) {L : ℝ} (hL : L ≠ 0) :
    deriv (deriv (effectivePotential M 0 L)) (3 * M) < 0 :=
  deriv_deriv_effectivePotential_light hM hL

example (M L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    effectivePotential M 0 L r = L ^ 2 * (r - 2 * M) / r ^ 3 :=
  effectivePotential_light_eq M L hr

example (hM : 0 < M) (L : ℝ) :
    IsMaxOn (effectivePotential M 0 L) (Ioi 0) (3 * M) :=
  isMaxOn_effectivePotential_light hM L

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
    (g : CoordinateMetric σ d U) {γ : ℝ → U} (p v : MinkowskiModel d)
    (hγ : ∀ t, (γ t : MinkowskiModel d) = p + t • v)
    (h : ∀ t k, ∑ i, ∑ j, christoffelOf g.coefficient (γ t) k i j * v i * v j = 0) :
    g.toLorentzMetric.IsGeodesicOn univ γ :=
  isGeodesicOn_univ_of_line g p v hγ h

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
    (g : CoordinateMetric σ d U) {γ : ℝ → U} (p v : MinkowskiModel d)
    (hγ : ∀ t, (γ t : MinkowskiModel d) = p + t • v) (t : ℝ) :
    g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * v i * v j :=
  form_curveVelocity_of_line g p v hγ t

example {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}
    (g : CoordinateMetric σ d U) {γ : ℝ → U} (p v : MinkowskiModel d)
    (hγ : ∀ t, (γ t : MinkowskiModel d) = p + t • v) (t : ℝ) (x : U) (w : MinkowskiModel d) :
    g.toLorentzMetric.form (γ t) (chartField (physicalChart x) w (γ t)) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * w i * v j :=
  pairing_curveVelocity_of_line g p v hγ t x w

example (M R : ℝ) :
    ℝ :=
  circularTimeRate M R

example (M R : ℝ) :
    ℝ :=
  circularAngleRate M R

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    circularTimeRate M R ^ 2 = R / (R - 3 * M) :=
  circularTimeRate_sq hM hR

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    circularAngleRate M R ^ 2 = circularTimeRate M R ^ 2 * (M / R ^ 3) :=
  circularAngleRate_sq hM hR

example (R : ℝ) :
    circularAngleRate 0 R = 0 :=
  circularAngleRate_zero R

example (R : ℝ) :
    circularTimeRate 0 R = 1 :=
  circularTimeRate_zero R

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (s : ℝ) :
    (![circularTimeRate M R * s, R, Real.pi / 2, circularAngleRate M R * s] :
      MinkowskiModel 3) ∈ domain M :=
  mem_domain_circular hM hR s

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (s : ℝ) :
    domain M :=
  circularOrbit hM hR s

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (s : ℝ) :
    (circularOrbit hM hR s : MinkowskiModel 3) =
      ![0, R, Real.pi / 2, 0] + s • ![circularTimeRate M R, 0, 0, circularAngleRate M R] :=
  circularOrbit_eq_line hM hR s

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    (metric hM).toLorentzMetric.IsGeodesicOn univ (circularOrbit hM hR) :=
  isGeodesicOn_circular hM hR

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (t : ℝ) :
    (metric hM).toLorentzMetric.form (circularOrbit hM hR t)
      (curveVelocity (circularOrbit hM hR) t) (curveVelocity (circularOrbit hM hR) t) = -1 :=
  form_curveVelocity_circular hM hR t

example {R : ℝ} (hR : 3 * 0 < R) (s : ℝ) :
    (circularOrbit le_rfl hR s : MinkowskiModel 3) = ![s, R, Real.pi / 2, 0] :=
  circularOrbit_zero hR s

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (t : ℝ) :
    (metric hM).toLorentzMetric.form (circularOrbit hM hR t)
      (chartField (physicalChart x₀) (Pi.single 0 1) (circularOrbit hM hR t))
      (curveVelocity (circularOrbit hM hR) t) = -((1 - 2 * M / R) * circularTimeRate M R) :=
  pairing_time_circular hM hR x₀ t

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (t : ℝ) :
    (metric hM).toLorentzMetric.form (circularOrbit hM hR t)
      (chartField (physicalChart x₀) (Pi.single 3 1) (circularOrbit hM hR t))
      (curveVelocity (circularOrbit hM hR) t) = R ^ 2 * circularAngleRate M R :=
  pairing_angle_circular hM hR x₀ t

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    ((1 - 2 * M / R) * circularTimeRate M R) ^ 2 = (1 - 2 * M / R) ^ 2 / (1 - 3 * M / R) :=
  circularEnergy_sq hM hR

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    (R ^ 2 * circularAngleRate M R) ^ 2 = M * R ^ 2 / (R - 3 * M) :=
  circularAngularMomentum_sq hM hR

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    deriv (effectivePotential M 1 (R ^ 2 * circularAngleRate M R)) R = 0 :=
  deriv_effectivePotential_circular hM hR

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    effectivePotential M 1 (R ^ 2 * circularAngleRate M R) R =
      ((1 - 2 * M / R) * circularTimeRate M R) ^ 2 :=
  effectivePotential_circular hM hR

example (M a : ℝ) :
    ℝ :=
  photonAngleRate M a

example (M a : ℝ) :
    photonAngleRate M a ^ 2 = a ^ 2 / (27 * M ^ 2) :=
  photonAngleRate_sq M a

example (hM : 0 < M) (a s : ℝ) :
    (![a * s, 3 * M, Real.pi / 2, photonAngleRate M a * s] : MinkowskiModel 3) ∈ domain M :=
  mem_domain_photon hM a s

example (hM : 0 < M) (a s : ℝ) :
    domain M :=
  photonOrbit hM a s

example (hM : 0 < M) (a s : ℝ) :
    (photonOrbit hM a s : MinkowskiModel 3) =
      ![0, 3 * M, Real.pi / 2, 0] + s • ![a, 0, 0, photonAngleRate M a] :=
  photonOrbit_eq_line hM a s

example (hM : 0 < M) (a : ℝ) :
    (metric hM.le).toLorentzMetric.IsGeodesicOn univ (photonOrbit hM a) :=
  isGeodesicOn_photonCircle hM a

example (hM : 0 < M) (a t : ℝ) :
    (metric hM.le).toLorentzMetric.form (photonOrbit hM a t)
      (curveVelocity (photonOrbit hM a) t) (curveVelocity (photonOrbit hM a) t) = 0 :=
  form_curveVelocity_photonCircle hM a t

end ProjectAinos.GeneralRelativity.SchwarzschildExterior

end SchwarzschildCircular

section PerihelionIntegral


namespace ProjectAinos.GeneralRelativity.Perihelion

open Set MeasureTheory

open scoped Real

example (M u₂ u₁ : ℝ) :
    ℝ :=
  apsidalAngle M u₂ u₁

example (u₂ u₁ : ℝ) :
    ∫ θ in (0 : ℝ)..π, Mechanics.turningParam u₂ u₁ θ = π * (u₁ + u₂) / 2 :=
  integral_turningParam u₂ u₁

example {u₂ u₁ : ℝ} (hu : u₂ ≤ u₁) (θ : ℝ) :
    Mechanics.turningParam u₂ u₁ θ ∈ Icc u₂ u₁ :=
  turningParam_mem_Icc_of_le hu θ

example {M u₂ u₁ : ℝ} (hM : 0 ≤ M) (hu₂ : 0 ≤ u₂) (hu : u₂ ≤ u₁) (θ : ℝ) :
    2 * M * (u₁ + u₂ + Mechanics.turningParam u₂ u₁ θ) ∈ Icc 0 (2 * M * (2 * u₁ + u₂)) :=
  apsidalArgument_mem_Icc hM hu₂ hu θ

example {M u₂ u₁ : ℝ} (hM : 0 ≤ M) (hu₂ : 0 ≤ u₂) (hu : u₂ ≤ u₁)
    (hsmall : 2 * M * (2 * u₁ + u₂) ≤ 1 / 4) :
    0 ≤ 2 * apsidalAngle M u₂ u₁ - 2 * π - 3 * π * M * (u₁ + u₂) ∧
      2 * apsidalAngle M u₂ u₁ - 2 * π - 3 * π * M * (u₁ + u₂) ≤
        4 * π * M ^ 2 * (2 * u₁ + u₂) ^ 2 :=
  apsidalAngle_bounds hM hu₂ hu hsmall

example (M a e : ℝ) (ha : 0 < a) (he : 0 ≤ e) (he1 : e < 1) :
    3 * π * M * (1 / (a * (1 - e)) + 1 / (a * (1 + e))) = 6 * π * M / (a * (1 - e ^ 2)) :=
  advance_eq_semiMajor M a e ha he he1

example {M a e : ℝ} (hM : 0 ≤ M) (ha : 0 < a) (he : 0 ≤ e) (he1 : e < 1)
    (hsmall : 8 * M * (3 + e) ≤ a * (1 - e ^ 2)) :
    0 ≤ 2 * apsidalAngle M (1 / (a * (1 + e))) (1 / (a * (1 - e))) - 2 * π -
        6 * π * M / (a * (1 - e ^ 2)) ∧
      2 * apsidalAngle M (1 / (a * (1 + e))) (1 / (a * (1 - e))) - 2 * π -
          6 * π * M / (a * (1 - e ^ 2)) ≤
        4 * π * M ^ 2 * ((3 + e) / (a * (1 - e ^ 2))) ^ 2 :=
  apsidalAngle_bounds_semiMajor hM ha he he1 hsmall

example (u₂ u₁ : ℝ) :
    apsidalAngle 0 u₂ u₁ = π :=
  apsidalAngle_zero_mass u₂ u₁

end ProjectAinos.GeneralRelativity.Perihelion

end PerihelionIntegral

section DeflectionIntegral


open scoped Real

namespace ProjectAinos.GeneralRelativity.LightDeflection

open Mechanics.Scattering Mechanics.Scattering.SmallAngle

example :
    ∫ ψ in (0 : ℝ)..π / 2, Real.sin ψ * deriv (fun u : ℝ => -u ^ 3) (Real.sin ψ) = -2 :=
  integral_sin_mul_deriv_neg_cube

example :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ ε : ℝ, |ε| ≤ δ → ∃ c : ℝ, IsClosest (fun u => -u ^ 3) ε c ∧
      ∀ ρ vinf : ℝ, 0 < ρ → 0 < vinf →
        |deflectionAngle (ρ * vinf) (speedSq (fun u => -u ^ 3) ρ vinf ε) (ρ / c) + 2 * ε| ≤
          C * ε ^ 2 :=
  exists_abs_deflectionAngle_add_le

example :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ M ρ : ℝ, 0 < ρ → 0 ≤ M → 2 * M / ρ ≤ δ →
      ∃ c : ℝ, IsClosest (fun u => -u ^ 3) (2 * M / ρ) c ∧ ∀ vinf : ℝ, 0 < vinf →
        |deflectionAngle (ρ * vinf) (speedSq (fun u => -u ^ 3) ρ vinf (2 * M / ρ)) (ρ / c) +
          4 * M / ρ| ≤ C * (M / ρ) ^ 2 :=
  exists_abs_deflectionAngle_schwarzschild_add_le

end ProjectAinos.GeneralRelativity.LightDeflection

end DeflectionIntegral

section SchwarzschildOrbit


open ContinuousLinearMap Set Filter TopologicalSpace

open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

open LorentzMetric (chartField curveVelocity)

open CoordinateMetric (physicalChart)

variable {M : ℝ}

example (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) :
    ℝ :=
  energy hM x₀ γ τ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) :
    energy hM x₀ γ τ₁ = energy hM x₀ γ τ₂ :=
  energy_eq hM x₀ hγ hs h₁ h₂

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    energy hM x₀ γ τ = (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) *
      deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 :=
  energy_eq_coord hM x₀ hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 =
      energy hM x₀ γ τ / (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) :=
  timeRate_eq_of_differentiableAt hM x₀ hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 =
      energy hM x₀ γ τ₀ / (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) :=
  timeRate_eq hM x₀ hγ hs h₀ hτ

example (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) :
    ℝ :=
  angularMomentumSq hM x₀ γ τ

example (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) :
    0 ≤ angularMomentumSq hM x₀ γ τ :=
  angularMomentumSq_nonneg hM x₀ γ τ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) :
    angularMomentumSq hM x₀ γ τ₁ = angularMomentumSq hM x₀ γ τ₂ :=
  angularMomentumSq_eq hM x₀ hγ hs h₁ h₂

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    angularMomentumSq hM x₀ γ τ =
      (γ τ : MinkowskiModel 3) 1 ^ 4 * (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2) :=
  angularMomentumSq_eq_coord hM x₀ hγ

example (hM : 0 ≤ M) (γ : ℝ → domain M) (τ : ℝ) :
    ℝ :=
  normalization hM γ τ

example (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) :
    normalization hM γ τ₁ = normalization hM γ τ₂ :=
  normalization_eq hM hγ hs h₁ h₂

example (hM : 0 ≤ M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    (metric hM).toLorentzMetric.form (γ τ) (curveVelocity γ τ) (curveVelocity γ τ) =
      -(1 - 2 * M / (γ τ : MinkowskiModel 3) 1) *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 0 ^ 2 +
        deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 /
          (1 - 2 * M / (γ τ : MinkowskiModel 3) 1) +
        (γ τ : MinkowskiModel 3) 1 ^ 2 * deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        (γ τ : MinkowskiModel 3) 1 ^ 2 * Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2 :=
  form_curveVelocity_eq_coord hM hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ ^ 2 - effectivePotential M (normalization hM γ τ)
        (Real.sqrt (angularMomentumSq hM x₀ γ τ)) ((γ τ : MinkowskiModel 3) 1) :=
  radial_sq_eq_of_differentiableAt hM x₀ hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ₀ ^ 2 - effectivePotential M (normalization hM γ τ₀)
        (Real.sqrt (angularMomentumSq hM x₀ γ τ₀)) ((γ τ : MinkowskiModel 3) 1) :=
  radial_sq_eq hM x₀ hγ hs h₀ hτ

example (γ : ℝ → domain M) (τ₀ τ : ℝ) :
    ℝ :=
  sweptAngle γ τ₀ τ

example (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    HasDerivAt (sweptAngle γ τ₀)
      (Real.sqrt (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2)) τ :=
  hasDerivAt_sweptAngle hM hγ hso hsc h₀ hτ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {τ : ℝ}
    (hγ : DifferentiableAt ℝ (fun t => (γ t : MinkowskiModel 3)) τ) :
    Real.sqrt (deriv (fun t => (γ t : MinkowskiModel 3)) τ 2 ^ 2 +
        Real.sin ((γ τ : MinkowskiModel 3) 2) ^ 2 *
          deriv (fun t => (γ t : MinkowskiModel 3)) τ 3 ^ 2) =
      Real.sqrt (angularMomentumSq hM x₀ γ τ) / (γ τ : MinkowskiModel 3) 1 ^ 2 :=
  sqrt_angular_eq hM x₀ hγ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s) (hτ : τ ∈ s) :
    HasDerivAt (sweptAngle γ τ₀)
      (Real.sqrt (angularMomentumSq hM x₀ γ τ₀) / (γ τ : MinkowskiModel 3) 1 ^ 2) τ :=
  hasDerivAt_sweptAngle_eq_div hM x₀ hγ hso hsc h₀ hτ

example (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    (hθ : ∀ σ ∈ s, (γ σ : MinkowskiModel 3) 2 = Real.pi / 2)
    (hφ : ∀ σ ∈ s, 0 ≤ deriv (fun t => (γ t : MinkowskiModel 3)) σ 3) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) :
    sweptAngle γ τ₀ τ = (γ τ : MinkowskiModel 3) 3 - (γ τ₀ : MinkowskiModel 3) 3 :=
  sweptAngle_equatorial hM hγ hso hsc hθ hφ h₀ hτ

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    energy hM x₀ (circularOrbit hM hR) τ = (1 - 2 * M / R) * circularTimeRate M R :=
  energy_circular hM hR x₀ τ

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (τ : ℝ) :
    normalization hM (circularOrbit hM hR) τ = 1 :=
  normalization_circular hM hR τ

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    Real.sqrt (angularMomentumSq hM x₀ (circularOrbit hM hR) τ) =
      R ^ 2 * circularAngleRate M R :=
  sqrt_angularMomentumSq_circular hM hR x₀ τ

example (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (τ : ℝ) :
    deriv (fun t => (circularOrbit hM hR t : MinkowskiModel 3)) τ 1 = 0 ∧
      energy hM x₀ (circularOrbit hM hR) τ ^ 2 = effectivePotential M 1
        (Real.sqrt (angularMomentumSq hM x₀ (circularOrbit hM hR) τ)) R :=
  radial_sq_eq_circular hM hR x₀ τ

end ProjectAinos.GeneralRelativity.SchwarzschildExterior

end SchwarzschildOrbit

section Perihelion


open Set Filter

open scoped Real Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

variable {M : ℝ}

example {E L u₁ u₂ : ℝ} (hu : u₁ ≠ u₂) (h₁ : E ^ 2 - (1 - 2 * M * u₁) * (1 + L ^ 2 * u₁ ^ 2) = 0)
    (h₂ : E ^ 2 - (1 - 2 * M * u₂) * (1 + L ^ 2 * u₂ ^ 2) = 0) (u : ℝ) :
    E ^ 2 - (1 - 2 * M * u) * (1 + L ^ 2 * u ^ 2) =
      L ^ 2 * (u₁ - u) * (u - u₂) * (1 - 2 * M * (u₁ + u₂ + u)) :=
  cubic_eq_factor_of_roots hu h₁ h₂ u

example (hM : 0 ≤ M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) {τ : ℝ} (hτ : τ ∈ s) :
    HasDerivAt (fun t => 1 / (γ t : MinkowskiModel 3) 1)
      (-deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2) τ :=
  hasDerivAt_inv_radius hM hγ hτ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) (hκ : normalization hM γ τ₀ = 1) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ₀ ^ 2 - (1 - 2 * M * (1 / (γ τ : MinkowskiModel 3) 1)) *
        (1 + Real.sqrt (angularMomentumSq hM x₀ γ τ₀) ^ 2 *
          (1 / (γ τ : MinkowskiModel 3) 1) ^ 2) :=
  radial_sq_eq_inv hM x₀ hγ hs h₀ hτ hκ

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    0 < 1 / (γ τ₂ : MinkowskiModel 3) 1 ∧
      1 / (γ τ₂ : MinkowskiModel 3) 1 < 1 / (γ τ₁ : MinkowskiModel 3) 1 ∧
      0 < Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) :=
  inverseRadius_lt_of_apsides hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) {τ : ℝ}
    (hτs : τ ∈ s) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) ^ 2 *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 - 1 / (γ τ : MinkowskiModel 3) 1) *
        (1 / (γ τ : MinkowskiModel 3) 1 - 1 / (γ τ₂ : MinkowskiModel 3) 1) *
        (1 - 2 * M * (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1 +
          1 / (γ τ : MinkowskiModel 3) 1)) :=
  radial_sq_eq_factor hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos hτs

example (hM : 0 ≤ M) (γ : ℝ → domain M) {τ : ℝ}
    (hpos : 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    -deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2 < 0 :=
  inv_radius_rate_neg hM γ hpos

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) {τ : ℝ}
    (hτs : τ ∈ s) :
    (-deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 / (γ τ : MinkowskiModel 3) 1 ^ 2) ^ 2 =
      Real.sqrt (angularMomentumSq hM.le x₀ γ τ₁) ^ 2 * (1 / (γ τ : MinkowskiModel 3) 1) ^ 4 *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 - 1 / (γ τ : MinkowskiModel 3) 1) *
        (1 / (γ τ : MinkowskiModel 3) 1 - 1 / (γ τ₂ : MinkowskiModel 3) 1) *
        (1 - 2 * M * (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1 +
          1 / (γ τ : MinkowskiModel 3) 1)) :=
  inv_radius_rate_sq_eq hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos hτs

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) ≤ 1 :=
  simple_apsides_le hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) < 1 :=
  simple_apsides_lt hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) :
    sweptAngle γ τ₁ τ₂ = Perihelion.apsidalAngle M (1 / (γ τ₂ : MinkowskiModel 3) 1)
      (1 / (γ τ₁ : MinkowskiModel 3) 1) :=
  angle_between_apsides hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ τ₃ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (h₃ : τ₃ ∈ s) (hτ : τ₁ < τ₂) (hτ' : τ₂ < τ₃)
    (hκ : normalization hM.le γ τ₁ = 1) (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hneg : ∀ τ ∈ Ioo τ₂ τ₃, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 < 0)
    (hr₃ : (γ τ₃ : MinkowskiModel 3) 1 = (γ τ₁ : MinkowskiModel 3) 1) :
    sweptAngle γ τ₂ τ₃ = Perihelion.apsidalAngle M (1 / (γ τ₂ : MinkowskiModel 3) 1)
      (1 / (γ τ₁ : MinkowskiModel 3) 1) :=
  return_half hM x₀ hγ hsc h₁ h₂ h₃ hτ hτ' hκ hr₁ hr₂ hpos hneg hr₃

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ τ₃ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (h₃ : τ₃ ∈ s) (hτ : τ₁ < τ₂) (hτ' : τ₂ < τ₃)
    (hκ : normalization hM.le γ τ₁ = 1) (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hneg : ∀ τ ∈ Ioo τ₂ τ₃, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 < 0)
    (hr₃ : (γ τ₃ : MinkowskiModel 3) 1 = (γ τ₁ : MinkowskiModel 3) 1) :
    sweptAngle γ τ₁ τ₃ = 2 * Perihelion.apsidalAngle M (1 / (γ τ₂ : MinkowskiModel 3) 1)
      (1 / (γ τ₁ : MinkowskiModel 3) 1) :=
  sweptAngle_between_perihelia hM x₀ hγ hsc h₁ h₂ h₃ hτ hτ' hκ hr₁ hr₂ hpos hneg hr₃

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hsmall : 2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) +
      1 / (γ τ₂ : MinkowskiModel 3) 1) ≤ 1 / 4) :
    0 ≤ 2 * sweptAngle γ τ₁ τ₂ - 2 * π - 3 * π * M *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ∧
      2 * sweptAngle γ τ₁ τ₂ - 2 * π - 3 * π * M *
          (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ≤
        4 * π * M ^ 2 *
          (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) ^ 2 :=
  perihelion_advance_bounds hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos hsmall

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (hτ : τ₁ < τ₂) (hκ : normalization hM.le γ τ₁ = 1)
    (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) {a e : ℝ}
    (ha₁ : (γ τ₁ : MinkowskiModel 3) 1 = a * (1 - e))
    (ha₂ : (γ τ₂ : MinkowskiModel 3) 1 = a * (1 + e)) (hsmall : 8 * M * (3 + e) ≤ a * (1 - e ^ 2)) :
    0 ≤ 2 * sweptAngle γ τ₁ τ₂ - 2 * π - 6 * π * M / (a * (1 - e ^ 2)) ∧
      2 * sweptAngle γ τ₁ τ₂ - 2 * π - 6 * π * M / (a * (1 - e ^ 2)) ≤
        4 * π * M ^ 2 * ((3 + e) / (a * (1 - e ^ 2))) ^ 2 :=
  perihelion_advance_bounds_semiMajor hM x₀ hγ hsc h₁ h₂ hτ hκ hr₁ hr₂ hpos ha₁ ha₂ hsmall

example (hM : 0 < M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM.le).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₁ τ₂ τ₃ : ℝ}
    (h₁ : τ₁ ∈ s) (h₂ : τ₂ ∈ s) (h₃ : τ₃ ∈ s) (hτ : τ₁ < τ₂) (hτ' : τ₂ < τ₃)
    (hκ : normalization hM.le γ τ₁ = 1) (hr₁ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₁ 1 = 0)
    (hr₂ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₂ 1 = 0)
    (hpos : ∀ τ ∈ Ioo τ₁ τ₂, 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hneg : ∀ τ ∈ Ioo τ₂ τ₃, deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 < 0)
    (hr₃ : (γ τ₃ : MinkowskiModel 3) 1 = (γ τ₁ : MinkowskiModel 3) 1)
    (hsmall : 2 * M * (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) +
      1 / (γ τ₂ : MinkowskiModel 3) 1) ≤ 1 / 4) :
    0 ≤ sweptAngle γ τ₁ τ₃ - 2 * π - 3 * π * M *
        (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ∧
      sweptAngle γ τ₁ τ₃ - 2 * π - 3 * π * M *
          (1 / (γ τ₁ : MinkowskiModel 3) 1 + 1 / (γ τ₂ : MinkowskiModel 3) 1) ≤
        4 * π * M ^ 2 *
          (2 * (1 / (γ τ₁ : MinkowskiModel 3) 1) + 1 / (γ τ₂ : MinkowskiModel 3) 1) ^ 2 :=
  perihelion_advance_between_perihelia hM x₀ hγ hsc h₁ h₂ h₃ hτ hτ' hκ hr₁ hr₂ hpos hneg hr₃ hsmall

end ProjectAinos.GeneralRelativity.SchwarzschildExterior

end Perihelion

section LightDeflection


open Set Filter MeasureTheory

open scoped Real ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski

open Mechanics.Scattering Mechanics.Scattering.SmallAngle

variable {M : ℝ}

example (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M) (τ : ℝ) :
    ℝ :=
  impactParameter hM x₀ γ τ

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) (hκ : normalization hM γ τ₀ = 0) (hE : energy hM x₀ γ τ₀ ≠ 0) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
        (2 * M / impactParameter hM x₀ γ τ₀) ((γ τ : MinkowskiModel 3) 1) :=
  radial_sq_eq_speedSq hM x₀ hγ hs h₀ hτ hκ hE

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hs : Convex ℝ s) {τ₀ τ : ℝ} (h₀ : τ₀ ∈ s)
    (hτ : τ ∈ s) (hκ : normalization hM γ τ₀ = 0) (hE : energy hM x₀ γ τ₀ ≠ 0) :
    deriv (fun t => (γ t : MinkowskiModel 3)) τ 1 ^ 2 =
      energy hM x₀ γ τ₀ ^ 2 * radicand (fun u => -u ^ 3)
        (2 * M / impactParameter hM x₀ γ τ₀,
          impactParameter hM x₀ γ τ₀ / (γ τ : MinkowskiModel 3) 1) :=
  radial_sq_eq_light hM x₀ hγ hs h₀ hτ hκ hE

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    {τ₀ : ℝ} (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0) (hE : 0 < energy hM x₀ γ τ₀)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) :
    IntegrableOn (angleDensity (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
        (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
          (2 * M / impactParameter hM x₀ γ τ₀))) (Ioi ((γ τ₀ : MinkowskiModel 3) 1)) ∧
      Tendsto (fun τ => sweptAngle γ τ₀ τ) atTop
        (𝓝 (∫ r in Ioi ((γ τ₀ : MinkowskiModel 3) 1),
          angleDensity (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
            (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
              (2 * M / impactParameter hM x₀ γ τ₀)) r)) :=
  tendsto_sweptAngle_atTop hM x₀ hγ hso hsc hs hκ hE hv hinf

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hso : IsOpen s) (hsc : Convex ℝ s)
    {τ₀ : ℝ} (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0) (hE : 0 < energy hM x₀ γ τ₀)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) :
    Tendsto (fun τ => 2 * sweptAngle γ τ₀ τ) atTop
      (𝓝 (π - deflectionAngle (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
        (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
          (2 * M / impactParameter hM x₀ γ τ₀)) ((γ τ₀ : MinkowskiModel 3) 1))) :=
  tendsto_two_mul_sweptAngle_atTop hM x₀ hγ hso hsc hs hκ hE hv hinf

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₀ : ℝ}
    (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0) (hE : 0 < energy hM x₀ γ τ₀)
    (hL : 0 < angularMomentumSq hM x₀ γ τ₀)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) {u : ℝ}
    (hu : u ∈ Ico 0 (impactParameter hM x₀ γ τ₀ / (γ τ₀ : MinkowskiModel 3) 1)) :
    0 < radicand (fun u => -u ^ 3) (2 * M / impactParameter hM x₀ γ τ₀, u) :=
  radicand_pos_light hM x₀ hγ hsc hs hκ hE hL hv hinf hu

example (hM : 0 ≤ M) (x₀ : domain M) {γ : ℝ → domain M} {s : Set ℝ}
    (hγ : (metric hM).toLorentzMetric.IsGeodesicOn s γ) (hsc : Convex ℝ s) {τ₀ : ℝ}
    (hs : Ici τ₀ ⊆ s) (hκ : normalization hM γ τ₀ = 0) (hE : 0 < energy hM x₀ γ τ₀)
    (hL : 0 < angularMomentumSq hM x₀ γ τ₀)
    (hr₀ : deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0)
    (hv : ∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1)
    (hinf : Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop) {c : ℝ}
    (hc : IsClosest (fun u => -u ^ 3) (2 * M / impactParameter hM x₀ γ τ₀) c) :
    c = impactParameter hM x₀ γ τ₀ / (γ τ₀ : MinkowskiModel 3) 1 :=
  closest_eq hM x₀ hγ hsc hs hκ hE hL hr₀ hv hinf hc

example :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
      (s : Set ℝ) (τ₀ : ℝ), (metric hM).toLorentzMetric.IsGeodesicOn s γ → Convex ℝ s →
      Ici τ₀ ⊆ s → normalization hM γ τ₀ = 0 → 0 < energy hM x₀ γ τ₀ →
      0 < angularMomentumSq hM x₀ γ τ₀ →
      deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0 →
      (∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) →
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop →
      2 * M / impactParameter hM x₀ γ τ₀ ≤ δ →
      IsClosest (fun u => -u ^ 3) (2 * M / impactParameter hM x₀ γ τ₀)
        (impactParameter hM x₀ γ τ₀ / (γ τ₀ : MinkowskiModel 3) 1) :=
  exists_isClosest_light

example :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (M : ℝ) (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
      (s : Set ℝ) (τ₀ : ℝ), (metric hM).toLorentzMetric.IsGeodesicOn s γ → Convex ℝ s →
      Ici τ₀ ⊆ s → normalization hM γ τ₀ = 0 → 0 < energy hM x₀ γ τ₀ →
      0 < angularMomentumSq hM x₀ γ τ₀ →
      deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0 →
      (∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) →
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop →
      2 * M / impactParameter hM x₀ γ τ₀ ≤ δ →
      |deflectionAngle (impactParameter hM x₀ γ τ₀ * energy hM x₀ γ τ₀)
          (speedSq (fun u => -u ^ 3) (impactParameter hM x₀ γ τ₀) (energy hM x₀ γ τ₀)
            (2 * M / impactParameter hM x₀ γ τ₀)) ((γ τ₀ : MinkowskiModel 3) 1) +
        4 * M / impactParameter hM x₀ γ τ₀| ≤ C * (M / impactParameter hM x₀ γ τ₀) ^ 2 :=
  deflection_bound

example :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (M : ℝ) (hM : 0 ≤ M) (x₀ : domain M) (γ : ℝ → domain M)
      (s : Set ℝ) (τ₀ : ℝ), (metric hM).toLorentzMetric.IsGeodesicOn s γ → IsOpen s →
      Convex ℝ s → Ici τ₀ ⊆ s → normalization hM γ τ₀ = 0 → 0 < energy hM x₀ γ τ₀ →
      0 < angularMomentumSq hM x₀ γ τ₀ →
      deriv (fun t => (γ t : MinkowskiModel 3)) τ₀ 1 = 0 →
      (∀ τ, τ₀ < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) →
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop →
      2 * M / impactParameter hM x₀ γ τ₀ ≤ δ →
      ∃ Φ : ℝ, Tendsto (fun τ => sweptAngle γ τ₀ τ) atTop (𝓝 Φ) ∧
        |2 * Φ - π - 4 * M / impactParameter hM x₀ γ τ₀| ≤
          C * (M / impactParameter hM x₀ γ τ₀) ^ 2 :=
  deflection_bound_sweptAngle

example :
    ∃ (x₀ : domain 0) (γ : ℝ → domain 0),
      (metric (le_refl (0 : ℝ))).toLorentzMetric.IsGeodesicOn univ γ ∧
      normalization (le_refl (0 : ℝ)) γ 0 = 0 ∧ energy (le_refl (0 : ℝ)) x₀ γ 0 = 1 ∧
      angularMomentumSq (le_refl (0 : ℝ)) x₀ γ 0 = 1 ∧
      deriv (fun t => (γ t : MinkowskiModel 3)) 0 1 = 0 ∧
      (∀ τ, 0 < τ → 0 < deriv (fun t => (γ t : MinkowskiModel 3)) τ 1) ∧
      Tendsto (fun τ => (γ τ : MinkowskiModel 3) 1) atTop atTop ∧
      Tendsto (fun τ => sweptAngle γ 0 τ) atTop (𝓝 (π / 2)) :=
  exists_ray_zero_mass

end ProjectAinos.GeneralRelativity.SchwarzschildExterior

end LightDeflection

section EquatorialComparison


namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian

open SmoothAlgebra SmoothRing FreeSmoothRing Mechanics SmoothGeometry

open Set TopologicalSpace

open scoped ContDiff Matrix

variable {d : ℕ}

example (x : Fin (d + 1) → TimeFunction) (τ : ℝ) :
    (⊤ : Opens (MinkowskiModel d)) :=
  coordinateCurve x τ

example (x : Fin (d + 1) → TimeFunction) (τ : ℝ) :
    (coordinateCurve x τ : MinkowskiModel d) = fun μ => x μ (fun _ => τ) :=
  coordinateCurve_val x τ

example (x : Fin (d + 1) → TimeFunction) :
    ContDiff ℝ ∞ (fun τ => (coordinateCurve x τ : MinkowskiModel d)) :=
  contDiff_coordinateCurve x

example (x : Fin (d + 1) → TimeFunction) :
    deriv (fun τ => (coordinateCurve x τ : MinkowskiModel d)) =
      fun τ => (coordinateCurve (fun μ => timeDerivative (x μ)) τ : MinkowskiModel d) :=
  deriv_coordinateCurve x

example (x : Fin (d + 1) → TimeFunction) (s : FreeSmoothRing (Fin (d + 1))) (τ : ℝ) :
    lift x s (fun _ => τ) = s.val (coordinateCurve x τ : MinkowskiModel d) :=
  lift_apply_coordinateCurve x s τ

example (a : Fin (d + 1)) (s : FreeSmoothRing (Fin (d + 1))) (z : MinkowskiModel d) :
    (partialDerivation a s).val z =
      fderiv ℝ (s.val : MinkowskiModel d → ℝ) z (Pi.single a 1) :=
  val_partialDerivation a s z

example (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1))) (μ α β : Fin (d + 1))
    (z : MinkowskiModel d) :
    (christoffelLower gm μ α β).val z = 1 / 2 *
      (fderiv ℝ ((gm μ β).val : MinkowskiModel d → ℝ) z (Pi.single α 1) +
        fderiv ℝ ((gm μ α).val : MinkowskiModel d → ℝ) z (Pi.single β 1) -
        fderiv ℝ ((gm α β).val : MinkowskiModel d → ℝ) z (Pi.single μ 1)) :=
  val_christoffelLower gm μ α β z

variable {σ : LorentzConvention}

example (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (g : CoordinateMetric σ d ⊤) (hg : ∀ y μ ν, g.coefficient y μ ν = (gm μ ν).val y)
    (y : MinkowskiModel d) (k i j : Fin (d + 1)) :
    CoordinateMetric.christoffelOf g.coefficient y k i j =
      ∑ l, (g.coefficient y)⁻¹ k l * (christoffelLower gm l i j).val y :=
  christoffelOf_eq_sum_christoffelLower gm g hg y k i j

example (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (g : CoordinateMetric σ d ⊤) (hg : ∀ y μ ν, g.coefficient y μ ν = (gm μ ν).val y)
    (x : Fin (d + 1) → TimeFunction) :
    IsCoordinateGeodesic gm x ↔ g.toLorentzMetric.IsGeodesicOn univ (coordinateCurve x) :=
  isCoordinateGeodesic_iff_isGeodesicOn gm g hg x

example (gm : Fin (d + 1) → Fin (d + 1) → FreeSmoothRing (Fin (d + 1)))
    (g : CoordinateMetric σ d ⊤) (hg : ∀ y μ ν, g.coefficient y μ ν = (gm μ ν).val y)
    (x : Fin (d + 1) → TimeFunction) (μ : Fin (d + 1)) (τ : ℝ) :
    (∑ ν, lift x (gm μ ν) * timeDerivative (x ν)) (fun _ => τ) =
      g.toLorentzMetric.form (coordinateCurve x τ)
        (LorentzMetric.chartField (CoordinateMetric.physicalChart (coordinateCurve x τ))
          (Pi.single μ 1) (coordinateCurve x τ))
        (LorentzMetric.curveVelocity (coordinateCurve x) τ) :=
  sum_lift_mul_timeDerivative_apply gm g hg x μ τ

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian

namespace ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics SmoothGeometry

open Set TopologicalSpace

open scoped ContDiff

variable {M : ℝ}

example (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    Fin 3 → ℝ :=
  diagonalCoefficient hM y

example (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    diagonalCoefficient hM y 0 = -(Real.exp (y 1) / radius M (y 1)) :=
  diagonalCoefficient_zero hM y

example (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    diagonalCoefficient hM y 1 = Real.exp (y 1) * radius M (y 1) :=
  diagonalCoefficient_one hM y

example (hM : 0 ≤ M) (y : MinkowskiModel 2) :
    diagonalCoefficient hM y 2 = radius M (y 1) ^ 2 :=
  diagonalCoefficient_two hM y

example (hM : 0 ≤ M) (μ : Fin 3) :
    ContDiff ℝ ∞ (fun y => diagonalCoefficient hM y μ) :=
  contDiff_diagonalCoefficient hM μ

example (hM : 0 ≤ M) :
    CoordinateMetric .timeNegative 2 ⊤ :=
  equatorialMetric hM

example (hM : 0 ≤ M) (y : MinkowskiModel 2) (μ ν : Fin 3) :
    (equatorialMetric hM).coefficient y μ ν = (metric hM μ ν).val y :=
  coefficient_equatorialMetric hM y μ ν

example (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) (μ ν : Fin 3) (τ : ℝ) :
    lift x (metric hM μ ν) (fun _ => τ) =
      (equatorialMetric hM).coefficient (coordinateCurve x τ) μ ν :=
  lift_metric_apply hM x μ ν τ

example (hM : 0 ≤ M) (x : Fin 3 → TimeFunction) :
    IsCoordinateGeodesic (metric hM) x ↔
      (equatorialMetric hM).toLorentzMetric.IsGeodesicOn univ (coordinateCurve x) :=
  isCoordinateGeodesic_iff hM x

example (hM : 0 ≤ M) (c : Fin 3 ⊕ Fin 3 → TimeFunction) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c ↔
      (∀ μ, c (Sum.inr μ) =
        ∑ ν, lift (position c) (metric hM μ ν) * timeDerivative (position c ν)) ∧
        (equatorialMetric hM).toLorentzMetric.IsGeodesicOn univ
          (coordinateCurve (position c)) :=
  isTrajectory_iff_isGeodesicOn hM c

example (hM : 0 ≤ M) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM)) c) (μ : Fin 3) (τ : ℝ) :
    c (Sum.inr μ) (fun _ => τ) =
      (equatorialMetric hM).toLorentzMetric.form (coordinateCurve (position c) τ)
        (LorentzMetric.chartField
          (CoordinateMetric.physicalChart (coordinateCurve (position c) τ))
          (Pi.single μ 1) (coordinateCurve (position c) τ))
        (LorentzMetric.curveVelocity (coordinateCurve (position c)) τ) :=
  momentum_apply hM h μ τ

example (hM : 0 ≤ M) (y : MinkowskiModel 2) (μ : Fin 3) :
    diagonalCoefficient hM y μ ≠ 0 :=
  diagonalCoefficient_ne_zero hM y μ

example (s₀ a b : ℝ) :
    Fin 3 → TimeFunction :=
  circularCurve s₀ a b

example (s₀ a b τ : ℝ) :
    (coordinateCurve (circularCurve s₀ a b) τ : MinkowskiModel 2) =
      ![0, s₀, 0] + τ • ![a, 0, b] :=
  coordinateCurve_circularCurve s₀ a b τ

example (hM : 0 ≤ M) {s₀ a b : ℝ} (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) :
    (equatorialMetric hM).toLorentzMetric.IsGeodesicOn univ
      (coordinateCurve (circularCurve s₀ a b)) :=
  isGeodesicOn_circularCurve hM h

example (hM : 0 ≤ M) {s₀ a b : ℝ} (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) :
    IsCoordinateGeodesic (metric hM) (circularCurve s₀ a b) :=
  isCoordinateGeodesic_circularCurve hM h

example (hM : 0 ≤ M) {s₀ a b : ℝ} (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM))
      (Sum.elim (circularCurve s₀ a b) fun μ => algebraMap ℝ TimeFunction
        (![-(Real.exp s₀ / radius M s₀) * a, 0, radius M s₀ ^ 2 * b] μ)) :=
  isTrajectory_circular hM h

example (hM : 0 ≤ M) {s₀ a b : ℝ} (h : b ^ 2 * radius M s₀ ^ 3 = M * a ^ 2) (τ : ℝ) :
    (equatorialMetric hM).toLorentzMetric.form (coordinateCurve (circularCurve s₀ a b) τ)
        (LorentzMetric.curveVelocity (coordinateCurve (circularCurve s₀ a b)) τ)
        (LorentzMetric.curveVelocity (coordinateCurve (circularCurve s₀ a b)) τ) =
      a ^ 2 * (3 * M - radius M s₀) / radius M s₀ :=
  form_curveVelocity_circularCurve hM h τ

example (hM : 0 ≤ M) (s₀ : ℝ) :
    Real.sqrt (M / radius M s₀ ^ 3) ^ 2 * radius M s₀ ^ 3 = M * 1 ^ 2 :=
  kepler_sq hM s₀

example (hM : 0 ≤ M) (s₀ : ℝ) :
    IsTrajectory (canonical (Fin 3)) (hamiltonian (inverse hM))
      (Sum.elim (circularCurve s₀ 1 (Real.sqrt (M / radius M s₀ ^ 3))) fun μ =>
        algebraMap ℝ TimeFunction (![-(Real.exp s₀ / radius M s₀) * 1, 0,
          radius M s₀ ^ 2 * Real.sqrt (M / radius M s₀ ^ 3)] μ)) :=
  isTrajectory_kepler hM s₀

end ProjectAinos.GeneralRelativity.GeodesicHamiltonian.SchwarzschildEquatorial

end EquatorialComparison
