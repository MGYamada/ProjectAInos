/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the central-field API: the exponential, the cosine and
the sine of an element of a C-infinity ring, polar co-ordinates as a canonical
transformation, the radial Hamiltonian as a reduction, the plane of the
motion, quadrature on an interval of monotone motion, and the orbit integrals.
Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.FreeSmoothRing ProjectAInos.Mechanics
open ProjectAInos.Mechanics.CentralField ProjectAInos.Mechanics.CyclicReduction
open Matrix Set

section Elementary

variable {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]

example (a : A) : ringCos a * ringCos a + ringSin a * ringSin a = 1 :=
  ringCos_mul_ringCos_add_ringSin_mul_ringSin a

example (d : SmoothDerivation A A) (a : A) : d (ringCos a) = -(ringSin a * d a) :=
  apply_ringCos d a

example (d : SmoothDerivation A A) (a : A) : d (ringSin a) = ringCos a * d a :=
  apply_ringSin d a

example (a : A) : exp a * exp (-a) = 1 := exp_mul_exp_neg a

end Elementary

section Polar

example : polarCoordinates (PhaseSpace.q 0) = r * cosφ := polarCoordinates_q_zero

example : polarCoordinates (PhaseSpace.q 1) = r * sinφ := polarCoordinates_q_one

example : polarCoordinates (PhaseSpace.p 0) = rInv * (pS * cosφ - pφ * sinφ) :=
  polarCoordinates_p_zero

example : polarCoordinates (PhaseSpace.p 1) = rInv * (pS * sinφ + pφ * cosφ) :=
  polarCoordinates_p_one

example : r * rInv = 1 := r_mul_rInv

/-- The polar co-ordinates are canonical. -/
example :
    IsPoissonHom (PhaseSpace.canonical (Fin 2)).toAlmostPoissonStructure
      (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).toAlmostPoissonStructure polarCoordinates :=
  isPoissonHom_polarCoordinates

example : polarCoordinates (PhaseSpace.p ⬝ᵥ PhaseSpace.p) =
    rInv * rInv * (pS * pS + pφ * pφ) :=
  polarCoordinates_p_sq

/-- The angular momentum is the momentum of the angle. -/
example : polarCoordinates (PhaseSpace.q 0 * PhaseSpace.p 1 - PhaseSpace.q 1 * PhaseSpace.p 0) =
    pφ :=
  polarCoordinates_angularMomentum

example (m : ℝ) (U : SmoothOperation 1) :
    CentralField.hamiltonian m U =
      algebraMap ℝ Plane (m⁻¹ / 2) * (PhaseSpace.p ⬝ᵥ PhaseSpace.p) +
        op U fun _ => PhaseSpace.q ⬝ᵥ PhaseSpace.q := rfl

example (m : ℝ) (V : SmoothOperation 1) :
    polarHamiltonian m V =
      algebraMap ℝ Polar (m⁻¹ / 2) * (rInv * rInv * (pS * pS + pφ * pφ)) + op V fun _ => s :=
  rfl

example (m : ℝ) (U : SmoothOperation 1) :
    polarCoordinates (CentralField.hamiltonian m U) = polarHamiltonian m (logPotential U) :=
  polarCoordinates_hamiltonian m U

/-- The angle is a cyclic co-ordinate. -/
example (m : ℝ) (V : SmoothOperation 1) (k : Fin 1) :
    partialDerivation (Sum.inl (Sum.inr k)) (polarHamiltonian m V) = 0 :=
  partialDerivation_polarHamiltonian m V k

end Polar

section Radial

/-- The radial Hamiltonian with the centrifugal energy. -/
example (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    radialHamiltonian m V ℓ =
      algebraMap ℝ Radial (m⁻¹ / 2) * (radialMomentum * radialMomentum) +
        algebraMap ℝ Radial (ℓ * ℓ * (m⁻¹ / 2)) * (radiusInv * radiusInv) +
        op V fun _ => PhaseSpace.q 0 :=
  radialHamiltonian_eq m V ℓ

example : (PhaseSpace.canonical (Fin 1)).bracket radius radialMomentum = 1 :=
  canonical_radius_radialMomentum

example : radius * radiusInv = 1 := radius_mul_radiusInv

/-- The class of the Hamiltonian in the reduced ring at `p_φ = ℓ`. -/
example (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    reductionHom (Fin 1) (fun _ : Fin 1 => ℓ) (radialHamiltonian m V ℓ) =
      (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)).reductionMap
        (momentumIdeal (Fin 1) fun _ : Fin 1 => ℓ)
        ⟨polarHamiltonian m V, polarHamiltonian_mem_normalizer m V ℓ⟩ :=
  reductionHom_radialHamiltonian m V ℓ

variable {m ℓ : ℝ} {U V : SmoothOperation 1}
  {x : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}

example
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1))
      (polarHamiltonian m (logPotential U)) x) :
    IsTrajectory (PhaseSpace.canonical (Fin 2)) (CentralField.hamiltonian m U)
      fun a => FreeSmoothRing.lift x (polarCoordinates (generator a)) :=
  isTrajectory_plane hx

/-- The radial motion. -/
example (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x)
    (hℓ : x (Sum.inr (Sum.inr 0)) = algebraMap ℝ TimeFunction ℓ) :
    IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ)
      fun a => x (Sum.map Sum.inl Sum.inl a) :=
  isTrajectory_radial hx hℓ

example (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x) :
    timeDerivative (x (Sum.inl (Sum.inr 0))) =
      FreeSmoothRing.lift x (algebraMap ℝ Polar m⁻¹ * (rInv * rInv * pφ)) :=
  timeDerivative_angle hx

/-- The orbit lies in a plane. -/
example (f : SmoothOperation 3) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory AngularMomentum.canonical (op f AngularMomentum.scalars) c) (t : ℝ) :
    ∑ a, (c (Sum.inl a) fun _ => t) *
      (FreeSmoothRing.lift c (AngularMomentum.M a) fun _ => 0) = 0 :=
  sum_q_mul_M_eq_zero f h t

end Radial

section Quadrature

/-- Quadrature on an interval of monotone motion. -/
example {r r' F w : ℝ → ℝ} {t₀ t₁ : ℝ}
    (hr : ∀ t ∈ uIcc t₀ t₁, HasDerivAt r (r' t) t) (hr' : ContinuousOn r' (uIcc t₀ t₁))
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < r' t) (hF : ∀ t ∈ uIcc t₀ t₁, r' t ^ 2 = F (r t))
    (hFc : ContinuousOn F (r '' uIcc t₀ t₁)) (hw : ContinuousOn w (r '' uIcc t₀ t₁)) :
    ∫ t in t₀..t₁, w (r t) = ∫ u in r t₀..r t₁, w u / √(F u) :=
  integral_comp_eq_integral_div_sqrt hr hr' hpos hF hFc hw

/-- Motion in one dimension. -/
example {x x' U : ℝ → ℝ} {m E t₀ t₁ : ℝ} (hm : 0 < m)
    (hx : ∀ t ∈ uIcc t₀ t₁, HasDerivAt x (x' t) t) (hx' : ContinuousOn x' (uIcc t₀ t₁))
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < x' t)
    (hE : ∀ t ∈ uIcc t₀ t₁, m / 2 * x' t ^ 2 + U (x t) = E)
    (hU : ContinuousOn U (x '' uIcc t₀ t₁)) :
    t₁ - t₀ = √(m / 2) * ∫ u in x t₀..x t₁, 1 / √(E - U u) :=
  sub_eq_sqrt_mul_integral_of_energy hm hx hx' hpos hE hU

variable {m ℓ : ℝ} {V : SmoothOperation 1}

example (m : ℝ) (V : SmoothOperation 1) (ℓ E u : ℝ) :
    radialSpeedSq m V ℓ E u = 2 / m * (E - V fun _ => Real.log u) - ℓ * ℓ / (m * m * (u * u)) :=
  rfl

example (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) :
    radiusAt y t = Real.exp (y (Sum.inl 0) fun _ => t) := rfl

example (m : ℝ) (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) :
    radialVelocityAt m y t = m⁻¹ * ((radiusAt y t)⁻¹ * y (Sum.inr 0) fun _ => t) := rfl

/-- The radial velocity is the derivative of the radius. -/
example {y : Fin 1 ⊕ Fin 1 → TimeFunction}
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) (t : ℝ) :
    HasDerivAt (radiusAt y) (radialVelocityAt m y t) t :=
  hasDerivAt_radiusAt hy t

/-- The radial equation. -/
example (hm : m ≠ 0) (V : SmoothOperation 1) (ℓ : ℝ) (y : Fin 1 ⊕ Fin 1 → TimeFunction)
    (t : ℝ) :
    radialVelocityAt m y t ^ 2 =
      radialSpeedSq m V ℓ (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t)
        (radiusAt y t) :=
  radialVelocityAt_sq hm V ℓ y t

/-- The time as an integral over the radius. -/
example (hm : m ≠ 0) {y : Fin 1 ⊕ Fin 1 → TimeFunction}
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) {t₀ t₁ : ℝ}
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < radialVelocityAt m y t) :
    t₁ - t₀ = ∫ u in radiusAt y t₀..radiusAt y t₁,
      1 / √(radialSpeedSq m V ℓ
        (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t₀) u) :=
  sub_eq_integral_radius hm hy hpos

/-- The angle as an integral over the radius. -/
example (hm : m ≠ 0) {x : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x)
    (hℓ : x (Sum.inr (Sum.inr 0)) = algebraMap ℝ TimeFunction ℓ) {t₀ t₁ : ℝ}
    (hpos : ∀ t ∈ uIcc t₀ t₁,
      0 < radialVelocityAt m (fun a => x (Sum.map Sum.inl Sum.inl a)) t) :
    (x (Sum.inl (Sum.inr 0)) fun _ => t₁) - (x (Sum.inl (Sum.inr 0)) fun _ => t₀) =
      ∫ u in radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₀..
          radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁,
        ℓ / (m * (u * u)) / √(radialSpeedSq m V ℓ
          (FreeSmoothRing.lift (fun a => x (Sum.map Sum.inl Sum.inl a))
            (radialHamiltonian m V ℓ) fun _ => t₀) u) :=
  angle_sub_eq_integral_radius hm hx hℓ hpos

end Quadrature
