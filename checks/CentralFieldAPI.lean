/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos

/-! Public consumers of the central-field API: the exponential, the cosine and
the sine of an element of a C-infinity ring, polar co-ordinates as a canonical
transformation, the radial Hamiltonian as a reduction, the plane of the
motion, quadrature on an interval of monotone motion, the orbit integrals,
quadrature up to simple turning points, the motion between two apsides and
the period of Kepler's problem.
Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAinos.SmoothAlgebra ProjectAinos.SmoothAlgebra.SmoothRing
open ProjectAinos.SmoothAlgebra.FreeSmoothRing ProjectAinos.Mechanics
open ProjectAinos.Mechanics.CentralField ProjectAinos.Mechanics.CyclicReduction
open Matrix Set
open scoped Real

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

section TurningPoints

example (u₁ u₂ θ : ℝ) :
    turningParam u₁ u₂ θ = (u₁ + u₂) / 2 + (u₂ - u₁) / 2 * Real.cos θ := rfl

/-- The regularization of the integral between two simple turning points. -/
example {u₁ u₂ : ℝ} (h : u₁ < u₂) (w G : ℝ → ℝ) :
    ∫ u in u₁..u₂, w u / √((u - u₁) * (u₂ - u) * G u) =
      ∫ θ in (0 : ℝ)..π, w (turningParam u₁ u₂ θ) / √(G (turningParam u₁ u₂ θ)) :=
  integral_div_sqrt_turning h w G

/-- The integrand is integrable between simple turning points. -/
example {u₁ u₂ : ℝ} (h : u₁ < u₂) {w G : ℝ → ℝ} (hw : ContinuousOn w (Icc u₁ u₂))
    (hG : ContinuousOn G (Icc u₁ u₂)) (hGpos : ∀ u ∈ Icc u₁ u₂, 0 < G u) :
    MeasureTheory.IntegrableOn (fun u => w u / √((u - u₁) * (u₂ - u) * G u)) (Icc u₁ u₂) :=
  integrableOn_div_sqrt_turning h hw hG hGpos

/-- Quadrature up to the turning points. -/
example {x x' w G : ℝ → ℝ} {t₁ t₂ u₁ u₂ : ℝ} (ht : t₁ < t₂) (hu : u₁ < u₂)
    (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < x' t)
    (h₁ : x t₁ = u₁) (h₂ : x t₂ = u₂)
    (hF : ∀ t ∈ Ioo t₁ t₂, x' t ^ 2 = (x t - u₁) * (u₂ - x t) * G (x t))
    (hw : ContinuousOn w (Icc u₁ u₂)) (hG : ContinuousOn G (Icc u₁ u₂))
    (hGpos : ∀ u ∈ Icc u₁ u₂, 0 < G u) :
    ∫ t in t₁..t₂, w (x t) = ∫ u in u₁..u₂, w u / √((u - u₁) * (u₂ - u) * G u) :=
  integral_comp_eq_integral_div_sqrt_turning ht hu hx hpos h₁ h₂ hF hw hG hGpos

/-- The time between two turning points, Landau–Lifshitz (11.5). -/
example {x x' U W : ℝ → ℝ} {m E t₁ t₂ u₁ u₂ : ℝ} (hm : 0 < m) (ht : t₁ < t₂) (hu : u₁ < u₂)
    (hx : ∀ t ∈ Icc t₁ t₂, HasDerivAt x (x' t) t) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < x' t)
    (h₁ : x t₁ = u₁) (h₂ : x t₂ = u₂)
    (hE : ∀ t ∈ Ioo t₁ t₂, m / 2 * x' t ^ 2 + U (x t) = E)
    (hU : ∀ u ∈ Icc u₁ u₂, E - U u = (u - u₁) * (u₂ - u) * W u)
    (hW : ContinuousOn W (Icc u₁ u₂)) (hWpos : ∀ u ∈ Icc u₁ u₂, 0 < W u) :
    t₂ - t₁ = √(m / 2) * ∫ u in u₁..u₂, 1 / √(E - U u) :=
  sub_eq_sqrt_mul_integral_of_energy_turning hm ht hu hx hpos h₁ h₂ hE hU hW hWpos

/-- The formula gives the half period of the oscillator. -/
example {m ω a : ℝ} (hm : 0 < m) (hω : 0 < ω) (ha : 0 < a) :
    √(m / 2) * ∫ u in -a..a, 1 / √(m * ω ^ 2 / 2 * a ^ 2 - m * ω ^ 2 / 2 * u ^ 2) = π / ω :=
  sqrt_mul_integral_oscillator hm hω ha

/-- The hypotheses hold for the motion `−a cos ωt` of the oscillator. -/
example {m ω a : ℝ} (hm : 0 < m) (hω : 0 < ω) (ha : 0 < a) :
    π / ω - 0 =
      √(m / 2) * ∫ u in -a..a, 1 / √(m * ω ^ 2 / 2 * a ^ 2 - m * ω ^ 2 / 2 * u ^ 2) :=
  sub_eq_sqrt_mul_integral_oscillator hm hω ha

end TurningPoints

section Apsides

variable {m ℓ α : ℝ} {V : SmoothOperation 1} {y : Fin 1 ⊕ Fin 1 → TimeFunction}

/-- The time between two apsides as a regular integral. -/
example (hm : m ≠ 0)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) {t₁ t₂ : ℝ}
    (ht : t₁ < t₂) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t) {G : ℝ → ℝ}
    (hF : ∀ u, 0 < u →
      radialSpeedSq m V ℓ (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t₁) u =
        (u - radiusAt y t₁) * (radiusAt y t₂ - u) * G u)
    (hG : ContinuousOn G (Icc (radiusAt y t₁) (radiusAt y t₂)))
    (hGpos : ∀ u ∈ Icc (radiusAt y t₁) (radiusAt y t₂), 0 < G u) :
    t₂ - t₁ = ∫ θ in (0 : ℝ)..π,
      1 / √(G (turningParam (radiusAt y t₁) (radiusAt y t₂) θ)) :=
  sub_eq_integral_turningParam_radius hm hy ht hpos hF hG hGpos

example (α E : ℝ) {u : ℝ} (hu : 0 < u) :
    radialSpeedSq m (keplerPotential α) ℓ E u =
      2 / m * (E + α / u) - ℓ * ℓ / (m * m * (u * u)) :=
  radialSpeedSq_kepler m α ℓ E hu

/-- Kepler's problem: the time from one apsis to the next. -/
example (hm : 0 < m) (hα : 0 < α)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1))
      (radialHamiltonian m (keplerPotential α) ℓ) y) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t)
    (h₁ : radialVelocityAt m y t₁ = 0) (h₂ : radialVelocityAt m y t₂ = 0) :
    t₂ - t₁ = π * ((radiusAt y t₁ + radiusAt y t₂) / 2) *
      √(m * ((radiusAt y t₁ + radiusAt y t₂) / 2) / α) :=
  kepler_sub_eq hm hα hy ht hpos h₁ h₂

/-- The period of an elliptic orbit, Landau–Lifshitz (15.8). -/
example (hm : 0 < m) (hα : 0 < α)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1))
      (radialHamiltonian m (keplerPotential α) ℓ) y) {t₁ t₂ t₃ : ℝ} (h12 : t₁ < t₂)
    (h23 : t₂ < t₃) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t)
    (hneg : ∀ t ∈ Ioo t₂ t₃, radialVelocityAt m y t < 0)
    (h₁ : radialVelocityAt m y t₁ = 0) (h₂ : radialVelocityAt m y t₂ = 0)
    (h₃ : radialVelocityAt m y t₃ = 0) :
    radiusAt y t₃ = radiusAt y t₁ ∧
      t₃ - t₁ = 2 * π * ((radiusAt y t₁ + radiusAt y t₂) / 2) *
        √(m * ((radiusAt y t₁ + radiusAt y t₂) / 2) / α) :=
  kepler_period hm hα hy h12 h23 hpos hneg h₁ h₂ h₃

/-- The angle described between two apsides, Landau–Lifshitz (14.10). -/
example {x : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction} (hm : m ≠ 0)
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x)
    (hℓ : x (Sum.inr (Sum.inr 0)) = algebraMap ℝ TimeFunction ℓ) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hpos : ∀ t ∈ Ioo t₁ t₂,
      0 < radialVelocityAt m (fun a => x (Sum.map Sum.inl Sum.inl a)) t) {G : ℝ → ℝ}
    (hF : ∀ u, 0 < u →
      radialSpeedSq m V ℓ (FreeSmoothRing.lift (fun a => x (Sum.map Sum.inl Sum.inl a))
          (radialHamiltonian m V ℓ) fun _ => t₁) u =
        (u - radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁) *
          (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂ - u) * G u)
    (hG : ContinuousOn G (Icc (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁)
      (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂)))
    (hGpos : ∀ u ∈ Icc (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁)
      (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂), 0 < G u) :
    (x (Sum.inl (Sum.inr 0)) fun _ => t₂) - (x (Sum.inl (Sum.inr 0)) fun _ => t₁) =
      ∫ θ in (0 : ℝ)..π,
        ℓ / (m * (turningParam (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁)
            (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂) θ *
          turningParam (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁)
            (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂) θ)) /
        √(G (turningParam (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁)
          (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂) θ)) :=
  angle_sub_eq_integral_turningParam_radius hm hx hℓ ht hpos hF hG hGpos

end Apsides
