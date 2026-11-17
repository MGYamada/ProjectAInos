/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.CentralField
public import ProjectAinos.Mechanics.Quadrature
public import ProjectAinos.Mechanics.TimePrimitive
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The orbit in a central field as integrals over the radius

Landau–Lifshitz (14.5)–(14.7). Along a trajectory of the radial Hamiltonian
with the angular momentum `ℓ` and the energy `E`, the radius satisfies
`ṙ² = (2/m)(E − V) − ℓ²/m²r²`. On an interval of time where `ṙ > 0`,

* `sub_eq_integral_radius`: `t₁ − t₀ = ∫ dr / √((2/m)(E − V) − ℓ²/m²r²)`;
* `angle_sub_eq_integral_radius`:
  `φ(t₁) − φ(t₀) = ∫ (ℓ/mr²) dr / √((2/m)(E − V) − ℓ²/m²r²)`.

The potential energy `V` is a smooth function of `log r`.

The interval contains no turning point of the radial motion. The integrals
between two turning points, which give the angle between the apsides, are
improper and are not treated.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Mechanics.CentralField

open SmoothAlgebra SmoothRing FreeSmoothRing Set

variable {m ℓ : ℝ} {V : SmoothOperation 1} {y : Fin 1 ⊕ Fin 1 → TimeFunction}

/-! ### The radial velocity -/

/-- `∂/∂s` on the radial phase space. -/
def dQ : SmoothDerivation Radial Radial := partialDerivation (Sum.inl 0)

/-- `∂/∂p_s` on the radial phase space. -/
def dP : SmoothDerivation Radial Radial := partialDerivation (Sum.inr 0)

theorem dP_q : dP (PhaseSpace.q 0) = 0 := partialDerivation_generator_of_ne (by simp)

theorem dP_p : dP (PhaseSpace.p 0) = 1 := partialDerivation_generator_self _

theorem dQ_radius : dQ radius = radius := by
  rw [radius, apply_exp, PhaseSpace.q, dQ, partialDerivation_generator_self, mul_one]

theorem dP_radius : dP radius = 0 := by
  rw [radius, apply_exp, PhaseSpace.q, dP, partialDerivation_generator_of_ne (by simp), mul_zero]

theorem dP_radiusInv : dP radiusInv = 0 := by
  rw [radiusInv, apply_exp, map_neg, PhaseSpace.q, dP,
    partialDerivation_generator_of_ne (by simp), neg_zero, mul_zero]

/-- `{r, H} = p_r / m`: the radial velocity. -/
theorem canonical_radius_radialHamiltonian (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ) :
    (PhaseSpace.canonical (Fin 1)).bracket radius (radialHamiltonian m V ℓ) =
      algebraMap ℝ Radial m⁻¹ * radialMomentum := by
  have h2 : algebraMap ℝ Radial m⁻¹ =
      algebraMap ℝ Radial (m⁻¹ / 2) + algebraMap ℝ Radial (m⁻¹ / 2) := by
    rw [← map_add]
    congr 1
    ring
  have hH : dP (radialHamiltonian m V ℓ) =
      algebraMap ℝ Radial (m⁻¹ / 2) *
        (radiusInv * radiusInv * (PhaseSpace.p 0 + PhaseSpace.p 0)) := by
    change dP (algebraMap ℝ Radial (m⁻¹ / 2) * (radiusInv * radiusInv *
      (PhaseSpace.p 0 * PhaseSpace.p 0 + algebraMap ℝ Radial ℓ * algebraMap ℝ Radial ℓ)) +
        op V fun _ => PhaseSpace.q 0) = _
    simp only [map_add, SmoothDerivation.map_mul, SmoothDerivation.chain, Fin.sum_univ_one,
      SmoothDerivation.map_algebraMap, dP_p, dP_q, dP_radiusInv, smul_eq_mul, mul_zero,
      add_zero, mul_one]
  have hb : (PhaseSpace.canonical (Fin 1)).bracket radius (radialHamiltonian m V ℓ) =
      dQ radius * dP (radialHamiltonian m V ℓ) - dP radius * dQ (radialHamiltonian m V ℓ) := by
    rw [PhaseSpace.canonical_bracket, Fin.sum_univ_one]
    rfl
  rw [hb, dQ_radius, dP_radius, hH, zero_mul, sub_zero, radialMomentum]
  linear_combination (2 * algebraMap ℝ Radial (m⁻¹ / 2) * radiusInv * PhaseSpace.p 0) *
    radius_mul_radiusInv - (radiusInv * PhaseSpace.p 0) * h2

/-! ### Values along a trajectory -/

/-- The radius at the time `t`. -/
def radiusAt (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) : ℝ :=
  Real.exp (y (Sum.inl 0) fun _ => t)

/-- The radial velocity `p_r / m` at the time `t`. -/
def radialVelocityAt (m : ℝ) (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) : ℝ :=
  m⁻¹ * ((radiusAt y t)⁻¹ * y (Sum.inr 0) fun _ => t)

/-- The square of the radial velocity as a function of the radius `u`, for
the energy `E` and the angular momentum `ℓ`:
`(2/m)(E − V(log u)) − ℓ²/m²u²`. -/
def radialSpeedSq (m : ℝ) (V : SmoothOperation 1) (ℓ E u : ℝ) : ℝ :=
  2 / m * (E - V fun _ => Real.log u) - ℓ * ℓ / (m * m * (u * u))

theorem radiusAt_pos (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) : 0 < radiusAt y t :=
  Real.exp_pos _

theorem lift_radius_apply (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) :
    FreeSmoothRing.lift y radius (fun _ => t) = radiusAt y t := by
  rw [lift_curve_apply, radius, SmoothRingHom.map_exp, PhaseSpace.q, lift_generator]
  rfl

theorem lift_radiusInv_apply (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) :
    FreeSmoothRing.lift y radiusInv (fun _ => t) = (radiusAt y t)⁻¹ := by
  rw [lift_curve_apply, radiusInv, SmoothRingHom.map_exp, SmoothRingHom.map_neg, PhaseSpace.q,
    lift_generator, radiusAt, ← Real.exp_neg]
  rfl

/-- The energy at the time `t`. -/
theorem lift_radialHamiltonian_apply (m : ℝ) (V : SmoothOperation 1) (ℓ : ℝ)
    (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) :
    FreeSmoothRing.lift y (radialHamiltonian m V ℓ) (fun _ => t) =
      m⁻¹ / 2 * ((radiusAt y t)⁻¹ * (radiusAt y t)⁻¹ *
        ((y (Sum.inr 0) fun _ => t) * (y (Sum.inr 0) fun _ => t) + ℓ * ℓ)) +
        V fun _ => y (Sum.inl 0) fun _ => t := by
  have hi := lift_radiusInv_apply y t
  rw [lift_curve_apply] at hi
  rw [lift_curve_apply]
  change FreeSmoothRing.lift (fun a => y a fun _ => t)
    (algebraMap ℝ Radial (m⁻¹ / 2) * (radiusInv * radiusInv *
      (PhaseSpace.p 0 * PhaseSpace.p 0 + algebraMap ℝ Radial ℓ * algebraMap ℝ Radial ℓ)) +
        op V fun _ => PhaseSpace.q 0) = _
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    SmoothRingHom.map_op, hi, PhaseSpace.p, PhaseSpace.q, lift_generator]
  rfl

/-- The radial velocity is the derivative of the radius. -/
theorem hasDerivAt_radiusAt
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) (t : ℝ) :
    HasDerivAt (radiusAt y) (radialVelocityAt m y t) t := by
  have h := TimeFunction.hasDerivAt_apply_const (FreeSmoothRing.lift y radius) t
  have hf : (fun s : ℝ => FreeSmoothRing.lift y radius fun _ => s) = radiusAt y :=
    funext fun s => lift_radius_apply y s
  have hi := lift_radiusInv_apply y t
  rw [lift_curve_apply] at hi
  have hv : timeDerivative (FreeSmoothRing.lift y radius) (fun _ => t) =
      radialVelocityAt m y t := by
    rw [hy.timeDerivative_lift, canonical_radius_radialHamiltonian, lift_curve_apply,
      radialMomentum, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, hi, PhaseSpace.p, lift_generator, radialVelocityAt]
    rfl
  rw [hf, hv] at h
  exact h

theorem continuous_radialVelocityAt
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) :
    Continuous (radialVelocityAt m y) := by
  have h := TimeFunction.continuous_apply_const (timeDerivative (FreeSmoothRing.lift y radius))
  have hf : (fun s : ℝ => timeDerivative (FreeSmoothRing.lift y radius) fun _ => s) =
      radialVelocityAt m y :=
    funext fun s => (TimeFunction.hasDerivAt_apply_const _ s).unique (by
      have hr : (fun s : ℝ => FreeSmoothRing.lift y radius fun _ => s) = radiusAt y :=
        funext fun s => lift_radius_apply y s
      rw [hr]
      exact hasDerivAt_radiusAt hy s)
  rwa [hf] at h

/-- The radial equation (Landau–Lifshitz (14.5)):
`ṙ² = (2/m)(E − V) − ℓ²/m²r²`. -/
theorem radialVelocityAt_sq (hm : m ≠ 0) (V : SmoothOperation 1) (ℓ : ℝ)
    (y : Fin 1 ⊕ Fin 1 → TimeFunction) (t : ℝ) :
    radialVelocityAt m y t ^ 2 =
      radialSpeedSq m V ℓ (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t)
        (radiusAt y t) := by
  have hr := (radiusAt_pos y t).ne'
  have hlog : Real.log (radiusAt y t) = y (Sum.inl 0) fun _ => t := Real.log_exp _
  rw [lift_radialHamiltonian_apply, radialSpeedSq, radialVelocityAt, hlog]
  field_simp
  ring

theorem continuousOn_radialSpeedSq (hm : m ≠ 0) (V : SmoothOperation 1) (ℓ E : ℝ)
    {s : Set ℝ} (hs : ∀ u ∈ s, u ≠ 0) : ContinuousOn (radialSpeedSq m V ℓ E) s := by
  have hV : ContinuousOn (fun u : ℝ => V fun _ => Real.log u) s :=
    (TimeFunction.continuous_apply_const V).comp_continuousOn
      (Real.continuousOn_log.mono fun u hu => hs u hu)
  refine (continuousOn_const.mul (continuousOn_const.sub hV)).sub
    (continuousOn_const.div ((continuous_const.mul (continuous_id.mul continuous_id)).continuousOn)
      fun u hu => mul_ne_zero (mul_ne_zero hm hm) (mul_ne_zero (hs u hu) (hs u hu)))

/-! ### The orbit integrals -/

/-- The time as a function of the radius (Landau–Lifshitz (14.6)): on an
interval where the radial velocity is positive,
`t₁ − t₀ = ∫ dr / √((2/m)(E − V) − ℓ²/m²r²)`. -/
theorem sub_eq_integral_radius (hm : m ≠ 0)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) {t₀ t₁ : ℝ}
    (hpos : ∀ t ∈ uIcc t₀ t₁, 0 < radialVelocityAt m y t) :
    t₁ - t₀ = ∫ u in radiusAt y t₀..radiusAt y t₁,
      1 / √(radialSpeedSq m V ℓ
        (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t₀) u) :=
  sub_eq_integral_one_div_sqrt (fun t _ => hasDerivAt_radiusAt hy t)
    (continuous_radialVelocityAt hy).continuousOn hpos
    (fun t _ => by
      rw [radialVelocityAt_sq hm V ℓ y t, hy.lift_hamiltonian_eq (fun _ => t) fun _ => t₀])
    (continuousOn_radialSpeedSq hm V ℓ _ (by
      rintro _ ⟨t, _, rfl⟩
      exact (radiusAt_pos y t).ne'))

variable {x : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}

/-- The angular velocity at the time `t`: `φ̇ = ℓ/mr²`
(Landau–Lifshitz (14.3)). -/
theorem timeDerivative_angle_apply (hm : m ≠ 0)
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x)
    (hℓ : x (Sum.inr (Sum.inr 0)) = algebraMap ℝ TimeFunction ℓ) (t : ℝ) :
    timeDerivative (x (Sum.inl (Sum.inr 0))) (fun _ => t) =
      ℓ / (m * (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t *
        radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t)) := by
  have hr := (radiusAt_pos (fun a => x (Sum.map Sum.inl Sum.inl a)) t).ne'
  have hi : FreeSmoothRing.lift (fun a => x a fun _ => t) rInv =
      (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t)⁻¹ := by
    rw [rInv, SmoothRingHom.map_exp, SmoothRingHom.map_neg, s, PhaseSpace.q, lift_generator,
      radiusAt, ← Real.exp_neg]
    rfl
  have hp : FreeSmoothRing.lift (fun a => x a fun _ => t) pφ = ℓ := by
    rw [pφ, PhaseSpace.p, lift_generator, hℓ, TimeFunction.algebraMap_apply]
  rw [timeDerivative_angle hx, lift_curve_apply, SmoothRingHom.map_mul, SmoothRingHom.map_mul,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, hi, hp]
  change m⁻¹ * (_ * _ * ℓ) = _
  field_simp

/-- The angle as a function of the radius (Landau–Lifshitz (14.7)): along a
trajectory with the angular momentum `ℓ`, on an interval where the radial
velocity is positive,
`φ(t₁) − φ(t₀) = ∫ (ℓ/mr²) dr / √((2/m)(E − V) − ℓ²/m²r²)`. -/
theorem angle_sub_eq_integral_radius (hm : m ≠ 0)
    (hx : IsTrajectory (PhaseSpace.canonical (Fin 1 ⊕ Fin 1)) (polarHamiltonian m V) x)
    (hℓ : x (Sum.inr (Sum.inr 0)) = algebraMap ℝ TimeFunction ℓ) {t₀ t₁ : ℝ}
    (hpos : ∀ t ∈ uIcc t₀ t₁,
      0 < radialVelocityAt m (fun a => x (Sum.map Sum.inl Sum.inl a)) t) :
    (x (Sum.inl (Sum.inr 0)) fun _ => t₁) - (x (Sum.inl (Sum.inr 0)) fun _ => t₀) =
      ∫ u in radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₀..
          radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₁,
        ℓ / (m * (u * u)) / √(radialSpeedSq m V ℓ
          (FreeSmoothRing.lift (fun a => x (Sum.map Sum.inl Sum.inl a))
            (radialHamiltonian m V ℓ) fun _ => t₀) u) := by
  have hy := isTrajectory_radial hx hℓ
  have hφ (t : ℝ) := timeDerivative_angle_apply hm hx hℓ t
  rw [TimeFunction.apply_sub_apply_eq_integral]
  simp only [hφ]
  exact integral_comp_eq_integral_div_sqrt (w := fun u => ℓ / (m * (u * u)))
    (fun t _ => hasDerivAt_radiusAt hy t) (continuous_radialVelocityAt hy).continuousOn hpos
    (fun t _ => by
      rw [radialVelocityAt_sq hm V ℓ _ t, hy.lift_hamiltonian_eq (fun _ => t) fun _ => t₀])
    (continuousOn_radialSpeedSq hm V ℓ _ (by
      rintro _ ⟨t, _, rfl⟩
      exact (radiusAt_pos _ t).ne'))
    (continuousOn_const.div
      ((continuous_const.mul (continuous_id.mul continuous_id)).continuousOn) (by
        rintro _ ⟨t, _, rfl⟩
        exact mul_ne_zero hm (mul_ne_zero (radiusAt_pos _ t).ne' (radiusAt_pos _ t).ne')))

end ProjectAinos.Mechanics.CentralField
