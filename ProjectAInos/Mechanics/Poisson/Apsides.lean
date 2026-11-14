/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.OrbitIntegral
public import ProjectAInos.Mechanics.TurningPoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The motion between two apsides

An apsis of the radial motion is a time at which the radial velocity
vanishes. Between two apsides `r₁ < r₂` at which the square of the radial
velocity has simple zeros, `ṙ² = (r − r₁)(r₂ − r) G(r)` with `G > 0`,

* `sub_eq_integral_turningParam_radius`: the time is
  `∫₀^π dθ / √G(r(θ))`, with `r(θ) = (r₁ + r₂)/2 + (r₂ − r₁)/2 · cos θ`;
* `angle_sub_eq_integral_turningParam_radius`: the angle described is
  `∫₀^π (ℓ/m r(θ)²) dθ / √G(r(θ))` (Landau–Lifshitz (14.10)).

For Kepler's problem, `V = −α/r`, the energy and the angular momentum are
determined by the apsides, `G(r) = 2α/(m (r₁ + r₂) r²)`, and

* `kepler_sub_eq`, `kepler_sub_eq_of_neg`: the time from one apsis to the
  next is `π a √(m a/α)` with `a = (r₁ + r₂)/2`;
* `kepler_period`: the time between two passages through the perihelion is
  `2π a √(m a/α) = 2π a^{3/2} √(m/α)`, Landau–Lifshitz (15.8). It depends on
  the semi-major axis only.

The statements are for a given trajectory. The parameter `θ` is the eccentric
anomaly, up to the direction in which it is counted.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.CentralField

open SmoothAlgebra SmoothRing FreeSmoothRing Set
open scoped Real

variable {m ℓ : ℝ} {V : SmoothOperation 1} {y : Fin 1 ⊕ Fin 1 → TimeFunction}

/-- Quadrature between two apsides: if the square of the radial velocity is
`(r − r₁)(r₂ − r) G(r)` with `G > 0`, then
`∫ w(r(t)) dt = ∫₀^π w(r(θ)) dθ / √G(r(θ))`. -/
theorem integral_comp_radiusAt_eq_integral_turningParam (hm : m ≠ 0)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) {t₁ t₂ : ℝ}
    (ht : t₁ < t₂) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t) {w G : ℝ → ℝ}
    (hF : ∀ u, 0 < u →
      radialSpeedSq m V ℓ (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t₁) u =
        (u - radiusAt y t₁) * (radiusAt y t₂ - u) * G u)
    (hw : ContinuousOn w (Icc (radiusAt y t₁) (radiusAt y t₂)))
    (hG : ContinuousOn G (Icc (radiusAt y t₁) (radiusAt y t₂)))
    (hGpos : ∀ u ∈ Icc (radiusAt y t₁) (radiusAt y t₂), 0 < G u) :
    ∫ t in t₁..t₂, w (radiusAt y t) =
      ∫ θ in (0 : ℝ)..π, w (turningParam (radiusAt y t₁) (radiusAt y t₂) θ) /
        √(G (turningParam (radiusAt y t₁) (radiusAt y t₂) θ)) := by
  have hlt : radiusAt y t₁ < radiusAt y t₂ :=
    lt_of_hasDerivAt_pos ht (fun t _ => hasDerivAt_radiusAt hy t) hpos
  rw [← integral_div_sqrt_turning hlt w G]
  exact integral_comp_eq_integral_div_sqrt_turning ht hlt (fun t _ => hasDerivAt_radiusAt hy t)
    hpos rfl rfl
    (fun t _ => by
      rw [radialVelocityAt_sq hm V ℓ y t, hy.lift_hamiltonian_eq (fun _ => t) fun _ => t₁,
        hF _ (radiusAt_pos y t)])
    hw hG hGpos

/-- The time between two apsides as a regular integral. -/
theorem sub_eq_integral_turningParam_radius (hm : m ≠ 0)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) {t₁ t₂ : ℝ}
    (ht : t₁ < t₂) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t) {G : ℝ → ℝ}
    (hF : ∀ u, 0 < u →
      radialSpeedSq m V ℓ (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t₁) u =
        (u - radiusAt y t₁) * (radiusAt y t₂ - u) * G u)
    (hG : ContinuousOn G (Icc (radiusAt y t₁) (radiusAt y t₂)))
    (hGpos : ∀ u ∈ Icc (radiusAt y t₁) (radiusAt y t₂), 0 < G u) :
    t₂ - t₁ = ∫ θ in (0 : ℝ)..π,
      1 / √(G (turningParam (radiusAt y t₁) (radiusAt y t₂) θ)) := by
  rw [← integral_comp_radiusAt_eq_integral_turningParam (w := fun _ => 1) hm hy ht hpos hF
    continuousOn_const hG hGpos, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- Quadrature between two apsides for a decreasing radius: from the apsis
`r(t₁)` down to the apsis `r(t₂)`. -/
theorem integral_comp_radiusAt_eq_integral_turningParam_of_neg (hm : m ≠ 0)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1)) (radialHamiltonian m V ℓ) y) {t₁ t₂ : ℝ}
    (ht : t₁ < t₂) (hneg : ∀ t ∈ Ioo t₁ t₂, radialVelocityAt m y t < 0) {w G : ℝ → ℝ}
    (hF : ∀ u, 0 < u →
      radialSpeedSq m V ℓ (FreeSmoothRing.lift y (radialHamiltonian m V ℓ) fun _ => t₁) u =
        (u - radiusAt y t₂) * (radiusAt y t₁ - u) * G u)
    (hw : ContinuousOn w (Icc (radiusAt y t₂) (radiusAt y t₁)))
    (hG : ContinuousOn G (Icc (radiusAt y t₂) (radiusAt y t₁)))
    (hGpos : ∀ u ∈ Icc (radiusAt y t₂) (radiusAt y t₁), 0 < G u) :
    ∫ t in t₁..t₂, w (radiusAt y t) =
      ∫ θ in (0 : ℝ)..π, w (turningParam (radiusAt y t₂) (radiusAt y t₁) θ) /
        √(G (turningParam (radiusAt y t₂) (radiusAt y t₁) θ)) := by
  have hlt : radiusAt y t₂ < radiusAt y t₁ :=
    lt_of_hasDerivAt_neg ht (fun t _ => hasDerivAt_radiusAt hy t) hneg
  rw [← integral_div_sqrt_turning hlt w G]
  exact integral_comp_eq_integral_div_sqrt_turning_of_neg ht hlt
    (fun t _ => hasDerivAt_radiusAt hy t) hneg rfl rfl
    (fun t _ => by
      rw [radialVelocityAt_sq hm V ℓ y t, hy.lift_hamiltonian_eq (fun _ => t) fun _ => t₁,
        hF _ (radiusAt_pos y t)])
    hw hG hGpos

variable {x : (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) → TimeFunction}

/-- The angle described between two apsides (Landau–Lifshitz (14.10)), as a
regular integral. -/
theorem angle_sub_eq_integral_turningParam_radius (hm : m ≠ 0)
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
          (radiusAt (fun a => x (Sum.map Sum.inl Sum.inl a)) t₂) θ)) := by
  have hy := isTrajectory_radial hx hℓ
  rw [TimeFunction.apply_sub_apply_eq_integral]
  simp only [timeDerivative_angle_apply hm hx hℓ]
  refine integral_comp_radiusAt_eq_integral_turningParam (w := fun u => ℓ / (m * (u * u)))
    hm hy ht hpos hF ?_ hG hGpos
  exact continuousOn_const.div
    ((continuous_const.mul (continuous_id.mul continuous_id)).continuousOn) fun u hu =>
      mul_ne_zero hm (mul_ne_zero
        ((radiusAt_pos _ t₁).trans_le hu.1).ne' ((radiusAt_pos _ t₁).trans_le hu.1).ne')

/-! ### Kepler's problem -/

/-- The potential energy `−α/r` of Kepler's problem as a function of
`s = log r`. -/
def keplerPotential (α : ℝ) : SmoothOperation 1 :=
  SmoothOperation.ofContDiff (fun x => -α * Real.exp (-(x 0)))
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ => ℝ) 0).neg))

theorem radialSpeedSq_kepler (m α ℓ E : ℝ) {u : ℝ} (hu : 0 < u) :
    radialSpeedSq m (keplerPotential α) ℓ E u =
      2 / m * (E + α / u) - ℓ * ℓ / (m * m * (u * u)) := by
  have h : keplerPotential α (fun _ => Real.log u) = -α / u := by
    change -α * Real.exp (-Real.log u) = -α / u
    rw [Real.exp_neg, Real.exp_log hu, div_eq_mul_inv]
  rw [radialSpeedSq, h]
  ring

/-- In Kepler's problem the two apsides determine the energy and the angular
momentum, and the square of the radial velocity is
`(u − r₁)(r₂ − u) · 2α/(m (r₁ + r₂) u²)`. -/
theorem kepler_radialSpeedSq_eq {α E r₁ r₂ : ℝ} (hm : 0 < m) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hlt : r₁ < r₂)
    (e1 : (0 : ℝ) ^ 2 = 2 / m * (E + α / r₁) - ℓ * ℓ / (m * m * (r₁ * r₁)))
    (e2 : (0 : ℝ) ^ 2 = 2 / m * (E + α / r₂) - ℓ * ℓ / (m * m * (r₂ * r₂))) {u : ℝ}
    (hu : 0 < u) :
    2 / m * (E + α / u) - ℓ * ℓ / (m * m * (u * u)) =
      (u - r₁) * (r₂ - u) * (2 * α / (m * (r₁ + r₂) * (u * u))) := by
  have hsum : 0 < r₁ + r₂ := add_pos hr₁ hr₂
  have f1 : 2 * m * (E * r₁ ^ 2 + α * r₁) = ℓ * ℓ := by
    field_simp at e1
    linear_combination -e1
  have f2 : 2 * m * (E * r₂ ^ 2 + α * r₂) = ℓ * ℓ := by
    field_simp at e2
    linear_combination -e2
  have hE : E * (r₁ + r₂) = -α := by
    have h0 : (r₁ - r₂) * (E * (r₁ + r₂) + α) = 0 := by
      have hm2 : (2 * m) ≠ 0 := by positivity
      apply mul_left_cancel₀ hm2
      linear_combination f1 - f2
    have h3 := (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hlt.ne)
    linear_combination h3
  have hℓ : ℓ * ℓ * (r₁ + r₂) = 2 * m * α * r₁ * r₂ := by
    linear_combination (-(r₁ + r₂)) * f1 + (2 * m * r₁ ^ 2) * hE
  have hEv : E = -α / (r₁ + r₂) := by
    rw [eq_div_iff hsum.ne']
    exact hE
  have hℓv : ℓ * ℓ = 2 * m * α * r₁ * r₂ / (r₁ + r₂) := by
    rw [eq_div_iff hsum.ne']
    exact hℓ
  rw [hEv, hℓv]
  field_simp
  ring

/-- The regular integral of Kepler's problem between the apsides `r₁ < r₂`:
`∫₀^π dθ / √(2α/(m (r₁ + r₂) r(θ)²)) = π a √(m a/α)` with `a = (r₁ + r₂)/2`. -/
theorem kepler_integral_turningParam {α r₁ r₂ : ℝ} (hm : 0 < m) (hα : 0 < α) (hr₁ : 0 < r₁)
    (hlt : r₁ < r₂) :
    ∫ θ in (0 : ℝ)..π,
        1 / √(2 * α / (m * (r₁ + r₂) * (turningParam r₁ r₂ θ * turningParam r₁ r₂ θ))) =
      π * ((r₁ + r₂) / 2) * √(m * ((r₁ + r₂) / 2) / α) := by
  have hsum : 0 < r₁ + r₂ := by linarith
  have hint : ∀ θ ∈ uIcc (0 : ℝ) π,
      1 / √(2 * α / (m * (r₁ + r₂) * (turningParam r₁ r₂ θ * turningParam r₁ r₂ θ))) =
      √(m * ((r₁ + r₂) / 2) / α) * turningParam r₁ r₂ θ := fun θ hθ => by
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    have hp : 0 < turningParam r₁ r₂ θ := hr₁.trans_le (turningParam_mem_Icc hlt hθ).1
    have hX : 2 * α / (m * (r₁ + r₂) * (turningParam r₁ r₂ θ * turningParam r₁ r₂ θ)) =
        (m * ((r₁ + r₂) / 2) / α * (turningParam r₁ r₂ θ * turningParam r₁ r₂ θ))⁻¹ := by
      field_simp
    rw [hX, Real.sqrt_inv, one_div, inv_inv, Real.sqrt_mul (by positivity),
      Real.sqrt_mul_self hp.le]
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_const_mul,
    integral_turningParam]
  ring

/-- Kepler's problem: the time from an apsis `r₁` up to the next apsis
`r₂ > r₁` is `π a √(m a/α)` with `a = (r₁ + r₂)/2`. -/
theorem kepler_sub_eq {α : ℝ} (hm : 0 < m) (hα : 0 < α)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1))
      (radialHamiltonian m (keplerPotential α) ℓ) y) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t)
    (h₁ : radialVelocityAt m y t₁ = 0) (h₂ : radialVelocityAt m y t₂ = 0) :
    t₂ - t₁ = π * ((radiusAt y t₁ + radiusAt y t₂) / 2) *
      √(m * ((radiusAt y t₁ + radiusAt y t₂) / 2) / α) := by
  have hr₁ := radiusAt_pos y t₁
  have hr₂ := radiusAt_pos y t₂
  have hlt : radiusAt y t₁ < radiusAt y t₂ :=
    lt_of_hasDerivAt_pos ht (fun t _ => hasDerivAt_radiusAt hy t) hpos
  have hsum : 0 < radiusAt y t₁ + radiusAt y t₂ := add_pos hr₁ hr₂
  have e1 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₁
  have e2 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₂
  rw [h₁, radialSpeedSq_kepler _ _ _ _ hr₁] at e1
  rw [h₂, hy.lift_hamiltonian_eq (fun _ => t₂) fun _ => t₁,
    radialSpeedSq_kepler _ _ _ _ hr₂] at e2
  have hF : ∀ u, 0 < u →
      radialSpeedSq m (keplerPotential α) ℓ
        (FreeSmoothRing.lift y (radialHamiltonian m (keplerPotential α) ℓ) fun _ => t₁) u =
      (u - radiusAt y t₁) * (radiusAt y t₂ - u) *
        (2 * α / (m * (radiusAt y t₁ + radiusAt y t₂) * (u * u))) := fun u hu => by
    rw [radialSpeedSq_kepler _ _ _ _ hu]
    exact kepler_radialSpeedSq_eq hm hr₁ hr₂ hlt e1 e2 hu
  rw [sub_eq_integral_turningParam_radius hm.ne' hy ht hpos hF
    (continuousOn_const.div
      ((continuous_const.mul (continuous_id.mul continuous_id)).continuousOn) fun u hu =>
        mul_ne_zero (mul_ne_zero hm.ne' hsum.ne')
          (mul_ne_zero (hr₁.trans_le hu.1).ne' (hr₁.trans_le hu.1).ne'))
    fun u hu => by
      have hu0 : 0 < u := hr₁.trans_le hu.1
      positivity]
  exact kepler_integral_turningParam hm hα hr₁ hlt

/-- Kepler's problem: the time from an apsis `r₁` down to the next apsis
`r₂ < r₁` is `π a √(m a/α)` with `a = (r₁ + r₂)/2`. -/
theorem kepler_sub_eq_of_neg {α : ℝ} (hm : 0 < m) (hα : 0 < α)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1))
      (radialHamiltonian m (keplerPotential α) ℓ) y) {t₁ t₂ : ℝ} (ht : t₁ < t₂)
    (hneg : ∀ t ∈ Ioo t₁ t₂, radialVelocityAt m y t < 0)
    (h₁ : radialVelocityAt m y t₁ = 0) (h₂ : radialVelocityAt m y t₂ = 0) :
    t₂ - t₁ = π * ((radiusAt y t₁ + radiusAt y t₂) / 2) *
      √(m * ((radiusAt y t₁ + radiusAt y t₂) / 2) / α) := by
  have hr₁ := radiusAt_pos y t₁
  have hr₂ := radiusAt_pos y t₂
  have hlt : radiusAt y t₂ < radiusAt y t₁ :=
    lt_of_hasDerivAt_neg ht (fun t _ => hasDerivAt_radiusAt hy t) hneg
  have hsum : 0 < radiusAt y t₂ + radiusAt y t₁ := add_pos hr₂ hr₁
  have e1 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₁
  have e2 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₂
  rw [h₁, radialSpeedSq_kepler _ _ _ _ hr₁] at e1
  rw [h₂, hy.lift_hamiltonian_eq (fun _ => t₂) fun _ => t₁,
    radialSpeedSq_kepler _ _ _ _ hr₂] at e2
  have hF : ∀ u, 0 < u →
      radialSpeedSq m (keplerPotential α) ℓ
        (FreeSmoothRing.lift y (radialHamiltonian m (keplerPotential α) ℓ) fun _ => t₁) u =
      (u - radiusAt y t₂) * (radiusAt y t₁ - u) *
        (2 * α / (m * (radiusAt y t₂ + radiusAt y t₁) * (u * u))) := fun u hu => by
    rw [radialSpeedSq_kepler _ _ _ _ hu]
    exact kepler_radialSpeedSq_eq hm hr₂ hr₁ hlt e2 e1 hu
  have hT := integral_comp_radiusAt_eq_integral_turningParam_of_neg (w := fun _ => 1) hm.ne' hy
    ht hneg hF continuousOn_const
    (continuousOn_const.div
      ((continuous_const.mul (continuous_id.mul continuous_id)).continuousOn) fun u hu =>
        mul_ne_zero (mul_ne_zero hm.ne' hsum.ne')
          (mul_ne_zero (hr₂.trans_le hu.1).ne' (hr₂.trans_le hu.1).ne'))
    fun u hu => by
      have hu0 : 0 < u := hr₂.trans_le hu.1
      positivity
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hT
  rw [hT, kepler_integral_turningParam hm hα hr₂ hlt, add_comm (radiusAt y t₂)]

/-- The period of an elliptic orbit (Landau–Lifshitz (15.8)): along a radial
trajectory of Kepler's problem, if the radius increases from an apsis at
`t₁` to an apsis at `t₂` and decreases to an apsis at `t₃`, then it returns
to its value at `t₁`, and `t₃ − t₁ = 2π a √(m a/α)` with the semi-major axis
`a = (r(t₁) + r(t₂))/2`. The time between two passages through the perihelion
is `2π a^{3/2} √(m/α)` and depends on `a` only. -/
theorem kepler_period {α : ℝ} (hm : 0 < m) (hα : 0 < α)
    (hy : IsTrajectory (PhaseSpace.canonical (Fin 1))
      (radialHamiltonian m (keplerPotential α) ℓ) y) {t₁ t₂ t₃ : ℝ} (h12 : t₁ < t₂)
    (h23 : t₂ < t₃) (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < radialVelocityAt m y t)
    (hneg : ∀ t ∈ Ioo t₂ t₃, radialVelocityAt m y t < 0)
    (h₁ : radialVelocityAt m y t₁ = 0) (h₂ : radialVelocityAt m y t₂ = 0)
    (h₃ : radialVelocityAt m y t₃ = 0) :
    radiusAt y t₃ = radiusAt y t₁ ∧
      t₃ - t₁ = 2 * π * ((radiusAt y t₁ + radiusAt y t₂) / 2) *
        √(m * ((radiusAt y t₁ + radiusAt y t₂) / 2) / α) := by
  have hr₁ := radiusAt_pos y t₁
  have hr₂ := radiusAt_pos y t₂
  have hr₃ := radiusAt_pos y t₃
  have hlt : radiusAt y t₁ < radiusAt y t₂ :=
    lt_of_hasDerivAt_pos h12 (fun t _ => hasDerivAt_radiusAt hy t) hpos
  have hlt' : radiusAt y t₃ < radiusAt y t₂ :=
    lt_of_hasDerivAt_neg h23 (fun t _ => hasDerivAt_radiusAt hy t) hneg
  have e1 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₁
  have e2 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₂
  have e3 := radialVelocityAt_sq hm.ne' (keplerPotential α) ℓ y t₃
  rw [h₁, radialSpeedSq_kepler _ _ _ _ hr₁] at e1
  rw [h₂, hy.lift_hamiltonian_eq (fun _ => t₂) fun _ => t₁,
    radialSpeedSq_kepler _ _ _ _ hr₂] at e2
  rw [h₃, hy.lift_hamiltonian_eq (fun _ => t₃) fun _ => t₁,
    radialSpeedSq_kepler _ _ _ _ hr₃, kepler_radialSpeedSq_eq hm hr₁ hr₂ hlt e1 e2 hr₃] at e3
  have h31 : radiusAt y t₃ = radiusAt y t₁ := by
    have hG : 0 < 2 * α / (m * (radiusAt y t₁ + radiusAt y t₂) *
        (radiusAt y t₃ * radiusAt y t₃)) := by positivity
    have h0 : (radiusAt y t₃ - radiusAt y t₁) * (radiusAt y t₂ - radiusAt y t₃) = 0 := by
      have h := e3.symm
      rw [zero_pow two_ne_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hG.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (sub_pos.mpr hlt').ne')
  refine ⟨h31, ?_⟩
  have hA := kepler_sub_eq hm hα hy h12 hpos h₁ h₂
  have hB := kepler_sub_eq_of_neg hm hα hy h23 hneg h₂ h₃
  rw [h31, add_comm (radiusAt y t₂)] at hB
  linear_combination hA + hB

end ProjectAInos.Mechanics.CentralField
