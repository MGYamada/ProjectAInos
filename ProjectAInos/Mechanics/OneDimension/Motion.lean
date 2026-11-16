/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OneDimension.Orbit
public import ProjectAInos.SmoothGeometry.ODE.FlowComplete

/-!
# The motion in a well is periodic

For one degree of freedom, `H = p²/2m + U(x)`, the Hamiltonian vector field on
the plane is `field m U = (p/m, −U′(x))`. For a well `IsWell U E a b`:

* `wellMotion m U a b` is a solution of Hamilton's equations defined for all
  times, with `wellMotion 0 = (a, 0)` (`hasDerivAt_wellMotion`). It is the
  level curve of `Orbit`, run with the angle `orbitAngle` that solves
  `dθ/dt = 1/λ(θ)`.
* It has the period `orbitPeriod`, the integral (11.5) of Landau–Lifshitz
  (`wellMotion_add_period`).
* Every point of the level `E` between the turning points is on this motion
  (`IsWell.exists_wellMotion_eq`), so every solution that starts at such a
  point has the same period (`IsWell.add_period_of_hasDerivAt`).

The level curve is closed, and the period of the motion is twice the time
between the turning points.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace ProjectAInos.Mechanics.OneDim

open SmoothGeometry.NonlinearODE

variable {U : ℝ → ℝ} {E a b m : ℝ}

/-- The Hamiltonian vector field `(p/m, −U′(x))` of one degree of freedom. -/
def field (m : ℝ) (U : ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.2 / m, -deriv U z.1)

/-- The energy `p²/2m + U(x)`. -/
def energy (m : ℝ) (U : ℝ → ℝ) (z : ℝ × ℝ) : ℝ := z.2 ^ 2 / (2 * m) + U z.1

theorem contDiff_field (m : ℝ) (hU : ContDiff ℝ ∞ U) : ContDiff ℝ ∞ (field m U) :=
  (contDiff_snd.div_const m).prodMk ((hU.deriv' (n := ∞)).comp contDiff_fst).neg

/-- The point of the level curve at the angle `θ`. -/
def orbitPoint (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) : ℝ × ℝ :=
  (orbitPosition a b θ, orbitMomentum m U a b θ)

/-- The time at which the motion from the left turning point has the angle `θ`. -/
def orbitTime (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) : ℝ := ∫ s in (0 : ℝ)..θ, orbitRate m U a b s

/-- The angle of the motion from the left turning point at the time `t`. -/
def orbitAngle (m : ℝ) (U : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  flow (fun ϑ => (orbitRate m U a b ϑ)⁻¹) (t, 0)

/-- The motion in the well that starts at the left turning point. -/
def wellMotion (m : ℝ) (U : ℝ → ℝ) (a b t : ℝ) : ℝ × ℝ :=
  orbitPoint m U a b (orbitAngle m U a b t)

namespace IsWell

theorem contDiff_orbitRate (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m : ℝ) :
    ContDiff ℝ ∞ (orbitRate m U a b) := by
  have hW : ContDiff ℝ ∞ fun θ => wellFactor U a b (orbitPosition a b θ) :=
    (contDiff_wellFactor_right hU a b).comp (contDiff_orbitPosition a b)
  exact contDiff_const.div (hW.sqrt fun θ => (h.wellFactor_orbitPosition_pos hU θ).ne')
    fun θ => (Real.sqrt_pos.mpr (h.wellFactor_orbitPosition_pos hU θ)).ne'

theorem contDiff_inv_orbitRate (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    ContDiff ℝ ∞ fun ϑ => (orbitRate m U a b ϑ)⁻¹ :=
  (h.contDiff_orbitRate hU m).inv fun θ => (h.orbitRate_pos hU hm θ).ne'

/-- The angle is defined for all times. -/
theorem flowDomain_inv_orbitRate (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    flowDomain (fun ϑ => (orbitRate m U a b ϑ)⁻¹) = univ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (contDiff_wellFactor_right hU a b).continuous.continuousOn (s := Icc a b)
  refine flowDomain_eq_univ_of_norm_le (h.contDiff_inv_orbitRate hU hm)
    (a := √C / √(m / 2)) (b := 0) fun θ => ?_
  have hWpos := h.wellFactor_orbitPosition_pos hU θ
  have hWle : wellFactor U a b (orbitPosition a b θ) ≤ C := by
    have := hC _ (orbitPosition_mem_Icc h.lt.le θ)
    rwa [Real.norm_of_nonneg hWpos.le] at this
  have hc : 0 < √(m / 2) := Real.sqrt_pos.mpr (by positivity)
  rw [zero_mul, add_zero, orbitRate, inv_div, Real.norm_of_nonneg (by positivity)]
  gcongr

theorem hasDerivAt_orbitAngle (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    HasDerivAt (orbitAngle m U a b) (orbitRate m U a b (orbitAngle m U a b t))⁻¹ t :=
  hasDerivAt_flow (h.contDiff_inv_orbitRate hU hm)
    (by rw [h.flowDomain_inv_orbitRate hU hm]; exact mem_univ _)

theorem hasDerivAt_orbitTime (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    HasDerivAt (orbitTime m U a b) (orbitRate m U a b θ) θ :=
  ((h.contDiff_orbitRate hU m).continuous.integral_hasStrictDerivAt 0 θ).hasDerivAt

theorem strictMono_orbitTime (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    StrictMono (orbitTime m U a b) :=
  strictMono_of_deriv_pos fun θ => by
    rw [(h.hasDerivAt_orbitTime hU m θ).deriv]
    exact h.orbitRate_pos hU hm θ

/-- The time of the angle of the time `t` is `t`. -/
theorem orbitTime_orbitAngle (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) : orbitTime m U a b (orbitAngle m U a b t) = t := by
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s => orbitTime m U a b (orbitAngle m U a b s) - s) 0 s := by
    intro s
    have h1 := (h.hasDerivAt_orbitTime hU m (orbitAngle m U a b s)).comp s
      (h.hasDerivAt_orbitAngle hU hm s)
    have h2 := h1.sub (hasDerivAt_id s)
    refine h2.congr_deriv ?_
    rw [mul_inv_cancel₀ (h.orbitRate_pos hU hm _).ne', sub_self]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have h0 : orbitTime m U a b (orbitAngle m U a b 0) - 0 = 0 := by
    simp [orbitAngle, orbitTime]
  linarith

/-- The angle of the time of the angle `θ` is `θ`. -/
theorem orbitAngle_orbitTime (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (θ : ℝ) : orbitAngle m U a b (orbitTime m U a b θ) = θ :=
  (h.strictMono_orbitTime hU hm).injective (h.orbitTime_orbitAngle hU hm _)

theorem orbitAngle_orbitPeriod (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    orbitAngle m U a b (orbitPeriod m U a b) = 2 * π :=
  h.orbitAngle_orbitTime hU hm (2 * π)

/-- The motion solves Hamilton's equations at every time. -/
theorem hasDerivAt_wellMotion (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    HasDerivAt (wellMotion m U a b) (field m U (wellMotion m U a b t)) t := by
  have hϑ := h.hasDerivAt_orbitAngle hU hm t
  have hx := (hasDerivAt_orbitPosition a b (orbitAngle m U a b t)).comp t hϑ
  have hp := (h.hasDerivAt_orbitMomentum hU m (orbitAngle m U a b t)).comp t hϑ
  have hne := (h.orbitRate_pos hU hm (orbitAngle m U a b t)).ne'
  have hpair := hx.prodMk hp
  refine hpair.congr_deriv ?_
  refine Prod.ext ?_ ?_
  · change (b - a) / 2 * Real.sin (orbitAngle m U a b t) *
        (orbitRate m U a b (orbitAngle m U a b t))⁻¹ =
      orbitMomentum m U a b (orbitAngle m U a b t) / m
    rw [← h.orbitRate_mul_orbitMomentum hU hm (orbitAngle m U a b t)]
    field_simp
  · change -(orbitRate m U a b (orbitAngle m U a b t) *
        deriv U (orbitPosition a b (orbitAngle m U a b t))) *
        (orbitRate m U a b (orbitAngle m U a b t))⁻¹ =
      -deriv U (orbitPosition a b (orbitAngle m U a b t))
    field_simp

theorem wellMotion_zero (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : wellMotion m U a b 0 = (a, 0) := by
  simp [wellMotion, orbitAngle, orbitPoint, orbitPosition_zero, orbitMomentum_zero]

theorem wellMotion_orbitPeriod (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    wellMotion m U a b (orbitPeriod m U a b) = (a, 0) := by
  rw [wellMotion, h.orbitAngle_orbitPeriod hU hm, orbitPoint]
  have e : (2 * π : ℝ) = 0 + 2 * π := by ring
  rw [e, orbitPosition_add_two_pi, orbitMomentum_add_two_pi, orbitPosition_zero,
    orbitMomentum_zero]

/-- The motion is periodic with the period `orbitPeriod`. -/
theorem wellMotion_add_period (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    wellMotion m U a b (t + orbitPeriod m U a b) = wellMotion m U a b t := by
  have hX : ContDiff ℝ 1 (field m U) := (contDiff_field m hU).of_le (by simp)
  refine eq_of_hasDerivAt_of_eq hX (f := fun s => wellMotion m U a b (s + orbitPeriod m U a b))
    (g := wellMotion m U a b) (s := 0) (t := t)
    (fun r _ => (h.hasDerivAt_wellMotion hU hm (r + orbitPeriod m U a b)).comp_add_const r _)
    (fun r _ => h.hasDerivAt_wellMotion hU hm r) ?_
  rw [zero_add, h.wellMotion_orbitPeriod hU hm, wellMotion_zero]

/-- The energy of the motion. -/
theorem energy_wellMotion (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (t : ℝ) :
    energy m U (wellMotion m U a b t) = E :=
  h.orbit_energy hU hm _

/-- The motion is the line of the flow through the left turning point. -/
theorem flow_field_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (t : ℝ) :
    (t, (a, (0 : ℝ))) ∈ flowDomain (field m U) ∧
      flow (field m U) (t, (a, 0)) = wellMotion m U a b t :=
  ⟨mem_flowDomain_of_hasDerivWithinAt (contDiff_field m hU).continuous
      (wellMotion_zero m U a b) fun r _ => (h.hasDerivAt_wellMotion hU hm r).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt ((contDiff_field m hU).of_le (by simp))
      (wellMotion_zero m U a b) fun r _ => (h.hasDerivAt_wellMotion hU hm r).hasDerivWithinAt⟩

/-- Every point of the level `E` between the turning points is a point of the
level curve. -/
theorem exists_orbitPoint_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc a b) (hE : energy m U z = E) :
    ∃ θ, orbitPoint m U a b θ = z := by
  have hba : 0 < b - a := sub_pos.mpr h.lt
  have hu1 : -1 ≤ (a + b - 2 * z.1) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith [hz.2]
  have hu2 : (a + b - 2 * z.1) / (b - a) ≤ 1 := by
    rw [div_le_iff₀ hba]
    linarith [hz.1]
  have hx : orbitPosition a b (Real.arccos ((a + b - 2 * z.1) / (b - a))) = z.1 := by
    rw [orbitPosition, Real.cos_arccos hu1 hu2]
    field_simp
    ring
  have hsin : 0 ≤ Real.sin (Real.arccos ((a + b - 2 * z.1) / (b - a))) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hsq : orbitMomentum m U a b (Real.arccos ((a + b - 2 * z.1) / (b - a))) ^ 2 = z.2 ^ 2 := by
    rw [h.orbitMomentum_sq hU hm, hx]
    have hne : (2 * m) ≠ 0 := by positivity
    rw [energy] at hE
    field_simp at hE
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hp
  · exact ⟨_, Prod.ext hx hp⟩
  · refine ⟨-Real.arccos ((a + b - 2 * z.1) / (b - a)), Prod.ext ?_ ?_⟩
    · change orbitPosition a b (-Real.arccos ((a + b - 2 * z.1) / (b - a))) = z.1
      rw [orbitPosition_neg, hx]
    · change orbitMomentum m U a b (-Real.arccos ((a + b - 2 * z.1) / (b - a))) = z.2
      rw [orbitMomentum_neg, hp, neg_neg]

/-- Every point of the level `E` between the turning points is reached by the
motion from the left turning point. -/
theorem exists_wellMotion_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc a b) (hE : energy m U z = E) :
    ∃ t, wellMotion m U a b t = z := by
  obtain ⟨θ, hθ⟩ := h.exists_orbitPoint_eq hU hm hz hE
  exact ⟨orbitTime m U a b θ, by rw [wellMotion, h.orbitAngle_orbitTime hU hm, hθ]⟩

/-- Landau–Lifshitz §11: every motion with the energy `E` between the turning
points is periodic, with the period `orbitPeriod`. -/
theorem add_period_of_hasDerivAt (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {y : ℝ → ℝ × ℝ} (hy : ∀ t, HasDerivAt y (field m U (y t)) t) (hz : (y 0).1 ∈ Icc a b)
    (hE : energy m U (y 0) = E) (t : ℝ) : y (t + orbitPeriod m U a b) = y t := by
  have hX : ContDiff ℝ 1 (field m U) := (contDiff_field m hU).of_le (by simp)
  obtain ⟨t₀, ht₀⟩ := h.exists_wellMotion_eq hU hm hz hE
  have hshift : ∀ s : ℝ, y s = wellMotion m U a b (s + t₀) := by
    intro s
    refine eq_of_hasDerivAt_of_eq hX (f := y) (g := fun r => wellMotion m U a b (r + t₀))
      (s := 0) (t := s) (fun r _ => hy r)
      (fun r _ => (h.hasDerivAt_wellMotion hU hm (r + t₀)).comp_add_const r t₀) ?_
    rw [zero_add, ht₀]
  rw [hshift, hshift t]
  have e : t + orbitPeriod m U a b + t₀ = t + t₀ + orbitPeriod m U a b := by ring
  rw [e, h.wellMotion_add_period hU hm]

/-- The same statement for the position: a solution of `m ẍ = −U′(x)` with the
energy `E` that starts between the turning points has the period `orbitPeriod`. -/
theorem position_add_period (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {x v : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (-deriv U (x t) / m) t) (h0 : x 0 ∈ Icc a b)
    (hE : m * v 0 ^ 2 / 2 + U (x 0) = E) (t : ℝ) : x (t + orbitPeriod m U a b) = x t := by
  have hy : ∀ s, HasDerivAt (fun s => (x s, m * v s)) (field m U (x s, m * v s)) s := by
    intro s
    have hp := (hv s).const_mul m
    have hpair := (hx s).prodMk hp
    refine hpair.congr_deriv (Prod.ext ?_ ?_)
    · change v s = m * v s / m
      field_simp
    · change m * (-deriv U (x s) / m) = -deriv U (x s)
      field_simp
  have hen : energy m U (x 0, m * v 0) = E := by
    rw [energy, ← hE]
    change (m * v 0) ^ 2 / (2 * m) + U (x 0) = m * v 0 ^ 2 / 2 + U (x 0)
    field_simp
  exact congrArg Prod.fst (h.add_period_of_hasDerivAt hU hm hy h0 hen t)

end IsWell

end ProjectAInos.Mechanics.OneDim
