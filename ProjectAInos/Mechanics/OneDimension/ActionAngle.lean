/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OneDimension.Area
public import ProjectAInos.Mechanics.OneDimension.Motion

/-!
# Action–angle variables for one degree of freedom

Landau–Lifshitz §50, for the motion in a well.

* `orbitAction` is the action variable `I = (1/2π) ∮ p dx`. Along a smooth
  family of wells `dI/dE = T/2π` (`hasDerivAt_orbitAction`), so the action is a
  strictly increasing function of the energy on an interval of the family
  (`strictMonoOn_orbitAction`): the energy is a function of the action, and
  `dE/dI = 2π/T` is the frequency.
* `orbitPhase` is the angle variable `φ = 2π t/T` of a point of the level curve.
  It increases by `2π` around the curve (`IsWell.orbitPhase_add_two_pi`), and
  along the motion `φ = (2π/T) t` (`IsWell.orbitPhase_orbitAngle`): the angle
  variable moves uniformly with the frequency `dE/dI`.
* `orbit_area_form`: in the chart `(E, θ)` of the family of level curves the
  area form `dx ∧ dp` is `dφ ∧ dI`. Both are `−λ dE ∧ dθ`: the variables
  `(φ, I)` are canonical.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped Real ContDiff

namespace ProjectAInos.Mechanics.OneDim

variable {U : ℝ → ℝ} {E a b m : ℝ}

/-- The action variable `I = (1/2π) ∮ p dx`. -/
def orbitAction (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : ℝ := orbitArea m U a b / (2 * π)

/-- The angle variable `φ = 2π t/T` of the point of the level curve at the
angle `θ`. -/
def orbitPhase (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) : ℝ :=
  2 * π * orbitTime m U a b θ / orbitPeriod m U a b

/-- `dI/dE = T/2π` along a smooth family of wells. -/
theorem hasDerivAt_orbitAction (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ} (hJ : IsOpen J)
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ} (hE₀ : E₀ ∈ J) :
    HasDerivAt (fun E => orbitAction m U (α E) (β E))
      (orbitPeriod m U (α E₀) (β E₀) / (2 * π)) E₀ :=
  (hasDerivAt_orbitArea hU hm hJ hα hβ hw hE₀).div_const (2 * π)

/-- The action is a strictly increasing function of the energy on an interval
of a smooth family of wells, so the energy is a function of the action. -/
theorem strictMonoOn_orbitAction (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ}
    (hJ : IsOpen J) {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {s : Set ℝ} (hs : s ⊆ J) (hconn : s.OrdConnected) :
    StrictMonoOn (fun E => orbitAction m U (α E) (β E)) s := by
  refine strictMonoOn_of_deriv_pos hconn.convex (fun E hE =>
    (hasDerivAt_orbitAction hU hm hJ hα hβ hw (hs hE)).continuousAt.continuousWithinAt)
    fun E hE => ?_
  have hEJ : E ∈ J := hs (interior_subset hE)
  rw [(hasDerivAt_orbitAction hU hm hJ hα hβ hw hEJ).deriv]
  exact div_pos ((hw E hEJ).orbitPeriod_pos hU hm) (by positivity)

namespace IsWell

/-- The time around the level curve is the period. -/
theorem orbitTime_add_two_pi (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    orbitTime m U a b (θ + 2 * π) = orbitTime m U a b θ + orbitPeriod m U a b := by
  have hd : ∀ s : ℝ, HasDerivAt
      (fun s => orbitTime m U a b (s + 2 * π) - orbitTime m U a b s) 0 s := by
    intro s
    have h1 := (h.hasDerivAt_orbitTime hU m (s + 2 * π)).comp_add_const s (2 * π)
    have h2 := h1.sub (h.hasDerivAt_orbitTime hU m s)
    refine h2.congr_deriv ?_
    rw [orbitRate_add_two_pi, sub_self]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) θ 0
  have h0 : orbitTime m U a b (0 + 2 * π) - orbitTime m U a b 0 = orbitPeriod m U a b := by
    simp [orbitTime, orbitPeriod]
  linarith

theorem hasDerivAt_orbitPhase (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    HasDerivAt (orbitPhase m U a b)
      (2 * π * orbitRate m U a b θ / orbitPeriod m U a b) θ :=
  ((h.hasDerivAt_orbitTime hU m θ).const_mul (2 * π)).div_const _

/-- The angle variable increases by `2π` around the level curve. -/
theorem orbitPhase_add_two_pi (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (θ : ℝ) : orbitPhase m U a b (θ + 2 * π) = orbitPhase m U a b θ + 2 * π := by
  have hT := (h.orbitPeriod_pos hU hm).ne'
  rw [orbitPhase, orbitPhase, h.orbitTime_add_two_pi hU m θ]
  field_simp

/-- Along the motion the angle variable is `(2π/T) t`: it moves uniformly, with
the frequency `2π/T = dE/dI`. -/
theorem orbitPhase_orbitAngle (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    orbitPhase m U a b (orbitAngle m U a b t) = 2 * π / orbitPeriod m U a b * t := by
  rw [orbitPhase, h.orbitTime_orbitAngle hU hm t]
  ring

end IsWell

/-- The variables `(φ, I)` are canonical: in the chart `(E, θ)` of a family of
level curves the area form `dx ∧ dp` is `dφ ∧ dI`. Here `dI` has no component
along `θ`, and both sides are `−λ` on the pair `(∂/∂E, ∂/∂θ)`. -/
theorem orbit_area_form (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ} (hJ : IsOpen J)
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ} (hE₀ : E₀ ∈ J) (θ : ℝ) {PE : ℝ}
    (hPE : HasDerivAt (fun E => orbitMomentum m U (α E) (β E) θ) PE E₀) :
    deriv (fun E => orbitPosition (α E) (β E) θ) E₀ *
        deriv (orbitMomentum m U (α E₀) (β E₀)) θ -
      deriv (orbitPosition (α E₀) (β E₀)) θ * PE =
      -(deriv (orbitPhase m U (α E₀) (β E₀)) θ *
        deriv (fun E => orbitAction m U (α E) (β E)) E₀) := by
  have h₀ := hw E₀ hE₀
  have hαd : HasDerivAt α (deriv α E₀) E₀ :=
    ((hα.contDiffAt (hJ.mem_nhds hE₀)).differentiableAt (by simp)).hasDerivAt
  have hβd : HasDerivAt β (deriv β E₀) E₀ :=
    ((hβ.contDiffAt (hJ.mem_nhds hE₀)).differentiableAt (by simp)).hasDerivAt
  have hen := orbitMomentum_mul_deriv_energy hU hm hJ hw hE₀ hαd hβd hPE
  have htan := h₀.orbitRate_mul_orbitMomentum hU hm θ
  have hT := (h₀.orbitPeriod_pos hU hm).ne'
  rw [(hasDerivAt_orbitPosition_energy hαd hβd θ).deriv,
    (h₀.hasDerivAt_orbitMomentum hU m θ).deriv, (hasDerivAt_orbitPosition _ _ θ).deriv,
    (h₀.hasDerivAt_orbitPhase hU m θ).deriv,
    (hasDerivAt_orbitAction hU hm hJ hα hβ hw hE₀).deriv, ← htan]
  have hsimp : 2 * π * orbitRate m U (α E₀) (β E₀) θ / orbitPeriod m U (α E₀) (β E₀) *
      (orbitPeriod m U (α E₀) (β E₀) / (2 * π)) = orbitRate m U (α E₀) (β E₀) θ := by
    field_simp
  rw [hsimp]
  linear_combination (-(orbitRate m U (α E₀) (β E₀) θ)) * hen

end ProjectAInos.Mechanics.OneDim
