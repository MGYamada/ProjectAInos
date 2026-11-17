/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.Mechanics.OneDimension.Oscillator

/-! Typed contracts for the motion in one dimension: divided differences, wells
with simple turning points, the level curve and its period, the periodic
motion, the derivative of the area in the energy, Abel's inversion formula and
action–angle variables. These examples use default elaborator options. -/

open ProjectAinos ProjectAinos.Mechanics ProjectAinos.Mechanics.OneDim
open ProjectAinos.SmoothAlgebra ProjectAinos.SmoothGeometry.NonlinearODE
open Set Filter MeasureTheory
open scoped Real Topology ContDiff ENNReal

noncomputable section

section DividedDifference

variable {U : ℝ → ℝ}

example (U : ℝ → ℝ) (p : ℝ × ℝ) :
    dividedDifference U p = ∫ t in (0 : ℝ)..1, deriv U (p.2 + t * (p.1 - p.2)) := rfl

example (hU : ContDiff ℝ 1 U) (x y : ℝ) :
    U x - U y = (x - y) * dividedDifference U (x, y) :=
  sub_eq_mul_dividedDifference hU x y

example (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (dividedDifference U) :=
  contDiff_dividedDifference hU

example (U : ℝ → ℝ) (x : ℝ) :
    dividedDifference U (x, x) = deriv U x :=
  dividedDifference_self U x

example (U : ℝ → ℝ) (q : ℝ × ℝ × ℝ) :
    dividedDifference₂ U q = ∫ t in (0 : ℝ)..1, (1 - t) * ∫ s in (0 : ℝ)..1,
      deriv (deriv U) (q.1 + t * (q.2.1 - q.1) + s * ((1 - t) * (q.2.2 - q.1))) := rfl

example (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (dividedDifference₂ U) :=
  contDiff_dividedDifference₂ hU

example (hU : ContDiff ℝ ∞ U) (a b x : ℝ) :
    dividedDifference U (b, x) - dividedDifference U (b, a) =
      (x - a) * dividedDifference₂ U (a, b, x) :=
  dividedDifference_sub hU a b x

example (hU : ContDiff ℝ ∞ U) {a b E : ℝ} (hab : a ≠ b)
    (ha : U a = E) (hb : U b = E) (x : ℝ) :
    E - U x = (x - a) * (b - x) * dividedDifference₂ U (a, b, x) :=
  sub_eq_mul_mul_dividedDifference₂ hU hab ha hb x


end DividedDifference

section Well

variable {U : ℝ → ℝ} {E a b : ℝ}

example (h : IsWell U E a b) : a < b := h.lt

example (h : IsWell U E a b) : U a = E := h.left

example (h : IsWell U E a b) : U b = E := h.right

example (h : IsWell U E a b) : deriv U a < 0 := h.deriv_left

example (h : IsWell U E a b) : 0 < deriv U b := h.deriv_right

example (h : IsWell U E a b) : ∀ x ∈ Ioo a b, U x < E := h.lt_energy

example (U : ℝ → ℝ) (a b x : ℝ) : wellFactor U a b x = dividedDifference₂ U (a, b, x) := rfl

example (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ × ℝ => wellFactor U q.1 q.2.1 q.2.2 :=
  contDiff_wellFactor hU

example (hU : ContDiff ℝ ∞ U) (a b : ℝ) :
    ContDiff ℝ ∞ (wellFactor U a b) :=
  contDiff_wellFactor_right hU a b

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    E - U x = (x - a) * (b - x) * wellFactor U a b x :=
  IsWell.sub_eq h hU x

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) :
    wellFactor U a b a = -deriv U a / (b - a) :=
  IsWell.wellFactor_left h hU

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) :
    wellFactor U a b b = deriv U b / (b - a) :=
  IsWell.wellFactor_right h hU

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) {x : ℝ}
    (hx : x ∈ Icc a b) :
    0 < wellFactor U a b x :=
  IsWell.wellFactor_pos h hU hx

example (hU : ContDiff ℝ ∞ U) (hab : a < b) (ha : U a = E)
    (hb : U b = E) (hda : deriv U a < 0) (hdb : 0 < deriv U b)
    (hW : ∀ x ∈ Icc a b, 0 < wellFactor U a b x) : IsWell U E a b :=
  isWell_of_wellFactor_pos hU hab ha hb hda hdb hW

example (hU : ContDiff ℝ ∞ U) {E₀ x₀ : ℝ} (hx₀ : U x₀ = E₀)
    (hd : deriv U x₀ ≠ 0) :
    ∃ (J : Set ℝ) (ξ : ℝ → ℝ), IsOpen J ∧ E₀ ∈ J ∧ ξ E₀ = x₀ ∧ ContDiffOn ℝ ∞ ξ J ∧
      ∀ E ∈ J, U (ξ E) = E :=
  exists_level_point hU hx₀ hd

example (hU : ContDiff ℝ ∞ U) {E₀ a₀ b₀ : ℝ} (h : IsWell U E₀ a₀ b₀) :
    ∃ (J : Set ℝ) (α β : ℝ → ℝ), IsOpen J ∧ E₀ ∈ J ∧ α E₀ = a₀ ∧ β E₀ = b₀ ∧
      ContDiffOn ℝ ∞ α J ∧ ContDiffOn ℝ ∞ β J ∧ ∀ E ∈ J, IsWell U E (α E) (β E) :=
  IsWell.exists_family hU h

example {k E : ℝ} (hk : 0 < k) (hE : 0 < E) :
    IsWell (fun x => k / 2 * x ^ 2) E (-√(2 * E / k)) √(2 * E / k) :=
  isWell_oscillator hk hE


end Well

section Orbit

variable {U : ℝ → ℝ} {E a b m : ℝ}

example (a b θ : ℝ) : orbitPosition a b θ = (a + b) / 2 - (b - a) / 2 * Real.cos θ := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) : orbitMomentum m U a b θ =
    √(2 * m) * ((b - a) / 2 * Real.sin θ) * √(wellFactor U a b (orbitPosition a b θ)) := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitRate m U a b θ = √(m / 2) / √(wellFactor U a b (orbitPosition a b θ)) := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) :
    orbitPeriod m U a b = ∫ θ in (0 : ℝ)..2 * π, orbitRate m U a b θ := rfl

example (a b : ℝ) :
    orbitPosition a b 0 = a :=
  orbitPosition_zero a b

example (a b : ℝ) :
    orbitPosition a b π = b :=
  orbitPosition_pi a b

example (a b θ : ℝ) :
    orbitPosition a b (θ + 2 * π) = orbitPosition a b θ :=
  orbitPosition_add_two_pi a b θ

example (a b θ : ℝ) :
    orbitPosition a b (-θ) = orbitPosition a b θ :=
  orbitPosition_neg a b θ

example (hab : a ≤ b) (θ : ℝ) :
    orbitPosition a b θ ∈ Icc a b :=
  orbitPosition_mem_Icc hab θ

example (a b θ : ℝ) :
    (orbitPosition a b θ - a) * (b - orbitPosition a b θ) = ((b - a) / 2 * Real.sin θ) ^ 2 :=
  orbitPosition_sub_mul_sub a b θ

example (a b θ : ℝ) :
    HasDerivAt (orbitPosition a b) ((b - a) / 2 * Real.sin θ) θ :=
  hasDerivAt_orbitPosition a b θ

example (a b : ℝ) :
    ContDiff ℝ ∞ (orbitPosition a b) :=
  contDiff_orbitPosition a b

example (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) :
    orbitMomentum m U a b 0 = 0 :=
  orbitMomentum_zero m U a b

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitMomentum m U a b (θ + 2 * π) = orbitMomentum m U a b θ :=
  orbitMomentum_add_two_pi m U a b θ

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitMomentum m U a b (-θ) = -orbitMomentum m U a b θ :=
  orbitMomentum_neg m U a b θ

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitRate m U a b (θ + 2 * π) = orbitRate m U a b θ :=
  orbitRate_add_two_pi m U a b θ

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitRate m U a b (-θ) = orbitRate m U a b θ :=
  orbitRate_neg m U a b θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (θ : ℝ) :
    0 < wellFactor U a b (orbitPosition a b θ) :=
  IsWell.wellFactor_orbitPosition_pos h hU θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (θ : ℝ) :
    0 < orbitRate m U a b θ :=
  IsWell.orbitRate_pos h hU hm θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (θ : ℝ) :
    orbitMomentum m U a b θ ^ 2 / (2 * m) + U (orbitPosition a b θ) = E :=
  IsWell.orbit_energy h hU hm θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (θ : ℝ) :
    orbitMomentum m U a b θ ^ 2 = 2 * m * (E - U (orbitPosition a b θ)) :=
  IsWell.orbitMomentum_sq h hU hm θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (θ : ℝ) :
    orbitRate m U a b θ * (orbitMomentum m U a b θ / m) = (b - a) / 2 * Real.sin θ :=
  IsWell.orbitRate_mul_orbitMomentum h hU hm θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (x : ℝ) :
    -deriv U x = (a + b - 2 * x) * wellFactor U a b x +
      (x - a) * (b - x) * deriv (wellFactor U a b) x :=
  IsWell.neg_deriv_eq h hU x

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    HasDerivAt (orbitMomentum m U a b)
      (-(orbitRate m U a b θ * deriv U (orbitPosition a b θ))) θ :=
  IsWell.hasDerivAt_orbitMomentum h hU m θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m : ℝ) :
    orbitPeriod m U a b = √(2 * m) * ∫ x in a..b, 1 / √(E - U x) :=
  IsWell.orbitPeriod_eq h hU m

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    0 < orbitPeriod m U a b :=
  IsWell.orbitPeriod_pos h hU hm


end Orbit

section Motion

variable {U : ℝ → ℝ} {E a b m : ℝ}

example (m : ℝ) (U : ℝ → ℝ) (z : ℝ × ℝ) : field m U z = (z.2 / m, -deriv U z.1) := rfl

example (m : ℝ) (U : ℝ → ℝ) (z : ℝ × ℝ) : energy m U z = z.2 ^ 2 / (2 * m) + U z.1 := rfl

example (m : ℝ) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (field m U) :=
  contDiff_field m hU

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitPoint m U a b θ = (orbitPosition a b θ, orbitMomentum m U a b θ) := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitTime m U a b θ = ∫ s in (0 : ℝ)..θ, orbitRate m U a b s := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b t : ℝ) :
    orbitAngle m U a b t = flow (fun ϑ => (orbitRate m U a b ϑ)⁻¹) (t, 0) := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b t : ℝ) :
    wellMotion m U a b t = orbitPoint m U a b (orbitAngle m U a b t) := rfl

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m : ℝ) :
    ContDiff ℝ ∞ (orbitRate m U a b) :=
  IsWell.contDiff_orbitRate h hU m

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    ContDiff ℝ ∞ fun ϑ => (orbitRate m U a b ϑ)⁻¹ :=
  IsWell.contDiff_inv_orbitRate h hU hm

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    flowDomain (fun ϑ => (orbitRate m U a b ϑ)⁻¹) = univ :=
  IsWell.flowDomain_inv_orbitRate h hU hm

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    HasDerivAt (orbitAngle m U a b) (orbitRate m U a b (orbitAngle m U a b t))⁻¹ t :=
  IsWell.hasDerivAt_orbitAngle h hU hm t

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    HasDerivAt (orbitTime m U a b) (orbitRate m U a b θ) θ :=
  IsWell.hasDerivAt_orbitTime h hU m θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    StrictMono (orbitTime m U a b) :=
  IsWell.strictMono_orbitTime h hU hm

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    orbitTime m U a b (orbitAngle m U a b t) = t :=
  IsWell.orbitTime_orbitAngle h hU hm t

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (θ : ℝ) :
    orbitAngle m U a b (orbitTime m U a b θ) = θ :=
  IsWell.orbitAngle_orbitTime h hU hm θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    orbitAngle m U a b (orbitPeriod m U a b) = 2 * π :=
  IsWell.orbitAngle_orbitPeriod h hU hm

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    HasDerivAt (wellMotion m U a b) (field m U (wellMotion m U a b t)) t :=
  IsWell.hasDerivAt_wellMotion h hU hm t

example (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) :
    wellMotion m U a b 0 = (a, 0) :=
  IsWell.wellMotion_zero m U a b

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    wellMotion m U a b (orbitPeriod m U a b) = (a, 0) :=
  IsWell.wellMotion_orbitPeriod h hU hm

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    wellMotion m U a b (t + orbitPeriod m U a b) = wellMotion m U a b t :=
  IsWell.wellMotion_add_period h hU hm t

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (t : ℝ) :
    energy m U (wellMotion m U a b t) = E :=
  IsWell.energy_wellMotion h hU hm t

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) (t : ℝ) :
    (t, (a, (0 : ℝ))) ∈ flowDomain (field m U) ∧
      flow (field m U) (t, (a, 0)) = wellMotion m U a b t :=
  IsWell.flow_field_eq h hU hm t

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc a b) (hE : energy m U z = E) :
    ∃ θ, orbitPoint m U a b θ = z :=
  IsWell.exists_orbitPoint_eq h hU hm hz hE

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {z : ℝ × ℝ} (hz : z.1 ∈ Icc a b) (hE : energy m U z = E) :
    ∃ t, wellMotion m U a b t = z :=
  IsWell.exists_wellMotion_eq h hU hm hz hE

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {y : ℝ → ℝ × ℝ} (hy : ∀ t, HasDerivAt y (field m U (y t)) t) (hz : (y 0).1 ∈ Icc a b)
    (hE : energy m U (y 0) = E) (t : ℝ) :
    y (t + orbitPeriod m U a b) = y t :=
  IsWell.add_period_of_hasDerivAt h hU hm hy hz hE t

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {x v : ℝ → ℝ} (hx : ∀ t, HasDerivAt x (v t) t)
    (hv : ∀ t, HasDerivAt v (-deriv U (x t) / m) t) (h0 : x 0 ∈ Icc a b)
    (hE : m * v 0 ^ 2 / 2 + U (x 0) = E) (t : ℝ) :
    x (t + orbitPeriod m U a b) = x t :=
  IsWell.position_add_period h hU hm hx hv h0 hE t


end Motion

section Area

variable {U : ℝ → ℝ} {E a b m : ℝ}

example (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : orbitArea m U a b =
    ∫ θ in (0 : ℝ)..2 * π, orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) := rfl

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m : ℝ) :
    Continuous (orbitMomentum m U a b) :=
  IsWell.continuous_orbitMomentum h hU m

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    orbitMomentum m U a b θ = √(2 * m * (E - U (orbitPosition a b θ))) :=
  IsWell.orbitMomentum_eq_sqrt h hU hm hθ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    orbitArea m U a b = 2 * ∫ x in a..b, √(2 * m * (E - U x)) :=
  IsWell.orbitArea_eq h hU hm

example (hU : ContDiff ℝ ∞ U) (m : ℝ) {J : Set ℝ}
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2)
      (Prod.fst ⁻¹' J) :=
  contDiffOn_orbitMomentum_family hU m hα hβ hw

example {α β : ℝ → ℝ} {E₀ α' β' : ℝ}
    (hα : HasDerivAt α α' E₀) (hβ : HasDerivAt β β' E₀) (θ : ℝ) :
    HasDerivAt (fun E => orbitPosition (α E) (β E) θ)
      ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) E₀ :=
  hasDerivAt_orbitPosition_energy hα hβ θ

example (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ}
    (hJ : IsOpen J) {α β : ℝ → ℝ} (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ}
    (hE₀ : E₀ ∈ J) {α' β' PE : ℝ} (hα : HasDerivAt α α' E₀) (hβ : HasDerivAt β β' E₀)
    {θ : ℝ} (hPE : HasDerivAt (fun E => orbitMomentum m U (α E) (β E) θ) PE E₀) :
    orbitMomentum m U (α E₀) (β E₀) θ * PE / m +
      deriv U (orbitPosition (α E₀) (β E₀) θ) *
        ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) = 1 :=
  orbitMomentum_mul_deriv_energy hU hm hJ hw hE₀ hα hβ hPE

example (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ} (hJ : IsOpen J)
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ} (hE₀ : E₀ ∈ J) :
    HasDerivAt (fun E => orbitArea m U (α E) (β E)) (orbitPeriod m U (α E₀) (β E₀)) E₀ :=
  hasDerivAt_orbitArea hU hm hJ hα hβ hw hE₀

example (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {E₀ a₀ b₀ : ℝ}
    (h : IsWell U E₀ a₀ b₀) :
    ∃ (J : Set ℝ) (α β : ℝ → ℝ), IsOpen J ∧ E₀ ∈ J ∧ α E₀ = a₀ ∧ β E₀ = b₀ ∧
      ContDiffOn ℝ ∞ α J ∧ ContDiffOn ℝ ∞ β J ∧ (∀ E ∈ J, IsWell U E (α E) (β E)) ∧
      HasDerivAt (fun E => orbitArea m U (α E) (β E)) (orbitPeriod m U a₀ b₀) E₀ :=
  IsWell.exists_hasDerivAt_orbitArea hU hm h


end Area

section Abel

variable {U : ℝ → ℝ}

example (u V : ℝ) :
    ∫⁻ E, ENNReal.ofReal (1 / √(E - u)) * ENNReal.ofReal (1 / √(V - E)) =
      if u < V then ENNReal.ofReal π else 0 :=
  lintegral_inv_sqrt_mul_inv_sqrt u V

example (hU : Measurable U) (Ω : Set ℝ) (V : ℝ) :
    ∫⁻ E, (∫⁻ x in Ω, ENNReal.ofReal (1 / √(E - U x))) * ENNReal.ofReal (1 / √(V - E)) =
      ENNReal.ofReal π * volume (Ω ∩ {x | U x < V}) :=
  lintegral_levelTime_mul hU Ω V

example {E a b m : ℝ} (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U)
    (hm : 0 < m) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (1 / √(E - U x)) =
      ENNReal.ofReal (orbitPeriod m U a b / √(2 * m)) :=
  IsWell.lintegral_inv_sqrt_eq h hU hm

example (hU : ContDiff ℝ ∞ U) {m : ℝ} (hm : 0 < m) {E₀ V : ℝ} {x₁ x₂ : ℝ → ℝ}
    (hV : IsWell U V (x₁ V) (x₂ V)) (hw : ∀ E ∈ Ioo E₀ V, IsWell U E (x₁ E) (x₂ E))
    (hnest : ∀ E ∈ Ioo E₀ V, ∀ x, x ∈ Ioo (x₁ E) (x₂ E) ↔ x ∈ Ioo (x₁ V) (x₂ V) ∧ U x < E)
    (hbot : ∀ x ∈ Ioo (x₁ V) (x₂ V), E₀ ≤ U x) :
    x₂ V - x₁ V = 1 / (π * √(2 * m)) *
      ∫ E in Ioo E₀ V, orbitPeriod m U (x₁ E) (x₂ E) / √(V - E) :=
  abel_inversion hU hm hV hw hnest hbot


end Abel

section ActionAngle

variable {U : ℝ → ℝ} {E a b m : ℝ}

example (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : orbitAction m U a b = orbitArea m U a b / (2 * π) := rfl

example (m : ℝ) (U : ℝ → ℝ) (a b θ : ℝ) :
    orbitPhase m U a b θ = 2 * π * orbitTime m U a b θ / orbitPeriod m U a b := rfl

example (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ} (hJ : IsOpen J)
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ} (hE₀ : E₀ ∈ J) :
    HasDerivAt (fun E => orbitAction m U (α E) (β E))
      (orbitPeriod m U (α E₀) (β E₀) / (2 * π)) E₀ :=
  hasDerivAt_orbitAction hU hm hJ hα hβ hw hE₀

example (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ}
    (hJ : IsOpen J) {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {s : Set ℝ} (hs : s ⊆ J) (hconn : s.OrdConnected) :
    StrictMonoOn (fun E => orbitAction m U (α E) (β E)) s :=
  strictMonoOn_orbitAction hU hm hJ hα hβ hw hs hconn

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    orbitTime m U a b (θ + 2 * π) = orbitTime m U a b θ + orbitPeriod m U a b :=
  IsWell.orbitTime_add_two_pi h hU m θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m θ : ℝ) :
    HasDerivAt (orbitPhase m U a b)
      (2 * π * orbitRate m U a b θ / orbitPeriod m U a b) θ :=
  IsWell.hasDerivAt_orbitPhase h hU m θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (θ : ℝ) :
    orbitPhase m U a b (θ + 2 * π) = orbitPhase m U a b θ + 2 * π :=
  IsWell.orbitPhase_add_two_pi h hU hm θ

example (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    (t : ℝ) :
    orbitPhase m U a b (orbitAngle m U a b t) = 2 * π / orbitPeriod m U a b * t :=
  IsWell.orbitPhase_orbitAngle h hU hm t

example (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ} (hJ : IsOpen J)
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ} (hE₀ : E₀ ∈ J) (θ : ℝ) {PE : ℝ}
    (hPE : HasDerivAt (fun E => orbitMomentum m U (α E) (β E) θ) PE E₀) :
    deriv (fun E => orbitPosition (α E) (β E) θ) E₀ *
        deriv (orbitMomentum m U (α E₀) (β E₀)) θ -
      deriv (orbitPosition (α E₀) (β E₀)) θ * PE =
      -(deriv (orbitPhase m U (α E₀) (β E₀)) θ *
        deriv (fun E => orbitAction m U (α E) (β E)) E₀) :=
  orbit_area_form hU hm hJ hα hβ hw hE₀ θ hPE


end ActionAngle

section Oscillator

variable {k m E : ℝ}

example (k : ℝ) :
    ContDiff ℝ ∞ fun x : ℝ => k / 2 * x ^ 2 :=
  contDiff_oscillator k

example (k x : ℝ) :
    deriv (fun x : ℝ => k / 2 * x ^ 2) x = k * x :=
  deriv_oscillator k x

example (hk : 0 < k) (hE : 0 < E) {x : ℝ}
    (hx : x ∈ Icc (-√(2 * E / k)) √(2 * E / k)) :
    wellFactor (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) x = k / 2 :=
  wellFactor_oscillator hk hE hx

example (hk : 0 < k) (hE : 0 < E) (m θ : ℝ) :
    orbitRate m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) θ = √(m / k) :=
  orbitRate_oscillator hk hE m θ

example (hk : 0 < k) (hE : 0 < E) (m : ℝ) :
    orbitPeriod m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) =
      2 * π * √(m / k) :=
  orbitPeriod_oscillator hk hE m

example (hk : 0 < k) (hm : 0 < m) (hE : 0 < E) :
    orbitAction m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k)) √(2 * E / k) =
      E * √(m / k) :=
  orbitAction_oscillator hk hm hE

example (hk : 0 < k) (hm : 0 < m) {V : ℝ} (hV : 0 < V) :
    √(2 * V / k) - -√(2 * V / k) = 1 / (π * √(2 * m)) *
      ∫ E in Ioo 0 V, orbitPeriod m (fun x : ℝ => k / 2 * x ^ 2) (-√(2 * E / k))
        √(2 * E / k) / √(V - E) :=
  abel_inversion_oscillator hk hm hV


end Oscillator
