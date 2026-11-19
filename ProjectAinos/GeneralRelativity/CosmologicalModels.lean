/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.FLRW
public import ProjectAinos.GeneralRelativity.ObserverMeasurement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The closed and the open isotropic models

Landau–Lifshitz, §§112–113, with `c = 1`, a coupling constant `κ` and `Λ = 0`. In the conformal
time `η` the lapse is the scale factor, `N = a` (`conformalData`), and the metric is
`ds² = a(η)² (−dη² + ψ_k⁻² (dx₁² + dx₂² + dx₃²))`. The Friedmann equations of
`FLRW.isEinstein_iff_friedmann` become, without denominators,
`a'² + k a² = (κρ + Λ) a⁴/3` and `2aa'' − a'² + k a² = (−κp + Λ) a⁴`
(`firstFriedmann_conformal_iff`, `secondFriedmann_conformal_iff`, `isEinstein_conformal_iff`).

* **Dust** `p = 0`, `ρ = c/(κa³)` (`dustDensity`, `isEinstein_dust`) and **radiation**
  `p = ρ/3`, `ρ = 3a₀²/(κa⁴)` (`radiationDensity`, `radiationPressure`, `isEinstein_radiation`).
* The exact models, each a solution of the Einstein equations with the comoving fluid for every
  `κ ≠ 0`:
  closed dust `a = a₀(1 − cos η)` on `(0, 2π)`, `ρ = 6a₀/(κa³)` (`closedDust`,
  `isEinstein_closedDust`, Landau–Lifshitz (112.8));
  closed radiation `a = a₀ sin η` on `(0, π)` (`closedRadiation`, `isEinstein_closedRadiation`,
  the form of (112.12)–(112.13));
  open dust `a = a₀(cosh η − 1)` on `η > 0` (`openDust`, `isEinstein_openDust`, (113.3));
  open radiation `a = a₀ sinh η` (`openRadiation`, `isEinstein_openRadiation`);
  flat dust `a = a₀η²`, `ρ = 12a₀/(κa³)` (`flatDust`, `isEinstein_flatDust`) and flat radiation
  `a = a₀η` (`flatRadiation`, `isEinstein_flatRadiation`). For `κ > 0` the densities are
  positive (`dustDensity_pos`, `radiationDensity_pos`).
* **The cosmic time.** `t(η)` with `dt/dη = a` (`closedDustTime`, `openDustTime`,
  `closedRadiationTime`, `openRadiationTime`, `flatDustTime`, `flatRadiationTime` and their
  `hasDerivAt_*` lemmas): closed dust `t = a₀(η − sin η)`, open dust `t = a₀(sinh η − η)`
  ((112.9), (113.4)). It is the proper time of the comoving observers:
  `properTime_comoving` (for any lapse `N` and any `T` with `T' = N`), `properTime_closedDust`,
  `properTime_openDust`; with `N = 1` the comoving observer of de Sitter space is an instance
  (`deSitterObserver`, `properTime_deSitter`).
* **Closed dust from the singularity to the maximal expansion**: `a ≤ 2a₀ = a(π)`,
  `ȧ(π) = 0`, and the cosmic time from `η = 0` to `η = π` is `πa_m/2` with `a_m = 2a₀`
  (`closedDust_a_le`, `closedDust_a_pi`, `deriv_closedDust_a_pi`, `closedDustTime_pi_sub_zero`,
  `tendsto_closedDust_age`); the whole cycle lasts `2πa₀` (`closedDustTime_two_pi_sub_zero`).
* **The open and flat models expand forever** (`open_expands_forever`, `open_strictMonoOn`): in
  the cosmic time on a connected set of times, with `k ≤ 0`, `Λ = 0`, `κ > 0`, a density
  `ρ ≥ 0` (and `ρ > 0` when `k = 0`) and the first Friedmann equation, `ȧ² = κρa²/3 − k` never
  vanishes, so an expansion at one time is an expansion at all times. The Milne universe is an
  instance (`milne_expands`).
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.CosmologicalModels

open SmoothGeometry CoordinateMetric FLRW

local notation "E" => MinkowskiModel 3

/-! ### The conformal time -/

/-- **The isotropic model in the conformal time** (Landau–Lifshitz, §112): the lapse is the scale
factor, `N = a`, so that `ds² = a(η)² (−dη² + ψ_k⁻² (dx₁² + dx₂² + dx₃²))` for `η ∈ I`. -/
def conformalData (I : Set ℝ) (a : ℝ → ℝ) (k : ℝ) (hI : IsOpen I) (ha : ContDiffOn ℝ ∞ a I)
    (hpos : ∀ η ∈ I, 0 < a η) : Data where
  I := I
  N := a
  a := a
  k := k
  isOpen_I := hI
  contDiffOn_N := ha
  contDiffOn_a := ha
  N_pos := hpos
  a_pos := hpos

variable {D : Data}

/-- **The first Friedmann equation in the conformal time**: with `N = a`, it is
`a'² + k a² = (κρ + Λ) a⁴/3`. -/
theorem firstFriedmann_conformal_iff (hN : D.N = D.a) {η : ℝ} (hη : η ∈ D.I) (κ Λ : ℝ)
    (ρ : ℝ → ℝ) :
    FirstFriedmann D κ Λ ρ η ↔
      deriv D.a η ^ 2 + D.k * D.a η ^ 2 = (κ * ρ η + Λ) * D.a η ^ 4 / 3 := by
  rw [firstFriedmann_iff_firstDefect hη, firstDefect, hN]
  constructor <;> intro h <;> linear_combination h

/-- **The second Friedmann equation in the conformal time**: with `N = a`, it is
`2aa'' − a'² + k a² = (−κp + Λ) a⁴`. -/
theorem secondFriedmann_conformal_iff (hN : D.N = D.a) {η : ℝ} (hη : η ∈ D.I) (κ Λ : ℝ)
    (p : ℝ → ℝ) :
    SecondFriedmann D κ Λ p η ↔
      2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 =
        (-κ * p η + Λ) * D.a η ^ 4 := by
  have ha := (D.a_pos η hη).ne'
  have he : secondDefect D κ Λ p η = D.a η * (2 * D.a η * deriv (deriv D.a) η -
      deriv D.a η ^ 2 + D.k * D.a η ^ 2 - (-κ * p η + Λ) * D.a η ^ 4) := by
    unfold secondDefect
    rw [hN]
    ring
  rw [secondFriedmann_iff_secondDefect hη, he, mul_eq_zero, sub_eq_zero]
  exact or_iff_right ha

/-- **The Einstein equations in the conformal time**: with `N = a`, the metric with the comoving
fluid satisfies `G_{ik} + Λ g_{ik} = κ T_{ik}` if and only if on `I`
`a'² + k a² = (κρ + Λ) a⁴/3` and `2aa'' − a'² + k a² = (−κp + Λ) a⁴`. -/
theorem isEinstein_conformal_iff (hN : D.N = D.a) (κ Λ : ℝ) (ρ p : ℝ → ℝ) :
    (metric D).IsEinstein κ Λ (perfectFluidStress D ρ p) ↔ ∀ η ∈ D.I,
      deriv D.a η ^ 2 + D.k * D.a η ^ 2 = (κ * ρ η + Λ) * D.a η ^ 4 / 3 ∧
        2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 =
          (-κ * p η + Λ) * D.a η ^ 4 := by
  rw [isEinstein_iff_friedmann]
  refine forall₂_congr fun η hη => ?_
  rw [firstFriedmann_conformal_iff hN hη, secondFriedmann_conformal_iff hN hη]

/-! ### Dust and radiation -/

/-- The density `ρ = c/(κa³)` of dust, whose energy `ρa³` in a comoving volume is constant. -/
def dustDensity (κ c : ℝ) (a : ℝ → ℝ) (η : ℝ) : ℝ := c / (κ * a η ^ 3)

/-- The density `ρ = 3a₀²/(κa⁴)` of radiation, whose energy `ρa⁴` is constant. -/
def radiationDensity (κ a₀ : ℝ) (a : ℝ → ℝ) (η : ℝ) : ℝ := 3 * a₀ ^ 2 / (κ * a η ^ 4)

/-- The pressure `p = ρ/3` of radiation. -/
def radiationPressure (κ a₀ : ℝ) (a : ℝ → ℝ) (η : ℝ) : ℝ := radiationDensity κ a₀ a η / 3

/-- For `κ > 0` and `c > 0` the dust density is positive where `a > 0`. -/
theorem dustDensity_pos {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) {a : ℝ → ℝ} {η : ℝ}
    (ha : 0 < a η) : 0 < dustDensity κ c a η := by
  unfold dustDensity
  positivity

/-- For `κ > 0` and `a₀ ≠ 0` the radiation density is positive where `a > 0`. -/
theorem radiationDensity_pos {κ a₀ : ℝ} (hκ : 0 < κ) (ha₀ : a₀ ≠ 0) {a : ℝ → ℝ} {η : ℝ}
    (ha : 0 < a η) : 0 < radiationDensity κ a₀ a η := by
  unfold radiationDensity
  positivity

/-- **Dust in the conformal time**: if `a'² + k a² = ca/3` and `2aa'' − a'² + k a² = 0` on `I`,
the metric with the dust `ρ = c/(κa³)`, `p = 0` satisfies the Einstein equations with `Λ = 0`. -/
theorem isEinstein_dust (hN : D.N = D.a) {κ : ℝ} (hκ : κ ≠ 0) (c : ℝ)
    (h1 : ∀ η ∈ D.I, deriv D.a η ^ 2 + D.k * D.a η ^ 2 = c * D.a η / 3)
    (h2 : ∀ η ∈ D.I, 2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 = 0) :
    (metric D).IsEinstein κ 0 (perfectFluidStress D (dustDensity κ c D.a) 0) := by
  rw [isEinstein_conformal_iff hN]
  intro η hη
  have ha := (D.a_pos η hη).ne'
  refine ⟨?_, ?_⟩
  · rw [h1 η hη, dustDensity]
    field_simp
    ring
  · rw [h2 η hη]
    simp

/-- **Radiation in the conformal time**: if `a'² + k a² = a₀²` and `2aa'' − a'² + k a² = −a₀²`
on `I`, the metric with the radiation `ρ = 3a₀²/(κa⁴)`, `p = ρ/3` satisfies the Einstein
equations with `Λ = 0`. -/
theorem isEinstein_radiation (hN : D.N = D.a) {κ : ℝ} (hκ : κ ≠ 0) (a₀ : ℝ)
    (h1 : ∀ η ∈ D.I, deriv D.a η ^ 2 + D.k * D.a η ^ 2 = a₀ ^ 2)
    (h2 : ∀ η ∈ D.I,
      2 * D.a η * deriv (deriv D.a) η - deriv D.a η ^ 2 + D.k * D.a η ^ 2 = -a₀ ^ 2) :
    (metric D).IsEinstein κ 0
      (perfectFluidStress D (radiationDensity κ a₀ D.a) (radiationPressure κ a₀ D.a)) := by
  rw [isEinstein_conformal_iff hN]
  intro η hη
  have ha := (D.a_pos η hη).ne'
  refine ⟨?_, ?_⟩
  · rw [h1 η hη, radiationDensity]
    field_simp
    ring
  · rw [h2 η hη, radiationPressure, radiationDensity]
    field_simp
    ring

/-! ### The closed model filled with dust -/

variable {a₀ : ℝ}

/-- `a₀(1 − cos η) > 0` for `0 < η < 2π`. -/
theorem closedDust_pos (ha₀ : 0 < a₀) {η : ℝ} (hη : η ∈ Ioo 0 (2 * π)) :
    0 < a₀ * (1 - Real.cos η) := by
  have hne : Real.cos η ≠ 1 := fun h =>
    hη.1.ne' ((Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hη.1, Real.pi_pos]) hη.2).mp h)
  exact mul_pos ha₀ (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one η) hne))

/-- **The closed model filled with dust** in the conformal time (Landau–Lifshitz, (112.8)):
`k = 1` and `a = a₀(1 − cos η)` for `0 < η < 2π`. -/
def closedDust (a₀ : ℝ) (ha₀ : 0 < a₀) : Data :=
  conformalData (Ioo 0 (2 * π)) (fun η => a₀ * (1 - Real.cos η)) 1 isOpen_Ioo
    (contDiff_const.mul (contDiff_const.sub Real.contDiff_cos)).contDiffOn
    fun _ hη => closedDust_pos ha₀ hη

/-- `a' = a₀ sin η`. -/
theorem deriv_closedDust_a (ha₀ : 0 < a₀) :
    deriv (closedDust a₀ ha₀).a = fun η => a₀ * Real.sin η := by
  funext η
  have h := ((Real.hasDerivAt_cos η).const_sub 1).const_mul a₀
  rw [show (closedDust a₀ ha₀).a = fun η => a₀ * (1 - Real.cos η) from rfl, h.deriv]
  ring

/-- `(a₀ sin η)' = a₀ cos η`. -/
theorem deriv_const_mul_sin (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.sin η) = fun η => a₀ * Real.cos η :=
  funext fun η => ((Real.hasDerivAt_sin η).const_mul a₀).deriv

/-- **The closed dust model solves the Einstein equations** with `ρ = 6a₀/(κa³)` and `p = 0`
(Landau–Lifshitz, (112.8)), for every `κ ≠ 0`. -/
theorem isEinstein_closedDust (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (closedDust a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (closedDust a₀ ha₀)
        (dustDensity κ (6 * a₀) (closedDust a₀ ha₀).a) 0) := by
  refine isEinstein_dust rfl hκ (6 * a₀) (fun η _ => ?_) (fun η _ => ?_)
  · rw [deriv_closedDust_a]
    simp only [closedDust, conformalData]
    linear_combination a₀ ^ 2 * Real.sin_sq_add_cos_sq η
  · rw [deriv_closedDust_a, deriv_const_mul_sin]
    simp only [closedDust, conformalData]
    linear_combination -a₀ ^ 2 * Real.sin_sq_add_cos_sq η

/-! ### The closed model filled with radiation -/

/-- **The closed model filled with radiation** in the conformal time (Landau–Lifshitz,
(112.12)–(112.13)): `k = 1` and `a = a₀ sin η` for `0 < η < π`. -/
def closedRadiation (a₀ : ℝ) (ha₀ : 0 < a₀) : Data :=
  conformalData (Ioo 0 π) (fun η => a₀ * Real.sin η) 1 isOpen_Ioo
    (contDiff_const.mul Real.contDiff_sin).contDiffOn
    fun _ hη => mul_pos ha₀ (Real.sin_pos_of_pos_of_lt_pi hη.1 hη.2)

/-- `(a₀ cos η)' = −a₀ sin η`. -/
theorem deriv_const_mul_cos (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.cos η) = fun η => -(a₀ * Real.sin η) := by
  funext η
  rw [((Real.hasDerivAt_cos η).const_mul a₀).deriv]
  ring

/-- **The closed radiation model solves the Einstein equations** with `ρ = 3a₀²/(κa⁴)` and
`p = ρ/3`, for every `κ ≠ 0`. -/
theorem isEinstein_closedRadiation (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (closedRadiation a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (closedRadiation a₀ ha₀)
        (radiationDensity κ a₀ (closedRadiation a₀ ha₀).a)
        (radiationPressure κ a₀ (closedRadiation a₀ ha₀).a)) := by
  have hd : deriv (closedRadiation a₀ ha₀).a = fun η => a₀ * Real.cos η :=
    deriv_const_mul_sin a₀
  refine isEinstein_radiation rfl hκ a₀ (fun η _ => ?_) (fun η _ => ?_)
  · rw [hd]
    simp only [closedRadiation, conformalData]
    linear_combination a₀ ^ 2 * Real.sin_sq_add_cos_sq η
  · rw [hd, deriv_const_mul_cos]
    simp only [closedRadiation, conformalData]
    linear_combination -a₀ ^ 2 * Real.sin_sq_add_cos_sq η

/-! ### The open model filled with dust -/

/-- `a₀(cosh η − 1) > 0` for `η > 0`. -/
theorem openDust_pos (ha₀ : 0 < a₀) {η : ℝ} (hη : η ∈ Ioi 0) : 0 < a₀ * (Real.cosh η - 1) :=
  mul_pos ha₀ (sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt hη)))

/-- **The open model filled with dust** in the conformal time (Landau–Lifshitz, (113.3)):
`k = −1` and `a = a₀(cosh η − 1)` for `η > 0`. -/
def openDust (a₀ : ℝ) (ha₀ : 0 < a₀) : Data :=
  conformalData (Ioi 0) (fun η => a₀ * (Real.cosh η - 1)) (-1) isOpen_Ioi
    (contDiff_const.mul (Real.contDiff_cosh.sub contDiff_const)).contDiffOn
    fun _ hη => openDust_pos ha₀ hη

/-- `a' = a₀ sinh η`. -/
theorem deriv_openDust_a (ha₀ : 0 < a₀) :
    deriv (openDust a₀ ha₀).a = fun η => a₀ * Real.sinh η :=
  funext fun η => (((Real.hasDerivAt_cosh η).sub_const 1).const_mul a₀).deriv

/-- `(a₀ sinh η)' = a₀ cosh η`. -/
theorem deriv_const_mul_sinh (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.sinh η) = fun η => a₀ * Real.cosh η :=
  funext fun η => ((Real.hasDerivAt_sinh η).const_mul a₀).deriv

/-- `(a₀ cosh η)' = a₀ sinh η`. -/
theorem deriv_const_mul_cosh (a₀ : ℝ) :
    deriv (fun η => a₀ * Real.cosh η) = fun η => a₀ * Real.sinh η :=
  funext fun η => ((Real.hasDerivAt_cosh η).const_mul a₀).deriv

/-- **The open dust model solves the Einstein equations** with `ρ = 6a₀/(κa³)` and `p = 0`
(Landau–Lifshitz, (113.3)), for every `κ ≠ 0`. -/
theorem isEinstein_openDust (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (openDust a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (openDust a₀ ha₀) (dustDensity κ (6 * a₀) (openDust a₀ ha₀).a) 0) := by
  refine isEinstein_dust rfl hκ (6 * a₀) (fun η _ => ?_) (fun η _ => ?_)
  · rw [deriv_openDust_a]
    simp only [openDust, conformalData]
    linear_combination -a₀ ^ 2 * Real.cosh_sq_sub_sinh_sq η
  · rw [deriv_openDust_a, deriv_const_mul_sinh]
    simp only [openDust, conformalData]
    linear_combination a₀ ^ 2 * Real.cosh_sq_sub_sinh_sq η

/-! ### The open model filled with radiation -/

/-- **The open model filled with radiation** in the conformal time: `k = −1` and
`a = a₀ sinh η` for `η > 0`. -/
def openRadiation (a₀ : ℝ) (ha₀ : 0 < a₀) : Data :=
  conformalData (Ioi 0) (fun η => a₀ * Real.sinh η) (-1) isOpen_Ioi
    (contDiff_const.mul Real.contDiff_sinh).contDiffOn
    fun _ hη => mul_pos ha₀ (Real.sinh_pos_iff.mpr hη)

/-- **The open radiation model solves the Einstein equations** with `ρ = 3a₀²/(κa⁴)` and
`p = ρ/3`, for every `κ ≠ 0`. -/
theorem isEinstein_openRadiation (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (openRadiation a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (openRadiation a₀ ha₀)
        (radiationDensity κ a₀ (openRadiation a₀ ha₀).a)
        (radiationPressure κ a₀ (openRadiation a₀ ha₀).a)) := by
  have hd : deriv (openRadiation a₀ ha₀).a = fun η => a₀ * Real.cosh η :=
    deriv_const_mul_sinh a₀
  refine isEinstein_radiation rfl hκ a₀ (fun η _ => ?_) (fun η _ => ?_)
  · rw [hd]
    simp only [openRadiation, conformalData]
    linear_combination a₀ ^ 2 * Real.cosh_sq_sub_sinh_sq η
  · rw [hd, deriv_const_mul_cosh]
    simp only [openRadiation, conformalData]
    linear_combination -a₀ ^ 2 * Real.cosh_sq_sub_sinh_sq η

/-! ### The flat models -/

/-- **The flat model filled with dust** in the conformal time: `k = 0` and `a = a₀η²` for
`η > 0`. -/
def flatDust (a₀ : ℝ) (ha₀ : 0 < a₀) : Data :=
  conformalData (Ioi 0) (fun η => a₀ * η ^ 2) 0 isOpen_Ioi
    (contDiff_const.mul (contDiff_id.pow 2)).contDiffOn
    fun _ hη => mul_pos ha₀ (pow_pos hη 2)

/-- `a' = 2a₀η`. -/
theorem deriv_flatDust_a (ha₀ : 0 < a₀) :
    deriv (flatDust a₀ ha₀).a = fun η => 2 * a₀ * η := by
  funext η
  rw [show (flatDust a₀ ha₀).a = fun η => a₀ * η ^ 2 from rfl,
    ((hasDerivAt_pow 2 η).const_mul a₀).deriv]
  push_cast
  ring

/-- `(2a₀η)' = 2a₀`. -/
theorem deriv_flatDust_velocity (a₀ : ℝ) : deriv (fun η : ℝ => 2 * a₀ * η) = fun _ => 2 * a₀ :=
  funext fun η => ((hasDerivAt_id' η).const_mul (2 * a₀)).deriv.trans (mul_one _)

/-- **The flat dust model solves the Einstein equations** with `ρ = 12a₀/(κa³)` and `p = 0`, for
every `κ ≠ 0`. -/
theorem isEinstein_flatDust (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (flatDust a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (flatDust a₀ ha₀) (dustDensity κ (12 * a₀) (flatDust a₀ ha₀).a) 0) := by
  refine isEinstein_dust rfl hκ (12 * a₀) (fun η _ => ?_) (fun η _ => ?_)
  · rw [deriv_flatDust_a]
    simp only [flatDust, conformalData]
    ring
  · rw [deriv_flatDust_a, deriv_flatDust_velocity]
    simp only [flatDust, conformalData]
    ring

/-- **The flat model filled with radiation** in the conformal time: `k = 0` and `a = a₀η` for
`η > 0`. -/
def flatRadiation (a₀ : ℝ) (ha₀ : 0 < a₀) : Data :=
  conformalData (Ioi 0) (fun η => a₀ * η) 0 isOpen_Ioi
    (contDiff_const.mul contDiff_id).contDiffOn
    fun _ hη => mul_pos ha₀ hη

/-- **The flat radiation model solves the Einstein equations** with `ρ = 3a₀²/(κa⁴)` and
`p = ρ/3`, for every `κ ≠ 0`. -/
theorem isEinstein_flatRadiation (ha₀ : 0 < a₀) {κ : ℝ} (hκ : κ ≠ 0) :
    (metric (flatRadiation a₀ ha₀)).IsEinstein κ 0
      (perfectFluidStress (flatRadiation a₀ ha₀)
        (radiationDensity κ a₀ (flatRadiation a₀ ha₀).a)
        (radiationPressure κ a₀ (flatRadiation a₀ ha₀).a)) := by
  have hd : deriv (flatRadiation a₀ ha₀).a = fun _ => a₀ :=
    funext fun η => ((hasDerivAt_id' η).const_mul a₀).deriv.trans (mul_one a₀)
  refine isEinstein_radiation rfl hκ a₀ (fun η _ => ?_) (fun η _ => ?_)
  · rw [hd]
    simp only [flatRadiation, conformalData]
    ring
  · rw [hd, deriv_const]
    simp only [flatRadiation, conformalData]
    ring

/-! ### The cosmic time -/

/-- The cosmic time `t = a₀(η − sin η)` of the closed dust model (Landau–Lifshitz, (112.9)). -/
def closedDustTime (a₀ η : ℝ) : ℝ := a₀ * (η - Real.sin η)

/-- The cosmic time `t = a₀(sinh η − η)` of the open dust model (Landau–Lifshitz, (113.4)). -/
def openDustTime (a₀ η : ℝ) : ℝ := a₀ * (Real.sinh η - η)

/-- The cosmic time `t = a₀(1 − cos η)` of the closed radiation model. -/
def closedRadiationTime (a₀ η : ℝ) : ℝ := a₀ * (1 - Real.cos η)

/-- The cosmic time `t = a₀(cosh η − 1)` of the open radiation model. -/
def openRadiationTime (a₀ η : ℝ) : ℝ := a₀ * (Real.cosh η - 1)

/-- The cosmic time `t = a₀η³/3` of the flat dust model. -/
def flatDustTime (a₀ η : ℝ) : ℝ := a₀ * η ^ 3 / 3

/-- The cosmic time `t = a₀η²/2` of the flat radiation model. -/
def flatRadiationTime (a₀ η : ℝ) : ℝ := a₀ * η ^ 2 / 2

/-- `dt/dη = a` for the closed dust model. -/
theorem hasDerivAt_closedDustTime (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (closedDustTime a₀) ((closedDust a₀ ha₀).a η) η :=
  ((hasDerivAt_id' η).sub (Real.hasDerivAt_sin η)).const_mul a₀

/-- `dt/dη = a` for the open dust model. -/
theorem hasDerivAt_openDustTime (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (openDustTime a₀) ((openDust a₀ ha₀).a η) η :=
  ((Real.hasDerivAt_sinh η).sub (hasDerivAt_id' η)).const_mul a₀

/-- `dt/dη = a` for the closed radiation model. -/
theorem hasDerivAt_closedRadiationTime (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (closedRadiationTime a₀) ((closedRadiation a₀ ha₀).a η) η :=
  (((Real.hasDerivAt_cos η).const_sub 1).const_mul a₀).congr_deriv (by
    simp only [closedRadiation, conformalData]
    ring)

/-- `dt/dη = a` for the open radiation model. -/
theorem hasDerivAt_openRadiationTime (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (openRadiationTime a₀) ((openRadiation a₀ ha₀).a η) η :=
  ((Real.hasDerivAt_cosh η).sub_const 1).const_mul a₀

/-- `dt/dη = a` for the flat dust model. -/
theorem hasDerivAt_flatDustTime (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (flatDustTime a₀) ((flatDust a₀ ha₀).a η) η :=
  (((hasDerivAt_pow 3 η).const_mul a₀).div_const 3).congr_deriv (by
    simp only [flatDust, conformalData]
    push_cast
    ring)

/-- `dt/dη = a` for the flat radiation model. -/
theorem hasDerivAt_flatRadiationTime (ha₀ : 0 < a₀) (η : ℝ) :
    HasDerivAt (flatRadiationTime a₀) ((flatRadiation a₀ ha₀).a η) η :=
  (((hasDerivAt_pow 2 η).const_mul a₀).div_const 2).congr_deriv (by
    simp only [flatRadiation, conformalData]
    push_cast
    ring)

/-- **The cosmic time is the proper time of the comoving observers** (Landau–Lifshitz, §§112,
114). For any isotropic model and a function `T` with `T' = N` on `I`, a smooth curve of the
domain that is at rest in the co-ordinates on `[a, b]`, `x(η) = x₀ + η e₀`, has the proper time
`T(x₀⁰ + b) − T(x₀⁰ + a)`: `dτ = N dη`. In the conformal time `N = a` and `T` is the cosmic
time; with `N = 1`, `T(t) = t` (`properTime_deSitter`). -/
theorem properTime_comoving (D : Data) {T : ℝ → ℝ} (hT : ∀ s ∈ D.I, HasDerivAt T (D.N s) s)
    {γ : ℝ → domain D} (hγ : ContDiff ℝ ∞ fun t => (γ t : E)) {x₀ : E} {a b : ℝ}
    (hrest : ∀ t ∈ uIcc a b, (γ t : E) = x₀ + t • Pi.single 0 1) :
    properTime (metric D).toLorentzMetric γ a b = T (x₀ 0 + b) - T (x₀ 0 + a) := by
  have hval (t : ℝ) (ht : t ∈ uIcc a b) : (γ t : E) 0 = x₀ 0 + t := by
    rw [hrest t ht]
    simp
  have htime (t : ℝ) (ht : t ∈ uIcc a b) : x₀ 0 + t ∈ D.I := by
    rw [← hval t ht]
    exact time_mem (γ t).property
  have hint : EqOn (fun t => Real.sqrt (-(metric D).form (γ t) (Pi.single 0 1) (Pi.single 0 1)))
      (fun t => D.N (x₀ 0 + t)) (uIcc a b) := by
    intro t ht
    have hform : (metric D).form (γ t) (Pi.single 0 1) (Pi.single 0 1) =
        -(D.N ((γ t : E) 0) ^ 2) := by
      change (metric D).coefficient (γ t) 0 0 = _
      rw [coefficient_metric, Matrix.diagonal_apply_eq]
      rfl
    simp only [hform, neg_neg, hval t ht]
    exact Real.sqrt_sq (D.N_pos _ (htime t ht)).le
  rw [properTime_atRest (metric D) hγ hrest, intervalIntegral.integral_congr hint]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hT _ (htime t ht)).comp_const_add (x₀ 0) t) ?_
  exact (D.contDiffOn_N.continuousOn.comp (continuous_const.add continuous_id).continuousOn
    fun t ht => htime t ht).intervalIntegrable

/-- In de Sitter space in the flat slicing (`N = 1`) the comoving observer through `x₀` is a
smooth curve of the domain, at rest at all times. -/
def deSitterObserver (x₀ : E) (t : ℝ) : domain Data.deSitter :=
  ⟨x₀ + t • Pi.single 0 1, mem_domain_deSitter _⟩

/-- **An instance of `properTime_comoving`**: the comoving observer of de Sitter space in the
flat slicing measures the co-ordinate time, `τ = b − a`. -/
theorem properTime_deSitter (x₀ : E) (a b : ℝ) :
    properTime (metric Data.deSitter).toLorentzMetric (deSitterObserver x₀) a b = b - a := by
  rw [properTime_comoving Data.deSitter (T := fun t => t) (fun s _ => hasDerivAt_id' s)
    (contDiff_const.add (contDiff_id.smul contDiff_const)) (x₀ := x₀) fun _ _ => rfl]
  ring

/-- **The proper time of a comoving observer of the closed dust model** is the cosmic time
`a₀(η − sin η)`. -/
theorem properTime_closedDust (ha₀ : 0 < a₀) {γ : ℝ → domain (closedDust a₀ ha₀)}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : E)) {x₀ : E} {a b : ℝ}
    (hrest : ∀ t ∈ uIcc a b, (γ t : E) = x₀ + t • Pi.single 0 1) :
    properTime (metric (closedDust a₀ ha₀)).toLorentzMetric γ a b =
      closedDustTime a₀ (x₀ 0 + b) - closedDustTime a₀ (x₀ 0 + a) :=
  properTime_comoving _ (fun s _ => hasDerivAt_closedDustTime ha₀ s) hγ hrest

/-- **The proper time of a comoving observer of the open dust model** is the cosmic time
`a₀(sinh η − η)`. -/
theorem properTime_openDust (ha₀ : 0 < a₀) {γ : ℝ → domain (openDust a₀ ha₀)}
    (hγ : ContDiff ℝ ∞ fun t => (γ t : E)) {x₀ : E} {a b : ℝ}
    (hrest : ∀ t ∈ uIcc a b, (γ t : E) = x₀ + t • Pi.single 0 1) :
    properTime (metric (openDust a₀ ha₀)).toLorentzMetric γ a b =
      openDustTime a₀ (x₀ 0 + b) - openDustTime a₀ (x₀ 0 + a) :=
  properTime_comoving _ (fun s _ => hasDerivAt_openDustTime ha₀ s) hγ hrest

/-! ### Closed dust from the singularity to the maximal expansion -/

/-- The closed dust model never exceeds `a_m = 2a₀`. -/
theorem closedDust_a_le (ha₀ : 0 < a₀) (η : ℝ) : (closedDust a₀ ha₀).a η ≤ 2 * a₀ := by
  change a₀ * (1 - Real.cos η) ≤ 2 * a₀
  nlinarith [Real.neg_one_le_cos η]

/-- The maximal expansion `a(π) = 2a₀` is reached at `η = π`. -/
theorem closedDust_a_pi (ha₀ : 0 < a₀) : (closedDust a₀ ha₀).a π = 2 * a₀ := by
  change a₀ * (1 - Real.cos π) = 2 * a₀
  rw [Real.cos_pi]
  ring

/-- At the maximal expansion the expansion stops: `a'(π) = 0`. -/
theorem deriv_closedDust_a_pi (ha₀ : 0 < a₀) : deriv (closedDust a₀ ha₀).a π = 0 := by
  rw [deriv_closedDust_a]
  simp

/-- **The time from the singularity to the maximal expansion** of the closed dust model is
`t(π) − t(0) = πa_m/2` with `a_m = a(π) = 2a₀`. -/
theorem closedDustTime_pi_sub_zero (ha₀ : 0 < a₀) :
    closedDustTime a₀ π - closedDustTime a₀ 0 = π * (closedDust a₀ ha₀).a π / 2 := by
  rw [closedDust_a_pi]
  simp [closedDustTime]
  ring

/-- The closed dust model lives for the cosmic time `t(2π) − t(0) = 2πa₀` from the singularity
to the collapse. -/
theorem closedDustTime_two_pi_sub_zero :
    closedDustTime a₀ (2 * π) - closedDustTime a₀ 0 = 2 * π * a₀ := by
  simp [closedDustTime]
  ring

/-- **The age at the maximal expansion as a limit of proper times**: the proper time
`t(π) − t(η)` of a comoving observer from `η` to the maximal expansion tends to `πa_m/2` as
`η → 0⁺`, the singularity. -/
theorem tendsto_closedDust_age (ha₀ : 0 < a₀) :
    Tendsto (fun η => closedDustTime a₀ π - closedDustTime a₀ η) (𝓝[>] 0)
      (𝓝 (π * (closedDust a₀ ha₀).a π / 2)) := by
  rw [← closedDustTime_pi_sub_zero ha₀]
  have hc : Continuous (closedDustTime a₀) :=
    continuous_const.mul (continuous_id.sub Real.continuous_sin)
  exact ((continuous_const.sub hc).tendsto 0).mono_left nhdsWithin_le_nhds

/-! ### The open models expand forever -/

/-- **The open and flat models expand forever** (Landau–Lifshitz, §113). In the cosmic time
`N = 1` on a connected set of times, with `k ≤ 0`, `Λ = 0`, `κ > 0` and a density `ρ ≥ 0` that is
positive when `k = 0`, a solution of the first Friedmann equation that expands at one time
expands at all times: `ȧ² = κρa²/3 − k > 0` never vanishes. -/
theorem open_expands_forever {D : Data} (hN : ∀ t ∈ D.I, D.N t = 1) (hI : IsPreconnected D.I)
    (hk : D.k ≤ 0) {κ : ℝ} (hκ : 0 < κ) {ρ : ℝ → ℝ} (h1 : ∀ t ∈ D.I, FirstFriedmann D κ 0 ρ t)
    (hρ : ∀ t ∈ D.I, 0 ≤ ρ t) (hρ₀ : D.k = 0 → ∀ t ∈ D.I, 0 < ρ t) {t₀ : ℝ} (ht₀ : t₀ ∈ D.I)
    (hexp : 0 < deriv D.a t₀) : ∀ t ∈ D.I, 0 < deriv D.a t := by
  have hne (t : ℝ) (ht : t ∈ D.I) : deriv D.a t ≠ 0 := by
    intro h0
    have e := (firstFriedmann_iff_firstDefect ht κ 0 ρ).mp (h1 t ht)
    rw [firstDefect, hN t ht, h0] at e
    have hk' : D.k = κ * ρ t * D.a t ^ 2 / 3 := by linear_combination e
    have ha := D.a_pos t ht
    have hρa : 0 ≤ κ * ρ t * D.a t ^ 2 / 3 := by
      have := hρ t ht
      positivity
    rcases hk.lt_or_eq with hlt | heq
    · linarith
    · have hp := hρ₀ heq t ht
      have : 0 < κ * ρ t * D.a t ^ 2 / 3 := by positivity
      linarith
  intro t ht
  by_contra hle'
  have hle := not_lt.mp hle'
  have hcont : ContinuousOn (deriv D.a) D.I :=
    (contDiffOn_deriv_of_contDiffOn D.isOpen_I D.contDiffOn_a).continuousOn
  obtain ⟨s, hs, hs0⟩ := hI.intermediate_value ht ht₀ hcont ⟨hle, hexp.le⟩
  exact hne s hs hs0

/-- **The scale factor of an open or flat model that expands once increases strictly** on the
whole connected set of times. -/
theorem open_strictMonoOn {D : Data} (hN : ∀ t ∈ D.I, D.N t = 1) (hI : IsPreconnected D.I)
    (hk : D.k ≤ 0) {κ : ℝ} (hκ : 0 < κ) {ρ : ℝ → ℝ} (h1 : ∀ t ∈ D.I, FirstFriedmann D κ 0 ρ t)
    (hρ : ∀ t ∈ D.I, 0 ≤ ρ t) (hρ₀ : D.k = 0 → ∀ t ∈ D.I, 0 < ρ t) {t₀ : ℝ} (ht₀ : t₀ ∈ D.I)
    (hexp : 0 < deriv D.a t₀) : StrictMonoOn D.a D.I :=
  strictMonoOn_of_deriv_pos (Real.convex_iff_isPreconnected.mpr hI) D.contDiffOn_a.continuousOn
    fun t ht => open_expands_forever hN hI hk hκ h1 hρ hρ₀ ht₀ hexp t (interior_subset ht)

/-- **An instance of `open_expands_forever`**: the empty Milne universe `a = t`, `k = −1`
expands at all times. -/
theorem milne_expands (κ : ℝ) (hκ : 0 < κ) : ∀ t ∈ Data.milne.I, 0 < deriv Data.milne.a t := by
  have h1 : ∀ t ∈ Data.milne.I, FirstFriedmann Data.milne κ 0 0 t := fun t ht =>
    (((isEinstein_iff_friedmann κ 0 0 0).mp
      (perfectFluidStress_zero (D := Data.milne) ▸ isEinstein_milne κ)) t ht).1
  have hd : deriv Data.milne.a = fun _ => 1 := funext fun t => deriv_id t
  refine open_expands_forever (fun _ _ => rfl) (isPreconnected_Ioi) (by norm_num [Data.milne])
    hκ h1 (fun _ _ => le_refl 0) (fun h => absurd h (by norm_num [Data.milne]))
    (t₀ := 1) (by simp [Data.milne]) ?_
  rw [hd]
  exact one_pos

end ProjectAinos.GeneralRelativity.CosmologicalModels
