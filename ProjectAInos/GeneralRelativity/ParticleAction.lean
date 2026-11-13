/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ProperTime

/-! # Intrinsic curved-spacetime particle actions

The quadratic action covers all causal types. The square-root free action
is used for massive timelike motion; no restriction to null variations is
built into either functional. Variational characterizations are separate
theorems, not assumptions in these definitions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped Manifold ContDiff

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The quadratic action of a parametrized curve on a prescribed spacetime. -/
def quadraticAction (g : LorentzMetric .timeNegative d M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (1 / 2 : ℝ) * g.form (γ t) (curveVelocity γ t) (curveVelocity γ t)

/-- Free particle action in units `c = 1`; physical mass positivity is explicit in later laws. -/
def freeAction (g : LorentzMetric .timeNegative d M) (m : ℝ)
    (γ : ℝ → M) (a b : ℝ) : ℝ := -m * properTime g γ a b

theorem quadraticAction_integrable (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b : ℝ) (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    IntervalIntegrable
      (fun t => (1 / 2 : ℝ) * g.form (γ t) (curveVelocity γ t) (curveVelocity γ t))
      volume a b :=
  ContinuousOn.intervalIntegrable fun t ht =>
    ((metricVelocity_continuousAt g (hγ t ht)).const_mul (1 / 2)).continuousWithinAt

theorem quadraticAction_add (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b c : ℝ)
    (hab : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t)
    (hbc : ∀ t ∈ uIcc b c, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    quadraticAction g γ a b + quadraticAction g γ b c = quadraticAction g γ a c :=
  intervalIntegral.integral_add_adjacent_intervals
    (quadraticAction_integrable g γ a b hab) (quadraticAction_integrable g γ b c hbc)

theorem freeAction_add (g : LorentzMetric .timeNegative d M) (m : ℝ)
    (γ : ℝ → M) (a b c : ℝ)
    (hab : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t)
    (hbc : ∀ t ∈ uIcc b c, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    freeAction g m γ a b + freeAction g m γ b c = freeAction g m γ a c := by
  simp only [freeAction, ← mul_add, properTime_add g γ a b c hab hbc]

theorem freeAction_nonpos (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 ≤ m) (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    freeAction g m γ a b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm) (properTime_nonneg g γ hab)

theorem freeAction_reparametrize (g : LorentzMetric .timeNegative d M) (m : ℝ)
    (γ : ℝ → M) (r : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ (r t))
    (hr : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 r t)
    (hpos : ∀ t ∈ uIcc a b, 0 ≤ deriv r t) :
    freeAction g m (γ ∘ r) a b = freeAction g m γ (r a) (r b) := by
  rw [freeAction, freeAction, properTime_reparametrize g γ r a b hγ hr hpos]

/-- Native geodesic norm conservation evaluates the quadratic action. -/
theorem quadraticAction_geodesic (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : g.IsGeodesicOn (uIcc a b) γ) :
    quadraticAction g γ a b = (b - a) / 2 *
      g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) := by
  unfold quadraticAction
  have he : (∫ t in a..b, (1 / 2 : ℝ) *
      g.form (γ t) (curveVelocity γ t) (curveVelocity γ t)) =
      ∫ _t in a..b, (1 / 2 : ℝ) * g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [hγ.metric_velocity_eq (convex_uIcc a b) ht left_mem_uIcc]
  rw [he]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem freeAction_geodesic (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {γ : ℝ → M} {a b : ℝ} (hγ : g.IsGeodesicOn (uIcc a b) γ) :
    freeAction g m γ a b = -m * ((b - a) * speedAlong g γ a) := by
  rw [freeAction, properTime_geodesic g hγ]

/-- A null reference curve has zero quadratic action, without constraining variations. -/
theorem quadraticAction_null (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b : ℝ)
    (h : ∀ t ∈ uIcc a b, g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0) :
    quadraticAction g γ a b = 0 := by
  unfold quadraticAction
  have he : (∫ t in a..b, (1 / 2 : ℝ) *
      g.form (γ t) (curveVelocity γ t) (curveVelocity γ t)) = ∫ _t in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [h t ht, mul_zero]
  rw [he]
  simp

theorem quadraticAction_chart (g : LorentzMetric .timeNegative d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (γ : ℝ → M) (a b : ℝ) (hstay : ∀ t ∈ uIcc a b, γ t ∈ e.source)
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ) I γ t) :
    quadraticAction g γ a b = ∫ t in a..b, (1 / 2 : ℝ) * g.chartMetric e (γ t)
      (deriv (e ∘ γ) t) (deriv (e ∘ γ) t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [← chartTangentMap_curveVelocity he (hstay t ht) (hγ t ht), chartMetric_apply,
    chartField_tangentMap he (hstay t ht)]

end ProjectAInos.GeneralRelativity
