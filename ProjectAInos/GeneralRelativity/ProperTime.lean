/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Geodesic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Proper time on a prescribed curved spacetime

The physical convention is time first, `(-+++)`, with `c = 1`. Velocities
belong to actual tangent fibres. The square-root functional is total, while
timelike hypotheses are explicit wherever positivity or normalization is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Timelike vectors for the physical negative-time convention. -/
def Timelike (g : LorentzMetric .timeNegative d M) {x : M} (v : TangentSpace I x) : Prop :=
  g.form x v v < 0

/-- The rate of proper time, without choosing a tangent-fibre norm. -/
def properSpeed (g : LorentzMetric .timeNegative d M) {x : M} (v : TangentSpace I x) : ℝ :=
  Real.sqrt (-g.form x v v)

@[simp] theorem properSpeed_smul (g : LorentzMetric .timeNegative d M)
    {x : M} (a : ℝ) (v : TangentSpace I x) :
    properSpeed g (a • v) = |a| * properSpeed g v := by
  unfold properSpeed
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [show -(a * (a * g.form x v v)) = a ^ 2 * (-g.form x v v) by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem properSpeed_nonneg (g : LorentzMetric .timeNegative d M)
    {x : M} (v : TangentSpace I x) : 0 ≤ properSpeed g v := Real.sqrt_nonneg _

theorem properSpeed_pos_iff (g : LorentzMetric .timeNegative d M)
    {x : M} (v : TangentSpace I x) : 0 < properSpeed g v ↔ Timelike g v := by
  simp [properSpeed, Timelike]

theorem properSpeed_sq (g : LorentzMetric .timeNegative d M)
    {x : M} {v : TangentSpace I x} (hv : Timelike g v) :
    properSpeed g v ^ 2 = -g.form x v v := Real.sq_sqrt (neg_nonneg.mpr hv.le)

/-- The intrinsic scalar integrand on a parametrized worldline. -/
def speedAlong (g : LorentzMetric .timeNegative d M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  properSpeed g (curveVelocity γ t)

/-- Proper time on a finite directed parameter interval. -/
def properTime (g : LorentzMetric .timeNegative d M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, speedAlong g γ t

/-- The signed metric square of a C¹ velocity is continuous along its curve. -/
theorem metricVelocity_continuousAt (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    ContinuousAt (fun s => g.form (γ s) (curveVelocity γ s) (curveVelocity γ s)) t := by
  have hV := curveVelocity_contMDiffAt (n := 0) (by simpa using hγ)
  have hp : ContMDiffAt 𝓘(ℝ) ((I).prod 𝓘(ℝ)) 0
      (fun s => (⟨γ s, g.form (γ s) (curveVelocity γ s) (curveVelocity γ s)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) t :=
    (((g.smooth (γ t)).of_le (by simp)).comp t (hγ.of_le (by norm_num))).clm_bundle_apply₂ hV hV
  rw [contMDiffAt_totalSpace] at hp
  exact hp.2.continuousAt

/-- Local C¹ regularity gives a continuous proper-time integrand, even at null vectors. -/
theorem speedAlong_continuousAt (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    ContinuousAt (speedAlong g γ) t :=
  (metricVelocity_continuousAt g hγ).neg.sqrt

theorem properTime_integrable (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b : ℝ) (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    IntervalIntegrable (speedAlong g γ) volume a b :=
  ContinuousOn.intervalIntegrable fun t ht =>
    (speedAlong_continuousAt g (hγ t ht)).continuousWithinAt

/-- Subdivision is intrinsic and does not require the pieces to lie in one chart. -/
theorem properTime_add (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b c : ℝ)
    (hab : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ t)
    (hbc : ∀ t ∈ uIcc b c, ContMDiffAt 𝓘(ℝ) I 1 γ t) :
    properTime g γ a b + properTime g γ b c = properTime g γ a c :=
  intervalIntegral.integral_add_adjacent_intervals
    (properTime_integrable g γ a b hab) (properTime_integrable g γ b c hbc)

theorem properTime_nonneg (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) : 0 ≤ properTime g γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)

@[simp] theorem properTime_self (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a : ℝ) : properTime g γ a a = 0 := by simp [properTime]

theorem properTime_symm (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b : ℝ) : properTime g γ b a = -properTime g γ a b :=
  intervalIntegral.integral_symm _ _

/-- Null curves have zero proper time; no normalized null velocity is introduced. -/
theorem properTime_null (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (a b : ℝ)
    (h : ∀ t ∈ uIcc a b, g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0) :
    properTime g γ a b = 0 := by
  unfold properTime
  have he : (∫ t in a..b, speedAlong g γ t) = ∫ _t in a..b, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp [speedAlong, properSpeed, h t ht]
  rw [he]
  simp

/-- The parameter-change formula also permits vanishing parameter speed. -/
theorem speedAlong_comp (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {r : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ (r t)) (hr : DifferentiableAt ℝ r t) :
    speedAlong g (γ ∘ r) t = |deriv r t| * speedAlong g γ (r t) := by
  unfold speedAlong
  rw [curveVelocity_comp hγ hr, properSpeed_smul]

/-- Orientation-preserving reparametrization preserves proper time.
All regularity is local near the closed integration interval. -/
theorem properTime_reparametrize (g : LorentzMetric .timeNegative d M)
    (γ : ℝ → M) (r : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 1 γ (r t))
    (hr : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 r t)
    (hpos : ∀ t ∈ uIcc a b, 0 ≤ deriv r t) :
    properTime g (γ ∘ r) a b = properTime g γ (r a) (r b) := by
  unfold properTime
  calc
    (∫ t in a..b, speedAlong g (γ ∘ r) t) =
        ∫ t in a..b, speedAlong g γ (r t) * deriv r t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [speedAlong_comp g ((hγ t ht).mdifferentiableAt (by norm_num))
        ((hr t ht).differentiableAt (by norm_num)), abs_of_nonneg (hpos t ht), mul_comm]
    _ = _ := by
      apply intervalIntegral.integral_comp_mul_deriv' (f := r) (f' := deriv r)
        (g := speedAlong g γ)
      · intro t ht
        exact ((hr t ht).differentiableAt (by norm_num)).hasDerivAt
      · intro t ht
        exact ((hr t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
      · rintro y ⟨t, ht, rfl⟩
        exact (speedAlong_continuousAt g (hγ t ht)).continuousWithinAt

/-- Proper time along an affine geodesic is interval length times its initial rate. -/
theorem properTime_geodesic (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : g.IsGeodesicOn (uIcc a b) γ) :
    properTime g γ a b = (b - a) * speedAlong g γ a := by
  unfold properTime
  have he : (∫ t in a..b, speedAlong g γ t) = ∫ _t in a..b, speedAlong g γ a := by
    apply intervalIntegral.integral_congr
    intro t ht
    unfold speedAlong properSpeed
    rw [hγ.metric_velocity_eq (convex_uIcc a b) ht (left_mem_uIcc)]
  rw [he]
  simp

/-- The proper-speed derivative follows from intrinsic metric compatibility. -/
theorem hasDerivAt_speedAlong (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : Timelike g (curveVelocity γ t)) :
    HasDerivAt (speedAlong g γ)
      (-g.form (γ t) (g.covariantAlong (curveVelocity γ) t) (curveVelocity γ t) /
        speedAlong g γ t) t := by
  have hV := (curveVelocity_contMDiffAt (n := 1) hγ).mdifferentiableAt (by norm_num)
  have hp := g.hasDerivAt_pairing_along (hγ.mdifferentiableAt (by norm_num)) hV hV
  have hn : -g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) ≠ 0 :=
    ne_of_gt (neg_pos.mpr hv)
  apply (hp.neg.sqrt hn).congr_deriv
  rw [g.symmetric (γ t) (curveVelocity γ t) (g.covariantAlong (curveVelocity γ) t)]
  dsimp [speedAlong, properSpeed]
  ring

/-- Normalize only timelike vectors when using the unit-velocity theorem below. -/
def fourVelocity (g : LorentzMetric .timeNegative d M) {x : M}
    (v : TangentSpace I x) : TangentSpace I x := (properSpeed g v)⁻¹ • v

theorem fourVelocity_unit (g : LorentzMetric .timeNegative d M) {x : M}
    {v : TangentSpace I x} (hv : Timelike g v) :
    g.form x (fourVelocity g v) (fourVelocity g v) = -1 := by
  have hs := properSpeed_sq g hv
  have hp : properSpeed g v ≠ 0 := ne_of_gt ((properSpeed_pos_iff g v).mpr hv)
  simp only [fourVelocity, map_smul, smul_apply, smul_eq_mul]
  field_simp
  nlinarith

/-- Any smooth coordinate chart computes the same scalar proper-time integrand. -/
theorem speedAlong_chart (g : LorentzMetric .timeNegative d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {t : ℝ} (ht : γ t ∈ e.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    speedAlong g γ t = Real.sqrt (-g.chartMetric e (γ t)
      (deriv (e ∘ γ) t) (deriv (e ∘ γ) t)) := by
  rw [← chartTangentMap_curveVelocity he ht hγ, chartMetric_apply,
    chartField_tangentMap he ht]
  rfl

/-- Chart formulas are valid on each regular segment, using geometric metric coefficients. -/
theorem properTime_chart (g : LorentzMetric .timeNegative d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (γ : ℝ → M) (a b : ℝ) (hstay : ∀ t ∈ uIcc a b, γ t ∈ e.source)
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ) I γ t) :
    properTime g γ a b = ∫ t in a..b, Real.sqrt (-g.chartMetric e (γ t)
      (deriv (e ∘ γ) t) (deriv (e ∘ γ) t)) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact speedAlong_chart g he (hstay t ht) (hγ t ht)

variable {d' : ℕ} {N : Type} [TopologicalSpace N]
  [ChartedSpace (MinkowskiModel d') N] [IsManifold 𝓘(ℝ, MinkowskiModel d') ∞ N]

/-- A metric-preserving map preserves proper time. Only differentiability along
the curve and metric preservation on its velocity are needed, even in different dimensions. -/
theorem properTime_map (g : LorentzMetric .timeNegative d M)
    (h : LorentzMetric .timeNegative d' N) (f : M → N) (γ : ℝ → M) (a b : ℝ)
    (hf : ∀ t ∈ uIcc a b, MDifferentiableAt I 𝓘(ℝ, MinkowskiModel d') f (γ t))
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ) I γ t)
    (hmetric : ∀ t ∈ uIcc a b,
      g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
        h.form (f (γ t)) (mfderiv I 𝓘(ℝ, MinkowskiModel d') f (γ t) (curveVelocity γ t))
          (mfderiv I 𝓘(ℝ, MinkowskiModel d') f (γ t) (curveVelocity γ t))) :
    properTime h (f ∘ γ) a b = properTime g γ a b := by
  apply intervalIntegral.integral_congr
  intro t ht
  have hd : curveVelocity (d := d') (f ∘ γ) t =
      mfderiv I 𝓘(ℝ, MinkowskiModel d') f (γ t) (curveVelocity γ t) := by
    unfold curveVelocity
    rw [mfderiv_comp t (hf t ht) (hγ t ht)]
    rfl
  simp only [speedAlong, properSpeed, hd, Function.comp_apply, ← hmetric t ht]

end ProjectAInos.GeneralRelativity
