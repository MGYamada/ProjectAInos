/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.FlowEquation
public import ProjectAinos.SmoothGeometry.ODE.LocalFlow

/-!
# The flow of a smooth vector field

For a vector field `X` on a Banach space:

* `flowDomain X` is the set of times `t` and points `x` such that the solution
  of `ẋ = X(x)` through `x` exists between the times `0` and `t`
  (`mem_flowDomain_iff`). Its section at a point is the maximal interval of
  existence.
* `flow X (t, x)` is the value of that solution at the time `t`.

For a smooth field the domain is open (`isOpen_flowDomain`), the flow is smooth
in the time and the point together on it (`contDiffOn_flow`), it solves the
equation (`hasDerivAt_flow`), and it is the only solution
(`flow_eq_of_hasDerivWithinAt`). Hence `isLocalFlowOn_flow`: the flow is a local
flow in the sense of `IsLocalFlowOn`, and the theorems for a given flow apply.

The proof applies the implicit function theorem to the integral equation on the
unit interval, in which the time is a factor. The derivative of that equation
in the curve is invertible at every solution, for every time, so no interval is
subdivided and no local solutions are glued.
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.NonlinearODE

open LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {t τ : ℝ} {x : E}

/-- The times and points for which the solution through the point exists up to
the time. -/
def flowDomain (X : E → E) : Set (ℝ × E) :=
  {p | ∃ γ : Curve E, IsFlowCurve X p.1 p.2 γ}

/-- The solution through a point up to a time, as a curve on the unit interval.
Outside the domain it is the constant curve. -/
def flowCurve (X : E → E) (p : ℝ × E) : Curve E :=
  open Classical in
  if h : p ∈ flowDomain X then h.choose else ContinuousMap.const unitInterval p.2

/-- The flow: the value at the time `p.1` of the solution through `p.2`. Outside
the domain it is the point itself. -/
def flow (X : E → E) (p : ℝ × E) : E := flowCurve X p 1

omit [CompleteSpace E] in
theorem isFlowCurve_flowCurve {p : ℝ × E} (h : p ∈ flowDomain X) :
    IsFlowCurve X p.1 p.2 (flowCurve X p) := by
  simp only [flowCurve, h, ↓reduceDIte]
  exact h.choose_spec

theorem flowCurve_eq (hX : ContDiff ℝ 1 X) {γ : Curve E} (h : IsFlowCurve X τ x γ) :
    flowCurve X (τ, x) = γ :=
  (isFlowCurve_flowCurve (p := (τ, x)) ⟨γ, h⟩).eq hX h

theorem flow_eq (hX : ContDiff ℝ 1 X) {γ : Curve E} (h : IsFlowCurve X τ x γ) :
    flow X (τ, x) = γ 1 := by
  rw [flow, flowCurve_eq hX h]

omit [CompleteSpace E] in
theorem zero_mem_flowDomain (X : E → E) (x : E) : (0, x) ∈ flowDomain X :=
  ⟨ContinuousMap.const unitInterval x, isFlowCurve_const X x⟩

omit [CompleteSpace E] in
@[simp] theorem flow_zero (X : E → E) (x : E) : flow X (0, x) = x := by
  have h := isFlowCurve_flowCurve (zero_mem_flowDomain X x) 1
  simpa [flow] using h

omit [CompleteSpace E] in
theorem mul_mem_flowDomain (h : (τ, x) ∈ flowDomain X) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) :
    (c * τ, x) ∈ flowDomain X :=
  ⟨rescale _ c, (isFlowCurve_flowCurve h).rescale hc⟩

omit [CompleteSpace E] in
/-- The times of a point form an interval that contains zero. -/
theorem mem_flowDomain_of_mem_uIcc (h : (t, x) ∈ flowDomain X) {s : ℝ}
    (hs : s ∈ uIcc 0 t) : (s, x) ∈ flowDomain X := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [uIcc_self, mem_singleton_iff] at hs
    rw [hs]
    exact zero_mem_flowDomain X x
  · have hc : s / t ∈ Icc (0 : ℝ) 1 := by
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · rw [uIcc_of_ge hneg.le] at hs
        exact ⟨div_nonneg_of_nonpos hs.2 hneg.le, (div_le_one_of_neg hneg).mpr hs.1⟩
      · rw [uIcc_of_le hpos.le] at hs
        exact ⟨div_nonneg hs.1 hpos.le, (div_le_one hpos).mpr hs.2⟩
    have h1 := mul_mem_flowDomain h hc
    rwa [div_mul_cancel₀ s ht] at h1

/-- The flow curve of a point of the domain is the flow at the fractions of the
time. -/
theorem flowCurve_apply (hX : ContDiff ℝ 1 X) (h : (τ, x) ∈ flowDomain X)
    (σ : unitInterval) : flowCurve X (τ, x) σ = flow X (σ * τ, x) := by
  rw [flow_eq hX ((isFlowCurve_flowCurve h).rescale σ.2), rescale_apply]
  simp

/-- The integral equation of the flow. -/
theorem flow_integral_eq (hX : ContDiff ℝ 1 X) (h : (t, x) ∈ flowDomain X) :
    flow X (t, x) = x + ∫ r in (0 : ℝ)..t, X (flow X (r, x)) := by
  have hγ := isFlowCurve_flowCurve h
  have h1 := hγ 1
  have hcongr : ∫ s in (0 : ℝ)..1, X (extend (flowCurve X (t, x)) s) =
      ∫ s in (0 : ℝ)..1, X (flow X (t * s, x)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have he : extend (flowCurve X (t, x)) s = flow X (s * t, x) :=
      (extend_coe (flowCurve X (t, x)) ⟨s, hs⟩).trans (flowCurve_apply hX h ⟨s, hs⟩)
    change X (extend (flowCurve X (t, x)) s) = X (flow X (t * s, x))
    rw [he, mul_comm]
  have hsm := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun r => X (flow X (r, x))) t
  rw [mul_zero, mul_one] at hsm
  change flow X (t, x) = _ at h1
  rw [h1]
  simp only [Icc.coe_one]
  rw [hcongr, hsm]

/-- The domain of the flow of a smooth field is open. -/
theorem isOpen_flowDomain (hX : ContDiff ℝ ∞ X) : IsOpen (flowDomain X) := by
  refine isOpen_iff_mem_nhds.mpr fun p hp => ?_
  obtain ⟨γ, hγ⟩ := hp
  obtain ⟨V, ψ, hV, hpV, -, -, hψ⟩ := exists_local_family hX hγ
  exact mem_of_superset (hV.mem_nhds hpV) fun q hq => ⟨ψ q, hψ q hq⟩

/-- The flow of a smooth field is smooth in the time and the point together. -/
theorem contDiffAt_flow (hX : ContDiff ℝ ∞ X) {p : ℝ × E} (hp : p ∈ flowDomain X) :
    ContDiffAt ℝ ∞ (flow X) p := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by simp)
  obtain ⟨V, ψ, hV, hpV, -, hψc, hψ⟩ := exists_local_family hX (isFlowCurve_flowCurve hp)
  have hev : ContDiff ℝ ∞ fun f : Curve E => f 1 :=
    (ContinuousMap.evalCLM ℝ (M := E) (1 : unitInterval)).contDiff
  have heval : ContDiffOn ℝ ∞ (fun q => ψ q 1) V := hev.comp_contDiffOn hψc
  have heq : flow X =ᶠ[𝓝 p] fun q => ψ q 1 :=
    Filter.eventually_of_mem (hV.mem_nhds hpV) fun q hq => flow_eq hX1 (hψ q hq)
  exact (heval.contDiffAt (hV.mem_nhds hpV)).congr_of_eventuallyEq heq

theorem contDiffOn_flow (hX : ContDiff ℝ ∞ X) : ContDiffOn ℝ ∞ (flow X) (flowDomain X) :=
  fun _ hp => (contDiffAt_flow hX hp).contDiffWithinAt

theorem continuousOn_flow (hX : ContDiff ℝ ∞ X) : ContinuousOn (flow X) (flowDomain X) :=
  (contDiffOn_flow hX).continuousOn

/-- The flow solves the equation, at every time of the domain. -/
theorem hasDerivAt_flow (hX : ContDiff ℝ ∞ X) (h : (t, x) ∈ flowDomain X) :
    HasDerivAt (fun s => flow X (s, x)) (X (flow X (t, x))) t := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by simp)
  have hpair : Continuous fun s : ℝ => (s, x) := continuous_id.prodMk continuous_const
  have hU : IsOpen {s : ℝ | (s, x) ∈ flowDomain X} := (isOpen_flowDomain hX).preimage hpair
  have hf : ContinuousOn (fun r => X (flow X (r, x))) {s : ℝ | (s, x) ∈ flowDomain X} :=
    hX.continuous.comp_continuousOn
      ((continuousOn_flow hX).comp hpair.continuousOn fun s hs => hs)
  have hint : IntervalIntegrable (fun r => X (flow X (r, x))) volume 0 t :=
    (hf.mono fun s hs => mem_flowDomain_of_mem_uIcc h hs).intervalIntegrable
  have hderiv := (intervalIntegral.integral_hasDerivAt_right hint
    (hf.stronglyMeasurableAtFilter hU t h) (hf.continuousAt (hU.mem_nhds h))).const_add x
  refine hderiv.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem (hU.mem_nhds h) fun s hs => flow_integral_eq hX1 hs

/-- The flow of a smooth field is a local flow on its domain. -/
theorem isLocalFlowOn_flow (hX : ContDiff ℝ ∞ X) :
    IsLocalFlowOn X (flow X) (flowDomain X) where
  isOpen := isOpen_flowDomain hX
  contDiffAt _ hp := (contDiffAt_flow hX hp).of_le (by simp)
  hasDerivAt _ hp := hasDerivAt_flow hX hp
  segment _ hp _ hs := mem_flowDomain_of_mem_uIcc hp hs
  initial p _ := flow_zero X p.2

/-- A solution between the times `0` and `t` puts the time `t` in the domain. -/
theorem mem_flowDomain_of_hasDerivWithinAt (hX : Continuous X) {y : ℝ → E} (h0 : y 0 = x)
    (hy : ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r) :
    (t, x) ∈ flowDomain X := by
  obtain ⟨γ, hγ, -⟩ := exists_isFlowCurve_of_hasDerivWithinAt hX h0 hy
  exact ⟨γ, hγ⟩

/-- A solution between the times `0` and `t` is the flow. -/
theorem flow_eq_of_hasDerivWithinAt (hX : ContDiff ℝ 1 X) {y : ℝ → E} (h0 : y 0 = x)
    (hy : ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r) :
    flow X (t, x) = y t := by
  obtain ⟨γ, hγ, hγy⟩ := exists_isFlowCurve_of_hasDerivWithinAt hX.continuous h0 hy
  rw [flow_eq hX hγ, hγy 1]
  simp

/-- The domain of the flow: the solution through the point exists between the
times `0` and `t`. -/
theorem mem_flowDomain_iff (hX : ContDiff ℝ ∞ X) :
    (t, x) ∈ flowDomain X ↔ ∃ y : ℝ → E, y 0 = x ∧
      ∀ r ∈ uIcc 0 t, HasDerivWithinAt y (X (y r)) (uIcc 0 t) r := by
  constructor
  · intro h
    exact ⟨fun s => flow X (s, x), flow_zero X x, fun r hr =>
      (hasDerivAt_flow hX (mem_flowDomain_of_mem_uIcc h hr)).hasDerivWithinAt⟩
  · rintro ⟨y, h0, hy⟩
    exact mem_flowDomain_of_hasDerivWithinAt hX.continuous h0 hy

end ProjectAinos.SmoothGeometry.NonlinearODE
