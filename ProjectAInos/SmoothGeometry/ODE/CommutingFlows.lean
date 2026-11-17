/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.FlowComplete
public import ProjectAInos.SmoothGeometry.ODE.FlowVariation

/-!
# Flows of commuting vector fields

Two smooth fields `A`, `B` on a Banach space commute if
`DA(y) B(y) = DB(y) A(y)` for all `y`.

* `fderiv_flow_apply_of_commute`: the flow of `A` carries `B` into itself,
  `D_x Φ_A(t, x) B(x) = B(Φ_A(t, x))`.
* `flow_add_of_commute`: the flow of `A + B` is the composition of the flows.
* `flow_smul_field`: the flow of `c A` at the time `T` is the flow of `A` at
  the time `c T`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A B : E → E} {t : ℝ} {x : E}

theorem const_mul_mem_uIcc {c r T : ℝ} (hr : r ∈ uIcc 0 T) : c * r ∈ uIcc 0 (c * T) := by
  rw [mem_uIcc] at hr ⊢
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases le_total 0 c with hc | hc
  · exact Or.inl ⟨mul_nonneg hc h1, mul_le_mul_of_nonneg_left h2 hc⟩
  · exact Or.inr ⟨mul_le_mul_of_nonpos_left h2 hc, mul_nonpos_of_nonpos_of_nonneg hc h1⟩
  · exact Or.inr ⟨mul_le_mul_of_nonneg_left h1 hc, mul_nonpos_of_nonneg_of_nonpos hc h2⟩
  · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos hc h2, mul_le_mul_of_nonpos_left h1 hc⟩

/-- A field that commutes with `A` is carried into itself by the flow of `A`. -/
theorem fderiv_flow_apply_of_commute (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hAB : ∀ y, fderiv ℝ A y (B y) = fderiv ℝ B y (A y)) (h : (t, x) ∈ flowDomain A) :
    fderiv ℝ (fun y => flow A (t, y)) x (B x) = B (flow A (t, x)) := by
  have hdom : ∀ s ∈ uIcc 0 t, (s, x) ∈ flowDomain A := fun s hs =>
    mem_flowDomain_of_mem_uIcc h hs
  have hv : ∀ s ∈ uIcc 0 t, HasDerivAt
      (fun s => fderiv ℝ (fun y => flow A (s, y)) x (B x) - B (flow A (s, x)))
      (fderiv ℝ A (flow A (s, x))
        (fderiv ℝ (fun y => flow A (s, y)) x (B x) - B (flow A (s, x)))) s := by
    intro s hs
    have hmem := hdom s hs
    have h1 := hasDerivAt_fderiv_of_isLocalFlow (Φ := flow A) (X := A)
      ((contDiffAt_flow hA hmem).of_le (by simp)) (hA.differentiable (by simp) _)
      (by
        filter_upwards [(isOpen_flowDomain hA).mem_nhds hmem] with p hp
        exact hasDerivAt_flow hA hp)
    have h2 : HasDerivAt (fun s => fderiv ℝ (fun y => flow A (s, y)) x (B x))
        ((fderiv ℝ A (flow A (s, x)) ∘L fderiv ℝ (fun y => flow A (s, y)) x) (B x)) s := by
      have h := h1.clm_apply (hasDerivAt_const s (B x))
      simpa using h
    have h3 : HasDerivAt (fun s => B (flow A (s, x)))
        (fderiv ℝ B (flow A (s, x)) (A (flow A (s, x)))) s :=
      (hB.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_flow hA hmem)
    refine (h2.sub h3).congr_deriv ?_
    rw [map_sub, hAB]
    rfl
  have hcont : ContinuousOn (fun s => fderiv ℝ A (flow A (s, x))) (uIcc 0 t) :=
    (hA.continuous_fderiv (by simp)).comp_continuousOn
      ((continuousOn_flow hA).comp (continuous_id.prodMk continuous_const).continuousOn hdom)
  obtain ⟨K, hK⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont
  have hmul : ∀ r ∈ Icc (0 : ℝ) 1, r * t ∈ uIcc 0 t := fun r hr => by
    rw [mul_comm]
    exact mul_mem_uIcc t hr
  have hf : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun r => fderiv ℝ (fun y => flow A (r * t, y)) x (B x) - B (flow A (r * t, x)))
      ((1 * t) • fderiv ℝ A (flow A (r * t, x))
        (fderiv ℝ (fun y => flow A (r * t, y)) x (B x) - B (flow A (r * t, x)))) r :=
    fun r hr => HasDerivAt.scomp r
      (g₁ := fun s => fderiv ℝ (fun y => flow A (s, y)) x (B x) - B (flow A (s, x)))
      (h := fun r => r * t) (hv (r * t) (hmul r hr)) ((hasDerivAt_id r).mul_const t)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun r => fderiv ℝ (fun y => flow A (r * t, y)) x (B x) - B (flow A (r * t, x)))
    (f' := fun r => (1 * t) • fderiv ℝ A (flow A (r * t, x))
      (fderiv ℝ (fun y => flow A (r * t, y)) x (B x) - B (flow A (r * t, x))))
    (K := |t| * K) (a := 0) (b := 1)
    (fun r hr => (hf r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hf r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt) (by simp)
    (fun r hr => by
      have h1 := hK (r * t) (hmul r ⟨hr.1, hr.2.le⟩)
      rw [norm_smul, Real.norm_eq_abs, one_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
    1 ⟨zero_le_one, le_rfl⟩
  simp only [one_mul] at hzero
  exact sub_eq_zero.mp hzero

/-- The flow of the sum of two commuting fields is the composition of their
flows. -/
theorem flow_add_of_commute (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hAB : ∀ y, fderiv ℝ A y (B y) = fderiv ℝ B y (A y)) {T : ℝ}
    (hBdom : ∀ r ∈ uIcc 0 T, (r, x) ∈ flowDomain B)
    (hAdom : ∀ r ∈ uIcc 0 T, (r, flow B (r, x)) ∈ flowDomain A) :
    (T, x) ∈ flowDomain (fun y => A y + B y) ∧
      flow (fun y => A y + B y) (T, x) = flow A (T, flow B (T, x)) := by
  have hy : ∀ r ∈ uIcc 0 T, HasDerivAt (fun r => flow A (r, flow B (r, x)))
      (A (flow A (r, flow B (r, x))) + B (flow A (r, flow B (r, x)))) r := by
    intro r hr
    have hmem := hAdom r hr
    have hΦ : DifferentiableAt ℝ (flow A) (r, flow B (r, x)) :=
      (contDiffAt_flow hA hmem).differentiableAt (by simp)
    have hpath : HasDerivAt (fun r => ((r, flow B (r, x)) : ℝ × E))
        ((1 : ℝ), B (flow B (r, x))) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_flow hB (hBdom r hr))
    have h1 : HasDerivAt (fun r => flow A (r, flow B (r, x)))
        (fderiv ℝ (flow A) (r, flow B (r, x)) ((1 : ℝ), B (flow B (r, x)))) r :=
      HasFDerivAt.comp_hasDerivAt r (l := flow A)
        (f := fun r => ((r, flow B (r, x)) : ℝ × E)) hΦ.hasFDerivAt hpath
    refine h1.congr_deriv ?_
    have e : (((1 : ℝ), B (flow B (r, x))) : ℝ × E) =
        ((1 : ℝ), (0 : E)) + ((0 : ℝ), B (flow B (r, x))) := by simp
    have ht := (hasDerivAt_slice_time hΦ).unique (hasDerivAt_flow hA hmem)
    have hpush := fderiv_flow_apply_of_commute hA hB hAB hmem
    rw [(hasFDerivAt_slice hΦ).fderiv] at hpush
    rw [e, map_add, ht]
    congr 1
  have h0 : (fun r => flow A (r, flow B (r, x))) 0 = x := by simp
  have hX : ContDiff ℝ ∞ fun y => A y + B y := hA.add hB
  exact ⟨mem_flowDomain_of_hasDerivWithinAt hX.continuous h0
      fun r hr => (hy r hr).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt (hX.of_le (by simp)) h0
      fun r hr => (hy r hr).hasDerivWithinAt⟩

/-- The flow of a multiple of a field is the flow at the multiple of the time. -/
theorem flow_smul_field (hA : ContDiff ℝ ∞ A) (c : ℝ) {T : ℝ}
    (h : (c * T, x) ∈ flowDomain A) :
    (T, x) ∈ flowDomain (fun y => c • A y) ∧
      flow (fun y => c • A y) (T, x) = flow A (c * T, x) := by
  have hy : ∀ r ∈ uIcc 0 T, HasDerivAt (fun r => flow A (c * r, x))
      (c • A (flow A (c * r, x))) r := by
    intro r hr
    have hmem : (c * r, x) ∈ flowDomain A := mem_flowDomain_of_mem_uIcc h (const_mul_mem_uIcc hr)
    have h1 : HasDerivAt (fun r => flow A (c * r, x)) ((c * 1) • A (flow A (c * r, x))) r :=
      HasDerivAt.scomp r (g₁ := fun s => flow A (s, x)) (h := fun r => c * r)
        (hasDerivAt_flow hA hmem) ((hasDerivAt_id r).const_mul c)
    refine h1.congr_deriv ?_
    rw [mul_one]
  have h0 : (fun r => flow A (c * r, x)) 0 = x := by simp
  have hX : ContDiff ℝ ∞ fun y => c • A y := contDiff_const.smul hA
  exact ⟨mem_flowDomain_of_hasDerivWithinAt hX.continuous h0
      fun r hr => (hy r hr).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt (hX.of_le (by simp)) h0
      fun r hr => (hy r hr).hasDerivWithinAt⟩

end ProjectAInos.SmoothGeometry.NonlinearODE
