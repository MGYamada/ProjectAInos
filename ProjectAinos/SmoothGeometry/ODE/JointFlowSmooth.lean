/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.JointFlow

/-!
# The joint flow as a smooth function of the times and the point

The field `(t, y) ↦ (0, Σᵢ tᵢ Xᵢ(y))` on `ℝ^ι × E` has the flow
`(t, x) ↦ (t, Φ_{Σ tᵢ Xᵢ}(r, x))`, so the joint flow is smooth in `(t, x)`.

* `contDiffAt_jointFlow`: the joint flow is smooth at `(t, x)` if the flow of
  `Σᵢ tᵢ Xᵢ` through `x` exists up to the time `1`.
* `jointFlow_zero_apply`: at the time zero the joint flow is the identity.
* `hasFDerivAt_jointFlow_zero`: at `(0, x)` the derivative of the joint flow is
  `(τ, v) ↦ Σᵢ τᵢ Xᵢ(x) + v`.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] {X : ι → E → E}

/-- The field `(t, y) ↦ (0, Σᵢ tᵢ Xᵢ(y))` on the times and the points. -/
def extendedJointField (X : ι → E → E) (p : (ι → ℝ) × E) : (ι → ℝ) × E :=
  (0, jointField X p.1 p.2)

omit [CompleteSpace E] in
theorem contDiff_extendedJointField (hX : ∀ i, ContDiff ℝ ∞ (X i)) :
    ContDiff ℝ ∞ (extendedJointField X) :=
  contDiff_const.prodMk (ContDiff.sum fun i _ =>
    (by fun_prop : ContDiff ℝ ∞ fun p : (ι → ℝ) × E => p.1 i).smul ((hX i).comp contDiff_snd))

/-- The flow of the extended field keeps the times and moves the point by the
flow of `Σᵢ tᵢ Xᵢ`. -/
theorem flow_extendedJointField (hX : ∀ i, ContDiff ℝ ∞ (X i)) {t : ι → ℝ} {x : E} {r : ℝ}
    (h : (r, x) ∈ flowDomain (jointField X t)) :
    (r, (t, x)) ∈ flowDomain (extendedJointField X) ∧
      flow (extendedJointField X) (r, (t, x)) = (t, flow (jointField X t) (r, x)) := by
  have hy : ∀ u ∈ uIcc 0 r, HasDerivAt (fun u => ((t, flow (jointField X t) (u, x)) : (ι → ℝ) × E))
      (extendedJointField X (t, flow (jointField X t) (u, x))) u := fun u hu =>
    (hasDerivAt_const u t).prodMk
      (hasDerivAt_flow (contDiff_jointField hX t) (mem_flowDomain_of_mem_uIcc h hu))
  have h0 : (fun u => ((t, flow (jointField X t) (u, x)) : (ι → ℝ) × E)) 0 = (t, x) := by simp
  have hY := contDiff_extendedJointField hX
  exact ⟨mem_flowDomain_of_hasDerivWithinAt hY.continuous h0
      fun u hu => (hy u hu).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt (hY.of_le (by simp)) h0
      fun u hu => (hy u hu).hasDerivWithinAt⟩

/-- A time of the extended field is a time of the field `Σᵢ tᵢ Xᵢ`. -/
theorem mem_flowDomain_jointField_of_extended (hX : ∀ i, ContDiff ℝ ∞ (X i)) {t : ι → ℝ}
    {x : E} {r : ℝ} (h : (r, (t, x)) ∈ flowDomain (extendedJointField X)) :
    (r, x) ∈ flowDomain (jointField X t) := by
  have hY := contDiff_extendedJointField hX
  have hz : ∀ u ∈ uIcc 0 r, HasDerivAt (fun u => flow (extendedJointField X) (u, (t, x)))
      (extendedJointField X (flow (extendedJointField X) (u, (t, x)))) u := fun u hu =>
    hasDerivAt_flow hY (mem_flowDomain_of_mem_uIcc h hu)
  have h1 : ∀ u ∈ uIcc 0 r, (flow (extendedJointField X) (u, (t, x))).1 = t := by
    intro u hu
    have hc := eq_of_hasDerivAt_zero
      (g := fun u => (flow (extendedJointField X) (u, (t, x))).1) (s := 0) (t := u)
      fun v hv => (ContinuousLinearMap.fst ℝ (ι → ℝ) E).hasFDerivAt.comp_hasDerivAt v
        (hz v (uIcc_subset_uIcc_left hu hv))
    simpa using hc
  have h2 : ∀ u ∈ uIcc 0 r, HasDerivAt (fun u => (flow (extendedJointField X) (u, (t, x))).2)
      (jointField X t (flow (extendedJointField X) (u, (t, x))).2) u := by
    intro u hu
    have h3 : HasDerivAt (fun u => (flow (extendedJointField X) (u, (t, x))).2)
        (jointField X (flow (extendedJointField X) (u, (t, x))).1
          (flow (extendedJointField X) (u, (t, x))).2) u :=
      (ContinuousLinearMap.snd ℝ (ι → ℝ) E).hasFDerivAt.comp_hasDerivAt u (hz u hu)
    rwa [h1 u hu] at h3
  exact mem_flowDomain_of_hasDerivWithinAt (contDiff_jointField hX t).continuous (by simp)
    fun u hu => (h2 u hu).hasDerivWithinAt

/-- The joint flow is a smooth function of the times and the point together. -/
theorem contDiffAt_jointFlow (hX : ∀ i, ContDiff ℝ ∞ (X i)) {t : ι → ℝ} {x : E}
    (h : (1, x) ∈ flowDomain (jointField X t)) :
    ContDiffAt ℝ ∞ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (t, x) := by
  have hY := contDiff_extendedJointField hX
  have hmem := (flow_extendedJointField hX h).1
  have hpair : Continuous fun p : (ι → ℝ) × E => (((1 : ℝ), p) : ℝ × ((ι → ℝ) × E)) :=
    continuous_const.prodMk continuous_id
  have hU : IsOpen {p : (ι → ℝ) × E | ((1 : ℝ), p) ∈ flowDomain (extendedJointField X)} :=
    (isOpen_flowDomain hY).preimage hpair
  have hsm : ContDiffAt ℝ ∞
      (fun p : (ι → ℝ) × E => (flow (extendedJointField X) ((1 : ℝ), p)).2) (t, x) :=
    contDiffAt_snd.comp (t, x)
      (ContDiffAt.comp (t, x) (g := flow (extendedJointField X))
        (f := fun p : (ι → ℝ) × E => (((1 : ℝ), p) : ℝ × ((ι → ℝ) × E)))
        (contDiffAt_flow hY hmem) (contDiffAt_const.prodMk contDiffAt_id))
  refine hsm.congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hmem] with p hp
  have hp' : ((1 : ℝ), (p.1, p.2)) ∈ flowDomain (extendedJointField X) := hp
  have h1 := (flow_extendedJointField hX (mem_flowDomain_jointField_of_extended hX hp')).2
  change jointFlow X p.1 p.2 = (flow (extendedJointField X) ((1 : ℝ), (p.1, p.2))).2
  rw [h1]
  rfl

/-- The times zero are in the domain of the flow of the zero field. -/
theorem one_mem_flowDomain_jointField_zero (X : ι → E → E) (y : E) :
    ((1 : ℝ), y) ∈ flowDomain (jointField X 0) ∧ flow (jointField X 0) ((1 : ℝ), y) = y := by
  have e : jointField X 0 = fun _ => (0 : E) := by
    funext z
    simp [jointField]
  rw [e]
  have hy : ∀ u ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun _ : ℝ => y) ((fun _ : E => (0 : E)) y) u :=
    fun u _ => hasDerivAt_const u y
  exact ⟨mem_flowDomain_of_hasDerivWithinAt continuous_const rfl
      fun u hu => (hy u hu).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt contDiff_const rfl fun u hu => (hy u hu).hasDerivWithinAt⟩

/-- At the time zero the joint flow is the identity. -/
theorem jointFlow_zero_apply (X : ι → E → E) (y : E) : jointFlow X 0 y = y :=
  (one_mem_flowDomain_jointField_zero X y).2

/-- The derivative of the joint flow at the time zero. -/
theorem hasFDerivAt_jointFlow_zero (hX : ∀ i, ContDiff ℝ ∞ (X i)) (x : E) :
    ∃ D : (ι → ℝ) × E →L[ℝ] E, (∀ (τ : ι → ℝ) (v : E), D (τ, v) = jointField X τ x + v) ∧
      HasStrictFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) D (0, x) := by
  have hsm := contDiffAt_jointFlow hX (one_mem_flowDomain_jointField_zero X x).1
  have hd : HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
      (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x)) (0, x) :=
    (hsm.differentiableAt (by simp)).hasFDerivAt
  refine ⟨fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x), fun τ v => ?_,
    hsm.hasStrictFDerivAt' hd (by simp)⟩
  -- the derivative along the times
  have hτ : fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x) (τ, 0) =
      jointField X τ x := by
    have hline : HasDerivAt (fun r : ℝ => ((r • τ, x) : (ι → ℝ) × E)) (τ, 0) 0 := by
      have h1 : HasDerivAt (fun r : ℝ => r • τ) ((1 : ℝ) • τ) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const τ
      rw [one_smul] at h1
      exact h1.prodMk (hasDerivAt_const (0 : ℝ) x)
    have hcomp : HasDerivAt (fun r : ℝ => jointFlow X (r • τ) x)
        (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x) (τ, 0)) 0 := by
      have h0 : HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
          (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x))
          ((0 : ℝ) • τ, x) := by
        rw [zero_smul]
        exact hd
      exact HasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (l := fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
        (f := fun r : ℝ => ((r • τ, x) : (ι → ℝ) × E)) h0 hline
    have hXτ := contDiff_jointField hX τ
    have hopen : IsOpen {r : ℝ | (r, x) ∈ flowDomain (jointField X τ)} :=
      (isOpen_flowDomain hXτ).preimage (continuous_id.prodMk continuous_const)
    have hflow : HasDerivAt (fun r : ℝ => flow (jointField X τ) (r, x))
        (jointField X τ (flow (jointField X τ) (0, x))) 0 :=
      hasDerivAt_flow hXτ (zero_mem_flowDomain _ x)
    rw [flow_zero] at hflow
    have hev : (fun r : ℝ => jointFlow X (r • τ) x) =ᶠ[𝓝 0]
        fun r => flow (jointField X τ) (r, x) := by
      filter_upwards [hopen.mem_nhds (zero_mem_flowDomain _ x)] with r hr
      have h1 := (flow_smul_field (A := jointField X τ) (x := x) (T := 1) hXτ r
        (by rw [mul_one]; exact hr)).2
      rw [jointFlow, jointField_smul, h1, mul_one]
    exact hcomp.unique (hflow.congr_of_eventuallyEq hev)
  -- the derivative along the point
  have hv : fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x) (0, v) = v := by
    have hline : HasDerivAt (fun r : ℝ => (((0 : ι → ℝ), x + r • v) : (ι → ℝ) × E)) (0, v) 0 := by
      have h1 : HasDerivAt (fun r : ℝ => x + r • v) ((1 : ℝ) • v) 0 :=
        ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      rw [one_smul] at h1
      exact (hasDerivAt_const (0 : ℝ) (0 : ι → ℝ)).prodMk h1
    have hcomp : HasDerivAt (fun r : ℝ => jointFlow X 0 (x + r • v))
        (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x) (0, v)) 0 := by
      have h0 : HasFDerivAt (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
          (fderiv ℝ (fun p : (ι → ℝ) × E => jointFlow X p.1 p.2) (0, x))
          ((0 : ι → ℝ), x + (0 : ℝ) • v) := by
        rw [zero_smul, add_zero]
        exact hd
      exact HasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (l := fun p : (ι → ℝ) × E => jointFlow X p.1 p.2)
        (f := fun r : ℝ => (((0 : ι → ℝ), x + r • v) : (ι → ℝ) × E)) h0 hline
    have hid : HasDerivAt (fun r : ℝ => jointFlow X 0 (x + r • v)) v 0 := by
      have e : (fun r : ℝ => jointFlow X 0 (x + r • v)) = fun r => x + r • v :=
        funext fun r => jointFlow_zero_apply X _
      rw [e]
      have h1 : HasDerivAt (fun r : ℝ => x + r • v) ((1 : ℝ) • v) 0 :=
        ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      rwa [one_smul] at h1
    exact hcomp.unique hid
  have e : ((τ, v) : (ι → ℝ) × E) = (τ, 0) + (0, v) := by simp
  rw [e, map_add, hτ, hv]

end ProjectAinos.SmoothGeometry.NonlinearODE
