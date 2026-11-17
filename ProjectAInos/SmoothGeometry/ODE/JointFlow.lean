/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.CommutingFlows
public import ProjectAInos.SmoothGeometry.ODE.FlowInvariant

/-!
# The joint flow of commuting vector fields

For fields `Xᵢ` on a Banach space and `t ∈ ℝ^ι`, `jointField X t = Σᵢ tᵢ Xᵢ` and
`jointFlow X t x` is the flow of this field at the time `1`.

* `PairwiseCommute X`: `DXᵢ(y) Xⱼ(y) = DXⱼ(y) Xᵢ(y)`. Then the fields
  `jointField X t` commute (`jointField_commute`).
* `IsInvariantSet X M`: the flows of all `jointField X t` are defined for all
  times on `M` and preserve it. `isInvariantSet_of_isCompact`: a compact set
  that the flows preserve, as long as they exist, is such a set.
* `jointFlow_add`, `jointFlow_zero`, `jointFlow_smul`: on an invariant set the
  joint flow is an action of the group `ℝ^ι`, and `r ↦ jointFlow X (r • t) x` is
  the solution of the field `jointField X t`.
* `contDiffAt_jointFlow`: the joint flow is smooth in `t` and `x` together.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ι : Type*} [Fintype ι] {X : ι → E → E} {M : Set E}

/-- The field `Σᵢ tᵢ Xᵢ`. -/
def jointField (X : ι → E → E) (t : ι → ℝ) (y : E) : E := ∑ i, t i • X i y

/-- The joint flow: the flow of `Σᵢ tᵢ Xᵢ` at the time `1`. -/
def jointFlow (X : ι → E → E) (t : ι → ℝ) (x : E) : E := flow (jointField X t) (1, x)

/-- The fields commute in pairs. -/
def PairwiseCommute (X : ι → E → E) : Prop :=
  ∀ i j y, fderiv ℝ (X i) y (X j y) = fderiv ℝ (X j) y (X i y)

omit [CompleteSpace E] in
theorem contDiff_jointField (hX : ∀ i, ContDiff ℝ ∞ (X i)) (t : ι → ℝ) :
    ContDiff ℝ ∞ (jointField X t) :=
  ContDiff.sum fun i _ => contDiff_const.smul (hX i)

omit [CompleteSpace E] in
theorem jointField_add (t s : ι → ℝ) :
    jointField X (t + s) = fun y => jointField X t y + jointField X s y := by
  funext y
  simp only [jointField, Pi.add_apply, add_smul, Finset.sum_add_distrib]

omit [CompleteSpace E] in
theorem jointField_smul (c : ℝ) (t : ι → ℝ) :
    jointField X (c • t) = fun y => c • jointField X t y := by
  funext y
  simp only [jointField, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

omit [CompleteSpace E] in
theorem fderiv_jointField (hX : ∀ i, ContDiff ℝ ∞ (X i)) (t : ι → ℝ) (y : E) :
    fderiv ℝ (jointField X t) y = ∑ i, t i • fderiv ℝ (X i) y := by
  have h : HasFDerivAt (fun y => ∑ i, t i • X i y) (∑ i, t i • fderiv ℝ (X i) y) y :=
    HasFDerivAt.fun_sum fun i _ =>
      ((hX i).differentiable (by simp) y).hasFDerivAt.const_smul (t i)
  exact h.fderiv

omit [CompleteSpace E] in
/-- The fields `Σᵢ tᵢ Xᵢ` commute. -/
theorem jointField_commute (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X)
    (t s : ι → ℝ) (y : E) :
    fderiv ℝ (jointField X t) y (jointField X s y) =
      fderiv ℝ (jointField X s) y (jointField X t y) := by
  have key : ∀ (c : ι → ℝ) (L : ι → E →L[ℝ] E) (v : E),
      (∑ i, c i • L i) v = ∑ i, c i • L i v := fun c L v => by
    change ContinuousLinearMap.apply ℝ E v (∑ i, c i • L i) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [fderiv_jointField hX, fderiv_jointField hX, key, key]
  simp only [jointField, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hc i j, smul_comm]

/-- A set on which the flows of all the fields `Σᵢ tᵢ Xᵢ` are defined for all
times and which they preserve. -/
structure IsInvariantSet (X : ι → E → E) (M : Set E) : Prop where
  /-- The flows are defined for all times on the set. -/
  mem_flowDomain : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ M → (r, x) ∈ flowDomain (jointField X t)
  /-- The flows preserve the set. -/
  flow_mem : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ M → flow (jointField X t) (r, x) ∈ M

/-- A compact set that the flows preserve, as long as they exist, is invariant
with complete flows. -/
theorem isInvariantSet_of_isCompact (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hM : IsCompact M)
    (hinv : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ M → (r, x) ∈ flowDomain (jointField X t) →
      flow (jointField X t) (r, x) ∈ M) : IsInvariantSet X M := by
  have hdom : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ M → (r, x) ∈ flowDomain (jointField X t) :=
    fun t r x hx => mem_flowDomain_of_isCompact (contDiff_jointField hX t) hM
      fun s _ hs => hinv t s x hx hs
  exact ⟨hdom, fun t r x hx => hinv t r x hx (hdom t r x hx)⟩

omit [CompleteSpace E] in
/-- The whole space is invariant if every field `Σᵢ tᵢ Xᵢ` is complete. -/
theorem isInvariantSet_univ (h : ∀ t : ι → ℝ, flowDomain (jointField X t) = univ) :
    IsInvariantSet X univ :=
  ⟨fun t r x _ => by rw [h t]; exact mem_univ _, fun _ _ _ _ => mem_univ _⟩

section Action

omit [CompleteSpace E] in
theorem jointFlow_mem (hM : IsInvariantSet X M) (t : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X t x ∈ M :=
  hM.flow_mem t 1 x hx

variable (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hc : PairwiseCommute X) (hM : IsInvariantSet X M)
include hX hc hM

/-- The joint flow is an action of `ℝ^ι` on an invariant set. -/
theorem jointFlow_add (t s : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X (t + s) x = jointFlow X t (jointFlow X s x) := by
  have h := (flow_add_of_commute (A := jointField X t) (B := jointField X s) (x := x) (T := 1)
    (contDiff_jointField hX t) (contDiff_jointField hX s) (jointField_commute hX hc t s)
    (fun r _ => hM.mem_flowDomain s r x hx)
    (fun r _ => hM.mem_flowDomain t r _ (hM.flow_mem s r x hx))).2
  rw [jointFlow, jointField_add]
  exact h

omit hc in
/-- Along a line of times the joint flow is the flow of the field of the
direction. -/
theorem jointFlow_smul (r : ℝ) (t : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X (r • t) x = flow (jointField X t) (r, x) := by
  have h := (flow_smul_field (A := jointField X t) (x := x) (T := 1) (contDiff_jointField hX t) r
    (hM.mem_flowDomain t (r * 1) x hx)).2
  rw [jointFlow, jointField_smul, h, mul_one]

omit hc in
theorem jointFlow_zero {x : E} (hx : x ∈ M) : jointFlow X 0 x = x := by
  have h := jointFlow_smul hX hM 0 0 hx
  rw [zero_smul] at h
  rw [h, flow_zero]

theorem jointFlow_neg (t : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X (-t) (jointFlow X t x) = x := by
  rw [← jointFlow_add hX hc hM (-t) t hx, neg_add_cancel, jointFlow_zero hX hM hx]

theorem jointFlow_comm (t s : ι → ℝ) {x : E} (hx : x ∈ M) :
    jointFlow X t (jointFlow X s x) = jointFlow X s (jointFlow X t x) := by
  rw [← jointFlow_add hX hc hM t s hx, ← jointFlow_add hX hc hM s t hx, add_comm]

omit hc in
/-- The derivative of the joint flow along a line of times. -/
theorem hasDerivAt_jointFlow_smul (t : ι → ℝ) {x : E} (hx : x ∈ M) (r : ℝ) :
    HasDerivAt (fun r : ℝ => jointFlow X (r • t) x)
      (jointField X t (jointFlow X (r • t) x)) r := by
  have e : (fun r : ℝ => jointFlow X (r • t) x) = fun r => flow (jointField X t) (r, x) :=
    funext fun r => jointFlow_smul hX hM r t hx
  rw [e, jointFlow_smul hX hM r t hx]
  exact hasDerivAt_flow (contDiff_jointField hX t) (hM.mem_flowDomain t r x hx)

end Action

end ProjectAInos.SmoothGeometry.NonlinearODE
