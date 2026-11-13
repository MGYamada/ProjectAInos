/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Bundle

/-! # Native form coefficients and overlap laws

Coefficients are obtained from actual tangent trivializations. The overlap
law is an equality of alternating maps, not an assumed transformation rule.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Coefficients in any tangent trivialization. -/
def coefficients {k : ℕ} (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] (α : NativeForm I M k) (x : M) : E [⋀^Fin k]→L[ℝ] ℝ :=
  (α x).compContinuousLinearMap (e.symmL ℝ x)

/-- The actual tangent transition gives the overlap law in every covariant slot. -/
theorem coefficients_change {k : ℕ} (e e' : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (α : NativeForm I M k)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    coefficients I e' α x = (coefficients I e α x).compContinuousLinearMap
      (e'.coordChangeL ℝ e x).toContinuousLinearMap := by
  rw [← e'.comp_continuousLinearEquivAt_eq_coord_change e ⟨hx', hx⟩]
  ext v
  simp only [coefficients, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  change e'.symmL ℝ x (v i) = e.symmL ℝ x
    ((e.continuousLinearEquivAt ℝ x hx) ((e'.continuousLinearEquivAt ℝ x hx').symm (v i)))
  rw [e.coe_continuousLinearEquivAt_eq hx, e'.symm_continuousLinearEquivAt_eq hx']
  exact (e.symmL_continuousLinearMapAt hx _).symm

/-- A smooth form has smooth coefficients in every actual tangent trivialization. -/
theorem SmoothForm.contMDiffAt_coefficients {k : ℕ}
    (α : SmoothForm I M k) (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞
      (coefficients I e (fun y => α y)) x := by
  let e₀ := trivializationAt E (TangentSpace I) x
  have hx₀ : x ∈ e₀.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hL := contMDiffAt_coordChangeL (IB := I) (n := ∞) hx hx₀
  have hα := α.coefficients_contMDiffAt I x
  apply (hL.compContinuousLinearMapCLM.clm_apply hα).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx, e₀.open_baseSet.mem_nhds hx₀] with y hy hy₀
  exact coefficients_change I e₀ e (fun z => α z) hy₀ hy

/-- Pointwise recovery shows that chart coefficients determine the native form. -/
theorem coefficients_recover {k : ℕ} (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] (α : NativeForm I M k) {x : M} (hx : x ∈ e.baseSet) :
    (coefficients I e α x).compContinuousLinearMap (e.continuousLinearMapAt ℝ x) = α x := by
  ext v
  change α x (fun i => e.symmL ℝ x (e.continuousLinearMapAt ℝ x (v i))) = α x v
  congr 1
  funext i
  exact e.symmL_continuousLinearMapAt hx (v i)

end ProjectAInos.SmoothGeometry.DifferentialForm
