/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.FlowComplete

/-!
# Quantities that are constant along a flow

A function of the time whose derivative vanishes between two times takes the
same value at them. Along a line of a flow the times between `0` and `t` are in
the domain, so a quantity whose derivative vanishes along every solution is
constant along the flow, also when the flow is not defined for all times.
-/

@[expose] public section
noncomputable section

open Set

namespace ProjectAinos.SmoothGeometry.NonlinearODE

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function whose derivative vanishes between two times takes the same value
at them. -/
theorem eq_of_hasDerivAt_zero {g : ℝ → F} {s t : ℝ}
    (hg : ∀ r ∈ uIcc s t, HasDerivAt g 0 r) : g t = g s := by
  rcases le_total s t with hst | hst
  · rw [uIcc_of_le hst] at hg
    exact constant_of_has_deriv_right_zero
      (fun r hr => (hg r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hg r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt) t ⟨hst, le_rfl⟩
  · rw [uIcc_of_ge hst] at hg
    exact (constant_of_has_deriv_right_zero
      (fun r hr => (hg r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hg r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt) s ⟨hst, le_rfl⟩).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E} {t : ℝ} {x : E}

/-- A quantity whose derivative vanishes along the solutions of the field is
constant along the flow. -/
theorem flow_invariant (hX : ContDiff ℝ (⊤ : ℕ∞) X) {f : E → F}
    (hf : ∀ {y : ℝ → E} {r : ℝ}, HasDerivAt y (X (y r)) r → HasDerivAt (fun s => f (y s)) 0 r)
    (h : (t, x) ∈ flowDomain X) : f (flow X (t, x)) = f x := by
  have hc := eq_of_hasDerivAt_zero (g := fun s => f (flow X (s, x))) (s := 0) (t := t)
    fun r hr => hf (hasDerivAt_flow hX (mem_flowDomain_of_mem_uIcc h hr))
  simpa using hc

end ProjectAinos.SmoothGeometry.NonlinearODE
