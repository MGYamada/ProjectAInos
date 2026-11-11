/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-! # Metric-independent differential forms on flat spaces

Forms are ambient functions. Open-domain results are stated on that domain,
and locality makes them independent of the ambient extension.
-/

@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Form (k : ℕ) := E → E [⋀^Fin k]→L[ℝ] ℝ

variable {E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ}

def exteriorDerivative (ω : Form E k) : Form E (k+1) := extDeriv ω

def pullback (f : E → F) (ω : Form F k) : Form E k :=
  fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem exteriorDerivative_squared (ω : Form E k) (hω : ContDiff ℝ 2 ω) :
    exteriorDerivative (exteriorDerivative ω) = 0 :=
  extDeriv_extDeriv hω (by simp)

theorem exteriorDerivative_local {ω η : Form E k} {U : Set E} (hU : IsOpen U)
    (h : Set.EqOn ω η U) : Set.EqOn (exteriorDerivative ω) (exteriorDerivative η) U := by
  intro x hx
  exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin
    (Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hx, h⟩))

theorem exteriorDerivative_squared_on (ω : Form E k) {U : Set E} (hU : IsOpen U)
    (hω : ContDiffOn ℝ 2 ω U) :
    Set.EqOn (exteriorDerivative (exteriorDerivative ω)) 0 U := by
  intro x hx
  exact extDeriv_extDeriv_apply ((hω x hx).contDiffAt (hU.mem_nhds hx)) (by simp)

theorem exteriorDerivative_pullback (f : E → F) (ω : Form F k)
    (hf : ContDiff ℝ 2 f) (hω : Differentiable ℝ ω) :
    exteriorDerivative (pullback f ω) = pullback f (exteriorDerivative ω) := by
  funext x
  exact extDeriv_pullback (hω (f x)) (hf.contDiffAt) (by simp)

@[simp] theorem pullback_id (ω : Form E k) : pullback id ω = ω := by
  funext x
  ext v
  simp [pullback, fderiv_id]

theorem pullback_comp (f : E → F) (g : F → G) (ω : Form G k)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    pullback (g ∘ f) ω = pullback f (pullback g ω) := by
  funext x
  ext v
  simp only [pullback, fderiv_comp x (hg (f x)) (hf x)]
  rfl

/-- Interior product, inserting the vector in the first slot. -/
def contract (v : E) (ω : Form E (k+1)) : Form E k := fun x => (ω x).curryLeft v

 theorem gauge_exteriorDerivative (A : Form E (k+1)) (χ : Form E k)
    (hA : Differentiable ℝ A) (hχ : ContDiff ℝ 2 χ) :
    extDeriv (A + extDeriv χ) = extDeriv A := by
  funext x
  rw [extDeriv_add (hA x)]
  · rw [extDeriv_extDeriv_apply hχ.contDiffAt (by simp), add_zero]
  · exact ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).differentiable.comp
      ((hχ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))) x

/-- Restriction to an open domain agrees with the ambient derivative. -/
theorem exteriorDerivative_restrict (ω : Form E k) {U : Set E} (hU : IsOpen U) :
    Set.EqOn (extDerivWithin ω U) (exteriorDerivative ω) U := by
  intro x hx
  rw [extDerivWithin, exteriorDerivative, extDeriv, fderivWithin_of_mem_nhds (hU.mem_nhds hx)]

theorem exteriorDerivative_pullback_on (f : E → F) (ω : Form F k) {U : Set E}
    (hf : ∀ x ∈ U, ContDiffAt ℝ 2 f x)
    (hω : ∀ x ∈ U, DifferentiableAt ℝ ω (f x)) :
    Set.EqOn (exteriorDerivative (pullback f ω)) (pullback f (exteriorDerivative ω)) U := by
  intro x hx
  exact extDeriv_pullback (hω x hx) (hf x hx) (by simp)

end ProjectAInos.SmoothGeometry.DifferentialForm
