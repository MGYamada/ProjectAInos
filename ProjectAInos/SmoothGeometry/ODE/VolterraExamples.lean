/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.Volterra
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # A nonconstant coefficient example for the Volterra solution

The equation `y' = (t / 2) y` on `[0,1]` has solution `exp(t²/4) y₀`.
This example exercises the smallness bound, differential-equation uniqueness
and the actual resolvent-defined solution, for arbitrary Banach vector values.
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap
open scoped Topology

namespace ProjectAInos.SmoothGeometry.LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A genuinely time-dependent coefficient with norm at most `1/2`. -/
def rampCoefficient : Curve (E →L[ℝ] E) :=
  ⟨fun t => ((t : ℝ) / 2) • ContinuousLinearMap.id ℝ E,
    (continuous_subtype_val.div_const 2).smul continuous_const⟩

omit [CompleteSpace E] in
theorem rampCoefficient_norm_le : ‖rampCoefficient (E := E)‖ ≤ 1 / 2 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  change ‖((t : ℝ) / 2) • ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg t.property.1 (by norm_num))]
  calc
    (t : ℝ) / 2 * ‖ContinuousLinearMap.id ℝ E‖ ≤ (t : ℝ) / 2 * 1 :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le)
        (div_nonneg t.property.1 (by norm_num))
    _ ≤ 1 / 2 := by simpa using div_le_div_of_nonneg_right t.property.2 (by norm_num : (0 : ℝ) ≤ 2)

/-- Exact agreement of the constructed solution with a nonconstant-coefficient
closed form. -/
theorem solution_ramp (y : E) (t : unitInterval) :
    solutionOperator (rampCoefficient (E := E)) y t = Real.exp ((t : ℝ) ^ 2 / 4) • y := by
  let f : Curve E := ⟨fun u => Real.exp ((u : ℝ) ^ 2 / 4) • y, by fun_prop⟩
  have hsmall : ‖rampCoefficient (E := E)‖ < 1 := rampCoefficient_norm_le.trans_lt (by norm_num)
  have hEq := eq_solution_of_hasDerivAt (E := E) hsmall y f (by simp [f])
  have hf : f = solutionOperator (rampCoefficient (E := E)) y := by
    apply hEq
    intro s hs
    have he : extend f =ᶠ[𝓝 s] fun u => Real.exp (u ^ 2 / 4) • y := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      simp [extend, projIcc_of_mem zero_le_one (mem_Icc_of_Ioo hu), f]
    have hd := ((((hasDerivAt_id s).pow 2).div_const 4).exp.smul_const y)
    have hc : extend rampCoefficient s (extend f s) =
        (Real.exp (s ^ 2 / 4) * (2 * s ^ (2 - 1) * 1 / 4)) • y := by
      simp only [extend, projIcc_of_mem zero_le_one (mem_Icc_of_Ioo hs), rampCoefficient, f,
        ContinuousMap.coe_mk, smul_apply, ContinuousLinearMap.id_apply,
        smul_smul]
      congr 1
      ring
    rw [hc]
    exact hd.congr_of_eventuallyEq he
  exact (congrArg (fun g : Curve E => g t) hf).symm

end ProjectAInos.SmoothGeometry.LinearODE
