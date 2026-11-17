/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.Propagator

/-!
# Growth of the solutions of a linear equation with an integrable coefficient

* `norm_le_mul_exp_integral_of_norm_deriv_le`: if `‖f′(r)‖ ≤ a(r) ‖f(r)‖` between
  `s` and `t`, with `a` continuous, then `‖f(t)‖ ≤ ‖f(s)‖ exp ∫ₛᵗ a`.
* `norm_propagator_apply_le_exp_integral`: `‖Φ(t, s) y‖ ≤ ‖y‖ exp ∫ₛᵗ ‖A‖`. The
  bound does not depend on the length of the interval when `‖A‖` is
  integrable on the line.
* `propagator_apply_comm`: a continuous linear map that commutes with the
  coefficient commutes with the propagator.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology

namespace ProjectAinos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gronwall's inequality with a continuous coefficient. -/
theorem norm_le_mul_exp_integral_of_norm_deriv_le {f f' : ℝ → E} {a : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (ha : Continuous a) (hf : ∀ r ∈ Icc s t, HasDerivAt f (f' r) r)
    (hbound : ∀ r ∈ Icc s t, ‖f' r‖ ≤ a r * ‖f r‖) :
    ‖f t‖ ≤ ‖f s‖ * Real.exp (∫ r in s..t, a r) := by
  have hstep : ∀ δ : ℝ, 0 < δ →
      ‖f t‖ ≤ (‖f s‖ + δ) * Real.exp ((∫ r in s..t, a r) + δ * (t - s)) := by
    intro δ hδ
    have hB' : ∀ r : ℝ, HasDerivAt (fun u => (‖f s‖ + δ) * Real.exp (∫ x in s..u, (a x + δ)))
        ((a r + δ) * ((‖f s‖ + δ) * Real.exp (∫ x in s..r, (a x + δ)))) r := by
      intro r
      have h1 : HasDerivAt (fun u => ∫ x in s..u, (a x + δ)) (a r + δ) r :=
        ((ha.add continuous_const).integral_hasStrictDerivAt s r).hasDerivAt
      have h2 := (h1.exp).const_mul (‖f s‖ + δ)
      refine h2.congr_deriv ?_
      ring
    have hpos : ∀ r : ℝ, 0 < (‖f s‖ + δ) * Real.exp (∫ x in s..r, (a x + δ)) := fun r =>
      mul_pos (add_pos_of_nonneg_of_pos (norm_nonneg _) hδ) (Real.exp_pos _)
    have hmain := image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (f := f) (f' := f')
      (a := s) (b := t)
      (B := fun u => (‖f s‖ + δ) * Real.exp (∫ x in s..u, (a x + δ)))
      (B' := fun r => (a r + δ) * ((‖f s‖ + δ) * Real.exp (∫ x in s..r, (a x + δ))))
      (fun r hr => (hf r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hf r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt)
      (by
        rw [intervalIntegral.integral_same, Real.exp_zero, mul_one]
        linarith)
      (fun r _ => (hB' r).continuousAt.continuousWithinAt)
      (fun r _ => (hB' r).hasDerivWithinAt)
      (fun r hr heq => by
        have h1 := hbound r ⟨hr.1, hr.2.le⟩
        rw [heq] at h1
        have h2 := hpos r
        nlinarith)
      (right_mem_Icc.mpr hst)
    have e : (∫ x in s..t, (a x + δ)) = (∫ r in s..t, a r) + δ * (t - s) := by
      rw [intervalIntegral.integral_add (ha.intervalIntegrable s t) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    rw [← e]
    exact hmain
  have hcont : Continuous fun δ : ℝ =>
      (‖f s‖ + δ) * Real.exp ((∫ r in s..t, a r) + δ * (t - s)) := by fun_prop
  have hlim : Tendsto (fun δ : ℝ => (‖f s‖ + δ) * Real.exp ((∫ r in s..t, a r) + δ * (t - s)))
      (𝓝[>] 0) (𝓝 (‖f s‖ * Real.exp (∫ r in s..t, a r))) := by
    have h := hcont.tendsto 0
    simp only [add_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => hstep δ hδ)

variable [CompleteSpace E]

/-- The growth of a solution of a linear equation: `‖Φ(t, s) y‖ ≤ ‖y‖ exp ∫ₛᵗ ‖A‖`. -/
theorem norm_propagator_apply_le_exp_integral (A : C(ℝ, E →L[ℝ] E)) {s t : ℝ} (hst : s ≤ t)
    (y : E) : ‖propagator A t s y‖ ≤ ‖y‖ * Real.exp (∫ r in s..t, ‖A r‖) := by
  have h := norm_le_mul_exp_integral_of_norm_deriv_le (f := fun r => propagator A r s y)
    (f' := fun r => A r (propagator A r s y)) (a := fun r => ‖A r‖) hst A.continuous.norm
    (fun r _ => hasDerivAt_propagator_apply A r s y)
    (fun r _ => (A r).le_opNorm _)
  rw [propagator_self] at h
  exact h

/-- A continuous linear map that commutes with the coefficient commutes with
the propagator. -/
theorem propagator_apply_comm (A : C(ℝ, E →L[ℝ] E)) (T : E →L[ℝ] E)
    (hT : ∀ (r : ℝ) (y : E), A r (T y) = T (A r y)) (t s : ℝ) (y : E) :
    propagator A t s (T y) = T (propagator A t s y) := by
  have hf : ∀ r : ℝ, HasDerivAt (fun r => T (propagator A r s y))
      (A r (T (propagator A r s y))) r := fun r =>
    (T.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_propagator_apply A r s y)).congr_deriv
      (hT r _).symm
  have h := eq_propagator_apply_of_hasDerivAt A (f := fun r => T (propagator A r s y))
    (s := s) (t := t)
    (continuous_iff_continuousAt.mpr fun r => (hf r).continuousAt).continuousOn
    (fun r _ => hf r)
  rw [propagator_self] at h
  exact h.symm

end ProjectAinos.SmoothGeometry.LinearODE
