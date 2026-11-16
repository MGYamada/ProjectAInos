/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.ParametricTrace
public import ProjectAInos.SmoothGeometry.ODE.PropagatorExpansion
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The instability zone of parametric resonance

The equation `ẍ + ω₀² (1 + h cos γt) x = 0` (Landau–Lifshitz (27.7)) has the
period `T = 2π/γ`. In the co-ordinates `a`, `b` with

`x = a cos (γt/2) + b sin (γt/2)`, `ẋ = (γ/2) (−a sin (γt/2) + b cos (γt/2))`,

the equation is a linear system whose coefficient is of the order of
`|ω₀² − γ²/4| + ω₀² |h|`, and after one period the two descriptions differ by
the sign. The expansion of the propagator of that system to second order gives
the trace of the monodromy matrix,

`tr M = −2 + (4π²/γ⁴) ((ω₀² − γ²/4)² − ω₀⁴ h²/4) + R`,

with an explicit bound of third order for `R`. Hence the motion is unstable
when `|ω₀² − γ²/4| < ω₀² |h|/2` and stable when the opposite inequality holds,
each up to the remainder. For `γ = 2ω₀ + ε` this is the zone
`−hω₀/2 < ε < hω₀/2` of Landau–Lifshitz (27.11), to first order.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Parametric

open Matrix SmoothAlgebra SmoothGeometry.LinearODE

/-! ### The trace of the monodromy matrix as a trace of the propagator -/

/-- The trace of an operator on the plane. -/
def planeTrace (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : ℝ := (L (1, 0)).1 + (L (0, 1)).2

theorem trace_monodromy_eq (p : TimeFunction) (T : ℝ) :
    (monodromy p T).trace = planeTrace (propagator (hillCoefficient p) T 0) := by
  rw [Matrix.trace_fin_two]
  change hillSolution p 1 0 (fun _ => T) + timeDerivative (hillSolution p 0 1) (fun _ => T) = _
  rw [timeDerivative_hillSolution]
  rfl

/-! ### The rotating co-ordinates -/

/-- `(a, b) ↦ (a, 0)`. -/
def e₁₁ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0

/-- `(a, b) ↦ (b, 0)`. -/
def e₁₂ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0

/-- `(a, b) ↦ (0, a)`. -/
def e₂₁ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- `(a, b) ↦ (0, b)`. -/
def e₂₂ : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The factor `(2/γ) (p(t) − γ²/4)` of the coefficient in the rotating co-ordinates. -/
def detuning (p : TimeFunction) (γ t : ℝ) : ℝ := 2 / γ * ((p fun _ => t) - γ ^ 2 / 4)

theorem continuous_detuning (p : TimeFunction) (γ : ℝ) : Continuous (detuning p γ) :=
  continuous_const.mul (p.contDiff_apply_const.continuous.sub continuous_const)

/-- The coefficient of the system for `(a, b)`. -/
def rotatingCoefficient (p : TimeFunction) (γ : ℝ) : C(ℝ, (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :=
  ⟨fun t => detuning p γ t •
      ((Real.cos (γ * t / 2) * Real.sin (γ * t / 2)) • e₁₁ + Real.sin (γ * t / 2) ^ 2 • e₁₂ -
        Real.cos (γ * t / 2) ^ 2 • e₂₁ - (Real.cos (γ * t / 2) * Real.sin (γ * t / 2)) • e₂₂),
    by
      have hd := continuous_detuning p γ
      fun_prop⟩

theorem rotatingCoefficient_apply (p : TimeFunction) (γ t : ℝ) (z : ℝ × ℝ) :
    rotatingCoefficient p γ t z =
      (detuning p γ t * (Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2) *
          Real.sin (γ * t / 2),
        -(detuning p γ t * (Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2) *
          Real.cos (γ * t / 2))) := by
  change (detuning p γ t •
      ((Real.cos (γ * t / 2) * Real.sin (γ * t / 2)) • e₁₁ + Real.sin (γ * t / 2) ^ 2 • e₁₂ -
        Real.cos (γ * t / 2) ^ 2 • e₂₁ - (Real.cos (γ * t / 2) * Real.sin (γ * t / 2)) • e₂₂)) z = _
  ext
  · simp [e₁₁, e₁₂, e₂₁, e₂₂]
    ring
  · simp [e₁₁, e₁₂, e₂₁, e₂₂]
    ring

/-- The change of co-ordinates `(a, b) ↦ (x, ẋ)` at the time `t`. -/
def rotation (γ t : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  Real.cos (γ * t / 2) • e₁₁ + Real.sin (γ * t / 2) • e₁₂ +
    (-(γ / 2 * Real.sin (γ * t / 2))) • e₂₁ + (γ / 2 * Real.cos (γ * t / 2)) • e₂₂

theorem rotation_apply (γ t : ℝ) (z : ℝ × ℝ) :
    rotation γ t z =
      (Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2,
        γ / 2 * (-(Real.sin (γ * t / 2)) * z.1 + Real.cos (γ * t / 2) * z.2)) := by
  ext
  · simp [rotation, e₁₁, e₁₂, e₂₁, e₂₂]
  · simp [rotation, e₁₁, e₁₂, e₂₁, e₂₂]
    ring

/-- A solution of the system for `(a, b)` gives a solution of the equation: the
propagators are conjugate by the change of co-ordinates. -/
theorem propagator_hillCoefficient_rotation (p : TimeFunction) {γ : ℝ} (hγ : γ ≠ 0) (t : ℝ)
    (w : ℝ × ℝ) :
    propagator (hillCoefficient p) t 0 (rotation γ 0 w) =
      rotation γ t (propagator (rotatingCoefficient p γ) t 0 w) := by
  let W : ℝ → ℝ × ℝ := fun r => propagator (rotatingCoefficient p γ) r 0 w
  have hW : ∀ r, HasDerivAt W (rotatingCoefficient p γ r (W r)) r :=
    fun r => hasDerivAt_propagator_apply (rotatingCoefficient p γ) r 0 w
  let f : ℝ → ℝ × ℝ := fun r => rotation γ r (W r)
  have hf : ∀ r, HasDerivAt f (hillCoefficient p r (f r)) r := by
    intro r
    have ha := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt r (hW r)
    have hb := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt r (hW r)
    have hθ : HasDerivAt (fun u : ℝ => γ * u / 2) (γ / 2) r := by
      simpa [mul_div_assoc] using ((hasDerivAt_id r).const_mul γ).div_const 2
    have hc := (Real.hasDerivAt_cos (γ * r / 2)).comp r hθ
    have hs := (Real.hasDerivAt_sin (γ * r / 2)).comp r hθ
    have h1 := (hc.mul ha).add (hs.mul hb)
    have h2 := ((hs.neg.mul ha).add (hc.mul hb)).const_mul (γ / 2)
    have h12 := h1.prodMk h2
    have hκ : γ / 2 * detuning p γ r = (p fun _ => r) - γ ^ 2 / 4 := by
      unfold detuning
      field_simp
    have hcs := Real.sin_sq_add_cos_sq (γ * r / 2)
    have hfr : f r = (Real.cos (γ * r / 2) * (W r).1 + Real.sin (γ * r / 2) * (W r).2,
        γ / 2 * (-(Real.sin (γ * r / 2)) * (W r).1 + Real.cos (γ * r / 2) * (W r).2)) :=
      rotation_apply γ r (W r)
    refine (h12.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => rotation_apply γ u (W u))
    rw [hillCoefficient_apply, hfr]
    simp only [rotatingCoefficient_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Function.comp_apply, Pi.neg_apply]
    ext
    · simp only
      ring
    · simp only
      linear_combination
        (-((Real.cos (γ * r / 2) * (W r).1 + Real.sin (γ * r / 2) * (W r).2) *
          (Real.sin (γ * r / 2) ^ 2 + Real.cos (γ * r / 2) ^ 2))) * hκ -
        ((p fun _ => r) - γ ^ 2 / 4) *
          (Real.cos (γ * r / 2) * (W r).1 + Real.sin (γ * r / 2) * (W r).2) * hcs
  have h := eq_propagator_apply_of_hasDerivAt (hillCoefficient p) (f := f) (s := 0) (t := t)
    (continuous_iff_continuousAt.mpr fun r => (hf r).continuousAt).continuousOn
    (fun r _ => hf r)
  have h0 : f 0 = rotation γ 0 w := by
    change rotation γ 0 (propagator (rotatingCoefficient p γ) 0 0 w) = _
    rw [propagator_self]
    rfl
  rw [h0] at h
  exact h.symm

/-- After one period the trace of the monodromy matrix is minus the trace of
the propagator in the rotating co-ordinates. -/
theorem trace_monodromy_eq_neg (p : TimeFunction) {γ : ℝ} (hγ : γ ≠ 0) :
    (monodromy p (2 * Real.pi / γ)).trace =
      -planeTrace (propagator (rotatingCoefficient p γ) (2 * Real.pi / γ) 0) := by
  have hθ : γ * (2 * Real.pi / γ) / 2 = Real.pi := by field_simp
  have h1 := propagator_hillCoefficient_rotation p hγ (2 * Real.pi / γ) (1, 0)
  have h2 := propagator_hillCoefficient_rotation p hγ (2 * Real.pi / γ) (0, 1)
  rw [rotation_apply, rotation_apply, hθ] at h1 h2
  simp only [mul_zero, zero_div, Real.cos_zero, Real.sin_zero, Real.cos_pi, Real.sin_pi,
    zero_mul, add_zero, neg_zero, mul_one, zero_add] at h1 h2
  have h2' : propagator (hillCoefficient p) (2 * Real.pi / γ) 0 (0, 1) =
      (2 / γ) • propagator (hillCoefficient p) (2 * Real.pi / γ) 0 (0, γ / 2) := by
    rw [← map_smul]
    congr 1
    ext
    · simp
    · simp
      field_simp
  rw [trace_monodromy_eq, planeTrace, planeTrace, h1, h2', h2]
  simp only [Prod.smul_snd, smul_eq_mul]
  field_simp
  ring

/-! ### The trace of an operator on the plane -/

theorem traceCLM_eq_planeTrace (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) : traceCLM L = planeTrace L := by
  rw [traceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ (Module.Basis.finTwoProd ℝ),
    Matrix.trace_fin_two, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one,
    Module.Basis.coe_finTwoProd_repr, Module.Basis.coe_finTwoProd_repr]
  rfl

theorem apply_eq_smul_add_smul (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (z : ℝ × ℝ) :
    L z = z.1 • L (1, 0) + z.2 • L (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- The trace of the square of an operator on the plane. -/
theorem planeTrace_comp_self (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    planeTrace (L ∘L L) =
      (L (1, 0)).1 ^ 2 + 2 * (L (0, 1)).1 * (L (1, 0)).2 + (L (0, 1)).2 ^ 2 := by
  unfold planeTrace
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    apply_eq_smul_add_smul L (L (1, 0)), apply_eq_smul_add_smul L (L (0, 1))]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ### The size of the coefficient in the rotating co-ordinates -/

theorem norm_rotatingCoefficient_le (p : TimeFunction) (γ t : ℝ) :
    ‖rotatingCoefficient p γ t‖ ≤ 2 * |detuning p γ t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [rotatingCoefficient_apply]
  have h1 : |z.1| ≤ ‖z‖ := norm_fst_le z
  have h2 : |z.2| ≤ ‖z‖ := norm_snd_le z
  have hc := Real.abs_cos_le_one (γ * t / 2)
  have hs := Real.abs_sin_le_one (γ * t / 2)
  have hX : |Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2| ≤ 2 * ‖z‖ := by
    calc |Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2|
        ≤ |Real.cos (γ * t / 2) * z.1| + |Real.sin (γ * t / 2) * z.2| := abs_add_le _ _
      _ = |Real.cos (γ * t / 2)| * |z.1| + |Real.sin (γ * t / 2)| * |z.2| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * ‖z‖ + 1 * ‖z‖ := add_le_add
        (mul_le_mul hc h1 (abs_nonneg _) zero_le_one)
        (mul_le_mul hs h2 (abs_nonneg _) zero_le_one)
      _ = 2 * ‖z‖ := by ring
  have hκ := abs_nonneg (detuning p γ t)
  refine (norm_prod_le_iff.mpr ⟨?_, ?_⟩)
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |detuning p γ t| * |Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2| *
          |Real.sin (γ * t / 2)|
        ≤ |detuning p γ t| * (2 * ‖z‖) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hX hκ) hs (abs_nonneg _)
            (mul_nonneg hκ (by positivity))
      _ = 2 * |detuning p γ t| * ‖z‖ := by ring
  · rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul]
    calc |detuning p γ t| * |Real.cos (γ * t / 2) * z.1 + Real.sin (γ * t / 2) * z.2| *
          |Real.cos (γ * t / 2)|
        ≤ |detuning p γ t| * (2 * ‖z‖) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hX hκ) hc (abs_nonneg _)
            (mul_nonneg hκ (by positivity))
      _ = 2 * |detuning p γ t| * ‖z‖ := by ring

/-! ### The modulated oscillator -/

/-- The coefficient `ω₀² (1 + h cos γt)` of Landau–Lifshitz (27.7). -/
def modulated (ω₀ h γ : ℝ) : TimeFunction :=
  algebraMap ℝ TimeFunction (ω₀ ^ 2) *
    (1 + algebraMap ℝ TimeFunction h * TimeFunction.cosMul γ)

theorem modulated_apply (ω₀ h γ t : ℝ) :
    modulated ω₀ h γ (fun _ => t) = ω₀ ^ 2 * (1 + h * Real.cos (γ * t)) := by
  simp [modulated, TimeFunction.mul_apply, TimeFunction.add_apply,
    TimeFunction.algebraMap_apply]

/-- The coefficient has the period `2π/γ`. -/
theorem shift_modulated (ω₀ h : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    TimeFunction.shift (2 * Real.pi / γ) (modulated ω₀ h γ) = modulated ω₀ h γ := by
  refine TimeFunction.ext_apply_const fun t => ?_
  rw [TimeFunction.shift_apply, modulated_apply, modulated_apply]
  have h1 : γ * (t + 2 * Real.pi / γ) = γ * t + 2 * Real.pi := by
    field_simp
  rw [h1, Real.cos_add_two_pi]

theorem detuning_modulated (ω₀ h γ t : ℝ) :
    detuning (modulated ω₀ h γ) γ t =
      2 / γ * (ω₀ ^ 2 - γ ^ 2 / 4 + ω₀ ^ 2 * h * Real.cos (γ * t)) := by
  rw [detuning, modulated_apply]
  ring

/-- The bound `(4/γ) (|ω₀² − γ²/4| + ω₀² |h|)` for the coefficient in the
rotating co-ordinates. -/
def zoneBound (ω₀ h γ : ℝ) : ℝ := 4 / γ * (|ω₀ ^ 2 - γ ^ 2 / 4| + ω₀ ^ 2 * |h|)

theorem zoneBound_nonneg (ω₀ h : ℝ) {γ : ℝ} (hγ : 0 < γ) : 0 ≤ zoneBound ω₀ h γ := by
  unfold zoneBound
  positivity

theorem norm_rotatingCoefficient_modulated_le (ω₀ h : ℝ) {γ : ℝ} (hγ : 0 < γ) (t : ℝ) :
    ‖rotatingCoefficient (modulated ω₀ h γ) γ t‖ ≤ zoneBound ω₀ h γ := by
  refine (norm_rotatingCoefficient_le _ γ t).trans ?_
  rw [detuning_modulated, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / γ)]
  have hcos := Real.abs_cos_le_one (γ * t)
  have h1 : |ω₀ ^ 2 - γ ^ 2 / 4 + ω₀ ^ 2 * h * Real.cos (γ * t)| ≤
      |ω₀ ^ 2 - γ ^ 2 / 4| + ω₀ ^ 2 * |h| := by
    calc |ω₀ ^ 2 - γ ^ 2 / 4 + ω₀ ^ 2 * h * Real.cos (γ * t)|
        ≤ |ω₀ ^ 2 - γ ^ 2 / 4| + |ω₀ ^ 2 * h * Real.cos (γ * t)| := abs_add_le _ _
      _ = |ω₀ ^ 2 - γ ^ 2 / 4| + ω₀ ^ 2 * |h| * |Real.cos (γ * t)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ω₀)]
      _ ≤ |ω₀ ^ 2 - γ ^ 2 / 4| + ω₀ ^ 2 * |h| * 1 := by
        gcongr
      _ = |ω₀ ^ 2 - γ ^ 2 / 4| + ω₀ ^ 2 * |h| := by ring
  have h2 : (0 : ℝ) ≤ 2 / γ := by positivity
  calc 2 * (2 / γ * |ω₀ ^ 2 - γ ^ 2 / 4 + ω₀ ^ 2 * h * Real.cos (γ * t)|)
      ≤ 2 * (2 / γ * (|ω₀ ^ 2 - γ ^ 2 / 4| + ω₀ ^ 2 * |h|)) := by gcongr
    _ = zoneBound ω₀ h γ := by
      unfold zoneBound
      ring

/-! ### The integral of the coefficient over a period -/

theorem integral_comp_mul_period (F : ℝ → ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    ∫ t in (0 : ℝ)..2 * Real.pi / γ, F (γ * t) = γ⁻¹ * ∫ u in (0 : ℝ)..2 * Real.pi, F u := by
  rw [intervalIntegral.integral_comp_mul_left F hγ, mul_zero, mul_div_cancel₀ _ hγ, smul_eq_mul]

theorem integral_sin_add_sin_mul_cos (α β : ℝ) :
    ∫ u in (0 : ℝ)..2 * Real.pi, (α * Real.sin u + β * (Real.sin u * Real.cos u)) = 0 := by
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_sin,
    integral_sin_mul_cos₁]
  simp

theorem integral_const_add_cos_add_cos_sq (α β δ : ℝ) :
    ∫ u in (0 : ℝ)..2 * Real.pi, (α + β * Real.cos u + δ * Real.cos u ^ 2) =
      2 * Real.pi * α + Real.pi * δ := by
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos, integral_cos_sq]
  simp
  ring

variable (ω₀ h : ℝ) {γ : ℝ}

/-- The mean of the diagonal entry vanishes. -/
theorem integral_detuning_mul_cos_mul_sin (hγ : γ ≠ 0) :
    ∫ t in (0 : ℝ)..2 * Real.pi / γ, detuning (modulated ω₀ h γ) γ t *
      (Real.cos (γ * t / 2) * Real.sin (γ * t / 2)) = 0 := by
  let F : ℝ → ℝ := fun u => (ω₀ ^ 2 - γ ^ 2 / 4) / γ * Real.sin u +
    ω₀ ^ 2 * h / γ * (Real.sin u * Real.cos u)
  have hF : ∀ t : ℝ, detuning (modulated ω₀ h γ) γ t *
      (Real.cos (γ * t / 2) * Real.sin (γ * t / 2)) = F (γ * t) := by
    intro t
    have h2 := Real.sin_two_mul (γ * t / 2)
    rw [show 2 * (γ * t / 2) = γ * t by ring] at h2
    rw [detuning_modulated]
    change _ = (ω₀ ^ 2 - γ ^ 2 / 4) / γ * Real.sin (γ * t) +
      ω₀ ^ 2 * h / γ * (Real.sin (γ * t) * Real.cos (γ * t))
    linear_combination
      (-(1 / γ) * (ω₀ ^ 2 - γ ^ 2 / 4 + ω₀ ^ 2 * h * Real.cos (γ * t))) * h2
  calc ∫ t in (0 : ℝ)..2 * Real.pi / γ, detuning (modulated ω₀ h γ) γ t *
        (Real.cos (γ * t / 2) * Real.sin (γ * t / 2))
      = ∫ t in (0 : ℝ)..2 * Real.pi / γ, F (γ * t) :=
        intervalIntegral.integral_congr (fun t _ => hF t)
    _ = γ⁻¹ * ∫ u in (0 : ℝ)..2 * Real.pi, F u := integral_comp_mul_period F hγ
    _ = 0 := by
      rw [show (∫ u in (0 : ℝ)..2 * Real.pi, F u) = 0 from
        integral_sin_add_sin_mul_cos _ _, mul_zero]

/-- The integral of the entry that multiplies `b`. -/
theorem integral_detuning_mul_sin_sq (hγ : γ ≠ 0) :
    ∫ t in (0 : ℝ)..2 * Real.pi / γ, detuning (modulated ω₀ h γ) γ t *
      Real.sin (γ * t / 2) ^ 2 =
      (2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) - Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2 := by
  let F : ℝ → ℝ := fun u => (ω₀ ^ 2 - γ ^ 2 / 4) / γ +
    (ω₀ ^ 2 * h - (ω₀ ^ 2 - γ ^ 2 / 4)) / γ * Real.cos u +
    -(ω₀ ^ 2 * h) / γ * Real.cos u ^ 2
  have hF : ∀ t : ℝ, detuning (modulated ω₀ h γ) γ t * Real.sin (γ * t / 2) ^ 2 =
      F (γ * t) := by
    intro t
    have h2 := Real.sin_sq_eq_half_sub (γ * t / 2)
    rw [show 2 * (γ * t / 2) = γ * t by ring] at h2
    rw [detuning_modulated, h2]
    change _ = (ω₀ ^ 2 - γ ^ 2 / 4) / γ +
      (ω₀ ^ 2 * h - (ω₀ ^ 2 - γ ^ 2 / 4)) / γ * Real.cos (γ * t) +
      -(ω₀ ^ 2 * h) / γ * Real.cos (γ * t) ^ 2
    ring
  calc ∫ t in (0 : ℝ)..2 * Real.pi / γ, detuning (modulated ω₀ h γ) γ t *
        Real.sin (γ * t / 2) ^ 2
      = ∫ t in (0 : ℝ)..2 * Real.pi / γ, F (γ * t) :=
        intervalIntegral.integral_congr (fun t _ => hF t)
    _ = γ⁻¹ * ∫ u in (0 : ℝ)..2 * Real.pi, F u := integral_comp_mul_period F hγ
    _ = (2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) - Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2 := by
      rw [show (∫ u in (0 : ℝ)..2 * Real.pi, F u) = _ from
        integral_const_add_cos_add_cos_sq _ _ _]
      field_simp
      ring

/-- The integral of the entry that multiplies `a`. -/
theorem integral_detuning_mul_cos_sq (hγ : γ ≠ 0) :
    ∫ t in (0 : ℝ)..2 * Real.pi / γ, detuning (modulated ω₀ h γ) γ t *
      Real.cos (γ * t / 2) ^ 2 =
      (2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) + Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2 := by
  let F : ℝ → ℝ := fun u => (ω₀ ^ 2 - γ ^ 2 / 4) / γ +
    (ω₀ ^ 2 * h + (ω₀ ^ 2 - γ ^ 2 / 4)) / γ * Real.cos u +
    ω₀ ^ 2 * h / γ * Real.cos u ^ 2
  have hF : ∀ t : ℝ, detuning (modulated ω₀ h γ) γ t * Real.cos (γ * t / 2) ^ 2 =
      F (γ * t) := by
    intro t
    have h2 := Real.cos_sq (γ * t / 2)
    rw [show 2 * (γ * t / 2) = γ * t by ring] at h2
    rw [detuning_modulated, h2]
    change _ = (ω₀ ^ 2 - γ ^ 2 / 4) / γ +
      (ω₀ ^ 2 * h + (ω₀ ^ 2 - γ ^ 2 / 4)) / γ * Real.cos (γ * t) +
      ω₀ ^ 2 * h / γ * Real.cos (γ * t) ^ 2
    ring
  calc ∫ t in (0 : ℝ)..2 * Real.pi / γ, detuning (modulated ω₀ h γ) γ t *
        Real.cos (γ * t / 2) ^ 2
      = ∫ t in (0 : ℝ)..2 * Real.pi / γ, F (γ * t) :=
        intervalIntegral.integral_congr (fun t _ => hF t)
    _ = γ⁻¹ * ∫ u in (0 : ℝ)..2 * Real.pi, F u := integral_comp_mul_period F hγ
    _ = (2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) + Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2 := by
      rw [show (∫ u in (0 : ℝ)..2 * Real.pi, F u) = _ from
        integral_const_add_cos_add_cos_sq _ _ _]
      field_simp

theorem integralCoefficient_apply_fst (A : C(ℝ, (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (s t : ℝ)
    (y : ℝ × ℝ) : (integralCoefficient A s t y).1 = ∫ r in s..t, (A r y).1 := by
  rw [← firstOrder_eq]
  exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm
    ((continuous_apply_const A y).intervalIntegrable s t)).symm

theorem integralCoefficient_apply_snd (A : C(ℝ, (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (s t : ℝ)
    (y : ℝ × ℝ) : (integralCoefficient A s t y).2 = ∫ r in s..t, (A r y).2 := by
  rw [← firstOrder_eq]
  exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm
    ((continuous_apply_const A y).intervalIntegrable s t)).symm

/-- The integral over a period of the coefficient in the rotating co-ordinates,
on the first basis vector. -/
theorem integralCoefficient_rotating_left (hγ : γ ≠ 0) :
    integralCoefficient (rotatingCoefficient (modulated ω₀ h γ) γ) 0 (2 * Real.pi / γ) (1, 0) =
      (0, -((2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) + Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2)) := by
  ext
  · rw [integralCoefficient_apply_fst]
    refine Eq.trans ?_ (integral_detuning_mul_cos_mul_sin ω₀ h hγ)
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rotatingCoefficient_apply]
    ring
  · rw [integralCoefficient_apply_snd]
    refine Eq.trans ?_ (congrArg Neg.neg (integral_detuning_mul_cos_sq ω₀ h hγ))
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rotatingCoefficient_apply]
    ring

/-- The same integral on the second basis vector. -/
theorem integralCoefficient_rotating_right (hγ : γ ≠ 0) :
    integralCoefficient (rotatingCoefficient (modulated ω₀ h γ) γ) 0 (2 * Real.pi / γ) (0, 1) =
      ((2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) - Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2, 0) := by
  ext
  · rw [integralCoefficient_apply_fst]
    refine Eq.trans ?_ (integral_detuning_mul_sin_sq ω₀ h hγ)
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rotatingCoefficient_apply]
    ring
  · rw [integralCoefficient_apply_snd]
    refine Eq.trans ?_ ((congrArg Neg.neg (integral_detuning_mul_cos_mul_sin ω₀ h hγ)).trans
      neg_zero)
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rotatingCoefficient_apply]
    ring

/-! ### The trace of the monodromy matrix -/

/-- The trace of the monodromy matrix of `ẍ + ω₀² (1 + h cos γt) x = 0` over
the period `2π/γ`, with the remainder of third order. -/
theorem abs_trace_monodromy_modulated_sub_le (hγ : 0 < γ) :
    |(monodromy (modulated ω₀ h γ) (2 * Real.pi / γ)).trace + 2 -
        4 * Real.pi ^ 2 / γ ^ 4 * ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4)| ≤
      Real.exp (zoneBound ω₀ h γ * (2 * Real.pi / γ)) *
        (zoneBound ω₀ h γ * (2 * Real.pi / γ)) ^ 3 / 3 := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  set G := rotatingCoefficient (modulated ω₀ h γ) γ with hG
  set T := 2 * Real.pi / γ with hT
  set g := zoneBound ω₀ h γ with hg
  have hT0 : 0 ≤ T := by positivity
  have hg0 : 0 ≤ g := zoneBound_nonneg ω₀ h hγ
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) T, ‖G r‖ ≤ g :=
    fun r _ => norm_rotatingCoefficient_modulated_le ω₀ h hγ r
  set P := integralCoefficient G 0 T with hP
  set S := secondOrderOperator G 0 T with hS
  set N := propagator G T 0 with hN
  -- the remainders on the two basis vectors
  have hrem : ∀ y : ℝ × ℝ, ‖N y - y - P y - S y‖ ≤
      ‖y‖ * Real.exp (g * (T - 0)) * (g * (T - 0)) ^ 3 / 6 := by
    intro y
    have h := norm_propagator_apply_sub_secondOrder_le (A := G) hT0 hbound hg0 y
    rwa [firstOrder_eq, secondOrder_eq] at h
  have h1 := hrem (1, 0)
  have h2 := hrem (0, 1)
  have hn1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hn2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  rw [hn1, one_mul, sub_zero] at h1
  rw [hn2, one_mul, sub_zero] at h2
  have h1' := (norm_fst_le _).trans h1
  have h2' := (norm_snd_le _).trans h2
  rw [Real.norm_eq_abs] at h1' h2'
  -- the terms of first and second order
  have hP1 := integralCoefficient_rotating_left ω₀ h hγ.ne'
  have hP2 := integralCoefficient_rotating_right ω₀ h hγ.ne'
  rw [← hG, ← hT, ← hP] at hP1 hP2
  have hS' : planeTrace S = 1 / 2 * planeTrace (P ∘L P) := by
    rw [← traceCLM_eq_planeTrace, ← traceCLM_eq_planeTrace]
    exact traceCLM_secondOrderOperator G 0 T
  have hPP : planeTrace (P ∘L P) = -2 *
      (((2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) - Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2) *
        ((2 * Real.pi * (ω₀ ^ 2 - γ ^ 2 / 4) + Real.pi * (ω₀ ^ 2 * h)) / γ ^ 2)) := by
    rw [planeTrace_comp_self, hP1, hP2]
    ring
  have htr := trace_monodromy_eq_neg (modulated ω₀ h γ) hγ.ne'
  rw [← hG, ← hT, ← hN] at htr
  have hsplit : (monodromy (modulated ω₀ h γ) T).trace + 2 -
      4 * Real.pi ^ 2 / γ ^ 4 * ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4) =
      -((N (1, 0) - (1, 0) - P (1, 0) - S (1, 0)).1 +
        (N (0, 1) - (0, 1) - P (0, 1) - S (0, 1)).2) := by
    have hS2 : (S (1, 0)).1 + (S (0, 1)).2 = planeTrace S := rfl
    have hN2 : (N (1, 0)).1 + (N (0, 1)).2 = planeTrace N := rfl
    rw [htr, ← hN2]
    simp only [Prod.fst_sub, Prod.snd_sub, hP1, hP2]
    have e : planeTrace S = -(4 * Real.pi ^ 2 / γ ^ 4 *
        ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4)) := by
      rw [hS', hPP]
      field_simp
      ring
    linear_combination -e - hS2
  rw [hsplit, abs_neg]
  calc |(N (1, 0) - (1, 0) - P (1, 0) - S (1, 0)).1 +
        (N (0, 1) - (0, 1) - P (0, 1) - S (0, 1)).2|
      ≤ |(N (1, 0) - (1, 0) - P (1, 0) - S (1, 0)).1| +
        |(N (0, 1) - (0, 1) - P (0, 1) - S (0, 1)).2| := abs_add_le _ _
    _ ≤ Real.exp (g * T) * (g * T) ^ 3 / 6 + Real.exp (g * T) * (g * T) ^ 3 / 6 :=
      add_le_add h1' h2'
    _ = Real.exp (g * T) * (g * T) ^ 3 / 3 := by ring

/-! ### The instability zone -/

/-- Instability (Landau–Lifshitz (27.11)): if `ω₀⁴ h²/4 − (ω₀² − γ²/4)²` exceeds
the remainder of third order, the equation has an unbounded solution. To first
order this is `|ω₀² − γ²/4| < ω₀² |h|/2`. -/
theorem exists_isHill_not_bounded_modulated (hγ : 0 < γ)
    (hzone : Real.exp (zoneBound ω₀ h γ * (2 * Real.pi / γ)) *
        (zoneBound ω₀ h γ * (2 * Real.pi / γ)) ^ 3 / 3 <
      4 * Real.pi ^ 2 / γ ^ 4 * (ω₀ ^ 4 * h ^ 2 / 4 - (ω₀ ^ 2 - γ ^ 2 / 4) ^ 2)) :
    ∃ x, IsHill (modulated ω₀ h γ) x ∧ ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  have h1 := (abs_le.mp (abs_trace_monodromy_modulated_sub_le ω₀ h hγ)).2
  apply exists_isHill_not_bounded_of_two_lt_abs_trace (shift_modulated ω₀ h hγ.ne')
    (by positivity)
  rw [lt_abs]
  right
  linarith

/-- Stability outside the zone: if `(ω₀² − γ²/4)² − ω₀⁴ h²/4` exceeds the
remainder of third order, and the coefficient in the rotating co-ordinates is
small, every solution is bounded. To first order this is
`|ω₀² − γ²/4| > ω₀² |h|/2`. -/
theorem exists_abs_apply_le_modulated (hγ : 0 < γ)
    (hsmall : zoneBound ω₀ h γ * (2 * Real.pi / γ) ≤ 1)
    (hzone : Real.exp (zoneBound ω₀ h γ * (2 * Real.pi / γ)) *
        (zoneBound ω₀ h γ * (2 * Real.pi / γ)) ^ 3 / 3 <
      4 * Real.pi ^ 2 / γ ^ 4 * ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4))
    {x : TimeFunction} (hx : IsHill (modulated ω₀ h γ) x) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  have h1 := abs_le.mp (abs_trace_monodromy_modulated_sub_le ω₀ h hγ)
  refine (forall_isHill_bounded_iff (shift_modulated ω₀ h hγ.ne') (by positivity)).mpr
    (Or.inl ?_) x hx
  set r := zoneBound ω₀ h γ * (2 * Real.pi / γ) with hr
  have hr0 : 0 ≤ r := mul_nonneg (zoneBound_nonneg ω₀ h hγ) (by positivity)
  -- the remainder is less than one
  have hR : Real.exp r * r ^ 3 / 3 < 1 := by
    have he : Real.exp r ≤ Real.exp 1 := Real.exp_le_exp.mpr hsmall
    have hp : r ^ 3 ≤ 1 := pow_le_one₀ hr0 hsmall
    have h3 := Real.exp_one_lt_d9
    have hmul : Real.exp r * r ^ 3 ≤ Real.exp 1 * 1 :=
      mul_le_mul he hp (by positivity) (Real.exp_pos 1).le
    linarith
  -- the main term is at most `1/16`
  have hK : 4 * Real.pi ^ 2 / γ ^ 4 * ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4) ≤
      1 / 16 := by
    set a := 2 * Real.pi / γ ^ 2 * |ω₀ ^ 2 - γ ^ 2 / 4| with ha
    have ha0 : 0 ≤ a := by positivity
    have hra : 4 * a ≤ r := by
      have hexp : r = 4 * a + 8 * Real.pi / γ ^ 2 * (ω₀ ^ 2 * |h|) := by
        rw [hr, ha]
        unfold zoneBound
        field_simp
        ring
      have hpos : 0 ≤ 8 * Real.pi / γ ^ 2 * (ω₀ ^ 2 * |h|) := by positivity
      linarith
    have ha4 : a ≤ 1 / 4 := by linarith
    have hsq : 4 * Real.pi ^ 2 / γ ^ 4 * (ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 = a ^ 2 := by
      rw [ha, mul_pow, sq_abs]
      field_simp
      ring
    have hneg : 0 ≤ 4 * Real.pi ^ 2 / γ ^ 4 * (ω₀ ^ 4 * h ^ 2 / 4) := by positivity
    have ha2 : a ^ 2 ≤ 1 / 16 := by nlinarith
    calc 4 * Real.pi ^ 2 / γ ^ 4 * ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4)
        = a ^ 2 - 4 * Real.pi ^ 2 / γ ^ 4 * (ω₀ ^ 4 * h ^ 2 / 4) := by
          rw [← hsq]
          ring
      _ ≤ 1 / 16 := by linarith
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2]

/-- Parametric resonance: for `γ = 2ω₀` and a modulation `0 < |h| ≤ 1/400` the
equation `ẍ + ω₀² (1 + h cos 2ω₀t) x = 0` has an unbounded solution. -/
theorem exists_isHill_not_bounded_modulated_resonance {ω₀ : ℝ} (hω₀ : 0 < ω₀) {h : ℝ}
    (hh : h ≠ 0) (hsmall : |h| ≤ 1 / 400) :
    ∃ x, IsHill (modulated ω₀ h (2 * ω₀)) x ∧
      ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  apply exists_isHill_not_bounded_modulated ω₀ h (by positivity : (0 : ℝ) < 2 * ω₀)
  have ha : 0 < |h| := abs_pos.mpr hh
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hr : zoneBound ω₀ h (2 * ω₀) * (2 * Real.pi / (2 * ω₀)) = 2 * Real.pi * |h| := by
    unfold zoneBound
    have h0 : ω₀ ^ 2 - (2 * ω₀) ^ 2 / 4 = 0 := by ring
    rw [h0, abs_zero, zero_add]
    field_simp
    ring
  have hK : 4 * Real.pi ^ 2 / (2 * ω₀) ^ 4 *
      (ω₀ ^ 4 * h ^ 2 / 4 - (ω₀ ^ 2 - (2 * ω₀) ^ 2 / 4) ^ 2) = Real.pi ^ 2 * |h| ^ 2 / 16 := by
    rw [sq_abs]
    field_simp
    ring
  rw [hr, hK]
  have hπa : Real.pi * |h| ≤ 3.15 / 400 := by nlinarith
  have hx1 : 2 * Real.pi * |h| ≤ 1 := by linarith
  have he : Real.exp (2 * Real.pi * |h|) ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have h9 := Real.exp_one_lt_d9
  have hkey : Real.exp 1 * (Real.pi * |h|) < 2.7182818286 * (3.15 / 400) :=
    mul_lt_mul h9 hπa (by positivity) (by norm_num)
  have hpos : 0 < Real.pi ^ 2 * |h| ^ 2 := by positivity
  calc Real.exp (2 * Real.pi * |h|) * (2 * Real.pi * |h|) ^ 3 / 3
      ≤ Real.exp 1 * (2 * Real.pi * |h|) ^ 3 / 3 := by gcongr
    _ = Real.pi ^ 2 * |h| ^ 2 * (8 / 3 * (Real.exp 1 * (Real.pi * |h|))) := by ring
    _ < Real.pi ^ 2 * |h| ^ 2 * (1 / 16) := by
      apply mul_lt_mul_of_pos_left _ hpos
      linarith
    _ = Real.pi ^ 2 * |h| ^ 2 / 16 := by ring

/-- Outside the zone: if `ω₀² |h| ≤ |ω₀² − γ²/4|` and `0 < |ω₀² − γ²/4| ≤ γ²/4000`,
every solution of `ẍ + ω₀² (1 + h cos γt) x = 0` is bounded. -/
theorem exists_abs_apply_le_modulated_of_le (hγ : 0 < γ) (hΔ : ω₀ ^ 2 - γ ^ 2 / 4 ≠ 0)
    (hΔs : |ω₀ ^ 2 - γ ^ 2 / 4| ≤ γ ^ 2 / 4000) (hh : ω₀ ^ 2 * |h| ≤ |ω₀ ^ 2 - γ ^ 2 / 4|)
    {x : TimeFunction} (hx : IsHill (modulated ω₀ h γ) x) :
    ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → |x fun _ => t| ≤ B := by
  set d := |ω₀ ^ 2 - γ ^ 2 / 4| with hd
  have hd0 : 0 < d := abs_pos.mpr hΔ
  set y := d / γ ^ 2 with hy
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 / 4000 := by
    rw [hy, div_le_iff₀ hγ2]
    linarith
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have h9 := Real.exp_one_lt_d9
  set r := zoneBound ω₀ h γ * (2 * Real.pi / γ) with hr
  have hr0 : 0 ≤ r := mul_nonneg (zoneBound_nonneg ω₀ h hγ) (by positivity)
  have hr_le : r ≤ 16 * Real.pi * y := by
    have hexp : r = 8 * Real.pi / γ ^ 2 * (d + ω₀ ^ 2 * |h|) := by
      rw [hr]
      unfold zoneBound
      rw [← hd]
      field_simp
      ring
    have h2 : 16 * Real.pi * y = 8 * Real.pi / γ ^ 2 * (d + d) := by
      rw [hy]
      field_simp
      ring
    rw [hexp, h2]
    have hc : 0 ≤ 8 * Real.pi / γ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  have hπy : Real.pi * y ≤ 3.15 / 4000 := by nlinarith
  have hr1 : r ≤ 1 := by linarith
  apply exists_abs_apply_le_modulated ω₀ h hγ hr1 _ hx
  have hR : Real.exp r * r ^ 3 / 3 ≤ Real.exp 1 * (16 * Real.pi * y) ^ 3 / 3 := by
    have he : Real.exp r ≤ Real.exp 1 := Real.exp_le_exp.mpr hr1
    have hp : r ^ 3 ≤ (16 * Real.pi * y) ^ 3 := pow_le_pow_left₀ hr0 hr_le 3
    have hmul : Real.exp r * r ^ 3 ≤ Real.exp 1 * (16 * Real.pi * y) ^ 3 :=
      mul_le_mul he hp (by positivity) (Real.exp_pos 1).le
    linarith
  have hkey : Real.exp 1 * (Real.pi * y) < 2.7182818286 * (3.15 / 4000) :=
    mul_lt_mul h9 hπy (by positivity) (by norm_num)
  have hpos : 0 < Real.pi ^ 2 * y ^ 2 := by positivity
  have hmid : Real.exp 1 * (16 * Real.pi * y) ^ 3 / 3 < 3 * (Real.pi ^ 2 * y ^ 2) := by
    calc Real.exp 1 * (16 * Real.pi * y) ^ 3 / 3
        = Real.pi ^ 2 * y ^ 2 * (4096 / 3 * (Real.exp 1 * (Real.pi * y))) := by ring
      _ < Real.pi ^ 2 * y ^ 2 * 3 := by
        apply mul_lt_mul_of_pos_left _ hpos
        linarith
      _ = 3 * (Real.pi ^ 2 * y ^ 2) := by ring
  have hK : 3 * (Real.pi ^ 2 * y ^ 2) ≤
      4 * Real.pi ^ 2 / γ ^ 4 * ((ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 - ω₀ ^ 4 * h ^ 2 / 4) := by
    have hsq : (ω₀ ^ 2 - γ ^ 2 / 4) ^ 2 = d ^ 2 := (sq_abs _).symm
    have hh2 : ω₀ ^ 4 * h ^ 2 ≤ d ^ 2 := by
      have h1 : (ω₀ ^ 2 * |h|) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) hh 2
      have h2 : (ω₀ ^ 2 * |h|) ^ 2 = ω₀ ^ 4 * h ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
      rwa [h2] at h1
    have h3 : 3 * (Real.pi ^ 2 * y ^ 2) = 4 * Real.pi ^ 2 / γ ^ 4 * (d ^ 2 - d ^ 2 / 4) := by
      rw [hy]
      field_simp
      ring
    rw [h3, hsq]
    have hc : 0 ≤ 4 * Real.pi ^ 2 / γ ^ 4 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hc
  exact lt_of_le_of_lt hR (hmid.trans_le hK)

end ProjectAInos.Mechanics.Parametric
