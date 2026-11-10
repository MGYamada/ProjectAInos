module

public import ProjectAInos.Mechanics.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum

/-!
# Adding a total time derivative to a Lagrangian

A boundary function `F(t, q)` defines a first-order Lagrangian by differentiating
it along a path. Its action is the endpoint difference of `F`. Symmetry of the
second derivative gives pointwise cancellation in the Euler–Lagrange residual.
-/

@[expose] public section

open ContinuousLinearMap MeasureTheory
open scoped ContDiff

namespace ProjectAInos.Mechanics

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {a b : ℝ} {F : ℝ × Q → ℝ} {L : Lagrangian Q} {q : ℝ → Q}

/-- `∂ₜF + ∂qF(v)` in time, position, and velocity coordinates. -/
noncomputable def totalTimeDerivative (F : ℝ × Q → ℝ) : Lagrangian Q :=
  fun t z => fderiv ℝ F (t, z.1) (1, z.2)

/-- The position differential of a function of time and position. -/
noncomputable def positionDifferential (F : ℝ × Q → ℝ) (x : ℝ × Q) : Q →L[ℝ] ℝ :=
  (fderiv ℝ F x).comp (inr ℝ ℝ Q)

/-- The total time derivative uses one derivative of `F`. -/
theorem contDiff_totalTimeDerivative {n : ℕ∞ω} (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (Function.uncurry (totalTimeDerivative F)) :=
  ((hF.fderiv_right (le_refl _)).comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).clm_apply
    (contDiff_const.prodMk (contDiff_snd.comp contDiff_snd))

private theorem hasDerivAt_timePosition {t : ℝ} (hq : DifferentiableAt ℝ q t) :
    HasDerivAt (fun s => (s, q s)) (1, deriv q t) t :=
  (hasDerivAt_id t).prodMk hq.hasDerivAt

/-- On a differentiable path, the added density is the ordinary time derivative. -/
theorem hasDerivAt_boundaryFunction {t : ℝ} (hF : DifferentiableAt ℝ F (t, q t))
    (hq : DifferentiableAt ℝ q t) :
    HasDerivAt (fun s => F (s, q s)) (totalTimeDerivative F t (q t, deriv q t)) t :=
  hF.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_timePosition hq)

/-- Integrating a total time derivative gives the endpoint difference, with orientation. -/
theorem action_totalTimeDerivative (hF : ContDiff ℝ 1 F) (hq : ContDiff ℝ 1 q) :
    action a b (totalTimeDerivative F) q = F (b, q b) - F (a, q a) := by
  have hcontinuous : Continuous (fun t => totalTimeDerivative F t (q t, deriv q t)) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).continuous.comp
      (continuous_id.prodMk hq.continuous)).clm_apply
        (continuous_const.prodMk hq.continuous_deriv_one)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_boundaryFunction
      (hF.differentiable one_ne_zero _) (hq.differentiable one_ne_zero t))
    (hcontinuous.intervalIntegrable a b)

/-- Adding the total derivative changes the action by the endpoint values of `F`. -/
theorem action_add_totalTimeDerivative (hL : Continuous (Function.uncurry L))
    (hF : ContDiff ℝ 1 F) (hq : ContDiff ℝ 1 q) :
    action a b (L + totalTimeDerivative F) q = action a b L q + (F (b, q b) - F (a, q a)) := by
  have hj := continuous_id.prodMk (hq.continuous.prodMk hq.continuous_deriv_one)
  have hLInt := (hL.comp hj).intervalIntegrable (μ := volume) a b
  have hDInt := ((contDiff_totalTimeDerivative (n := 0) hF).continuous.comp hj).intervalIntegrable
    (μ := volume) a b
  calc
    _ = action a b L q + action a b (totalTimeDerivative F) q :=
      intervalIntegral.integral_add hLInt hDInt
    _ = _ := by rw [action_totalTimeDerivative hF hq]

/-- The boundary term is constant along every fixed-endpoint variation. -/
theorem stationary_add_totalTimeDerivative_iff (hL : Continuous (Function.uncurry L))
    (hF : ContDiff ℝ 1 F) (hq : ContDiff ℝ 1 q) :
    Stationary a b (L + totalTimeDerivative F) q ↔ Stationary a b L q := by
  have hshift (η : ℝ → Q) (hη : FixedEndpointVariation a b η) :
      (fun ε => action a b (L + totalTimeDerivative F) (Variational.perturb q η ε)) =
        fun ε => action a b L (Variational.perturb q η ε) + (F (b, q b) - F (a, q a)) := by
    funext ε
    have hp : ContDiff ℝ 1 (Variational.perturb q η ε) :=
      hq.add ((hη.smooth.of_le (by norm_num)).const_smul ε)
    rw [action_add_totalTimeDerivative hL hF hp, hη.perturb_left, hη.perturb_right]
  constructor
  · intro hs η hη
    have h := hs η hη
    rw [hshift η hη] at h
    simpa only [add_sub_cancel_right] using h.sub_const (F (b, q b) - F (a, q a))
  · intro hs η hη
    rw [hshift η hη]
    exact (hs η hη).add_const _

private theorem differentiable_fderiv_boundary (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (fderiv ℝ F) :=
  (hF.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

private theorem fderiv_totalTimeDerivative (hF : ContDiff ℝ 2 F) (t : ℝ) (z w : Q × Q) :
    fderiv ℝ (totalTimeDerivative F t) z w =
      fderiv ℝ F (t, z.1) (0, w.2) + fderiv ℝ (fderiv ℝ F) (t, z.1) (0, w.1) (1, z.2) := by
  have hpos : HasFDerivAt (fun y : Q × Q => (t, y.1))
      ((0 : Q × Q →L[ℝ] ℝ).prod (fst ℝ Q Q)) z :=
    (hasFDerivAt_const t z).prodMk hasFDerivAt_fst
  have hvel : HasFDerivAt (fun y : Q × Q => ((1 : ℝ), y.2))
      ((0 : Q × Q →L[ℝ] ℝ).prod (snd ℝ Q Q)) z :=
    (hasFDerivAt_const (1 : ℝ) z).prodMk hasFDerivAt_snd
  have h := (((differentiable_fderiv_boundary hF (t, z.1)).hasFDerivAt.comp z hpos).clm_apply
    hvel).fderiv
  exact congrArg (fun D : Q × Q →L[ℝ] ℝ => D w) h

/-- A total derivative shifts momentum by the position differential of its boundary function. -/
theorem momentum_totalTimeDerivative (hF : ContDiff ℝ 2 F) (q : ℝ → Q) (t : ℝ) :
    momentum (totalTimeDerivative F) q t = positionDifferential F (t, q t) := by
  apply ContinuousLinearMap.ext
  intro w
  change fderiv ℝ (totalTimeDerivative F t) (q t, deriv q t) (0, w) =
    fderiv ℝ F (t, q t) (0, w)
  rw [fderiv_totalTimeDerivative hF, show ((0, 0) : ℝ × Q) = 0 from rfl,
    map_zero, zero_apply, add_zero]

private theorem hasDerivAt_positionDifferential (hF : ContDiff ℝ 2 F) {t : ℝ}
    (hq : DifferentiableAt ℝ q t) :
    HasDerivAt (fun s => positionDifferential F (s, q s))
      ((fderiv ℝ (fderiv ℝ F) (t, q t) (1, deriv q t)).comp (inr ℝ ℝ Q)) t := by
  have h := (differentiable_fderiv_boundary hF (t, q t)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_timePosition hq)
  simpa only [positionDifferential, Function.comp_def, comp_zero, add_zero] using
    h.clm_comp (hasDerivAt_const t (inr ℝ ℝ Q))

/-- Symmetry of the second derivative identifies the position term with the
rate of change of the momentum shift. -/
theorem force_totalTimeDerivative (hF : ContDiff ℝ 2 F) {t : ℝ}
    (hq : DifferentiableAt ℝ q t) :
    force (totalTimeDerivative F) q t = deriv (fun s => positionDifferential F (s, q s)) t := by
  rw [(hasDerivAt_positionDifferential hF hq).deriv]
  apply ContinuousLinearMap.ext
  intro w
  change fderiv ℝ (totalTimeDerivative F t) (q t, deriv q t) (w, 0) =
    fderiv ℝ (fderiv ℝ F) (t, q t) (1, deriv q t) (0, w)
  rw [fderiv_totalTimeDerivative hF, show ((0, 0) : ℝ × Q) = 0 from rfl, map_zero, zero_add]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- A total time derivative has zero Euler–Lagrange residual. -/
theorem eulerLagrange_totalTimeDerivative (hF : ContDiff ℝ 2 F) {t : ℝ}
    (hq : DifferentiableAt ℝ q t) : eulerLagrange (totalTimeDerivative F) q t = 0 := by
  have hm : momentum (totalTimeDerivative F) q = fun s => positionDifferential F (s, q s) :=
    funext (momentum_totalTimeDerivative hF q)
  rw [eulerLagrange, hm, force_totalTimeDerivative hF hq, sub_self]

/-- The Euler–Lagrange covector is unchanged pointwise. A C² boundary function
suffices because the proof differentiates only its first differential. -/
theorem eulerLagrange_add_totalTimeDerivative (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hF : ContDiff ℝ 2 F) (hq : ContDiff ℝ 2 q) (t : ℝ) :
    eulerLagrange (L + totalTimeDerivative F) q t = eulerLagrange L q t := by
  have hLdiff (s : ℝ) (z : Q × Q) : DifferentiableAt ℝ (L s) z :=
    ((hL.differentiable (by norm_num)).comp
      ((differentiable_const (c := s)).prodMk differentiable_id)) z
  have hDdiff (s : ℝ) (z : Q × Q) : DifferentiableAt ℝ (totalTimeDerivative F s) z :=
    (((contDiff_totalTimeDerivative (n := 1) hF).differentiable one_ne_zero).comp
      ((differentiable_const (c := s)).prodMk differentiable_id)) z
  have hsum (s : ℝ) : fderiv ℝ ((L + totalTimeDerivative F) s) (q s, deriv q s) =
      fderiv ℝ (L s) (q s, deriv q s) + fderiv ℝ (totalTimeDerivative F s) (q s, deriv q s) :=
    fderiv_add (hLdiff s _) (hDdiff s _)
  have hm : momentum (L + totalTimeDerivative F) q =
      fun s => momentum L q s + positionDifferential F (s, q s) := by
    funext s
    simp only [momentum, hsum, add_comp, ← momentum_totalTimeDerivative hF q s]
  have hf : force (L + totalTimeDerivative F) q t = force L q t + force (totalTimeDerivative F) q t := by
    simp only [force, hsum, add_comp]
  have hqdiff := hq.differentiable (by norm_num) t
  rw [eulerLagrange, hm, hf, deriv_fun_add
    ((contDiff_momentum hL hq).differentiable one_ne_zero t)
    (hasDerivAt_positionDifferential hF hqdiff).differentiableAt,
    force_totalTimeDerivative hF hqdiff, add_sub_add_right_eq_sub, eulerLagrange]

end ProjectAInos.Mechanics
