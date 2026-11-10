module

public import ProjectAInos.Mechanics.SmoothLagrangian
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Mechanical examples and boundary checks

The natural scalar Lagrangian yields Newton's equation. These examples also
exercise nonzero endpoint derivatives of variations and degenerate intervals.
-/

@[expose] public section

noncomputable section

open Set ContinuousLinearMap
open scoped ContDiff

namespace ProjectAInos.Mechanics

/-- Kinetic energy minus a position-dependent potential, for one coordinate. -/
def natural (m : ℝ) (V : ℝ → ℝ) : Lagrangian ℝ :=
  fun _ z => m / 2 * (z.2 * z.2) - V z.1

theorem contDiff_natural (m : ℝ) {V : ℝ → ℝ} (hV : ContDiff ℝ 2 V) :
    ContDiff ℝ 2 (Function.uncurry (natural m V)) :=
  (contDiff_const.mul ((contDiff_snd.comp contDiff_snd).mul
    (contDiff_snd.comp contDiff_snd))).sub
      (hV.comp (contDiff_fst.comp contDiff_snd))

theorem fderiv_natural (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V)
    (t : ℝ) (z : ℝ × ℝ) :
    fderiv ℝ (natural m V t) z =
      (m * z.2) • snd ℝ ℝ ℝ - deriv V z.1 • fst ℝ ℝ ℝ := by
  have hv : HasFDerivAt (fun w : ℝ × ℝ => w.2) (snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  have h := ((hv.mul hv).const_mul (m / 2)).sub
    ((hV z.1).hasDerivAt.hasFDerivAt.comp z hasFDerivAt_fst)
  change fderiv ℝ (fun w : ℝ × ℝ => m / 2 * (w.2 * w.2) - V w.1) z = _
  rw [show fderiv ℝ (fun w : ℝ × ℝ => m / 2 * (w.2 * w.2) - V w.1) z = _ from h.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp only [sub_apply, smul_apply, add_apply, comp_apply,
    toSpanSingleton_apply, smul_eq_mul]
  change m / 2 * (z.2 * w.2 + z.2 * w.2) - w.1 * deriv V z.1 =
    m * z.2 * w.2 - deriv V z.1 * w.1
  ring

@[simp] theorem force_natural (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V)
    (q : ℝ → ℝ) (t : ℝ) :
    force (natural m V) q t = (-deriv V (q t)) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp [force, fderiv_natural m hV]

@[simp] theorem momentum_natural (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V)
    (q : ℝ → ℝ) (t : ℝ) :
    momentum (natural m V) q t = (m * deriv q t) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp [momentum, fderiv_natural m hV]

/-- The residual has the expected force and acceleration signs. -/
theorem eulerLagrange_natural (m : ℝ) {V : ℝ → ℝ} (hV : Differentiable ℝ V)
    {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (t : ℝ) :
    eulerLagrange (natural m V) q t =
      (-deriv V (q t) - m * deriv (deriv q) t) • ContinuousLinearMap.id ℝ ℝ := by
  have hdq : Differentiable ℝ (deriv q) :=
    (hq.deriv' (n := 1)).differentiable one_ne_zero
  have hp := (((hdq t).hasDerivAt.const_mul m).smul_const
    (ContinuousLinearMap.id ℝ ℝ)).deriv
  have hm : momentum (natural m V) q =
      fun s => (m * deriv q s) • ContinuousLinearMap.id ℝ ℝ :=
    funext (momentum_natural m hV q)
  rw [eulerLagrange, hm, hp, force_natural m hV]
  exact (_root_.sub_smul _ _ _).symm

/-- The fixed-endpoint principle gives Newton's equation for every C² potential.
No sign or nonzero assumption on `m` is needed for this identity. -/
theorem stationary_natural_iff {a b m : ℝ} {V q : ℝ → ℝ}
    (hab : a < b) (hV : ContDiff ℝ 2 V) (hq : ContDiff ℝ 2 q) :
    Stationary a b (natural m V) q ↔
      ∀ t ∈ Ioo a b, m * deriv (deriv q) t = -deriv V (q t) := by
  rw [stationary_iff_eulerLagrange hab (contDiff_natural m hV) hq]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  rw [eulerLagrange_natural m (hV.differentiable (by norm_num)) hq]
  constructor
  · intro h
    have hv := congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) h
    simp only [smul_apply, id_apply, smul_eq_mul, mul_one, zero_apply] at hv
    exact (sub_eq_zero.mp hv).symm
  · intro h
    simp only [h, sub_self, zero_smul]

/-- A smooth endpoint-vanishing variation that need not vanish near either end. -/
theorem polynomial_fixedEndpointVariation {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] (a b : ℝ) (v : Q) :
    FixedEndpointVariation a b (fun t => ((t - a) * (b - t)) • v) := by
  refine ⟨((contDiff_id.sub contDiff_const).mul
    (contDiff_const.sub contDiff_id)).smul contDiff_const, ?_, ?_⟩ <;> simp

/-- Fixed endpoints impose no zero-velocity condition on the variation. -/
theorem polynomial_variation_left_derivative (a b : ℝ) :
    deriv (fun t => (t - a) * (b - t)) a = b - a := by
  have h := (((hasDerivAt_id a).sub_const a).mul
    ((hasDerivAt_const a b).sub (hasDerivAt_id a))).deriv
  simpa only [Pi.mul_def, Pi.sub_def, id_eq, sub_self, zero_mul, one_mul, add_zero] using h

/-- A zero-length action is stationary for every path and Lagrangian; this is why
`a < b` appears in the equation-detecting theorem. -/
theorem stationary_self {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (a : ℝ) (L : Lagrangian Q) (q : ℝ → Q) : Stationary a a L q := by
  intro η _
  simpa only [action, intervalIntegral.integral_same] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))

/-- Every uniform straight-line motion is stationary for the free-particle action. -/
theorem stationary_free_affine {a b : ℝ} (hab : a < b) (m v x : ℝ) :
    Stationary a b (natural m (fun _ => 0)) (fun t => v * t + x) := by
  have hq : ContDiff ℝ 2 (fun t : ℝ => v * t + x) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  apply (stationary_natural_iff hab contDiff_const hq).2
  have hd : deriv (fun t : ℝ => v * t + x) = fun _ => v := by
    funext t
    simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul v).add_const x).deriv
  intro t _
  simp [hd]

/-- The variational criterion rejects an accelerated free-particle path. -/
theorem not_stationary_free_square :
    ¬ Stationary 0 1 (natural 1 (fun _ => 0)) (fun t => t * t) := by
  intro hs
  have he := (stationary_natural_iff (by norm_num : (0 : ℝ) < 1)
    contDiff_const (contDiff_id.mul contDiff_id)).1 hs
  have hd : deriv (fun t : ℝ => t * t) = fun t => 2 * t := by
    funext t
    convert ((hasDerivAt_id t).mul (hasDerivAt_id t)).deriv using 1 <;> simp [Pi.mul_def]
    ring
  have hdd (t : ℝ) : deriv (deriv (fun s : ℝ => s * s)) t = 2 := by
    rw [hd]
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul 2).deriv
  have h := he (1 / 2) (by constructor <;> norm_num)
  norm_num [hdd] at h

/-- With no configuration coordinates, every variation is the zero variation. -/
theorem stationary_no_coordinates (a b : ℝ) (L : Lagrangian (Fin 0 → ℝ))
    (q : ℝ → Fin 0 → ℝ) : Stationary a b L q := by
  intro η _
  have heq (ε : ℝ) : Variational.perturb q η ε = q :=
    funext fun _ => Subsingleton.elim _ _
  simpa only [heq] using hasDerivAt_const (0 : ℝ) (action a b L q)

end ProjectAInos.Mechanics
