module

public import ProjectAInos.Mechanics.Basic
public import ProjectAInos.Variational.IntegrationByParts
import Mathlib.Tactic.NormNum

/-!
# The first variation of a mechanical action

Joint C² regularity on a finite interval justifies differentiating the action.
Integration by parts then gives the Euler–Lagrange pairing and the endpoint term.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace ProjectAInos.Mechanics

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {a b : ℝ} {L : Lagrangian Q} {q η : ℝ → Q}

/-- The mechanical first variation in position and velocity coordinates. -/
noncomputable def firstVariation (a b : ℝ) (L : Lagrangian Q) (q η : ℝ → Q) : ℝ :=
  ∫ t in a..b, force L q t (η t) + momentum L q t (deriv η t)

/-- C² paths have an integrable mechanical density on every finite interval. -/
theorem intervalIntegrable_density (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hq : ContDiff ℝ 2 q) :
    IntervalIntegrable (fun t => L t (q t, deriv q t)) volume a b :=
  (hL.continuous.comp (continuous_id.prodMk (contDiff_positionVelocity hq).continuous)).intervalIntegrable _ _

/-- The first variation is the derivative of the actual action. Integrability and
uniform domination are consequences of regularity and compactness. -/
theorem hasDerivAt_action_firstVariation (hab : a ≤ b)
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) :
    HasDerivAt (fun ε => action a b L (Variational.perturb q η ε))
      (firstVariation a b L q η) 0 := by
  have hi : firstVariation a b L q η =
      Variational.firstVariation (volume.restrict (Icc a b)) (toVariational L) q η := by
    simp only [firstVariation, Variational.firstVariation, firstVariationDensity_eq hL]
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [hi]
  simpa only [action_eq_variational hab] using
    (Variational.hasDerivAt_action_restrict_compact (μ := volume) isCompact_Icc
      (contDiff_toVariational hL) hq hη).2

/-- The full first-variation formula retains the momentum pairing at both ends. -/
theorem firstVariation_eq_boundary_add_integral
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q)
    (hη : ContDiff ℝ 2 η) :
    firstVariation a b L q η =
      (momentum L q b (η b) - momentum L q a (η a)) +
        ∫ t in a..b, eulerLagrange L q t (η t) := by
  have hP := contDiff_momentum hL hq
  have hP' : Continuous (deriv (momentum L q)) :=
    (hP.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  exact Variational.interval_firstVariation_pairing
    (fun t _ => (hP.differentiable one_ne_zero t).hasDerivAt)
    (fun t _ => (hη.differentiable (by norm_num) t).hasDerivAt)
    (((contDiff_force hL hq).continuous.clm_apply hη.continuous).intervalIntegrable _ _)
    ((hP'.clm_apply hη.continuous).intervalIntegrable _ _)
    ((hP.continuous.clm_apply (contDiff_positionVelocity hη).continuous.snd).intervalIntegrable _ _)

/-- Fixed endpoints remove precisely the boundary term. -/
theorem firstVariation_fixedEndpoints
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q)
    (hη : FixedEndpointVariation a b η) :
    firstVariation a b L q η = ∫ t in a..b, eulerLagrange L q t (η t) := by
  simpa only [hη.left, hη.right, map_zero, sub_self, zero_add] using
    firstVariation_eq_boundary_add_integral (a := a) (b := b)
      hL hq (hη.smooth.of_le (by norm_num))

/-- The action derivative for a fixed-endpoint variation is the residual pairing. -/
theorem hasDerivAt_action_eulerLagrange (hab : a ≤ b)
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q)
    (hη : FixedEndpointVariation a b η) :
    HasDerivAt (fun ε => action a b L (Variational.perturb q η ε))
      (∫ t in a..b, eulerLagrange L q t (η t)) 0 := by
  rw [← firstVariation_fixedEndpoints hL hq hη]
  exact hasDerivAt_action_firstVariation hab hL hq (hη.smooth.of_le (by norm_num))

end ProjectAInos.Mechanics
