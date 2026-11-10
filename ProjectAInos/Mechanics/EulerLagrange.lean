module

public import ProjectAInos.Mechanics.FirstVariation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.NormNum

/-!
# Fixed-endpoint stationarity and the Euler–Lagrange equations

For `a < b`, a C² mechanical Lagrangian and a C² path, fixed-endpoint
stationarity is equivalent to the Euler–Lagrange equation on `(a, b)`.
The forward implication uses the fundamental lemma, by testing with all
compactly supported smooth scalar functions multiplied by a fibre vector.
The reverse implication applies to every smooth endpoint-vanishing variation,
including variations with nonzero derivatives at the endpoints.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace ProjectAInos.Mechanics

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  {a b : ℝ} {L : Lagrangian Q} {q : ℝ → Q}

/-- The fixed-endpoint variational principle is equivalent to the classical
Euler–Lagrange equation in the interior of a nondegenerate time interval. -/
theorem stationary_iff_eulerLagrange (hab : a < b)
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q) :
    Stationary a b L q ↔ ∀ t ∈ Ioo a b, eulerLagrange L q t = 0 := by
  refine ⟨?_, fun h η hη => ?_⟩
  · intro hs t ht
    ext v
    let R : ℝ → ℝ := fun s => eulerLagrange L q s v
    have hR : Continuous R := (continuous_eulerLagrange hL hq).clm_apply continuous_const
    have ha := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hR.continuousOn.locallyIntegrableOn (μ := volume) measurableSet_Ioo)
      (fun g hg _hgK hgI => by
        let ζ : ℝ → Q := fun s => g s • v
        have hga : g a = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => (lt_irrefl a) (hgI h).1)
        have hgb : g b = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => (lt_irrefl b) (hgI h).2)
        have hζ : FixedEndpointVariation a b ζ :=
          ⟨hg.smul contDiff_const, by simp [ζ, hga], by simp [ζ, hgb]⟩
        have hz := (hasDerivAt_action_eulerLagrange hab.le hL hq hζ).unique (hs ζ hζ)
        have heq : (∫ s in a..b, eulerLagrange L q s (ζ s)) = ∫ s, g s • R s := by
          simp only [ζ, R, map_smul]
          rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hs (hgI h)), zero_smul]
        exact heq.symm.trans hz)
    have hr : R =ᵐ[volume.restrict (Ioo a b)] (fun _ => 0) :=
      (ae_restrict_iff' measurableSet_Ioo).2 ha
    exact Measure.eqOn_open_of_ae_eq hr isOpen_Ioo hR.continuousOn
      continuous_const.continuousOn ht
  · have hz : (∫ t in a..b, eulerLagrange L q t (η t)) = 0 := by
      rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
      exact setIntegral_eq_zero_of_ae_eq_zero
        (.of_forall fun t ht => by simp [h t ht])
    simpa only [hz] using hasDerivAt_action_eulerLagrange hab.le hL hq hη

/-- The familiar form `d/dt (∂L/∂v) = ∂L/∂q`. -/
theorem stationary_iff_momentum_equation (hab : a < b)
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hq : ContDiff ℝ 2 q) :
    Stationary a b L q ↔ ∀ t ∈ Ioo a b, deriv (momentum L q) t = force L q t := by
  rw [stationary_iff_eulerLagrange hab hL hq]
  simp only [eulerLagrange, sub_eq_zero]
  exact forall_congr' fun _ => forall_congr' fun _ => eq_comm

end ProjectAInos.Mechanics
