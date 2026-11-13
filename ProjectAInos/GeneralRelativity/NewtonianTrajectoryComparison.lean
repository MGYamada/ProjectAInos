/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianAccelerationBounds
public import Mathlib.Analysis.ODE.Gronwall

/-! # Finite-interval comparison of Newtonian and relativistic solutions -/

@[expose] public section
noncomputable section

open Set TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped ContDiff

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
variable {U : Opens E} (f : NewtonianMetricFamily U)

/-- The physical phase field in the Newtonian limit, on position and velocity. -/
def newtonianPhaseField (t : ℝ) (z : S × S) : S × S :=
  (z.2, -f.spatialGradient (Fin.cons t z.1))

/-- The physical phase field for the relativistic family in coordinate time. -/
def relativisticPhaseField (c t : ℝ) (z : S × S) : S × S :=
  (z.2, f.acceleration c (Fin.cons t z.1) z.2)

theorem spatialGradient_sub_le {x y : E} (hseg : segment ℝ x y ⊆ U) :
    ‖f.spatialGradient y - f.spatialGradient x‖ ≤ f.bound * ‖y - x‖ := by
  have hD (z : E) (hz : z ∈ segment ℝ x y) :
      DifferentiableAt ℝ (fderiv ℝ f.potential) z :=
    (((f.potential_smooth.contDiffAt (U.isOpen.mem_nhds (hseg hz))).fderiv_right
      (m := 1) (by simp)).differentiableAt (by simp))
  have hconv : Convex ℝ (segment ℝ x y) := convex_segment x y
  have h := hconv.norm_image_sub_le_of_norm_fderiv_le hD
    (fun z hz => f.potential_bound.second z (hseg hz))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg f.bound_nonneg (norm_nonneg _))).mpr
  intro i
  change ‖(fderiv ℝ f.potential y - fderiv ℝ f.potential x) (Pi.single i.succ 1)‖ ≤ _
  exact ((fderiv ℝ f.potential y - fderiv ℝ f.potential x).le_opNorm
    (Pi.single i.succ 1)).trans (by simpa [Pi.norm_single] using h)

private theorem cons_sub_norm_le (t : ℝ) (x y : S) :
    ‖(Fin.cons t x : E) - Fin.cons t y‖ ≤ ‖x - y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change ‖t - t‖ ≤ _
    simp
  · exact norm_le_pi_norm (x - y) j

theorem newtonianPhaseField_sub_le (t : ℝ) (z w : S × S)
    (hseg : segment ℝ (Fin.cons t w.1 : E) (Fin.cons t z.1) ⊆ U) :
    ‖f.newtonianPhaseField t z - f.newtonianPhaseField t w‖ ≤
      max 1 f.bound * ‖z - w‖ := by
  have h₁ : ‖z.1 - w.1‖ ≤ ‖z - w‖ := le_max_left _ _
  have h₂ : ‖z.2 - w.2‖ ≤ ‖z - w‖ := le_max_right _ _
  have hxy := (cons_sub_norm_le t z.1 w.1).trans h₁
  change max ‖z.2 - w.2‖
    ‖-f.spatialGradient (Fin.cons t z.1) - -f.spatialGradient (Fin.cons t w.1)‖ ≤ _
  rw [neg_sub_neg, norm_sub_rev (f.spatialGradient (Fin.cons t w.1))]
  apply max_le
  · calc
      _ ≤ ‖z - w‖ := h₂
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left 1 f.bound) (norm_nonneg (z - w))
  · have hg := f.spatialGradient_sub_le hseg
    have hm : f.bound * ‖(Fin.cons t z.1 : E) - Fin.cons t w.1‖ ≤
        f.bound * ‖z - w‖ := mul_le_mul_of_nonneg_left hxy f.bound_nonneg
    have hM : f.bound * ‖z - w‖ ≤ max 1 f.bound * ‖z - w‖ :=
      mul_le_mul_of_nonneg_right (le_max_right 1 f.bound) (norm_nonneg (z - w))
    exact hg.trans (hm.trans hM)

/-- Comparison on a common interval of existence. The coordinate segments
joining the two solutions must stay inside the open domain, as they do when
both solutions stay in a convex coordinate ball at each time. -/
theorem phase_error_gronwall {c a b V δ : ℝ} (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2)
    (hV : 0 ≤ V) {z w : ℝ → S × S}
    (hz : ContinuousOn z (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hz' : ∀ t ∈ Ico a b, HasDerivWithinAt z (f.relativisticPhaseField c t (z t)) (Ici t) t)
    (hw' : ∀ t ∈ Ico a b, HasDerivWithinAt w (f.newtonianPhaseField t (w t)) (Ici t) t)
    (hseg : ∀ t ∈ Ico a b, segment ℝ (Fin.cons t (w t).1 : E) (Fin.cons t (z t).1) ⊆ U)
    (hspeed : ∀ t ∈ Ico a b, ‖(z t).2‖ ≤ V) (hδ : ‖z a - w a‖ ≤ δ) :
    ∀ t ∈ Icc a b,
      ‖z t - w t‖ ≤ gronwallBound δ (max 1 f.bound) (f.accelerationErrorConstant V / c^2) (t - a) := by
  refine norm_le_gronwallBound_of_norm_deriv_right_le (hz.sub hw)
    (fun t ht => (hz' t ht).sub (hw' t ht)) hδ ?_
  intro t ht
  let Z := f.relativisticPhaseField c t (z t)
  let W := f.newtonianPhaseField t (w t)
  let N := f.newtonianPhaseField t (z t)
  have hq := hseg t ht (right_mem_segment ℝ _ _)
  have herr : ‖Z - N‖ ≤ f.accelerationErrorConstant V / c^2 := by
    change max ‖(z t).2 - (z t).2‖
      ‖f.acceleration c (Fin.cons t (z t).1) (z t).2 - -f.spatialGradient (Fin.cons t (z t).1)‖ ≤ _
    rw [sub_self, norm_zero, sub_neg_eq_add, max_eq_right (norm_nonneg _)]
    simpa only [epsilon, div_eq_mul_inv] using
      f.acceleration_error hc hlarge ⟨_, hq⟩ hV (hspeed t ht)
  have hL : ‖N - W‖ ≤ max 1 f.bound * ‖z t - w t‖ :=
    f.newtonianPhaseField_sub_le t (z t) (w t) (hseg t ht)
  change ‖Z - W‖ ≤ _
  calc
    _ ≤ ‖Z - N‖ + ‖N - W‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
