/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianLipschitz
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.MetricSpace.Thickening

/-! # Common existence intervals inside a Newtonian trajectory tube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Metric TopologicalSpace Filter
open scoped Topology NNReal ContDiff

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
local notation "P" => (S × S)
variable {U : Opens E} (f : NewtonianMetricFamily U)

private def clip (r x : ℝ) : ℝ := min r (max (-r) x)

private theorem clip_lipschitz (r : ℝ) : LipschitzWith 1 (clip r) := by
  have h := (LipschitzWith.const (α := ℝ) r).min
    ((LipschitzWith.const (α := ℝ) (-r)).max (LipschitzWith.id (α := ℝ)))
  unfold clip
  simpa using h

private theorem abs_clip_le {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : |clip r x| ≤ r := by
  rw [abs_le]
  exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩

private def clipPhase (r : ℝ) (z : P) : P :=
  (fun i => clip r (z.1 i), fun i => clip r (z.2 i))

private theorem clipPhase_lipschitz (r : ℝ) : LipschitzWith 1 (clipPhase r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  change max ‖(clipPhase r x - clipPhase r y).1‖ ‖(clipPhase r x - clipPhase r y).2‖ ≤ _
  have h (a b : S) : ‖(fun i => clip r (a i) - clip r (b i))‖ ≤ ‖a-b‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have hi := (clip_lipschitz r).dist_le_mul (a i) (b i)
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul] at hi
    exact hi.trans (norm_le_pi_norm (a-b) i)
  exact max_le_max (h x.1 y.1) (h x.2 y.2)

private theorem clipPhase_norm_le {r : ℝ} (hr : 0 ≤ r) (x : P) : ‖clipPhase r x‖ ≤ r := by
  rw [Prod.norm_def]
  apply max_le
  · exact (pi_norm_le_iff_of_nonneg hr).mpr fun i => by
      simpa only [clipPhase, Real.norm_eq_abs] using abs_clip_le hr (x.1 i)
  · exact (pi_norm_le_iff_of_nonneg hr).mpr fun i => by
      simpa only [clipPhase, Real.norm_eq_abs] using abs_clip_le hr (x.2 i)

private theorem clipPhase_eq {r : ℝ} {x : P} (hx : ‖x‖ ≤ r) : clipPhase r x = x := by
  have h₁ : ‖x.1‖ ≤ r := (le_max_left _ _ : ‖x.1‖ ≤ ‖x‖).trans hx
  have h₂ : ‖x.2‖ ≤ r := (le_max_right _ _ : ‖x.2‖ ≤ ‖x‖).trans hx
  have h (a : ℝ) (ha : |a| ≤ r) : clip r a = a := by
    rw [clip, max_eq_right (abs_le.mp ha).1, min_eq_right (abs_le.mp ha).2]
  exact Prod.ext (funext fun i => h _ (spaceComponent_abs_le h₁ i))
    (funext fun i => h _ (spaceComponent_abs_le h₂ i))

private theorem clipPhase_norm_le_self (r : ℝ) (hr : 0 ≤ r) (x : P) :
    ‖clipPhase r x‖ ≤ ‖x‖ := by
  have h0 : clipPhase r 0 = 0 := clipPhase_eq (by simpa using hr)
  have h := (clipPhase_lipschitz r).dist_le_mul x 0
  simpa only [h0, dist_zero_right, NNReal.coe_one, one_mul] using h

private theorem cons_phase_dist_le (t : ℝ) (w p : P) :
    dist (Fin.cons t (w+p).1 : E) (Fin.cons t w.1) ≤ ‖p‖ := by
  rw [dist_eq_norm]
  refine (cons_sub_norm_le t (w+p).1 w.1).trans ?_
  change ‖w.1 + p.1 - w.1‖ ≤ ‖p‖
  rw [add_sub_cancel_left]
  exact le_max_left _ _

private theorem rightDeriv_of_Icc {a b t : ℝ} {g : ℝ → P} {v : P}
    (ht : t ∈ Ico a b) (h : HasDerivWithinAt g v (Icc a b) t) :
    HasDerivWithinAt g v (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  apply mem_of_superset
    (inter_mem (self_mem_nhdsWithin : Ici t ∈ 𝓝[Ici t] t)
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)))
  exact fun x hx => ⟨ht.1.trans hx.1, hx.2⟩

/-- A trajectory on a compact interval in the coordinate domain admits a
single positive radius for its position tube. -/
theorem exists_trajectory_tube {a b : ℝ} {w : ℝ → P}
    (hw : ContinuousOn w (Icc a b))
    (hpos : ∀ t ∈ Icc a b, (Fin.cons t (w t).1 : E) ∈ U) :
    ∃ r > (0 : ℝ), ∀ t ∈ Icc a b,
      closedBall (Fin.cons t (w t).1 : E) r ⊆ U := by
  let q : ℝ → E := fun t => Fin.cons t (w t).1
  have hq : ContinuousOn q (Icc a b) := by
    apply continuousOn_pi.mpr
    intro i
    refine Fin.cases continuous_id.continuousOn (fun j => ?_) i
    exact (continuous_apply j).comp_continuousOn hw.fst
  have hcompact := isCompact_Icc.image_of_continuousOn hq
  obtain ⟨r, hr, hsub⟩ := hcompact.exists_cthickening_subset_open U.isOpen
    (image_subset_iff.mpr hpos)
  exact ⟨r, hr, fun t ht => (closedBall_subset_cthickening (mem_image_of_mem q ht) r).trans hsub⟩

/-- A nearby relativistic solution exists on the full interval of the
Newtonian reference trajectory once the endpoint error budget fits in the tube. -/
theorem exists_relativistic_on_Icc {a b c r V δ : ℝ} (hab : a ≤ b)
    (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2) (hr : 0 < r) (hδ : 0 ≤ δ)
    (w : ℝ → P) (z₀ : P)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (f.newtonianPhaseField t (w t)) (Icc a b) t)
    (htube : ∀ t ∈ Icc a b, closedBall (Fin.cons t (w t).1 : E) r ⊆ U)
    (hspeed : ∀ t ∈ Icc a b, ‖(w t).2‖ + r ≤ V)
    (hinit : ‖z₀ - w a‖ ≤ δ)
    (hfit : gronwallBound δ (max 1 f.bound) (f.accelerationErrorConstant V / c^2) (b-a) < r) :
    ∃ z : ℝ → P, z a = z₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt z (f.relativisticPhaseField c t (z t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, (Fin.cons t (z t).1 : E) ∈ U ∧ ‖(z t).2‖ ≤ V ∧
        ‖z t - w t‖ ≤ gronwallBound δ (max 1 f.bound)
          (f.accelerationErrorConstant V / c^2) (t-a)) := by
  have hwc : ContinuousOn w (Icc a b) := HasDerivWithinAt.continuousOn hw
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hV : 0 ≤ V := by linarith [hspeed a ha, norm_nonneg (w a).2]
  have hK := f.bound_nonneg
  have hlarge' : 9 * f.bound < c^2 := by linarith
  let C := f.accelerationErrorConstant V / c^2
  let L := max 1 f.bound
  have hC : 0 ≤ C := div_nonneg (f.accelerationErrorConstant_nonneg hV) (sq_nonneg c)
  have hL : 0 ≤ L := zero_le_one.trans (le_max_left _ _)
  let p := fun t y => w t + clipPhase r y
  let F := fun t y => f.relativisticPhaseField c t (p t y) - f.newtonianPhaseField t (w t)
  have hball (t : ℝ) (y : P) :
      (Fin.cons t (p t y).1 : E) ∈ closedBall (Fin.cons t (w t).1 : E) r :=
    (cons_phase_dist_le t (w t) (clipPhase r y)).trans (clipPhase_norm_le hr.le y)
  have hq (t : ℝ) (ht : t ∈ Icc a b) (y : P) : (Fin.cons t (p t y).1 : E) ∈ U :=
    htube t ht (hball t y)
  have hv (t : ℝ) (ht : t ∈ Icc a b) (y : P) : ‖(p t y).2‖ ≤ V := by
    change ‖(w t).2 + (clipPhase r y).2‖ ≤ V
    exact (norm_add_le _ _).trans ((add_le_add_right
      ((le_max_right _ _ : ‖(clipPhase r y).2‖ ≤ ‖clipPhase r y‖).trans
        (clipPhase_norm_le hr.le y)) _).trans (hspeed t ht))
  have hseg (t : ℝ) (ht : t ∈ Icc a b) (y y' : P) :
      segment ℝ (Fin.cons t (p t y).1 : E) (Fin.cons t (p t y').1) ⊆ U :=
    ((convex_closedBall (Fin.cons t (w t).1 : E) r).segment_subset (hball t y) (hball t y')).trans
      (htube t ht)
  have hwball (t : ℝ) : (Fin.cons t (w t).1 : E) ∈ closedBall (Fin.cons t (w t).1 : E) r :=
    mem_closedBall_self hr.le
  have hF (t : ℝ) (ht : t ∈ Icc a b) (y : P) : ‖F t y‖ ≤ L * ‖clipPhase r y‖ + C := by
    let Z := f.relativisticPhaseField c t (p t y)
    let N := f.newtonianPhaseField t (p t y)
    let W := f.newtonianPhaseField t (w t)
    have he : ‖Z - N‖ ≤ C := by
      change max ‖(p t y).2 - (p t y).2‖
        ‖f.acceleration c (Fin.cons t (p t y).1) (p t y).2 -
          -f.spatialGradient (Fin.cons t (p t y).1)‖ ≤ C
      rw [sub_self, norm_zero, sub_neg_eq_add, max_eq_right (norm_nonneg _)]
      simpa only [C, epsilon, div_eq_mul_inv] using
        f.acceleration_error hc hlarge ⟨_, hq t ht y⟩ hV (hv t ht y)
    have hn := f.newtonianPhaseField_sub_le t (p t y) (w t)
      (((convex_closedBall (Fin.cons t (w t).1 : E) r).segment_subset
        (hwball t) (hball t y)).trans (htube t ht))
    have hp : p t y - w t = clipPhase r y := by unfold p; abel
    rw [hp] at hn
    change ‖Z - W‖ ≤ _
    exact (norm_sub_le_norm_sub_add_norm_sub Z N W).trans (by linarith)
  let K : ℝ≥0 := ⟨f.phaseLipschitzConstant V, zero_le_one.trans (le_max_left _ _)⟩
  have hLip (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (F t) := by
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    rw [dist_eq_norm, dist_eq_norm]
    unfold F
    rw [sub_sub_sub_cancel_right]
    have h := f.relativisticPhaseField_sub_le hc hlarge t (p t y) (p t y')
      (hv t ht y) (hv t ht y') (hseg t ht y' y)
    have hp : p t y - p t y' = clipPhase r y - clipPhase r y' := by unfold p; abel
    rw [hp] at h
    have hcLip := (clipPhase_lipschitz r).dist_le_mul y y'
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul] at hcLip
    exact h.trans (mul_le_mul_of_nonneg_left hcLip K.property)
  have hcont (y : P) : ContinuousOn (fun t => F t y) (Icc a b) := by
    have hp : ContinuousOn (fun t => p t y) (Icc a b) := hwc.add continuousOn_const
    have hcoord {z : ℝ → S} (hz : ContinuousOn z (Icc a b)) :
        ContinuousOn (fun t => (Fin.cons t (z t) : E)) (Icc a b) := by
      apply continuousOn_pi.mpr
      intro i
      refine Fin.cases continuous_id.continuousOn (fun j => ?_) i
      exact (continuous_apply j).comp_continuousOn hz
    apply ContinuousOn.sub
    · apply hp.snd.prodMk
      intro t ht
      let g : E × S → S := fun q => f.acceleration c q.1 q.2
      let j : ℝ → E × S := fun u => (Fin.cons u (p u y).1, (p u y).2)
      change ContinuousWithinAt (g ∘ j) (Icc a b) t
      have hg : ContinuousAt g (j t) :=
        (f.acceleration_contDiffAt hc hlarge' (hq t ht y)).continuousAt
      exact hg.comp_continuousWithinAt (((hcoord hp.fst).prodMk hp.snd) t ht)
    · apply hwc.snd.prodMk
      apply ContinuousOn.neg
      intro t ht
      have hpos := htube t ht (hwball t)
      have hD := ((f.potential_smooth.contDiffAt (U.isOpen.mem_nhds hpos)).fderiv_right
        (m := 1) (by simp)).continuousAt
      apply continuousWithinAt_pi.mpr
      intro i
      let j : ℝ → E := fun u => Fin.cons u (w u).1
      have hj : ContinuousWithinAt j (Icc a b) t := hcoord hwc.fst t ht
      have hD' : ContinuousAt (fderiv ℝ f.potential) (j t) := hD
      have hcomp : ContinuousWithinAt (fderiv ℝ f.potential ∘ j) (Icc a b) t :=
        hD'.comp_continuousWithinAt hj
      exact (continuous_eval_const (Pi.single i.succ 1)).continuousAt.comp_continuousWithinAt hcomp
  let M : ℝ≥0 := ⟨L*r + C, add_nonneg (mul_nonneg hL hr.le) hC⟩
  let rad : ℝ≥0 := M * ⟨b-a, sub_nonneg.mpr hab⟩
  let e₀ := z₀ - w a
  let a₀ : Icc a b := ⟨a, ha⟩
  have hPL : IsPicardLindelof F a₀ e₀ rad 0 M K := by
    refine ⟨fun t ht => (hLip t ht).lipschitzOnWith, fun y _ => hcont y, ?_, ?_⟩
    · intro t ht y _
      exact (hF t ht y).trans (add_le_add_left
        (mul_le_mul_of_nonneg_left (clipPhase_norm_le hr.le y) hL) C)
    · change (M : ℝ) * max (b-a) (a-a) ≤ (rad : ℝ) - 0
      simp [rad, sub_nonneg.mpr hab]
      rfl
  obtain ⟨e, hea, he'⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hbnd : ∀ t ∈ Icc a b, ‖e t‖ ≤ gronwallBound δ L C (t-a) := by
    refine norm_le_gronwallBound_of_norm_deriv_right_le
      (HasDerivWithinAt.continuousOn he') (fun t ht => rightDeriv_of_Icc ht
        (he' t ⟨ht.1, ht.2.le⟩)) ?_ ?_
    · change ‖e a‖ ≤ δ
      rw [show e a = e₀ from hea]
      exact hinit
    · intro t ht
      exact (hF t ⟨ht.1, ht.2.le⟩ (e t)).trans (add_le_add_left
        (mul_le_mul_of_nonneg_left (clipPhase_norm_le_self r hr.le (e t)) hL) C)
  have hclip (t : ℝ) (ht : t ∈ Icc a b) : clipPhase r (e t) = e t :=
    clipPhase_eq ((hbnd t ht).trans
      (((gronwallBound_mono hδ hC hL) (sub_le_sub_right ht.2 a)).trans hfit.le))
  let z := fun t => w t + e t
  refine ⟨z, ?_, ?_, ?_⟩
  · change w a + e a = z₀
    rw [show e a = e₀ from hea]
    dsimp [e₀]
    abel
  · intro t ht
    have h := (hw t ht).add (he' t ht)
    change HasDerivWithinAt z (f.newtonianPhaseField t (w t) + F t (e t)) (Icc a b) t at h
    unfold F p at h
    rw [hclip t ht] at h
    simpa only [add_sub_cancel] using h
  · intro t ht
    have hp' : p t (e t) = z t := by simp [p, z, hclip t ht]
    refine ⟨hp' ▸ hq t ht (e t), hp' ▸ hv t ht (e t), ?_⟩
    change ‖w t + e t - w t‖ ≤ _
    rw [add_sub_cancel_left]
    exact hbnd t ht

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
