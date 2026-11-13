/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianExistence
public import Mathlib.Topology.Algebra.Order.Field

/-! # Quantitative finite-time Newtonian limits -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Metric Filter TopologicalSpace
open scoped Topology

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily

local notation "E" => NewtonianCoordinates
local notation "S" => NewtonianSpace
local notation "P" => (S × S)
variable {U : Opens E} (f : NewtonianMetricFamily U)

/-- The coefficient of the forcing term in Gronwall's bound. -/
def gronwallForcingFactor (L T : ℝ) : ℝ :=
  if L = 0 then T else (Real.exp (L*T) - 1) / L

/-- The two contributions to Gronwall's bound, including the zero-Lipschitz case. -/
theorem gronwallBound_split (δ L η T : ℝ) :
    gronwallBound δ L η T =
      δ * Real.exp (L*T) + η * gronwallForcingFactor L T := by
  by_cases h : L = 0
  · simp [h, gronwallBound_K0, gronwallForcingFactor]
  · rw [gronwallBound_of_K_ne_0 h, gronwallForcingFactor, ite_eq_right h]
    ring

theorem gronwallForcingFactor_nonneg {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    0 ≤ gronwallForcingFactor L T := by
  unfold gronwallForcingFactor
  split
  · exact hT
  · apply div_nonneg _ hL
    rw [sub_nonneg, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hL hT)

private theorem tendsto_epsilon : Tendsto epsilon atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))

/-- For fixed Lipschitz constant and time span, vanishing initial and forcing
errors make the endpoint Gronwall bound vanish. -/
theorem tendsto_gronwallBound_atTop {δ : ℝ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (L C T : ℝ) :
    Tendsto (fun c => gronwallBound (δ c) L (C/c^2) T) atTop (𝓝 0) := by
  have he : Tendsto (fun c : ℝ => C / c^2) atTop (𝓝 0) := by
    simpa only [epsilon, div_eq_mul_inv, mul_zero] using tendsto_epsilon.const_mul C
  simpa only [gronwallBound_split, zero_mul, add_zero] using
    (hδ.mul_const (Real.exp (L*T))).add (he.mul_const (gronwallForcingFactor L T))

/-- For a common interval, a Gronwall estimate with a vanishing initial error
and inverse-square forcing implies uniform convergence. -/
theorem tendstoUniformlyOn_of_phase_error {a b L C : ℝ} {δ : ℝ → ℝ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hδ : Tendsto δ atTop (𝓝 0))
    (hδ₀ : ∀ᶠ c in atTop, 0 ≤ δ c) {z : ℝ → ℝ → P} {w : ℝ → P}
    (herr : ∀ᶠ c : ℝ in atTop, ∀ t ∈ Icc a b,
      ‖z c t - w t‖ ≤ gronwallBound (δ c) L (C / c^2) (t-a)) :
    TendstoUniformlyOn z w atTop (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have h := (tendsto_gronwallBound_atTop hδ L C (b-a)).eventually (Iio_mem_nhds hη)
  filter_upwards [herr, hδ₀, h] with c hc hc₀ hb t ht
  rw [dist_comm, dist_eq_norm]
  exact (hc t ht).trans_lt (((gronwallBound_mono hc₀
    (div_nonneg hC (sq_nonneg c)) hL) (sub_le_sub_right ht.2 a)).trans_lt hb)

/-- An inverse-square initial phase error propagates at the same rate on a
fixed finite interval. The coefficient formula is valid at `L = 0`. -/
theorem phase_error_rate_of_gronwall {a b L C D : ℝ}
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hD : 0 ≤ D) {c : ℝ} {z w : ℝ → P}
    (herr : ∀ t ∈ Icc a b,
      ‖z t - w t‖ ≤ gronwallBound (D/c^2) L (C/c^2) (t-a)) :
    ∀ t ∈ Icc a b,
      ‖z t - w t‖ ≤
        (D * Real.exp (L*(b-a)) + C * gronwallForcingFactor L (b-a)) / c^2 := by
  intro t ht
  have h := (herr t ht).trans
    ((gronwallBound_mono (div_nonneg hD (sq_nonneg c))
      (div_nonneg hC (sq_nonneg c)) hL) (sub_le_sub_right ht.2 a))
  rw [gronwallBound_split] at h
  refine h.trans_eq ?_
  ring

/-- For a Newtonian trajectory on a fixed finite interval and converging
initial phase points, choose relativistic solutions on that same interval
for all sufficiently large `c`. The chosen phase trajectories converge
uniformly and retain a quantitative Gronwall estimate on the interval. -/
theorem exists_uniform_newtonian_limit {a b : ℝ} (hab : a ≤ b) (w : ℝ → P)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (f.newtonianPhaseField t (w t)) (Icc a b) t)
    (hpos : ∀ t ∈ Icc a b, (Fin.cons t (w t).1 : E) ∈ U)
    (z₀ : ℝ → P) (hinit : Tendsto z₀ atTop (𝓝 (w a))) :
    ∃ (V : ℝ) (z : ℝ → ℝ → P), 0 ≤ V ∧ TendstoUniformlyOn z w atTop (Icc a b) ∧
      ∀ᶠ c : ℝ in atTop, z c a = z₀ c ∧
        (∀ t ∈ Icc a b,
          HasDerivWithinAt (z c) (f.relativisticPhaseField c t (z c t)) (Icc a b) t) ∧
        (∀ t ∈ Icc a b, (Fin.cons t (z c t).1 : E) ∈ U ∧ ‖(z c t).2‖ ≤ V ∧
          ‖z c t - w t‖ ≤ gronwallBound ‖z₀ c - w a‖ (max 1 f.bound)
            (f.accelerationErrorConstant V / c^2) (t-a)) := by
  have hwc := HasDerivWithinAt.continuousOn hw
  obtain ⟨r, hr, htube⟩ := exists_trajectory_tube hwc hpos
  obtain ⟨W, hW, hspeed⟩ :=
    (isCompact_Icc.image_of_continuousOn hwc.snd).isBounded.exists_pos_norm_le
  let V := W + r
  have hV : 0 ≤ V := by dsimp [V]; linarith
  let δ := fun c : ℝ => ‖z₀ c - w a‖
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, sub_self, norm_zero] using (hinit.sub (tendsto_const_nhds (x := w a))).norm
  have htail : ∀ᶠ c : ℝ in atTop, 24 * f.bound + 2 ≤ c := eventually_ge_atTop _
  have hfit := (tendsto_gronwallBound_atTop hδ (max 1 f.bound)
    (f.accelerationErrorConstant V) (b-a)).eventually (Iio_mem_nhds hr)
  have hsol : ∀ᶠ c : ℝ in atTop, ∃ z : ℝ → P, z a = z₀ c ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt z (f.relativisticPhaseField c t (z t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, (Fin.cons t (z t).1 : E) ∈ U ∧ ‖(z t).2‖ ≤ V ∧
        ‖z t - w t‖ ≤ gronwallBound (δ c) (max 1 f.bound)
          (f.accelerationErrorConstant V / c^2) (t-a)) := by
    filter_upwards [htail, hfit] with c hc hf
    have hK := f.bound_nonneg
    have hc₁ : 1 ≤ c := by linarith
    have hc₂ : 24 * f.bound < c^2 := by nlinarith [sq_nonneg (c-1)]
    exact f.exists_relativistic_on_Icc hab hc₁ hc₂ hr (norm_nonneg _) w (z₀ c) hw htube
      (fun t ht => add_le_add_left (hspeed _ (mem_image_of_mem _ ht)) r) le_rfl hf
  classical
  let z (c : ℝ) : ℝ → P := if h : ∃ z : ℝ → P, z a = z₀ c ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt z (f.relativisticPhaseField c t (z t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, (Fin.cons t (z t).1 : E) ∈ U ∧ ‖(z t).2‖ ≤ V ∧
        ‖z t - w t‖ ≤ gronwallBound (δ c) (max 1 f.bound)
          (f.accelerationErrorConstant V / c^2) (t-a))
    then Classical.choose h else w
  have hz : ∀ᶠ c : ℝ in atTop, z c a = z₀ c ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt (z c) (f.relativisticPhaseField c t (z c t)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, (Fin.cons t (z c t).1 : E) ∈ U ∧ ‖(z c t).2‖ ≤ V ∧
        ‖z c t - w t‖ ≤ gronwallBound (δ c) (max 1 f.bound)
          (f.accelerationErrorConstant V / c^2) (t-a)) := by
    filter_upwards [hsol] with c hc
    simpa only [z, dite_eq_left hc] using Classical.choose_spec hc
  refine ⟨V, z, hV, ?_, hz⟩
  exact tendstoUniformlyOn_of_phase_error (zero_le_one.trans (le_max_left _ _))
    (f.accelerationErrorConstant_nonneg hV) hδ (Eventually.of_forall fun _ => norm_nonneg _)
    (hz.mono fun _ h t ht => (h.2.2 t ht).2.2)

/-- Inverse-square initial errors give inverse-square phase convergence
on the common finite interval. -/
theorem exists_newtonian_limit_with_rate {a b : ℝ} (hab : a ≤ b) (w : ℝ → P)
    (hw : ∀ t ∈ Icc a b, HasDerivWithinAt w (f.newtonianPhaseField t (w t)) (Icc a b) t)
    (hpos : ∀ t ∈ Icc a b, (Fin.cons t (w t).1 : E) ∈ U)
    (z₀ : ℝ → P) {D : ℝ} (hD : 0 ≤ D)
    (hinit : ∀ᶠ c : ℝ in atTop, ‖z₀ c - w a‖ ≤ D/c^2) :
    ∃ C ≥ (0 : ℝ), ∃ z : ℝ → ℝ → P, TendstoUniformlyOn z w atTop (Icc a b) ∧
      ∀ᶠ c : ℝ in atTop, z c a = z₀ c ∧
        (∀ t ∈ Icc a b,
          HasDerivWithinAt (z c) (f.relativisticPhaseField c t (z c t)) (Icc a b) t) ∧
        (∀ t ∈ Icc a b, (Fin.cons t (z c t).1 : E) ∈ U ∧ ‖z c t - w t‖ ≤ C/c^2) := by
  have hzero : Tendsto (fun c : ℝ => D/c^2) atTop (𝓝 0) := by
    simpa only [epsilon, div_eq_mul_inv, mul_zero] using tendsto_epsilon.const_mul D
  have hT : Tendsto z₀ atTop (𝓝 (w a)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero
        (Eventually.of_forall fun _ => norm_nonneg _) hinit)
  obtain ⟨V,z,hV,hconv,hsol⟩ := f.exists_uniform_newtonian_limit hab w hw hpos z₀ hT
  let L := max 1 f.bound
  let B := f.accelerationErrorConstant V
  have hL : 0 ≤ L := zero_le_one.trans (le_max_left _ _)
  have hB : 0 ≤ B := f.accelerationErrorConstant_nonneg hV
  let C := D * Real.exp (L*(b-a)) + B * gronwallForcingFactor L (b-a)
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hD (Real.exp_nonneg _))
    (mul_nonneg hB (gronwallForcingFactor_nonneg hL (sub_nonneg.mpr hab)))
  refine ⟨C,hC,z,hconv,?_⟩
  filter_upwards [hinit,hsol] with c hc hz
  refine ⟨hz.1,hz.2.1,?_⟩
  intro t ht
  refine ⟨(hz.2.2 t ht).1,?_⟩
  apply phase_error_rate_of_gronwall hL hB hD _ t ht
  intro s hs
  apply (hz.2.2 s hs).2.2.trans
  rw [gronwallBound_split, gronwallBound_split]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)) _

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
