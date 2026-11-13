/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.VariationStationary
public import ProjectAInos.SmoothGeometry.Lorentzian.VariationTesting
public import ProjectAInos.SmoothGeometry.Lorentzian.AccelerationRegularity

/-! # Stationarity under all fixed-endpoint manifold variations

The admissible variations are actual C² families through a native curve.
The quadratic action admits null reference curves and unrestricted test families.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity
open SmoothGeometry LorentzMetric Variational

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Stationarity of the quadratic action under every actual admissible family. -/
def QuadraticStationary (g : LorentzMetric .timeNegative d M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ V : ManifoldCurveVariation («E» := E) γ a b,
    HasDerivAt (fun ε => quadraticAction g (fun t => V.family (ε, t)) a b) 0 0

/-- Stationarity of the massive action under every actual admissible family.
Timelike character is imposed on the reference curve in the equivalence theorem. -/
def FreeStationary (g : LorentzMetric .timeNegative d M) (m : ℝ)
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ V : ManifoldCurveVariation («E» := E) γ a b,
    HasDerivAt (fun ε => freeAction g m (fun t => V.family (ε, t)) a b) 0 0

/-- First variation with its residual expressed along the specified reference curve. -/
theorem quadraticAction_variation_hasDerivAt (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (V : ManifoldCurveVariation («E» := E) γ a b) :
    HasDerivAt (fun ε => quadraticAction g (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, -g.form (γ t) (variationField V t)
        (g.covariantAlong (curveVelocity γ) t)) 0 := by
  have href : (fun t => V.family (0, t)) = γ := funext V.reference
  have h := quadraticAction_family_fixedEndpoint g V.regular
    (V.left_fixed.mono fun ε hε => hε.trans (V.reference a).symm)
    (V.right_fixed.mono fun ε hε => hε.trans (V.reference b).symm)
  apply h.congr_deriv
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  unfold variationField
  rw [href, V.reference t]
  rfl

/-- The massive first variation uses the speed-weighted non-affine acceleration. -/
theorem freeAction_variation_hasDerivAt (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {γ : ℝ → M} {a b : ℝ} (V : ManifoldCurveVariation («E» := E) γ a b)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    HasDerivAt (fun ε => freeAction g m (fun t => V.family (ε, t)) a b)
      (∫ t in a..b, -(m / speedAlong g γ t) * g.form (γ t) (variationField V t)
        (g.covariantAlong (curveVelocity γ) t -
          (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t)) 0 := by
  have href : (fun t => V.family (0, t)) = γ := funext V.reference
  have h := freeAction_family_fixedEndpoint g m V.regular (by
    intro t ht
    unfold Timelike
    rw [href, V.reference t]
    exact hv t ht)
    (V.left_fixed.mono fun ε hε => hε.trans (V.reference a).symm)
    (V.right_fixed.mono fun ε hε => hε.trans (V.reference b).symm)
  apply h.congr_deriv
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  unfold variationField
  rw [href, V.reference t]
  rfl

/-- On every smooth Lorentz manifold, quadratic stationarity is equivalent
to the affine geodesic equation in the interval interior. -/
theorem quadraticStationary_iff_geodesic (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    QuadraticStationary g γ a b ↔ g.IsGeodesicOn (Ioo a b) γ := by
  have hinc : Ioo a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self
  constructor
  · intro hs
    have hz := g.eq_zero_of_variation_pairing hab hγ
      (g.covariantAlong (curveVelocity γ)) (fun e he w t ht hx => ?_)
      (fun V => ?_)
    · exact fun t ht => ⟨hγ t (hinc ht), hz t ht⟩
    · exact (g.contDiffAt_pairing_along ((hγ t (hinc ht)).of_le (by norm_num))
        (((chartField_contMDiffAt he hx w).of_le (by simp)).comp t
          ((hγ t (hinc ht)).of_le (by norm_num)))
        (g.covariantAcceleration_contMDiffAt (hγ t (hinc ht)))).continuousAt
    · have h := (quadraticAction_variation_hasDerivAt g V).unique (hs V)
      rw [intervalIntegral.integral_neg, neg_eq_zero] at h
      exact h
  · intro hg V
    apply (quadraticAction_variation_hasDerivAt g V).congr_deriv
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab.le
        intro t ht
        simp only [(hg t ht).2, map_zero, neg_zero]
      _ = 0 := by simp

/-- Positive-mass timelike stationarity is equivalent to the non-affine
geodesic equation, including the derivative of the proper-speed rate. -/
theorem freeStationary_iff_acceleration (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    FreeStationary g m γ a b ↔ ∀ t ∈ Ioo a b,
      g.covariantAlong (curveVelocity γ) t =
        (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t := by
  have hinc : Ioo a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self
  have hspeed (t : ℝ) (ht : t ∈ uIcc a b) : 0 < speedAlong g γ t :=
    (properSpeed_pos_iff g _).mpr (hv t ht)
  constructor
  · intro hs
    let R : AlongField (d := d) γ := fun t => -(m / speedAlong g γ t) •
      (g.covariantAlong (curveVelocity γ) t -
        (deriv (speedAlong g γ) t / speedAlong g γ t) • curveVelocity γ t)
    have hz := g.eq_zero_of_variation_pairing hab hγ R (fun e he w t ht hx => ?_)
      (fun V => ?_)
    · intro t ht
      have hn : -(m / speedAlong g γ t) ≠ 0 := neg_ne_zero.mpr
        (div_ne_zero hm.ne' (hspeed t (hinc ht)).ne')
      exact sub_eq_zero.mp ((smul_eq_zero.mp (hz t ht)).resolve_left hn)
    · have hcurve : ContMDiffAt 𝓘(ℝ) I 0 γ t := (hγ t (hinc ht)).of_le (by norm_num)
      have hfield : ContMDiffAt 𝓘(ℝ) ((I).prod I) 0
          (fun s => TotalSpace.mk' E (γ s) (chartField e w (γ s))) t :=
        ((chartField_contMDiffAt he hx w).of_le (by simp)).comp t hcurve
      have hA := (g.contDiffAt_pairing_along hcurve hfield
        (g.covariantAcceleration_contMDiffAt (hγ t (hinc ht)))).continuousAt
      have hT := (g.contDiffAt_pairing_along hcurve hfield
        ((curveVelocity_contMDiffAt (n := 1) (hγ t (hinc ht))).of_le
          (by norm_num))).continuousAt
      have hc := contDiffAt_speedAlong g (hγ t (hinc ht)) (hv t (hinc ht))
      have hd : ContinuousAt (deriv (speedAlong g γ)) t :=
        (hc.derivWithin (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).continuousAt
      have hcont := ((continuousAt_const (y := m)).div hc.continuousAt (hspeed t (hinc ht)).ne').neg.mul
        (hA.sub ((hd.div hc.continuousAt (hspeed t (hinc ht)).ne').mul hT))
      simpa only [R, map_smul, map_sub, smul_eq_mul] using! hcont
    · have h := (freeAction_variation_hasDerivAt g m V hv).unique (hs V)
      simpa only [R, map_smul, smul_eq_mul] using h
  · intro ha V
    apply (freeAction_variation_hasDerivAt g m V hv).congr_deriv
    calc
      _ = ∫ _t in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hab.le
        intro t ht
        simp only [ha t ht, sub_self, map_zero, mul_zero]
      _ = 0 := by simp

/-- The proper-speed factor is forced by the metric, so the massive
stationarity condition is equivalently tangential acceleration. -/
theorem freeStationary_iff_tangential (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    FreeStationary g m γ a b ↔ ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t := by
  rw [freeStationary_iff_acceleration g hm hab hγ hv]
  constructor
  · intro h t ht
    exact ⟨_, h t ht⟩
  · intro h t ht
    have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact ⟨ht.1.le, ht.2.le⟩
    obtain ⟨k, hk⟩ := h t ht
    rw [acceleration_factor_eq g (hγ t ht') (hv t ht') hk]
    exact hk

end ProjectAInos.GeneralRelativity
