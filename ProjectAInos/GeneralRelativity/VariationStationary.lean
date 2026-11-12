/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.VariationBoundary

/-! # Fixed-endpoint manifold families and stationary motion

Endpoint fixing is an actual local condition on the family, from which
zero endpoint variation fields are derived. The motion-to-stationarity
direction applies to arbitrary smooth Lorentz manifolds.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity
open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- Fixed endpoints eliminate the quadratic boundary term on any manifold. -/
theorem quadraticAction_family_fixedEndpoint (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b)) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, -g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
        (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t)) ε₀ := by
  have hleft := familyVelocity_fst_eq_zero_of_eventually_const
    ((hΓ a left_mem_uIcc).mdifferentiableAt (by norm_num)) ha
  have hright := familyVelocity_fst_eq_zero_of_eventually_const
    ((hΓ b right_mem_uIcc).mdifferentiableAt (by norm_num)) hb
  simpa only [hleft, hright, map_zero, zero_apply, sub_zero, zero_add] using
    quadraticAction_family_firstVariation g hΓ

/-- Fixed endpoints eliminate the massive boundary term, leaving the full
non-affine acceleration residual. -/
theorem freeAction_family_fixedEndpoint (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b)) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, -(m / speedAlong g (fun s => Γ (ε₀, s)) t) *
        g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
          (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t -
            (deriv (speedAlong g (fun s => Γ (ε₀, s))) t /
              speedAlong g (fun s => Γ (ε₀, s)) t) •
              curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ := by
  have hleft := familyVelocity_fst_eq_zero_of_eventually_const
    ((hΓ a left_mem_uIcc).mdifferentiableAt (by norm_num)) ha
  have hright := familyVelocity_fst_eq_zero_of_eventually_const
    ((hΓ b right_mem_uIcc).mdifferentiableAt (by norm_num)) hb
  simpa only [hleft, hright, map_zero, zero_apply, mul_zero, sub_zero, zero_add]
    using freeAction_family_firstVariation g m hΓ hv

/-- Every affine geodesic is stationary under arbitrary fixed-endpoint
manifold families. Null reference curves require no constraint on variations. -/
theorem quadraticAction_family_stationary_of_geodesic (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ} (hab : a ≤ b)
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b))
    (hg : g.IsGeodesicOn (Ioo a b) (fun s => Γ (ε₀, s))) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b) 0 ε₀ := by
  apply (quadraticAction_family_fixedEndpoint g hΓ ha hb).congr_deriv
  calc
    _ = ∫ _t in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      simp only [(hg t ht).2, map_zero, neg_zero]
    _ = 0 := by simp

/-- Tangential timelike acceleration gives massive stationarity for every
fixed-endpoint manifold family; the speed factor is determined geometrically. -/
theorem freeAction_family_stationary_of_tangential (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ} (hab : a ≤ b)
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t))
    (ha : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, a) = Γ (ε₀, a))
    (hb : ∀ᶠ ε in 𝓝 ε₀, Γ (ε, b) = Γ (ε₀, b))
    (hacc : ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t =
        k • curveVelocity (fun s => Γ (ε₀, s)) t) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b) 0 ε₀ := by
  apply (freeAction_family_fixedEndpoint g m hΓ hv ha hb).congr_deriv
  calc
    _ = ∫ _t in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      have ht' : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨ht.1.le, ht.2.le⟩
      obtain ⟨k, hk⟩ := hacc t ht
      have he := acceleration_factor_eq g (familySlice_contMDiffAt (hΓ t ht')) (hv t ht') hk
      simp only [hk, he, sub_self, map_zero, mul_zero]
    _ = 0 := by simp

end ProjectAInos.GeneralRelativity
