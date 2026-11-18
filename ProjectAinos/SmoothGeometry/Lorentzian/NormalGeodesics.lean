/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Geodesic
public import ProjectAinos.SmoothGeometry.Lorentzian.CurveFamily

/-!
# Families of geodesics normal to a slice

Landau–Lifshitz, §97. For a two-parameter family `Γ(s, t)` whose curves `t ↦ Γ(s, t)` are
geodesics with the same metric norm `c` of their velocity, the pairing of the velocity with
the variation field is constant along each curve (`familyVelocity_pairing_eq`): its derivative
is `g(γ̇, D_t V) = g(γ̇, D_s γ̇) = ½ ∂_s g(γ̇, γ̇) = 0` by the interchange of the covariant
derivatives of a family. So a variation field orthogonal to the velocity at `t = 0` stays
orthogonal (`familyVelocity_orthogonal`): this is the lemma of Gauss behind the synchronous
reference system, whose time lines are geodesics normal to a slice.
-/

@[expose] public section

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- **The velocity of a family of geodesics has a constant pairing with the variation field**:
if the curves `t ↦ Γ(s, t)` are geodesics on `[0, τ]` with the same metric norm `c` of their
velocity for all `s` in an open interval, the pairing `g(γ̇, ∂_s Γ)` is constant in `t`. -/
theorem familyVelocity_pairing_eq (g : LorentzMetric σ d M) {Γ : ℝ × ℝ → M}
    {s₁ s₂ s₀ τ c : ℝ} (hs₀ : s₀ ∈ Ioo s₁ s₂) (hτ : 0 ≤ τ)
    (hreg : ∀ s ∈ Ioo s₁ s₂, ∀ t ∈ Icc 0 τ, ContMDiffAt J I 2 Γ (s, t))
    (hgeo : ∀ s ∈ Ioo s₁ s₂, g.IsGeodesicOn (Icc 0 τ) (fun t => Γ (s, t)))
    (hnorm : ∀ s ∈ Ioo s₁ s₂, g.form (Γ (s, 0)) (curveVelocity (fun t => Γ (s, t)) 0)
      (curveVelocity (fun t => Γ (s, t)) 0) = c) :
    ∀ t ∈ Icc 0 τ, g.form (Γ (s₀, t)) (curveVelocity (fun t => Γ (s₀, t)) t)
        (familyVelocity Γ (1, 0) (s₀, t)) =
      g.form (Γ (s₀, 0)) (curveVelocity (fun t => Γ (s₀, t)) 0)
        (familyVelocity Γ (1, 0) (s₀, 0)) := by
  have hderiv : ∀ t ∈ Icc 0 τ, HasDerivAt (fun t => g.form (Γ (s₀, t))
      (curveVelocity (fun t => Γ (s₀, t)) t) (familyVelocity Γ (1, 0) (s₀, t))) 0 t := by
    intro t ht
    have hΓ := hreg s₀ hs₀ t ht
    have hslice := familySlice_contMDiffAt hΓ
    have h := g.hasDerivAt_pairing_along (hslice.mdifferentiableAt (by norm_num))
      ((curveVelocity_contMDiffAt (n := 1) hslice).mdifferentiableAt (by norm_num))
      ((familyVariation_contMDiffAt hΓ).mdifferentiableAt (by norm_num))
    refine h.congr_deriv ?_
    rw [(hgeo s₀ hs₀ t ht).2, map_zero, zero_apply, zero_add,
      ← covariantAlong_family_interchange g hΓ]
    -- the second term is `½ ∂_s g(γ̇, γ̇)` along `s ↦ Γ(s, t)`, and `g(γ̇, γ̇) = c` near `s₀`
    have hW (s : ℝ) (hs : s ∈ Ioo s₁ s₂) :
        curveVelocity (fun t' => Γ (s, t')) t = familyVelocity Γ (0, 1) (s, t) :=
      curveVelocity_family_snd ((hreg s hs t ht).mdifferentiableAt (by norm_num))
    have hβ : ContMDiffAt 𝓘(ℝ) I 2 (fun s => Γ (s, t)) s₀ :=
      hΓ.comp s₀ ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
    have hV : ContMDiffAt 𝓘(ℝ) ((I).prod I) 1
        (fun s => TotalSpace.mk' E (Γ (s, t)) (familyVelocity Γ (0, 1) (s, t))) s₀ :=
      (familyVelocity_contMDiffAt (0, 1) hΓ).comp s₀
        ((contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt)
    have hp := g.hasDerivAt_pairing_along (hβ.mdifferentiableAt (by norm_num))
      (hV.mdifferentiableAt (by norm_num)) (hV.mdifferentiableAt (by norm_num))
    have hconst : (fun s => g.form (Γ (s, t)) (familyVelocity Γ (0, 1) (s, t))
        (familyVelocity Γ (0, 1) (s, t))) =ᶠ[𝓝 s₀] fun _ => c := by
      filter_upwards [isOpen_Ioo.mem_nhds hs₀] with s hs
      rw [← hW s hs, ← hnorm s hs]
      exact (hgeo s hs).metric_velocity_eq (convex_Icc 0 τ) ht (left_mem_Icc.mpr hτ)
    have hzero := hp.unique ((hasDerivAt_const s₀ c).congr_of_eventuallyEq hconst)
    rw [g.symmetric (Γ (s₀, t)) (g.covariantAlong _ s₀)] at hzero
    rw [hW s₀ hs₀]
    linarith
  have hcont : ContinuousOn (fun t => g.form (Γ (s₀, t))
      (curveVelocity (fun t => Γ (s₀, t)) t) (familyVelocity Γ (1, 0) (s₀, t))) (Icc 0 τ) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  exact fun t ht => constant_of_has_deriv_right_zero hcont
    (fun t ht' => (hderiv t (Ico_subset_Icc_self ht')).hasDerivWithinAt) t ht

/-- **Lemma of Gauss for normal geodesics**: a variation field of a family of geodesics with
the same metric norm of their velocity that is orthogonal to the velocity at `t = 0` stays
orthogonal to it. -/
theorem familyVelocity_orthogonal (g : LorentzMetric σ d M) {Γ : ℝ × ℝ → M}
    {s₁ s₂ s₀ τ c : ℝ} (hs₀ : s₀ ∈ Ioo s₁ s₂) (hτ : 0 ≤ τ)
    (hreg : ∀ s ∈ Ioo s₁ s₂, ∀ t ∈ Icc 0 τ, ContMDiffAt J I 2 Γ (s, t))
    (hgeo : ∀ s ∈ Ioo s₁ s₂, g.IsGeodesicOn (Icc 0 τ) (fun t => Γ (s, t)))
    (hnorm : ∀ s ∈ Ioo s₁ s₂, g.form (Γ (s, 0)) (curveVelocity (fun t => Γ (s, t)) 0)
      (curveVelocity (fun t => Γ (s, t)) 0) = c)
    (horth : g.form (Γ (s₀, 0)) (curveVelocity (fun t => Γ (s₀, t)) 0)
      (familyVelocity Γ (1, 0) (s₀, 0)) = 0) :
    ∀ t ∈ Icc 0 τ, g.form (Γ (s₀, t)) (curveVelocity (fun t => Γ (s₀, t)) t)
      (familyVelocity Γ (1, 0) (s₀, t)) = 0 := fun t ht => by
  rw [familyVelocity_pairing_eq g hs₀ hτ hreg hgeo hnorm t ht, horth]

end ProjectAinos.SmoothGeometry.LorentzMetric
