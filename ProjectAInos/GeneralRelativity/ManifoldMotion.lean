/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ManifoldStationary
public import ProjectAInos.GeneralRelativity.FiniteProperTime
public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelUniqueness

/-! # Reparametrized and null stationary motion on Lorentz manifolds -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity
open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Unit proper speed makes massive stationarity equivalent to affine motion. -/
theorem freeStationary_iff_geodesic_of_unitSpeed (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hunit : ∀ t ∈ uIcc a b, speedAlong g γ t = 1) :
    FreeStationary g m γ a b ↔ g.IsGeodesicOn (Ioo a b) γ := by
  have hinc : Ioo a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self
  have hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t) := by
    intro t ht
    apply (properSpeed_pos_iff g _).mp
    change 0 < speedAlong g γ t
    rw [hunit t ht]
    norm_num
  rw [freeStationary_iff_acceleration g hm hab hγ hv]
  have hd : ∀ t ∈ Ioo a b, deriv (speedAlong g γ) t = 0 := by
    intro t ht
    have he : speedAlong g γ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hunit s (hinc hs)
    rw [he.deriv_eq, deriv_const]
  constructor
  · intro h t ht
    exact ⟨hγ t (hinc ht), by simpa only [hd t ht, zero_div, zero_smul] using h t ht⟩
  · intro h t ht
    simpa only [hd t ht, zero_div, zero_smul] using (h t ht).2

/-- Massive stationarity is equivalent to an actual regular local C²
reparametrization to affine geodesic motion. -/
theorem freeStationary_iff_localGeodesic (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t)) :
    FreeStationary g m γ a b ↔
      ∀ t₀ ∈ Ioo a b, ∃ e : OpenPartialHomeomorph ℝ ℝ,
        t₀ ∈ e.source ∧ e.source ⊆ Ioo a b ∧
        (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧ 0 < deriv e.symm τ) ∧
        g.IsGeodesicOn e.target (γ ∘ e.symm) := by
  have hinc : Ioo a b ⊆ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self
  rw [freeStationary_iff_tangential g hm hab hγ hv]
  constructor
  · intro ha t₀ ht₀
    obtain ⟨e, _, he₀, hsub, _, hi, hg⟩ := exists_properTime_geodesic_parameter g
      (fun s hs => hγ s (hinc hs)) (fun s hs => hv s (hinc hs)) ha ht₀
    refine ⟨e, he₀, hsub, ?_, hg⟩
    intro τ hτ
    refine ⟨(hi τ hτ).1, ?_⟩
    rw [(hi τ hτ).2.1.deriv]
    exact inv_pos.mpr ((properSpeed_pos_iff g _).mpr (hv _ (hinc (hsub (e.map_target hτ)))))
  · intro h t ht
    obtain ⟨e, he, hsub, hi, hg⟩ := h t ht
    have hτ := e.map_source he
    have ha := tangential_acceleration_of_reparam g
      (hγ _ (hinc (hsub (e.map_target hτ))))
      (hi _ hτ).1 (hi _ hτ).2.ne' (hg _ hτ).2
    have heq : e.symm (e t) = t := e.left_inv he
    exact heq ▸ ha

/-- A stationary massive worldline admits one proper-time inverse over
the entire finite segment, with endpoints and affine motion proved. -/
theorem freeStationary_finite_properTime (g : LorentzMetric .timeNegative d M)
    {m : ℝ} (hm : 0 < m) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity γ t))
    (hs : FreeStationary g m γ a b) :
    ∃ r : ℝ → ℝ,
      r 0 = a ∧ r (properTime g γ a b) = b ∧
      MapsTo r (Icc 0 (properTime g γ a b)) (Icc a b) ∧
      (∀ τ ∈ Icc 0 (properTime g γ a b),
        ContDiffAt ℝ 2 r τ ∧ HasDerivAt r (speedAlong g γ (r τ))⁻¹ τ ∧
        properTime g γ a (r τ) = τ ∧ speedAlong g (γ ∘ r) τ = 1) ∧
      g.IsGeodesicOn (Ioo 0 (properTime g γ a b)) (γ ∘ r) := by
  have ha := (freeStationary_iff_tangential g hm hab hγ hv).mp hs
  obtain ⟨e, he, hsource, himage, hinvimage, hleft, hright, hi, hg⟩ :=
    exists_finite_properTime_geodesic g hab.le
      (by simpa only [uIcc_of_le hab.le] using hγ)
      (by simpa only [uIcc_of_le hab.le] using hv) ha
  have htarget : Icc 0 (properTime g γ a b) ⊆ e.target := by
    rw [← himage]
    rintro _ ⟨t, ht, rfl⟩
    exact e.map_source (hsource ht)
  refine ⟨e.symm, hleft, hright, ?_, ?_, hg⟩
  · intro τ hτ
    rw [← hinvimage]
    exact ⟨τ, hτ, rfl⟩
  · intro τ hτ
    refine ⟨(hi τ (htarget hτ)).1, (hi τ (htarget hτ)).2.1, ?_, (hi τ (htarget hτ)).2.2⟩
    rw [← he]
    exact e.right_inv (htarget hτ)

/-- Stationarity also forces the affine equation at both finite endpoints
when the reference curve has the stated local C² extensions. -/
theorem QuadraticStationary.geodesic_closed {g : LorentzMetric .timeNegative d M}
    {γ : ℝ → M} {a b : ℝ} (hs : QuadraticStationary g γ a b) (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.IsGeodesicOn (Icc a b) γ := by
  have hg := (quadraticStationary_iff_geodesic g hab hγ).mp hs
  have hcl := hg.closure (by simpa only [closure_Ioo hab.ne, uIcc_of_le hab.le] using hγ)
  simpa only [closure_Ioo hab.ne] using hcl

/-- Nonzero null initial velocity stays nonzero and null on the whole
closed stationary segment. No variation is constrained to be null. -/
theorem QuadraticStationary.null_initial {g : LorentzMetric .timeNegative d M}
    {γ : ℝ → M} {a b : ℝ} (hs : QuadraticStationary g γ a b) (hab : a < b)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hnull : curveVelocity (d := d) γ a ≠ 0 ∧
      g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) = 0) :
    ∀ t ∈ Icc a b, curveVelocity (d := d) γ t ≠ 0 ∧
      g.form (γ t) (curveVelocity γ t) (curveVelocity γ t) = 0 := by
  intro t ht
  exact ((hs.geodesic_closed hab hγ).null_iff (convex_Icc a b)
    (left_mem_Icc.mpr hab.le) ht).mp hnull

end ProjectAInos.GeneralRelativity
