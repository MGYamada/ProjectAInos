/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ProperTimeParameter
public import ProjectAInos.Variational.Parameter

/-! # A single proper-time parameter over a finite timelike segment

Local C² regularity and timelikeness near the closed segment yield a
regular clock on a larger open interval. Positivity gives one inverse
covering the entire segment, including both endpoints.
-/

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

/-- Timelikeness and C² regularity on a closed finite segment extend to a
slightly larger open parameter interval. -/
theorem exists_timelike_interval (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    ∃ l r : ℝ, l < a ∧ b < r ∧ ∀ t ∈ Ioo l r,
      ContMDiffAt 𝓘(ℝ) I 2 γ t ∧ Timelike g (curveVelocity γ t) := by
  have hn : ∀ t ∈ Icc a b, ∀ᶠ s in 𝓝 t,
      ContMDiffAt 𝓘(ℝ) I 2 γ s ∧ Timelike g (curveVelocity γ s) := by
    intro t ht
    have hreg := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp (hγ t ht)
    have htime := (metricVelocity_continuousAt g ((hγ t ht).of_le (by norm_num))).eventually
      (gt_mem_nhds (hv t ht))
    exact hreg.and htime
  exact Variational.exists_Ioo_superset_Icc (fun t ht => ⟨hγ t ht, hv t ht⟩)
    (hn a ⟨le_rfl, hab⟩) (hn b ⟨hab, le_rfl⟩)

/-- A global-on-the-segment clock chart, constructed from the actual integral.
The inverse is C² and has unit rate even at the two endpoints; the closed
interval and both endpoint correspondences are proved explicitly. -/
theorem exists_finite_properTime_parameter (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ a ∧ Icc a b ⊆ e.source ∧ StrictMonoOn e e.source ∧
      e '' Icc a b = Icc 0 (properTime g γ a b) ∧
      e.symm '' Icc 0 (properTime g γ a b) = Icc a b ∧
      e.symm 0 = a ∧ e.symm (properTime g γ a b) = b ∧
      ∀ τ ∈ e.target,
        ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1 := by
  obtain ⟨l, r, hla, hbr, hgood⟩ := exists_timelike_interval g hab hγ hv
  have hsub : Icc a b ⊆ Ioo l r := fun _ ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hbr⟩
  have ha := hsub ⟨le_rfl, hab⟩
  have hc := properTime_contDiffOn g (fun t ht => (hgood t ht).1)
    (fun t ht => (hgood t ht).2) ha
  have hd : ∀ t ∈ Ioo l r, HasDerivAt (properTime g γ a) (speedAlong g γ t) t :=
    fun t ht => properTime_hasDerivAt_right g
      (fun s hs => (hgood s hs).1.of_le (by norm_num)) ha ht
  have hp : ∀ t ∈ Ioo l r, 0 < speedAlong g γ t :=
    fun t ht => (properSpeed_pos_iff g _).mpr (hgood t ht).2
  obtain ⟨e, he, hsource, hm, hinv⟩ := Variational.exists_positive_parameter_chart
    (properTime g γ a) hc (fun t ht => by rw [(hd t ht).deriv]; exact hp t ht)
  have hs : Icc a b ⊆ e.source := by rw [hsource]; exact hsub
  have hea : e a = 0 := by rw [he, properTime_self]
  have heb : e b = properTime g γ a b := by rw [he]
  have himage : e '' Icc a b = Icc 0 (properTime g γ a b) := by
    rw [← hea, ← heb]
    exact (e.continuousOn.mono hs).image_Icc_of_monotoneOn hab (hm.monotoneOn.mono hs)
  have hinvimage : e.symm '' Icc 0 (properTime g γ a b) = Icc a b := by
    rw [← himage]
    exact e.symm_image_image_of_subset_source hs
  refine ⟨e, he, hs, hm, himage, hinvimage, ?_, ?_, ?_⟩
  · rw [← hea]
    exact e.left_inv (hs ⟨le_rfl, hab⟩)
  · rw [← heb]
    exact e.left_inv (hs ⟨hab, le_rfl⟩)
  · intro τ hτ
    have ht : e.symm τ ∈ Ioo l r := by rw [← hsource]; exact e.map_target hτ
    have hi : HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ := by
      simpa only [(hd _ ht).deriv] using (hinv τ hτ).2
    refine ⟨(hinv τ hτ).1, hi, ?_⟩
    rw [speedAlong_comp g ((hgood _ ht).1.mdifferentiableAt (by norm_num)) hi.differentiableAt,
      hi.deriv, abs_of_pos (inv_pos.mpr (hp _ ht)), inv_mul_cancel₀ (hp _ ht).ne']

/-- The common inverse sends tangential motion on the whole original segment
to affine motion throughout the corresponding proper-time interior. -/
theorem geodesic_finite_properTime_inverse (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t))
    (ha : ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t)
    (e : OpenPartialHomeomorph ℝ ℝ) (hs : Icc a b ⊆ e.source)
    (hm : StrictMonoOn e e.source)
    (hi : ∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
      HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ) :
    g.IsGeodesicOn (Ioo (e a) (e b)) (γ ∘ e.symm) := by
  let f := e.restrOpen (Ioo a b) isOpen_Ioo
  have hfsource : f.source = Ioo a b := by
    change e.source ∩ Ioo a b = Ioo a b
    exact inter_eq_right.mpr (fun _ ht => hs ⟨ht.1.le, ht.2.le⟩)
  have hftarget : f.target = Ioo (e a) (e b) := by
    rw [← f.image_source_eq_target, hfsource]
    exact (e.continuousOn.mono hs).image_Ioo_of_strictMonoOn hab (hm.mono hs)
  have hg := geodesic_properTime_inverse g
    (fun t ht => hγ t ⟨ht.1.le, ht.2.le⟩) (fun t ht => hv t ⟨ht.1.le, ht.2.le⟩)
    (fun t ht => by
      obtain ⟨k, hk⟩ := ha t ht
      rw [acceleration_factor_eq g (hγ t ⟨ht.1.le, ht.2.le⟩) (hv t ⟨ht.1.le, ht.2.le⟩) hk]
      exact hk) f (by rw [hfsource])
    (fun τ hτ => hi τ hτ.1)
  rw [hftarget] at hg
  exact hg

/-- Finite timelike pregeodesic motion has a single proper-time inverse with
both endpoints, unit rate, and an affine equation on the entire interior. -/
theorem exists_finite_properTime_geodesic (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t))
    (ha : ∀ t ∈ Ioo a b, ∃ k : ℝ,
      g.covariantAlong (curveVelocity γ) t = k • curveVelocity γ t) :
    ∃ e : OpenPartialHomeomorph ℝ ℝ,
      (e : ℝ → ℝ) = properTime g γ a ∧ Icc a b ⊆ e.source ∧
      e '' Icc a b = Icc 0 (properTime g γ a b) ∧
      e.symm '' Icc 0 (properTime g γ a b) = Icc a b ∧
      e.symm 0 = a ∧ e.symm (properTime g γ a b) = b ∧
      (∀ τ ∈ e.target, ContDiffAt ℝ 2 e.symm τ ∧
        HasDerivAt e.symm (speedAlong g γ (e.symm τ))⁻¹ τ ∧
        speedAlong g (γ ∘ e.symm) τ = 1) ∧
      g.IsGeodesicOn (Ioo 0 (properTime g γ a b)) (γ ∘ e.symm) := by
  obtain ⟨e, he, hs, hm, himage, hinvimage, hleft, hright, hi⟩ :=
    exists_finite_properTime_parameter g hab hγ hv
  refine ⟨e, he, hs, himage, hinvimage, hleft, hright, hi, ?_⟩
  have hg := geodesic_finite_properTime_inverse g hab hγ hv ha e hs hm
    (fun τ hτ => ⟨(hi τ hτ).1, (hi τ hτ).2.1⟩)
  simpa only [he, properTime_self] using hg

theorem properTime_pos (g : LorentzMetric .timeNegative d M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hv : ∀ t ∈ Icc a b, Timelike g (curveVelocity γ t)) :
    0 < properTime g γ a b := by
  obtain ⟨e, he, hs, hm, _⟩ := exists_finite_properTime_parameter g hab.le hγ hv
  have h := hm (hs ⟨le_rfl, hab.le⟩) (hs ⟨hab.le, le_rfl⟩) hab
  simpa only [he, properTime_self] using h

end ProjectAInos.GeneralRelativity
