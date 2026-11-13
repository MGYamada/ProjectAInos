/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelFrame
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Clopen

/-! # Uniqueness on parameter intervals and nonvanishing of null velocity

Local parallel frames test vector equality by metric pairings. Propagating
that equality through a connected interval avoids any global trivialization
or global Hausdorff assumption on the manifold.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle ContinuousLinearMap Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

private theorem parallel_eq_of_frame (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {s : Set ℝ} {t₀ : ℝ}
    {P : ∀ t, TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t)}
    (hs : Convex ℝ s) (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn s W)
    (hP : ∀ v, g.IsParallelOn s (fun t => P t v)) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hPb : (P b).IsInvertible) (hinit : V a = W a) : V b = W b := by
  apply (g.flat (γ b)).injective
  ext w
  let z := (P b).inverse w
  have hz : P b z = w := hPb.self_apply_inverse w
  have h1 := g.parallel_pairing_eq hs hγ hV (hP z) ha hb
  have h2 := g.parallel_pairing_eq hs hγ hW (hP z) ha hb
  change g.form (γ b) (V b) w = g.form (γ b) (W b) w
  calc
    g.form (γ b) (V b) w = g.form (γ a) (V a) (P a z) := by simpa only [hz] using h1.symm
    _ = g.form (γ a) (W a) (P a z) := by rw [hinit]
    _ = g.form (γ b) (W b) w := by simpa only [hz] using h2

/-- Equality of parallel fields propagates throughout any convex parameter
set. Closed intervals are included, with the regular endpoint extensions
required by `IsParallelOn`. -/
theorem parallel_eq_iff (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {s : Set ℝ}
    (hs : Convex ℝ s) (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn s W) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) : V a = W a ↔ V b = W b := by
  refine hs.isPreconnected.induction₂ (fun a b => V a = W a ↔ V b = W b) ?_
    (fun _ _ _ _ _ _ hab hbc => hab.trans hbc) (fun _ _ _ _ hab => hab.symm) ha hb
  intro x hx
  obtain ⟨δ, hδ, P, _, hP, hinv⟩ := g.exists_localParallelFrame (hγ x hx)
  have hxδ : x ∈ Ioo (x - δ) (x + δ) := ⟨by linarith, by linarith⟩
  have hn : Ioo (x - δ) (x + δ) ∈ 𝓝[s] x :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hxδ)
  filter_upwards [hn, self_mem_nhdsWithin] with y hy hys
  have hconv := hs.inter (convex_Ioo (x - δ) (x + δ))
  have hγd : ∀ t ∈ s ∩ Ioo (x - δ) (x + δ), MDifferentiableAt 𝓘(ℝ) I γ t :=
    fun t ht => (hγ t ht.1).mdifferentiableAt (by norm_num)
  have hV' := hV.mono (inter_subset_left (s := s) (t := Ioo (x - δ) (x + δ)))
  have hW' := hW.mono (inter_subset_left (s := s) (t := Ioo (x - δ) (x + δ)))
  have hP' (v : TangentSpace I (γ x)) :
      g.IsParallelOn (s ∩ Ioo (x - δ) (x + δ)) (fun t => P t v) :=
    (hP v).mono inter_subset_right
  exact ⟨g.parallel_eq_of_frame hconv hγd hV' hW' hP' ⟨hx, hxδ⟩ ⟨hys, hy⟩ (hinv y hy).1,
    g.parallel_eq_of_frame hconv hγd hV' hW' hP' ⟨hys, hy⟩ ⟨hx, hxδ⟩ (hinv x hxδ).1⟩

/-- A parallel field vanishes either everywhere or nowhere on a convex
parameter set. The assertion uses linear uniqueness, not metric norm alone. -/
theorem IsParallelOn.eq_zero_iff {g : LorentzMetric σ d M}
    {γ : ℝ → M} {V : AlongField (d := d) γ} {s : Set ℝ}
    (hV : g.IsParallelOn s V) (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ) I 2 γ t) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    V a = 0 ↔ V b = 0 :=
  g.parallel_eq_iff hs hγ hV
    (g.isParallelOn_zero fun t ht => (hγ t ht).mdifferentiableAt (by norm_num)) ha hb

/-- Nonzero geodesic velocity cannot become zero, including in the null case. -/
theorem IsGeodesicOn.velocity_ne_zero_iff {g : LorentzMetric σ d M}
    {γ : ℝ → M} {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    curveVelocity (d := d) γ a ≠ 0 ↔ curveVelocity (d := d) γ b ≠ 0 :=
  not_congr (h.velocity_parallel.eq_zero_iff hs (fun t ht => (h t ht).1) ha hb)

/-- A nonzero null geodesic velocity stays nonzero and null throughout a
convex parameter interval. No normalization or time orientation is used. -/
theorem IsGeodesicOn.null_iff {g : LorentzMetric σ d M}
    {γ : ℝ → M} {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (curveVelocity (d := d) γ a ≠ 0 ∧ g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) = 0) ↔
      (curveVelocity (d := d) γ b ≠ 0 ∧ g.form (γ b) (curveVelocity γ b) (curveVelocity γ b) = 0) :=
  and_congr (h.velocity_ne_zero_iff hs ha hb) (h.null_norm_iff hs ha hb)

end ProjectAInos.SmoothGeometry.LorentzMetric
