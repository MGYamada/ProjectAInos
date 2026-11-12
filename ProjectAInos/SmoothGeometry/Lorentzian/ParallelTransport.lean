/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelExtension

/-! # Parallel transport on finite regular curve segments

Transport acts between the actual endpoint tangent spaces. Its characterization
by parallel fields proves independence of the local frames used in its
construction, preservation of the metric, reversal, and subdivision.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle ContinuousLinearMap Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- A finite regular segment has an endpoint linear equivalence characterized
by every parallel field, preserving the metric. -/
theorem exists_parallelTransport (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    ∃ T : TangentSpace I (γ a) ≃L[ℝ] TangentSpace I (γ b),
      (∀ V : AlongField (d := d) γ, g.IsParallelOn (uIcc a b) V → T (V a) = V b) ∧
      ∀ v w, g.form (γ b) (T v) (T w) = g.form (γ a) v w := by
  obtain ⟨P, hinit, hpar⟩ := g.exists_parallelFrameOn_segment hγ
  have hm (v w : TangentSpace I (γ a)) :
      g.form (γ a) v w = g.form (γ b) (P b v) (P b w) := by
    simpa only [hinit, id_apply] using g.parallel_pairing_eq (convex_uIcc a b)
      (fun t ht => (hγ t ht).mdifferentiableAt (by norm_num))
      (hpar v) (hpar w) left_mem_uIcc right_mem_uIcc
  obtain ⟨T, hT⟩ := g.isInvertible_of_metric g (γ a) (γ b) (P b) hm
  have happly (v : TangentSpace I (γ a)) : T v = P b v :=
    congrArg (fun L : TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ b) => L v) hT
  refine ⟨T, ?_, fun v w => by rw [happly, happly]; exact (hm v w).symm⟩
  intro V hV
  rw [happly]
  apply (g.parallel_eq_iff (convex_uIcc a b) hγ (hpar (V a)) hV
    left_mem_uIcc right_mem_uIcc).mp
  rw [hinit, id_apply]

/-- Metric-preserving linear transport between the actual endpoint fibres
of a prescribed `C²` curve. No completeness or global chart is assumed. -/
def parallelTransport (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    TangentSpace I (γ a) ≃L[ℝ] TangentSpace I (γ b) :=
  Classical.choose (g.exists_parallelTransport hγ)

/-- Every parallel field computes transport, independently of the chosen
local frames and charts. -/
theorem parallelTransport_apply_eq (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    {V : AlongField (d := d) γ} (hV : g.IsParallelOn (uIcc a b) V) :
    g.parallelTransport hγ (V a) = V b :=
  (Classical.choose_spec (g.exists_parallelTransport hγ)).1 V hV

/-- Transport preserves the full bilinear metric, for both sign conventions. -/
theorem parallelTransport_metric (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (v w : TangentSpace I (γ a)) :
    g.form (γ b) (g.parallelTransport hγ v) (g.parallelTransport hγ w) =
      g.form (γ a) v w :=
  (Classical.choose_spec (g.exists_parallelTransport hγ)).2 v w

@[simp] theorem parallelTransport_self (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a : ℝ} (hγ : ∀ t ∈ uIcc a a, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.parallelTransport hγ = ContinuousLinearEquiv.refl ℝ (TangentSpace I (γ a)) := by
  ext v
  obtain ⟨V, hinit, hV⟩ := g.exists_parallel_on_segment hγ v
  simpa only [hinit, ContinuousLinearEquiv.refl_apply] using g.parallelTransport_apply_eq hγ hV

/-- Reversing the endpoints inverts parallel transport along the same curve. -/
theorem parallelTransport_reverse (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hrev : ∀ t ∈ uIcc b a, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.parallelTransport hrev = (g.parallelTransport hγ).symm := by
  ext v
  obtain ⟨V, hinit, hV⟩ := g.exists_parallel_on_segment hrev v
  have hback := g.parallelTransport_apply_eq hrev hV
  have hforward := g.parallelTransport_apply_eq hγ (by simpa only [uIcc_comm] using hV)
  apply (g.parallelTransport hγ).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [hinit] at hback hforward
  rw [hback, hforward]

/-- Subdivision of a regular segment composes its transport maps. -/
theorem parallelTransport_trans (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b c : ℝ}
    (hγ : ∀ t ∈ uIcc a c, ContMDiffAt 𝓘(ℝ) I 2 γ t) (hb : b ∈ uIcc a c) :
    (g.parallelTransport (a := a) (b := b)
      (fun t ht => hγ t (uIcc_subset_uIcc_left hb ht))).trans
      (g.parallelTransport (a := b) (b := c)
        (fun t ht => hγ t (uIcc_subset_uIcc_right hb ht))) = g.parallelTransport hγ := by
  ext v
  obtain ⟨V, hinit, hV⟩ := g.exists_parallel_on_segment hγ v
  have hleft := g.parallelTransport_apply_eq
    (fun t ht => hγ t (uIcc_subset_uIcc_left hb ht))
    (hV.mono (uIcc_subset_uIcc_left hb))
  have hright := g.parallelTransport_apply_eq
    (fun t ht => hγ t (uIcc_subset_uIcc_right hb ht))
    (hV.mono (uIcc_subset_uIcc_right hb))
  have hfull := g.parallelTransport_apply_eq hγ hV
  simp only [ContinuousLinearEquiv.trans_apply]
  rw [hinit] at hleft hfull
  rw [hleft, hright, hfull]

/-- A `C²` parameter change with image in the original segment preserves
endpoint transport. Neither monotonicity nor nonzero parameter speed is
required; in particular this includes affine path reversal. -/
theorem parallelTransport_reparam (g : LorentzMetric σ d M)
    {γ : ℝ → M} {r : ℝ → ℝ} {a b : ℝ}
    (hγ : ∀ t ∈ uIcc (r a) (r b), ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hr : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 r t)
    (hm : MapsTo r (uIcc a b) (uIcc (r a) (r b))) :
    g.parallelTransport (γ := γ ∘ r) (a := a) (b := b)
      (fun t ht => (hγ (r t) (hm ht)).comp t (hr t ht).contMDiffAt) =
        g.parallelTransport hγ := by
  ext v
  obtain ⟨V, hinit, hV⟩ := g.exists_parallel_on_segment hγ v
  have hpull := hV.reparam (fun t ht => (hr t ht).differentiableAt (by norm_num))
    (fun t ht => (hγ t ht).mdifferentiableAt (by norm_num)) hm
  have h := g.parallelTransport_apply_eq (γ := γ ∘ r) (a := a) (b := b)
    (fun t ht => (hγ (r t) (hm ht)).comp t (hr t ht).contMDiffAt) hpull
  have horig := g.parallelTransport_apply_eq hγ hV
  rw [hinit] at h horig
  exact h.trans horig.symm

end ProjectAInos.SmoothGeometry.LorentzMetric
