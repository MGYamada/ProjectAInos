/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelUniqueness

/-! # Extending parallel frames along prescribed finite path segments

Overlapping local parallel frames agree after their initial values are
identified. Gluing and connectedness then extend them along every regular
finite segment, without a global manifold frame or a completeness premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle ContinuousLinearMap Set Metric
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

private def HasParallelFrameNear (g : LorentzMetric σ d M) (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∃ l r, a ∈ Ioo l r ∧ b ∈ Ioo l r ∧
    (∀ t ∈ Ioo l r, ContMDiffAt 𝓘(ℝ) I 2 γ t) ∧
    ∃ P : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t),
      P a = ContinuousLinearMap.id ℝ _ ∧ ∀ v, g.IsParallelOn (Ioo l r) (fun t => P t v)

private theorem HasParallelFrameNear.local (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ a) :
    ∀ᶠ b in 𝓝 a, HasParallelFrameNear g γ a b := by
  obtain ⟨ε, hε, P, hinit, hpar, _⟩ := g.exists_localParallelFrame hγ
  have ha : a ∈ Ioo (a - ε) (a + ε) := ⟨by linarith, by linarith⟩
  have hγn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp hγ
  have hn : ∀ᶠ t in 𝓝 a, t ∈ Ioo (a - ε) (a + ε) := isOpen_Ioo.mem_nhds ha
  obtain ⟨δ, hδ, hgood⟩ := Metric.eventually_nhds_iff_ball.mp
    (Filter.Eventually.and hn hγn)
  have hball {t : ℝ} (ht : t ∈ Ioo (a - δ) (a + δ)) : t ∈ ball a δ := by rwa [Real.ball_eq_Ioo]
  have haδ : a ∈ Ioo (a - δ) (a + δ) := ⟨by linarith, by linarith⟩
  filter_upwards [isOpen_Ioo.mem_nhds haδ] with b hb
  exact ⟨a - δ, a + δ, haδ, hb, fun t ht => (hgood t (hball ht)).2, P, hinit,
    fun v => (hpar v).mono (fun t ht => (hgood t (hball ht)).1)⟩

private theorem HasParallelFrameNear.symm {g : LorentzMetric σ d M}
    {γ : ℝ → M} {a b : ℝ} (h : HasParallelFrameNear g γ a b) :
    HasParallelFrameNear g γ b a := by
  obtain ⟨l, r, ha, hb, hγ, P, hinit, hpar⟩ := h
  have hm (v w : TangentSpace I (γ a)) :
      g.form (γ a) v w = g.form (γ b) (P b v) (P b w) := by
    simpa only [hinit, id_apply] using g.parallel_pairing_eq (convex_Ioo l r)
      (fun t ht => (hγ t ht).mdifferentiableAt (by norm_num)) (hpar v) (hpar w) ha hb
  have hinv := g.isInvertible_of_metric g (γ a) (γ b) (P b) hm
  refine ⟨l, r, hb, ha, hγ, fun t => (P t).comp (P b).inverse, ?_, ?_⟩
  · ext v
    exact hinv.self_apply_inverse v
  · intro v
    exact hpar ((P b).inverse v)

private theorem HasParallelFrameNear.trans {g : LorentzMetric σ d M}
    {γ : ℝ → M} {a b c : ℝ} (hab : HasParallelFrameNear g γ a b)
    (hbc : HasParallelFrameNear g γ b c) : HasParallelFrameNear g γ a c := by
  classical
  obtain ⟨l, r, ha, hb, hγ, P, hPinit, hP⟩ := hab
  obtain ⟨l', r', hb', hc, hγ', Q, hQinit, hQ⟩ := hbc
  have hOverlap (v : TangentSpace I (γ a)) {t : ℝ} (ht : t ∈ Ioo l r ∩ Ioo l' r') :
      P t v = Q t (P b v) := by
    apply (g.parallel_eq_iff ((convex_Ioo l r).inter (convex_Ioo l' r'))
      (fun t ht => hγ t ht.1) ((hP v).mono inter_subset_left)
      ((hQ (P b v)).mono inter_subset_right) ⟨hb, hb'⟩ ht).mp
    rw [hQinit, id_apply]
  let R : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t) :=
    fun t => if t ∈ Ioo l r then P t else (Q t).comp (P b)
  have hR (v : TangentSpace I (γ a)) :
      g.IsParallelOn (Ioo l r ∪ Ioo l' r') (fun t => R t v) := by
    have hleft : g.IsParallelOn (Ioo l r) (fun t => R t v) :=
      (hP v).congr isOpen_Ioo (fun t ht => by simp only [R, ite_eq_left ht])
    have hright : g.IsParallelOn (Ioo l' r') (fun t => R t v) := by
      apply (hQ (P b v)).congr isOpen_Ioo
      intro t ht
      by_cases htl : t ∈ Ioo l r
      · simpa only [R, ite_eq_left htl] using hOverlap v ⟨htl, ht⟩
      · simp only [R, ite_eq_right htl, comp_apply]
    intro t ht
    exact ht.elim (hleft t) (hright t)
  have hunion : Ioo l r ∪ Ioo l' r' = Ioo (min l l') (max r r') :=
    Ioo_union_Ioo' (by linarith [hb.2, hb'.1]) (by linarith [hb.1, hb'.2])
  refine ⟨min l l', max r r', ?_, ?_, ?_, R, ?_, ?_⟩
  · rw [← hunion]
    exact Or.inl ha
  · rw [← hunion]
    exact Or.inr hc
  · intro t ht
    rw [← hunion] at ht
    exact ht.elim (hγ t) (hγ' t)
  · simpa only [R, ite_eq_left ha] using hPinit
  · simpa only [hunion] using hR

/-- A regular prescribed finite path segment admits a common linear
parallel extension for every initial tangent vector. The proof glues local
frames across charts; it does not assume a global chart or bounded tangent
coordinates for the entire segment. -/
theorem exists_parallelFrameOn_segment (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    ∃ P : ∀ t, TangentSpace I (γ a) →L[ℝ] TangentSpace I (γ t),
      P a = ContinuousLinearMap.id ℝ _ ∧
        ∀ v, g.IsParallelOn (uIcc a b) (fun t => P t v) := by
  have h : HasParallelFrameNear g γ a b :=
    (convex_uIcc a b).isPreconnected.induction₂ (HasParallelFrameNear g γ)
      (fun t ht => (HasParallelFrameNear.local g (hγ t ht)).filter_mono nhdsWithin_le_nhds)
      (fun _ _ _ _ _ _ hab hbc => hab.trans hbc)
      (fun _ _ _ _ hab => hab.symm) left_mem_uIcc right_mem_uIcc
  obtain ⟨l, r, ha, hb, _, P, hinit, hpar⟩ := h
  refine ⟨P, hinit, fun v => (hpar v).mono ?_⟩
  intro t ht
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at ht
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, ht.1, ht.2]
  · rw [uIcc_of_ge hba] at ht
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, ht.1, ht.2]

/-- Parallel fields exist on the whole prescribed regular finite segment
for every initial tangent vector. -/
theorem exists_parallel_on_segment (g : LorentzMetric σ d M)
    {γ : ℝ → M} {a b : ℝ} (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (v : TangentSpace I (γ a)) :
    ∃ V : AlongField (d := d) γ, V a = v ∧ g.IsParallelOn (uIcc a b) V := by
  obtain ⟨P, hinit, hpar⟩ := g.exists_parallelFrameOn_segment hγ
  refine ⟨fun t => P t v, ?_, hpar v⟩
  change P a v = v
  rw [hinit, id_apply]

end ProjectAInos.SmoothGeometry.LorentzMetric
