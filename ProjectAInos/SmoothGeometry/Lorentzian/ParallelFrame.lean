/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelLocal
public import ProjectAInos.SmoothGeometry.Lorentzian.Naturality

/-! # Local parallel frames and linear metric-preserving transport

A finite collection of local ODE solutions supplies a common interval for
all initial vectors. Metric nondegeneracy makes the resulting maps
invertible. No frame on the whole manifold is assumed.
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

theorem IsParallelOn.mono {g : LorentzMetric σ d M} {γ : ℝ → M}
    {V : AlongField (d := d) γ} {s u : Set ℝ} (h : g.IsParallelOn s V) (hu : u ⊆ s) :
    g.IsParallelOn u V := fun t ht => h t (hu ht)

/-- Parallelism is local, so equal fields on an open parameter domain have
the same regularity and covariant derivative there. -/
theorem IsParallelOn.congr {g : LorentzMetric σ d M} {γ : ℝ → M}
    {V W : AlongField (d := d) γ} {s : Set ℝ} (hW : g.IsParallelOn s W)
    (hs : IsOpen s) (heq : ∀ t ∈ s, V t = W t) : g.IsParallelOn s V := by
  intro t ht
  have hn : ∀ᶠ r in 𝓝 t, V r = W r := Filter.eventually_of_mem (hs.mem_nhds ht) heq
  refine ⟨(hW t ht).1.congr_of_eventuallyEq ?_, ?_⟩
  · exact hn.mono fun r hr => congrArg (TotalSpace.mk' E (γ r)) hr
  · rw [g.covariantAlong_congr hn, (hW t ht).2]

/-- Sums of parallel fields are parallel. -/
theorem IsParallelOn.add {g : LorentzMetric σ d M} {γ : ℝ → M}
    {V W : AlongField (d := d) γ} {s : Set ℝ}
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn s W) : g.IsParallelOn s (V + W) := by
  intro t ht
  refine ⟨alongField_mdifferentiableAt_add (hV t ht).1 (hW t ht).1, ?_⟩
  rw [g.covariantAlong_add (hV t ht).1 (hW t ht).1, (hV t ht).2, (hW t ht).2, add_zero]

/-- Constant scalar multiples of parallel fields are parallel. -/
theorem IsParallelOn.smul_const {g : LorentzMetric σ d M} {γ : ℝ → M}
    {V : AlongField (d := d) γ} {s : Set ℝ} (hV : g.IsParallelOn s V) (a : ℝ) :
    g.IsParallelOn s (a • V) := by
  intro t ht
  refine ⟨alongField_mdifferentiableAt_smul (differentiableAt_const a) (hV t ht).1, ?_⟩
  change g.covariantAlong (fun r => a • V r) t = 0
  rw [g.covariantAlong_smul (differentiableAt_const a) (hV t ht).1,
    deriv_const, zero_smul, (hV t ht).2, smul_zero, add_zero]

/-- The zero along field is parallel on a differentiable curve. -/
theorem isParallelOn_zero (g : LorentzMetric σ d M) {γ : ℝ → M} {s : Set ℝ}
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t) : g.IsParallelOn s (0 : AlongField (d := d) γ) := by
  intro t ht
  have hV := alongField_zero_mdifferentiableAt (hγ t ht)
  refine ⟨hV, (g.covariantAlong_eq_zero_iff_hasDerivAt
    (IsManifold.chart_mem_maximalAtlas (γ t)) (mem_chart_source E (γ t)) (hγ t ht) hV).mpr ?_⟩
  have heq : alongComponents (chartAt E (γ t)) (γ := γ) (fun _ => 0) = fun _ => 0 := by
    funext r
    exact map_zero _
  rw [heq, map_zero]
  exact hasDerivAt_const t 0

/-- Finite linear combinations of parallel fields share their parameter domain. -/
theorem IsParallelOn.sum {g : LorentzMetric σ d M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t)
    {ι : Type*} (f : Finset ι) (V : ι → AlongField (d := d) γ)
    (hV : ∀ i ∈ f, g.IsParallelOn s (V i)) : g.IsParallelOn s (∑ i ∈ f, V i) := by
  classical
  induction f using Finset.induction_on with
  | empty => simpa using g.isParallelOn_zero hγ
  | @insert i f hi ih =>
    rw [Finset.sum_insert hi]
    exact (hV i (Finset.mem_insert_self _ _)).add (ih fun j hj => hV j (Finset.mem_insert_of_mem hj))

/-- A common local parallel frame transports every initial tangent vector
linearly. Every transport map in this interval is invertible and preserves
the Lorentz metric. The interval depends on the curve and base time, not
on the initial vector. -/
theorem exists_localParallelFrame (g : LorentzMetric σ d M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t₀) :
    ∃ ε > (0 : ℝ), ∃ P : ∀ t, TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t),
      P t₀ = ContinuousLinearMap.id ℝ _ ∧
      (∀ v, g.IsParallelOn (Ioo (t₀ - ε) (t₀ + ε)) (fun t => P t v)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), (P t).IsInvertible ∧
        ∀ v w, g.form (γ t₀) v w = g.form (γ t) (P t v) (P t w) := by
  classical
  let e := chartAt E (γ t₀)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t₀)
  have hx : γ t₀ ∈ e.source := mem_chart_source E (γ t₀)
  choose ε hε V hinit hpar using fun i : Fin (d + 1) =>
    g.exists_parallel_local hγ (chartField e (Pi.single i 1) (γ t₀))
  have hn : ∀ᶠ t in 𝓝 t₀, ∀ i, t ∈ Ioo (t₀ - ε i) (t₀ + ε i) :=
    Filter.eventually_all.mpr fun i => isOpen_Ioo.mem_nhds ⟨by linarith [hε i], by linarith [hε i]⟩
  have hγn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hγ.of_le (by norm_num))
  obtain ⟨δ, hδ, hgood⟩ := Metric.eventually_nhds_iff_ball.mp (hn.and hγn)
  have hball {t : ℝ} (ht : t ∈ Ioo (t₀ - δ) (t₀ + δ)) : t ∈ ball t₀ δ := by
    rwa [Real.ball_eq_Ioo]
  have hγd : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), MDifferentiableAt 𝓘(ℝ) I γ t :=
    fun t ht => (hgood t (hball ht)).2.mdifferentiableAt (by norm_num)
  let P : ∀ t, TangentSpace I (γ t₀) →L[ℝ] TangentSpace I (γ t) := fun t =>
    ∑ i, ((proj i : E →L[ℝ] ℝ).comp (chartTangentMap e (γ t₀))).smulRight (V i t)
  have hP (v : TangentSpace I (γ t₀)) :
      g.IsParallelOn (Ioo (t₀ - δ) (t₀ + δ)) (fun t => P t v) := by
    have h := IsParallelOn.sum hγd Finset.univ
      (fun i => (chartTangentMap e (γ t₀) v i) • V i) (fun i _ =>
        ((hpar i).mono (fun t ht => (hgood t (hball ht)).1 i)).smul_const _)
    have heq : (fun t => P t v) = ∑ i, (chartTangentMap e (γ t₀) v i) • V i := by
      funext t
      simp only [P, sum_apply, smulRight_apply, comp_apply, proj_apply,
        Finset.sum_apply, Pi.smul_apply]
    rw [heq]
    exact h
  have hPinit : P t₀ = ContinuousLinearMap.id ℝ _ := by
    ext v
    simp only [P, sum_apply, smulRight_apply, comp_apply, proj_apply, id_apply, hinit]
    have h := LinearMap.pi_apply_eq_sum_univ (chartFieldMap e (γ t₀)).toLinearMap
      (chartTangentMap e (γ t₀) v)
    have hb (i : Fin (d + 1)) : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
      ext j
      simp [Pi.single_apply, eq_comm]
    simp_rw [hb] at h
    exact h.symm.trans (chartField_tangentMap he hx v)
  have ht₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hmetric (t : ℝ) (ht : t ∈ Ioo (t₀ - δ) (t₀ + δ))
      (v w : TangentSpace I (γ t₀)) :
      g.form (γ t₀) v w = g.form (γ t) (P t v) (P t w) := by
    simpa only [hPinit, id_apply] using g.parallel_pairing_eq (convex_Ioo _ _) hγd (hP v) (hP w) ht₀ ht
  exact ⟨δ, hδ, P, hPinit, hP, fun t ht =>
    ⟨g.isInvertible_of_metric g (γ t₀) (γ t) (P t) (hmetric t ht), hmetric t ht⟩⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
