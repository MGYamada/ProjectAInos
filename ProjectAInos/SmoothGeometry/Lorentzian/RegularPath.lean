/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelTransport

/-! # Regular path segments with named endpoints

A segment is a curve regular on `[0,1]`, including local extensions at the
endpoints. Endpoint equalities identify the actual tangent fibres; they do
not choose a frame. Its underlying path is an ordinary continuous `Path`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The canonical identification of tangent fibres at equal points. -/
def tangentCongr {x y : M} (h : x = y) : TangentSpace I x ≃L[ℝ] TangentSpace I y := by
  subst y
  exact ContinuousLinearEquiv.refl ℝ _

@[simp] theorem tangentCongr_rfl (x : M) :
    tangentCongr (d := d) (rfl : x = x) = ContinuousLinearEquiv.refl ℝ _ := rfl

theorem tangentCongr_symm {x y : M} (h : x = y) :
    tangentCongr (d := d) h.symm = (tangentCongr h).symm := by subst y; rfl

@[simp] theorem tangentCongr_trans {x y z : M} (h : x = y) (k : y = z) :
    (tangentCongr (d := d) h).trans (tangentCongr k) = tangentCongr (h.trans k) := by
  subst y z
  rfl

@[simp] theorem totalSpace_tangentCongr {x y : M} (h : x = y) (v : TangentSpace I x) :
    TotalSpace.mk' E y (tangentCongr h v) = TotalSpace.mk' E x v := by subst y; rfl

theorem tangentCongr_symm_apply_apply {x y : M} (h : x = y) (v : TangentSpace I x) :
    tangentCongr h.symm (tangentCongr h v) = v := by subst y; rfl

theorem tangentCongr_apply_symm_apply {x y : M} (h : x = y) (v : TangentSpace I y) :
    tangentCongr h (tangentCongr h.symm v) = v := by subst y; rfl

variable [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- A `C²` segment from `x` to `y`, with endpoint extensions explicit. -/
structure RegularPath (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
    (x y : M) where
  curve : ℝ → M
  source : curve 0 = x
  target : curve 1 = y
  regular : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) 2 curve t

namespace RegularPath

variable {x y z : M} (p : RegularPath d M x y)

/-- Forget differentiability and retain the actual continuous path. -/
def toPath : Path x y where
  toFun t := p.curve t
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    (fun t ht => (p.regular t ht).continuousAt.continuousWithinAt)
  source' := p.source
  target' := p.target

@[simp] theorem toPath_apply (t : unitInterval) : p.toPath t = p.curve t := rfl

/-- Traverse the same regular segment in the opposite direction. -/
def reverse : RegularPath d M y x where
  curve t := p.curve (1 - t)
  source := by simpa using p.target
  target := by simpa using p.source
  regular t ht := by
    have hr : ContDiff ℝ 2 (fun t : ℝ => 1 - t) := by fun_prop
    exact (p.regular (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).comp t
      hr.contMDiff.contMDiffAt

@[simp] theorem toPath_reverse : p.reverse.toPath = p.toPath.symm := by
  ext t
  rfl

variable {σ : LorentzConvention} (g : LorentzMetric σ d M)

/-- Transport along a regular segment, using only canonical endpoint casts. -/
def transport : TangentSpace I x ≃L[ℝ] TangentSpace I y :=
  ((tangentCongr p.source.symm).trans (g.parallelTransport (a := 0) (b := 1)
    (fun t ht => p.regular t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)))).trans
      (tangentCongr p.target)

/-- Intrinsic parallel fields characterize the named-endpoint map. -/
theorem transport_apply_eq {V : LorentzMetric.AlongField (d := d) p.curve}
    (hV : g.IsParallelOn (Icc (0 : ℝ) 1) V) :
    p.transport g (tangentCongr p.source (V 0)) = tangentCongr p.target (V 1) := by
  simp only [transport, ContinuousLinearEquiv.trans_apply,
    tangentCongr_symm_apply_apply p.source]
  apply congrArg (tangentCongr p.target)
  exact g.parallelTransport_apply_eq (a := 0) (b := 1) _
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hV)

theorem transport_metric (v w : TangentSpace I x) :
    g.form y (p.transport g v) (p.transport g w) = g.form x v w := by
  have hc {a b : M} (h : a = b) (u v : TangentSpace I a) :
      g.form b (tangentCongr h u) (tangentCongr h v) = g.form a u v := by subst b; rfl
  simp only [transport, ContinuousLinearEquiv.trans_apply, hc, g.parallelTransport_metric]

/-- Every initial vector admits a native parallel field along the segment,
with endpoints given by transport. -/
theorem exists_parallel (v : TangentSpace I x) :
    ∃ V : LorentzMetric.AlongField (d := d) p.curve,
      g.IsParallelOn (Icc (0 : ℝ) 1) V ∧ tangentCongr p.source (V 0) = v ∧
        tangentCongr p.target (V 1) = p.transport g v := by
  obtain ⟨V, hinit, hV⟩ := g.exists_parallel_on_segment (a := 0) (b := 1)
    (fun t ht => p.regular t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))
    (tangentCongr p.source.symm v)
  have hV' : g.IsParallelOn (Icc (0 : ℝ) 1) V := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hV
  have hi : tangentCongr p.source (V 0) = v := by
    rw [hinit, tangentCongr_apply_symm_apply p.source]
  exact ⟨V, hV', hi, by rw [← p.transport_apply_eq g hV', hi]⟩

/-- Parallel fields with the same initial value agree at every parameter
of the regular segment. -/
theorem parallel_unique {V W : LorentzMetric.AlongField (d := d) p.curve}
    (hV : g.IsParallelOn (Icc (0 : ℝ) 1) V) (hW : g.IsParallelOn (Icc (0 : ℝ) 1) W)
    (hinit : tangentCongr p.source (V 0) = tangentCongr p.source (W 0))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : V t = W t := by
  apply (g.parallel_eq_iff (convex_Icc 0 1) p.regular hV hW
    (left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) ht).mp
  exact (tangentCongr p.source).injective hinit

/-- Path reversal inverts the named-endpoint transport. -/
theorem transport_reverse : p.reverse.transport g = (p.transport g).symm := by
  ext v
  obtain ⟨V, hV, hstart, hend⟩ := p.exists_parallel g ((p.transport g).symm v)
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun t : ℝ => 1 - t) t := by
    intros; fun_prop
  have hm : MapsTo (fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hrev := hV.reparam hr
    (fun t ht => (p.regular t ht).mdifferentiableAt (by norm_num)) hm
  have h := p.reverse.transport_apply_eq g hrev
  dsimp only [reverse] at h
  have hc {a b : ℝ} (hab : a = b) {z : M} (ha : p.curve a = z) (hb : p.curve b = z) :
      tangentCongr ha (V a) = tangentCongr hb (V b) := by subst b; rfl
  have h' : p.reverse.transport g (tangentCongr p.target (V 1)) =
      tangentCongr p.source (V 0) := by
    rw [hc (sub_zero 1) p.reverse.source p.target, hc (sub_self 1) p.reverse.target p.source] at h
    exact h
  rw [hend, ContinuousLinearEquiv.apply_symm_apply, hstart] at h'
  exact h'

/-- A native parallel field is an actual continuous path in the tangent
bundle, with its endpoint casts made explicit. -/
def parallelPath {V : LorentzMetric.AlongField (d := d) p.curve}
    (hV : g.IsParallelOn (Icc (0 : ℝ) 1) V) :
    Path (TotalSpace.mk' E x (tangentCongr p.source (V 0)))
      (TotalSpace.mk' E y (tangentCongr p.target (V 1))) where
  toFun t := TotalSpace.mk' E (p.curve t) (V t)
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    (fun t ht => (hV t ht).1.continuousAt.continuousWithinAt)
  source' := (totalSpace_tangentCongr p.source (V 0)).symm
  target' := (totalSpace_tangentCongr p.target (V 1)).symm

/-- The continuous parallel lift projects to the original path exactly. -/
theorem parallelPath_map {V : LorentzMetric.AlongField (d := d) p.curve}
    (hV : g.IsParallelOn (Icc (0 : ℝ) 1) V) :
    (p.parallelPath g hV).map (FiberBundle.continuous_proj E (TangentSpace I)) = p.toPath := by
  ext t
  rfl

end RegularPath
end ProjectAInos.SmoothGeometry
