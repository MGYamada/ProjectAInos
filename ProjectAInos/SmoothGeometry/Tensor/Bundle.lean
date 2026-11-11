/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.Contraction
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Iterated tangent and cotangent tensor bundles

Finite tensor types are represented by iterated hom bundles. In particular,
`hom tangent scalar` is the cotangent bundle, and repeatedly taking homs
constructs arbitrary mixed tensors. Each construction uses mathlib's actual
bundle topology and smooth transition maps. Only the local model is normed;
there is no assumed global frame or preferred norm on tangent fibres.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- Bundle data retained together so iterated hom constructions can be recursive.
Every instance is supplied by the concrete tangent, scalar, or hom construction. -/
structure SmoothBundle where
  Model : Type
  [modelNormed : NormedAddCommGroup Model]
  [modelSpace : NormedSpace ℝ Model]
  [modelFinite : FiniteDimensional ℝ Model]
  Fiber : M → Type
  [fiberAdd : ∀ x, AddCommGroup (Fiber x)]
  [fiberModule : ∀ x, Module ℝ (Fiber x)]
  [fiberTopology : ∀ x, TopologicalSpace (Fiber x)]
  [fiberTopAdd : ∀ x, IsTopologicalAddGroup (Fiber x)]
  [fiberSMul : ∀ x, ContinuousSMul ℝ (Fiber x)]
  [totalTopology : TopologicalSpace (TotalSpace Model Fiber)]
  [fiberBundle : FiberBundle Model Fiber]
  [vectorBundle : VectorBundle ℝ Model Fiber]
  [smooth : ContMDiffVectorBundle ∞ Model Fiber I]

attribute [instance] SmoothBundle.modelNormed SmoothBundle.modelSpace
  SmoothBundle.modelFinite SmoothBundle.fiberAdd SmoothBundle.fiberModule
  SmoothBundle.fiberTopology SmoothBundle.fiberTopAdd SmoothBundle.fiberSMul
  SmoothBundle.totalTopology SmoothBundle.fiberBundle
  SmoothBundle.vectorBundle SmoothBundle.smooth

namespace SmoothBundle

/-- The trivial real line bundle. -/
abbrev scalar : SmoothBundle I (M := M) where
  Model := ℝ
  Fiber := Bundle.Trivial M ℝ

/-- The existing tangent bundle, not a replacement with globally constant charts. -/
abbrev tangent [FiniteDimensional ℝ E] [IsManifold I ∞ M] : SmoothBundle I (M := M) where
  Model := E
  Fiber := TangentSpace I

/-- Homs of two smooth finite-dimensional bundles, with their induced charts. -/
abbrev hom (A B : SmoothBundle I (M := M)) : SmoothBundle I (M := M) where
  Model := A.Model →L[ℝ] B.Model
  Fiber x := A.Fiber x →L[ℝ] B.Fiber x

/-- Smooth sections retain the native hom/tangent bundle smoothness predicate. -/
abbrev Section (A : SmoothBundle I (M := M)) := Cₛ^∞⟮I; A.Model, A.Fiber⟯

/-- Evaluate a smooth tensor-valued linear map on a smooth argument. -/
def apply (A B : SmoothBundle I (M := M)) (L : (hom I A B).Section I)
    (v : A.Section I) : B.Section I :=
  ⟨fun x => (L x : A.Fiber x →L[ℝ] B.Fiber x) (v x),
    L.contMDiff.clm_bundle_apply v.contMDiff⟩

/-- Composition contracts a matching output/input pair of tensor bundles. -/
def compose (A B C : SmoothBundle I (M := M))
    (L : (hom I B C).Section I) (K : (hom I A B).Section I) :
    (hom I A C).Section I := Tensor.comp L K

/-- Trace contraction of an endomorphism of any finite tensor bundle. -/
def contract (A : SmoothBundle I (M := M)) (L : (hom I A A).Section I) : C^∞⟮I, M; ℝ⟯ :=
  Tensor.trace A.Model L

/-- Contract the endomorphism indices while retaining the remaining argument.
For `A = B = tangent`, this contracts a `(1,2)` tensor to a covector. -/
def partialContract (A B : SmoothBundle I (M := M))
    (L : (hom I A (hom I B B)).Section I) : (hom I A (scalar I)).Section I :=
  Tensor.comp (Tensor.traceSection B.Model) L

@[simp] theorem partialContract_apply (A B : SmoothBundle I (M := M))
    (L : (hom I A (hom I B B)).Section I) (x : M) (v : A.Fiber x) :
    partialContract I A B L x v = LinearMap.trace ℝ (B.Fiber x) (L x v).toLinearMap :=
  Tensor.fiberTrace_apply B.Model x (L x v)

/-- Local tensor coefficients are extracted from the geometric section. -/
def coefficients (A : SmoothBundle I (M := M))
    (e : Trivialization A.Model (TotalSpace.proj : TotalSpace A.Model A.Fiber → M))
    (T : A.Section I) (x : M) : A.Model := (e ⟨x, T x⟩).2

theorem coefficients_transition (A : SmoothBundle I (M := M))
    (e e' : Trivialization A.Model (TotalSpace.proj : TotalSpace A.Model A.Fiber → M))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (T : A.Section I)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    coefficients I A e' T x = e.coordChangeL ℝ e' x (coefficients I A e T x) := by
  rw [Trivialization.coordChangeL_apply e e' ⟨hx, hx'⟩]
  simp [coefficients, hx]

/-- Tensor coefficients are smooth wherever their bundle chart is defined. -/
theorem coefficients_contMDiffOn (A : SmoothBundle I (M := M))
    (e : Trivialization A.Model (TotalSpace.proj : TotalSpace A.Model A.Fiber → M))
    [MemTrivializationAtlas e] (T : A.Section I) :
    ContMDiffOn I 𝓘(ℝ, A.Model) ∞ (coefficients I A e T) e.baseSet := by
  intro x hx
  have h := ((contMDiffAt_section x).mp (T.contMDiff x)).contMDiffWithinAt (s := e.baseSet)
  exact contMDiffWithinAt_id.change_section_trivialization h
    ((trivializationAt A.Model A.Fiber x).mem_source.mpr
      (FiberBundle.mem_baseSet_trivializationAt' x)) (e.mem_source.mpr hx)

end SmoothBundle

/-- Finite expressions generating tangent, cotangent and mixed tensor bundles. -/
inductive Shape
  | scalar
  | tangent
  | hom (domain codomain : Shape)

namespace Shape

/-- One covariant index. -/
abbrev cotangent : Shape := .hom .tangent .scalar

/-- A scalar-valued tensor taking `s` tangent-vector arguments. -/
@[reducible] def covariant : ℕ → Shape
  | 0 => .scalar
  | s + 1 => .hom .tangent (covariant s)

/-- A tensor with `r` contravariant and `s` covariant indices.
The contravariant slots take covectors as arguments. -/
@[reducible] def mixed (r s : ℕ) : Shape :=
  Nat.rec (covariant s) (fun _ a => .hom cotangent a) r

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- Interpret tensor expressions by actual smooth hom-bundle constructions. -/
@[reducible] def bundle : Shape → SmoothBundle I (M := M)
  | .scalar => SmoothBundle.scalar I
  | .tangent => SmoothBundle.tangent I
  | .hom a b => SmoothBundle.hom I (bundle a) (bundle b)

/-- Transport a tensor through an isomorphism of tangent fibres. Cotangent
arguments transform in the inverse direction, as prescribed by `arrowCongr`. -/
def map (s : Shape) {N : Type} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y) :
    (s.bundle I).Fiber x ≃L[ℝ] (s.bundle I).Fiber y :=
  match s with
  | .scalar => ContinuousLinearEquiv.refl ℝ ℝ
  | .tangent => e
  | .hom a b => (a.map e).arrowCongr (b.map e)

variable {N P : Type} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]

@[simp] theorem map_scalar {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (r : ℝ) : map I .scalar e r = r := rfl

@[simp] theorem map_tangent {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (v : TangentSpace I x) : map I .tangent e v = e v := rfl

theorem map_hom_apply (a b : Shape) {x : M} {y : N}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (A : (a.bundle I).Fiber x →L[ℝ] (b.bundle I).Fiber x)
    (v : (a.bundle I).Fiber y) :
    (map I (.hom a b) e A : (a.bundle I).Fiber y →L[ℝ] (b.bundle I).Fiber y) v =
      map I b e (A ((map I a e).symm v)) := rfl

@[simp] theorem map_refl (s : Shape) (x : M) :
    map I s (ContinuousLinearEquiv.refl ℝ (TangentSpace I x)) =
      ContinuousLinearEquiv.refl ℝ ((s.bundle I).Fiber x) := by
  induction s with
  | scalar => rfl
  | tangent => rfl
  | hom a b ha hb =>
    change (map I a _).arrowCongr (map I b _) = _
    rw [ha, hb]
    ext L v
    rfl

@[simp] theorem map_symm (s : Shape) {x : M} {y : N}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y) :
    map I s e.symm = (map I s e).symm := by
  induction s with
  | scalar => rfl
  | tangent => rfl
  | hom a b ha hb =>
    change (map I a e.symm).arrowCongr (map I b e.symm) =
      ((map I a e).arrowCongr (map I b e)).symm
    rw [ha, hb, ContinuousLinearEquiv.arrowCongr_symm]

theorem map_trans (s : Shape) {x : M} {y : N} {z : P}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (f : TangentSpace I y ≃L[ℝ] TangentSpace I z) :
    map I s (e.trans f) = (map I s e).trans (map I s f) := by
  induction s with
  | scalar => rfl
  | tangent => rfl
  | hom a b ha hb =>
    change (map I a (e.trans f)).arrowCongr (map I b (e.trans f)) =
      ((map I a e).arrowCongr (map I b e)).trans
        ((map I a f).arrowCongr (map I b f))
    rw [ha, hb]
    ext L v
    rfl

/-- Pull a tensor back through an invertible tangent map. -/
def pullback (s : Shape) {x : M} {y : N} (e : TangentSpace I x ≃L[ℝ] TangentSpace I y) :
    (s.bundle I).Fiber y ≃L[ℝ] (s.bundle I).Fiber x := map I s e.symm

theorem pullback_trans (s : Shape) {x : M} {y : N} {z : P}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (f : TangentSpace I y ≃L[ℝ] TangentSpace I z) :
    pullback I s (e.trans f) = (pullback I s f).trans (pullback I s e) :=
  map_trans I s f.symm e.symm

/-- Contraction of matching indices commutes with tensor coordinate changes. -/
theorem trace_map (s : Shape) {x : M} {y : N}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (A : (s.bundle I).Fiber x →L[ℝ] (s.bundle I).Fiber x) :
    LinearMap.trace ℝ ((s.bundle I).Fiber y)
        (map I (.hom s s) e A).toLinearMap =
      LinearMap.trace ℝ ((s.bundle I).Fiber x) A.toLinearMap :=
  LinearMap.trace_conj' A.toLinearMap (map I s e).toLinearEquiv

/-- Partial contraction transforms in precisely the remaining tensor argument. -/
theorem partialTrace_map (a b : Shape) {x : M} {y : N}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y)
    (L : (a.bundle I).Fiber x →L[ℝ]
      (b.bundle I).Fiber x →L[ℝ] (b.bundle I).Fiber x)
    (v : (a.bundle I).Fiber y) :
    LinearMap.trace ℝ ((b.bundle I).Fiber y)
        ((map I (.hom a (.hom b b)) e L) v).toLinearMap =
      LinearMap.trace ℝ ((b.bundle I).Fiber x) (L ((map I a e).symm v)).toLinearMap := by
  rw [map_hom_apply]
  exact trace_map I b e _

end Shape
end ProjectAInos.SmoothGeometry.Tensor
