/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.HomMap
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Smooth tensor transport and pullback

The recursive tensor maps preserve smoothness in native bundle coordinates.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor.Shape

variable {E H M N P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [TopologicalSpace P] [ChartedSpace H P]

/-- Smoothness of tensor transport read in the native local bundle charts. -/
def SmoothTransportAt (s : Shape) (a : P → M) (b : P → N)
    (e : ∀ q, TangentSpace I (a q) ≃L[ℝ] TangentSpace I (b q)) (p : P) : Prop :=
  ContMDiffAt I 𝓘(ℝ, (s.bundle I (M := M)).Model →L[ℝ]
    (s.bundle I (M := N)).Model) ∞
    (fun q => inCoordinates (s.bundle I (M := M)).Model (s.bundle I (M := M)).Fiber
      (s.bundle I (M := N)).Model (s.bundle I (M := N)).Fiber
      (a p) (a q) (b p) (b q) (map I s (e q)).toContinuousLinearMap) p

/-- Smooth tangent isomorphisms induce smooth transport in every tensor type.
Both directions are proved together, because hom tensors reverse their input slot. -/
theorem smoothTransportAt (s : Shape) {a : P → M} {b : P → N} {p : P}
    (e : ∀ q, TangentSpace I (a q) ≃L[ℝ] TangentSpace I (b q))
    (ha : ContMDiffAt I I ∞ a p) (hb : ContMDiffAt I I ∞ b p)
    (he : SmoothTransportAt I .tangent a b e p)
    (hei : SmoothTransportAt I .tangent b a (fun q => (e q).symm) p) :
    SmoothTransportAt I s a b e p ∧
      SmoothTransportAt I s b a (fun q => (e q).symm) p := by
  induction s with
  | scalar =>
    have hc : ContMDiffAt I 𝓘(ℝ, ℝ →L[ℝ] ℝ) ∞
        (fun _ : P => ContinuousLinearMap.id ℝ ℝ) p := contMDiffAt_const
    constructor <;> simpa [SmoothTransportAt, map, inCoordinates] using hc
  | tangent => exact ⟨he, hei⟩
  | hom s t hs ht =>
    constructor
    · apply SmoothBundle.contMDiffAt_homMap I (s.bundle I) (t.bundle I)
        (s.bundle I) (t.bundle I) ha hb (fun q => map I s (e q)) (fun q => map I t (e q))
      · simpa only [SmoothTransportAt, map_symm] using hs.2
      · exact ht.1
    · apply SmoothBundle.contMDiffAt_homMap I (s.bundle I) (t.bundle I)
        (s.bundle I) (t.bundle I) hb ha (fun q => map I s (e q).symm)
        (fun q => map I t (e q).symm)
      · simpa only [SmoothTransportAt, map_symm, ContinuousLinearEquiv.symm_symm] using hs.1
      · exact ht.2

/-- An invertible smooth tangent family has smooth inverse and tensor transports. -/
theorem smoothTransportAt_of_tangent (s : Shape) {a : P → M} {b : P → N} {p : P}
    (e : ∀ q, TangentSpace I (a q) ≃L[ℝ] TangentSpace I (b q))
    (ha : ContMDiffAt I I ∞ a p) (hb : ContMDiffAt I I ∞ b p)
    (he : SmoothTransportAt I .tangent a b e p) :
    SmoothTransportAt I s a b e p ∧
      SmoothTransportAt I s b a (fun q => (e q).symm) p :=
  smoothTransportAt I s e ha hb he
    (SmoothBundle.contMDiffAt_inverse I (SmoothBundle.tangent I) (SmoothBundle.tangent I)
      ha hb e he)

/-- The actual derivative of a diffeomorphism, viewed as a tangent-fibre equivalence. -/
def tangentEquiv (f : M ≃ₘ⟮I, I⟯ N) (x : M) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (f x) :=
  f.mfderivToContinuousLinearEquiv (by simp) x

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
@[simp] theorem tangentEquiv_toContinuousLinearMap (f : M ≃ₘ⟮I, I⟯ N) (x : M) :
    (tangentEquiv I f x).toContinuousLinearMap = mfderiv I I f x :=
  f.mfderivToContinuousLinearEquiv_coe (by simp)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
@[simp] theorem tangentEquiv_apply (f : M ≃ₘ⟮I, I⟯ N) (x : M)
    (v : TangentSpace I x) : tangentEquiv I f x v = mfderiv I I f x v :=
  congrArg (fun L => L v) (tangentEquiv_toContinuousLinearMap I f x)

/-- Smoothness of the derivative and inverse derivative yields smooth transport
of every finite tensor type, with no assumed tensor-field regularity theorem. -/
theorem smoothTransportAt_diffeomorph (s : Shape) (f : M ≃ₘ⟮I, I⟯ N) (x : M) :
    SmoothTransportAt I s id f (tangentEquiv I f) x ∧
      SmoothTransportAt I s f id (fun y => (tangentEquiv I f y).symm) x := by
  apply smoothTransportAt_of_tangent I s (tangentEquiv I f) contMDiffAt_id f.contMDiff.contMDiffAt
  simp only [SmoothTransportAt, map, tangentEquiv_toContinuousLinearMap]
  convert! (f.contMDiff.contMDiffAt (x := x)).mfderiv_const (m := ∞) (by simp) using 1

/-- Pullback of a smooth tensor field by a diffeomorphism is smooth on the
actual source tensor bundle. The map in each fibre is the inverse derivative. -/
def pullbackField (s : Shape) (f : M ≃ₘ⟮I, I⟯ N)
    (T : (s.bundle I (M := N)).Section I) : (s.bundle I (M := M)).Section I :=
  ⟨fun x => pullback I s (tangentEquiv I f x) (T (f x)), by
    intro x
    exact (smoothTransportAt_diffeomorph I s f x).2.clm_apply_of_inCoordinates
      ((T.contMDiff.comp f.contMDiff) x) contMDiffAt_id⟩

@[simp] theorem pullbackField_apply (s : Shape) (f : M ≃ₘ⟮I, I⟯ N)
    (T : (s.bundle I (M := N)).Section I) (x : M) :
    pullbackField I s f T x = pullback I s (tangentEquiv I f x) (T (f x)) := rfl

/-- The usual covector pullback formula uses the manifold derivative. -/
theorem pullbackField_covector_apply (f : M ≃ₘ⟮I, I⟯ N)
    (T : (cotangent.bundle I (M := N)).Section I) (x : M) (v : TangentSpace I x) :
    pullbackField I cotangent f T x v = T (f x) (mfderiv I I f x v) := by
  change T (f x) ((tangentEquiv I f x).symm.symm v) = _
  rw [ContinuousLinearEquiv.symm_symm, tangentEquiv_apply]

/-- Covariant two-tensor pullback transforms both arguments by the derivative. -/
theorem pullbackField_covariantTwo_apply (f : M ≃ₘ⟮I, I⟯ N)
    (T : ((mixed 0 2).bundle I (M := N)).Section I) (x : M)
    (v w : TangentSpace I x) :
    pullbackField I (mixed 0 2) f T x v w =
      T (f x) (mfderiv I I f x v) (mfderiv I I f x w) := by
  change T (f x) ((tangentEquiv I f x).symm.symm v)
    ((tangentEquiv I f x).symm.symm w) = _
  simp only [ContinuousLinearEquiv.symm_symm, tangentEquiv_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
@[simp] theorem tangentEquiv_refl (x : M) :
    tangentEquiv I (Diffeomorph.refl I M ∞) x =
      ContinuousLinearEquiv.refl ℝ (TangentSpace I x) := by
  ext v
  rw [tangentEquiv_apply]
  change mfderiv I I id x v = v
  rw [mfderiv_id]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
theorem tangentEquiv_trans [IsManifold I ∞ P]
    (f : M ≃ₘ⟮I, I⟯ N) (g : N ≃ₘ⟮I, I⟯ P) (x : M) :
    tangentEquiv I (f.trans g) x =
      (tangentEquiv I f x).trans (tangentEquiv I g (f x)) := by
  ext v
  change tangentEquiv I (f.trans g) x v = tangentEquiv I g (f x) (tangentEquiv I f x v)
  rw [tangentEquiv_apply I (f.trans g) x v,
    tangentEquiv_apply I g (f x) (tangentEquiv I f x v), tangentEquiv_apply I f x v]
  rw [Diffeomorph.coe_trans, mfderiv_comp x (g.contMDiff.mdifferentiableAt (by simp))
    (f.contMDiff.mdifferentiableAt (by simp))]
  rfl

@[simp] theorem pullbackField_refl (s : Shape) (T : (s.bundle I (M := M)).Section I) :
    pullbackField I s (Diffeomorph.refl I M ∞) T = T := by
  ext x
  simp [pullbackField_apply, pullback]

/-- Pullback reverses composition, as an equality of smooth tensor fields. -/
theorem pullbackField_trans [IsManifold I ∞ P] (s : Shape)
    (f : M ≃ₘ⟮I, I⟯ N) (g : N ≃ₘ⟮I, I⟯ P)
    (T : (s.bundle I (M := P)).Section I) :
    pullbackField I s (f.trans g) T = pullbackField I s f (pullbackField I s g T) := by
  ext x
  simp only [pullbackField_apply, tangentEquiv_trans, pullback_trans,
    ContinuousLinearEquiv.trans_apply, Diffeomorph.coe_trans, Function.comp_apply]

@[simp] theorem pullbackField_symm (s : Shape) (f : M ≃ₘ⟮I, I⟯ N)
    (T : (s.bundle I (M := M)).Section I) :
    pullbackField I s f (pullbackField I s f.symm T) = T := by
  rw [← pullbackField_trans, Diffeomorph.self_trans_symm, pullbackField_refl]

/-- Trace contraction of a tensor field commutes with pullback. -/
theorem contract_pullbackField (s : Shape) (f : M ≃ₘ⟮I, I⟯ N)
    (T : ((hom s s).bundle I (M := N)).Section I) (x : M) :
    SmoothBundle.contract I (s.bundle I (M := M)) (pullbackField I (hom s s) f T) x =
      SmoothBundle.contract I (s.bundle I (M := N)) T (f x) :=
  trace_map I s (tangentEquiv I f x).symm (T (f x))

/-- Partial contraction also commutes with pullback, retaining the other slot. -/
theorem partialContract_pullbackField (s t : Shape) (f : M ≃ₘ⟮I, I⟯ N)
    (T : ((hom s (hom t t)).bundle I (M := N)).Section I) :
    SmoothBundle.partialContract I (s.bundle I (M := M)) (t.bundle I (M := M))
      (pullbackField I (hom s (hom t t)) f T) =
    pullbackField I (hom s scalar) f
      (SmoothBundle.partialContract I (s.bundle I (M := N)) (t.bundle I (M := N)) T) := by
  ext x v
  change fiberTrace (t.bundle I (M := M)).Model x
      ((map I (hom s (hom t t)) (tangentEquiv I f x).symm (T (f x))) v) =
    fiberTrace (t.bundle I (M := N)).Model (f x)
      (T (f x) ((map I s (tangentEquiv I f x).symm).symm v))
  rw [fiberTrace_apply, fiberTrace_apply]
  exact partialTrace_map I s t (tangentEquiv I f x).symm (T (f x)) v

end ProjectAInos.SmoothGeometry.Tensor.Shape
