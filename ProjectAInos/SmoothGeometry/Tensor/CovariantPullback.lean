/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.HomPullback
public import ProjectAInos.SmoothGeometry.Tensor.Pullback

/-! # Covariant tensor pullback along arbitrary smooth maps

Every covariant slot is precomposed with the actual tangent map. Source
and target dimensions may differ, and no injectivity, surjectivity or
inverse derivative is required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor.Shape

variable {E H M F H' N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] (J : ModelWithCorners ℝ F H')
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Pull back a covariant tensor through any continuous linear tangent map.
The map between native tensor fibres is itself continuous linear. -/
def covariantPullback (n : ℕ) {x : M} {y : N}
    (L : TangentSpace I x →L[ℝ] TangentSpace J y) :
    ((covariant n).bundle J).Fiber y →L[ℝ] ((covariant n).bundle I).Fiber x :=
  match n with
  | 0 => ContinuousLinearMap.id ℝ ℝ
  | n + 1 => (postcomp (TangentSpace I x) (covariantPullback n L)).comp
      (precomp (((covariant n).bundle J).Fiber y) L)

@[simp] theorem covariantPullback_zero {x : M} {y : N}
    (L : TangentSpace I x →L[ℝ] TangentSpace J y) (r : ℝ) :
    covariantPullback I J 0 L r = r := rfl

/-- Evaluation removes one slot, applying the tangent map to its argument. -/
@[simp] theorem covariantPullback_succ_apply (n : ℕ) {x : M} {y : N}
    (L : TangentSpace I x →L[ℝ] TangentSpace J y)
    (T : ((covariant (n + 1)).bundle J).Fiber y) (v : TangentSpace I x) :
    covariantPullback I J (n + 1) L T v = covariantPullback I J n L (T (L v)) := rfl

@[simp] theorem covariantPullback_id (n : ℕ) (x : M) :
    covariantPullback I I n (ContinuousLinearMap.id ℝ (TangentSpace I x)) =
      ContinuousLinearMap.id ℝ (((covariant n).bundle I).Fiber x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext T v
    change covariantPullback I I n (ContinuousLinearMap.id ℝ (TangentSpace I x)) (T v) = T v
    rw [ih]
    rfl

variable {G H'' P : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H''] (K : ModelWithCorners ℝ G H'')
  [TopologicalSpace P] [ChartedSpace H'' P]

/-- Smooth tangent maps give smooth covariant pullback maps in bundle charts. -/
theorem contMDiffAt_covariantPullback (n : ℕ) {a : P → M} {b : P → N} {p : P}
    (ha : ContMDiffAt K I ∞ a p) (hb : ContMDiffAt K J ∞ b p)
    (L : ∀ q, TangentSpace I (a q) →L[ℝ] TangentSpace J (b q))
    (hL : ContMDiffAt K 𝓘(ℝ, E →L[ℝ] F) ∞
      (fun q => inCoordinates E (TangentSpace I) F (TangentSpace J)
        (a p) (a q) (b p) (b q) (L q)) p) :
    ContMDiffAt K 𝓘(ℝ, ((covariant n).bundle J (M := N)).Model →L[ℝ]
      ((covariant n).bundle I (M := M)).Model) ∞
      (fun q => inCoordinates ((covariant n).bundle J (M := N)).Model
        ((covariant n).bundle J (M := N)).Fiber
        ((covariant n).bundle I (M := M)).Model ((covariant n).bundle I (M := M)).Fiber
        (b p) (b q) (a p) (a q) (covariantPullback I J n (L q))) p := by
  induction n with
  | zero =>
    have hc : ContMDiffAt K 𝓘(ℝ, ℝ →L[ℝ] ℝ) ∞
        (fun _ : P => ContinuousLinearMap.id ℝ ℝ) p := contMDiffAt_const
    simpa [covariantPullback, covariant, bundle, inCoordinates] using hc
  | succ n ih =>
    exact SmoothBundle.contMDiffAt_homPullback J I K
      (SmoothBundle.tangent J) ((covariant n).bundle J)
      (SmoothBundle.tangent I) ((covariant n).bundle I) hb ha L
      (fun q => covariantPullback I J n (L q)) hL ih

/-- Pullback of a smooth covariant tensor by an arbitrary smooth map. -/
def covariantPullbackField (n : ℕ) (f : C^∞⟮I, M; J, N⟯)
    (T : ((covariant n).bundle J (M := N)).Section J) :
    ((covariant n).bundle I (M := M)).Section I :=
  ⟨fun x => covariantPullback I J n (mfderiv I J f x) (T (f x)), by
    intro x
    have hL := contMDiffAt_covariantPullback I J I n (p := x) contMDiffAt_id
      f.contMDiff.contMDiffAt (fun q => mfderiv I J f q)
      (f.contMDiff.contMDiffAt.mfderiv_const (m := ∞) (by simp))
    exact hL.clm_apply_of_inCoordinates ((T.contMDiff.comp f.contMDiff) x)
      contMDiffAt_id⟩

@[simp] theorem covariantPullbackField_apply (n : ℕ) (f : C^∞⟮I, M; J, N⟯)
    (T : ((covariant n).bundle J (M := N)).Section J) (x : M) :
    covariantPullbackField I J n f T x =
      covariantPullback I J n (mfderiv I J f x) (T (f x)) := rfl

theorem covariantPullbackField_one_apply (f : C^∞⟮I, M; J, N⟯)
    (T : (cotangent.bundle J (M := N)).Section J) (x : M) (v : TangentSpace I x) :
    covariantPullbackField I J 1 f T x v = T (f x) (mfderiv I J f x v) := rfl

theorem covariantPullbackField_two_apply (f : C^∞⟮I, M; J, N⟯)
    (T : ((covariant 2).bundle J (M := N)).Section J) (x : M)
    (v w : TangentSpace I x) :
    covariantPullbackField I J 2 f T x v w =
      T (f x) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

@[simp] theorem covariantPullbackField_id (n : ℕ)
    (T : ((covariant n).bundle I (M := M)).Section I) :
    covariantPullbackField I I n (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) T = T := by
  ext x : 1
  change covariantPullback I I n (mfderiv I I id x) (T x) = T x
  rw [mfderiv_id, covariantPullback_id]
  rfl

/-- Constant maps annihilate every positive covariant rank. -/
@[simp] theorem covariantPullback_zeroMap (n : ℕ) {x : M} {y : N} :
    covariantPullback I J (n + 1) (0 : TangentSpace I x →L[ℝ] TangentSpace J y) = 0 := by
  ext T v
  change covariantPullback I J n 0 (T 0) = 0
  simp

@[simp] theorem covariantPullbackField_const (n : ℕ) (y : N)
    (T : ((covariant (n + 1)).bundle J (M := N)).Section J) :
    covariantPullbackField I J (n + 1) (ContMDiffMap.const y : C^∞⟮I, M; J, N⟯) T = 0 := by
  ext x : 1
  change covariantPullback I J (n + 1) (mfderiv I J (fun _ : M => y) x) (T y) = 0
  rw [mfderiv_const, covariantPullback_zeroMap]
  rfl

section Diffeomorphism

variable {N' : Type} [TopologicalSpace N'] [ChartedSpace H N'] [IsManifold I ∞ N']

/-- On invertible tangent maps this construction agrees with mixed-tensor pullback. -/
theorem covariantPullback_eq_pullback (n : ℕ) {x : M} {y : N'}
    (e : TangentSpace I x ≃L[ℝ] TangentSpace I y) :
    covariantPullback I I n e.toContinuousLinearMap =
      (pullback I (covariant n) e).toContinuousLinearMap := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext T v
    change covariantPullback I I n e.toContinuousLinearMap (T (e v)) =
      pullback I (covariant n) e (T (e v))
    rw [ih]
    rfl

/-- The existing diffeomorphism API is preserved as an equality of smooth sections. -/
theorem covariantPullbackField_diffeomorph (n : ℕ) (f : M ≃ₘ⟮I, I⟯ N')
    (T : ((covariant n).bundle I (M := N')).Section I) :
    covariantPullbackField I I n f.toContMDiffMap T = pullbackField I (covariant n) f T := by
  ext x : 1
  change covariantPullback I I n (mfderiv I I f x) (T (f x)) =
    pullback I (covariant n) (tangentEquiv I f x) (T (f x))
  rw [← tangentEquiv_toContinuousLinearMap, covariantPullback_eq_pullback]
  rfl

end Diffeomorphism

variable [FiniteDimensional ℝ G] [IsManifold K ∞ P]

/-- Fibrewise pullback reverses composition, including dimension-changing maps. -/
theorem covariantPullback_comp (n : ℕ) {x : M} {y : N} {z : P}
    (L : TangentSpace I x →L[ℝ] TangentSpace J y)
    (Q : TangentSpace J y →L[ℝ] TangentSpace K z) :
    covariantPullback I K n (Q.comp L) =
      (covariantPullback I J n L).comp (covariantPullback J K n Q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext T v
    change covariantPullback I K n (Q.comp L) (T (Q (L v))) =
      covariantPullback I J n L (covariantPullback J K n Q (T (Q (L v))))
    rw [ih]
    rfl

/-- Pullback reverses composition as an equality of smooth tensor fields. -/
theorem covariantPullbackField_comp (n : ℕ) (f : C^∞⟮I, M; J, N⟯)
    (g : C^∞⟮J, N; K, P⟯) (T : ((covariant n).bundle K (M := P)).Section K) :
    covariantPullbackField I K n (g.comp f) T =
      covariantPullbackField I J n f (covariantPullbackField J K n g T) := by
  ext x : 1
  change covariantPullback I K n (mfderiv I K (g ∘ f) x) (T (g (f x))) =
    covariantPullback I J n (mfderiv I J f x)
      (covariantPullback J K n (mfderiv J K g (f x)) (T (g (f x))))
  rw [mfderiv_comp x (g.contMDiff.mdifferentiableAt (by simp))
    (f.contMDiff.mdifferentiableAt (by simp)), covariantPullback_comp I J K]
  rfl

end ProjectAInos.SmoothGeometry.Tensor.Shape
