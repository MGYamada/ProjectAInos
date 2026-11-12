/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Bundle
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Native form pullback along arbitrary smooth maps

Pullback uses the actual tangent map in every alternating slot. The source
and target may have different dimensions; no inverse tangent map is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  (J : ModelWithCorners ℝ F H') [TopologicalSpace N] [ChartedSpace H' N]

/-- Pullback on actual tangent fibres, before imposing regularity. -/
def nativePullback {k : ℕ} (f : M → N) (α : NativeForm J N k) : NativeForm I M k :=
  fun x => (α (f x)).compContinuousLinearMap (mfderiv I J f x)

@[simp] theorem nativePullback_apply {k : ℕ} (f : M → N) (α : NativeForm J N k)
    (x : M) (v : Fin k → TangentSpace I x) :
    nativePullback I J f α x v = α (f x) (fun i => mfderiv I J f x (v i)) := rfl

/-- In degree zero pullback is scalar composition, even for constant maps. -/
theorem nativePullback_degreeZero (f : M → N) (α : NativeForm J N 0) (x : M)
    (v : Fin 0 → TangentSpace I x) :
    nativePullback I J f α x v = α (f x) (fun i => Fin.elim0 i) := by
  rw [nativePullback_apply]
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem nativePullback_id {k : ℕ} (α : NativeForm I M k) :
    nativePullback I I id α = α := by
  funext x
  ext v
  simp only [nativePullback_apply, mfderiv_id]
  rfl

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- Pullback regularity is local at the source point and its image. -/
theorem contMDiffAt_nativePullback {k : ℕ} {f : M → N} {α : NativeForm J N k} {x : M}
    (hf : ContMDiffAt I J ∞ f x)
    (hα : ContMDiffAt J (J.prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) (f x)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (nativePullback I J f α y)) x := by
  apply (contMDiffAt_form_iff I).mpr
  have hL := hf.mfderiv_const (m := ∞) (by simp)
  have hα := ((contMDiffAt_form_iff J).mp hα).comp x hf
  apply (hL.compContinuousLinearMapCLM.clm_apply hα).congr_of_eventuallyEq
  have hN : ∀ᶠ y in 𝓝 x, f y ∈ (trivializationAt F (TangentSpace J) (f x)).baseSet :=
    hf.continuousAt
      ((trivializationAt F (TangentSpace J) (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x)))
  filter_upwards [hN] with y hy
  ext v
  change α (f y) (fun i => mfderiv I J f y
      ((trivializationAt E (TangentSpace I) x).symmL ℝ y (v i))) =
    α (f y) (fun i => (trivializationAt F (TangentSpace J) (f x)).symmL ℝ (f y)
      ((trivializationAt F (TangentSpace J) (f x)).continuousLinearMapAt ℝ (f y)
        (mfderiv I J f y ((trivializationAt E (TangentSpace I) x).symmL ℝ y (v i)))))
  congr 1
  funext i
  exact ((trivializationAt F (TangentSpace J) (f x)).symmL_continuousLinearMapAt hy _).symm

/-- A smooth map pulls smooth native forms back to smooth native forms. -/
theorem contMDiff_nativePullback {k : ℕ} (f : C^∞⟮I, M; J, N⟯)
    (α : SmoothForm J N k) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x
        (nativePullback I J f (fun y => α y) x)) :=
  fun x => contMDiffAt_nativePullback I J (f.contMDiff x) (α.contMDiff (f x))

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Native pullback depends only on the germ of its map. -/
theorem nativePullback_congr_map {k : ℕ} {f g : M → N} {x : M}
    (h : f =ᶠ[𝓝 x] g) (α : NativeForm J N k) :
    nativePullback I J f α x = nativePullback I J g α x := by
  unfold nativePullback
  rw [h.mfderiv_eq, h.eq_of_nhds]
  rfl

/-- Bundled smooth pullback, including noninvertible and dimension-changing maps. -/
def smoothPullback {k : ℕ} (f : C^∞⟮I, M; J, N⟯) (α : SmoothForm J N k) :
    SmoothForm I M k :=
  ⟨nativePullback I J f (fun y => α y), contMDiff_nativePullback I J f α⟩

@[simp] theorem smoothPullback_apply {k : ℕ} (f : C^∞⟮I, M; J, N⟯)
    (α : SmoothForm J N k) (x : M) (v : Fin k → TangentSpace I x) :
    smoothPullback I J f α x v = α (f x) (fun i => mfderiv I J f x (v i)) := rfl

@[simp] theorem smoothPullback_id {k : ℕ} (α : SmoothForm I M k) :
    smoothPullback I I (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) α = α := by
  ext x v
  change α x (fun i => mfderiv I I id x (v i)) = α x v
  rw [mfderiv_id]
  rfl

/-- A constant map annihilates every form of positive degree. -/
@[simp] theorem smoothPullback_const (k : ℕ) (y : N) (α : SmoothForm J N (k + 1)) :
    smoothPullback I J (ContMDiffMap.const y : C^∞⟮I, M; J, N⟯) α = 0 := by
  ext x v
  change α y (fun i => mfderiv I J (fun _ : M => y) x (v i)) = 0
  rw [mfderiv_const]
  exact (α y).map_zero

/-- Pullback is linear in the form, for a fixed smooth map. -/
def smoothPullbackLinear {k : ℕ} (f : C^∞⟮I, M; J, N⟯) :
    SmoothForm J N k →ₗ[ℝ] SmoothForm I M k where
  toFun := smoothPullback I J f
  map_add' α β := by ext x v; rfl
  map_smul' r α := by ext x v; rfl

@[simp] theorem smoothPullbackLinear_apply {k : ℕ} (f : C^∞⟮I, M; J, N⟯)
    (α : SmoothForm J N k) : smoothPullbackLinear I J f α = smoothPullback I J f α := rfl

variable {G H'' P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  (K : ModelWithCorners ℝ G H'') [TopologicalSpace P] [ChartedSpace H'' P]
  [IsManifold K ∞ P]

omit [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold K ∞ P] in
/-- The native composition law only needs differentiability at the relevant points. -/
theorem nativePullback_comp_at {k : ℕ} {f : M → N} {g : N → P} {x : M}
    (hf : MDifferentiableAt I J f x) (hg : MDifferentiableAt J K g (f x))
    (α : NativeForm K P k) :
    nativePullback I K (g ∘ f) α x =
      nativePullback I J f (nativePullback J K g α) x := by
  ext v
  simp only [nativePullback_apply, mfderiv_comp x hg hf]
  rfl

/-- Pullback reverses composition as an equality of smooth sections. -/
theorem smoothPullback_comp {k : ℕ} (f : C^∞⟮I, M; J, N⟯)
    (g : C^∞⟮J, N; K, P⟯) (α : SmoothForm K P k) :
    smoothPullback I K (g.comp f) α = smoothPullback I J f (smoothPullback J K g α) := by
  ext x v
  change α (g (f x)) (fun i => mfderiv I K (g ∘ f) x (v i)) =
    α (g (f x)) (fun i => mfderiv J K g (f x) (mfderiv I J f x (v i)))
  rw [mfderiv_comp x (g.contMDiff.mdifferentiableAt (by simp))
    (f.contMDiff.mdifferentiableAt (by simp))]
  rfl

end ProjectAInos.SmoothGeometry.DifferentialForm
