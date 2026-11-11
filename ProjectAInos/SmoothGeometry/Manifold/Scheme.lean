/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.Euclidean
public import ProjectAInos.SmoothGeometry.Manifold.Charts
public import ProjectAInos.SmoothGeometry.Restrict

/-! # Smooth manifolds as C∞ schemes

Finite-dimensional boundaryless smooth manifolds with Euclidean chart models
are C∞ schemes. The structure sheaf is the actual smooth-function sheaf.
No global chart, global frame, Hausdorffness or countability premise is used
in the local-affine proof.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.Manifold

open CategoryTheory TopologicalSpace

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- Each coordinate neighbourhood is a scheme through its open Euclidean chart. -/
def chartScheme (x : M) : Scheme :=
  Scheme.ofOpenImmersion (euclideanScheme n)
    ((isoOfDiffeomorph (chartDiffeomorph (n := n) x)).hom ≫
      map (Subtype.val : chartTarget (n := n) x → (Fin n → ℝ)) contMDiff_subtype_val)

/-- The common scheme construction for Euclidean space and curved manifolds. -/
def scheme : Scheme :=
  Scheme.ofOpenCover (locallyRingedSpace 𝓘(ℝ, Fin n → ℝ) M) fun (x : M) =>
    ⟨chartScheme n M x,
      map (Subtype.val : chartSource (n := n) x → M) contMDiff_subtype_val,
      ⟨⟨x, mem_chart_source (Fin n → ℝ) x⟩, rfl⟩, inferInstance⟩

variable {n M} {m : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (Fin m → ℝ) N]
  [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ N]

/-- A smooth map of manifolds induces a morphism of their constructed C∞ schemes. -/
def schemeMap (f : M → N) (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) ∞ f) :
    scheme n M ⟶ scheme m N := ⟨map f hf⟩

@[simp] theorem schemeMap_id : schemeMap (M := M) (n := n) id contMDiff_id = 𝟙 _ := rfl

variable {k : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (Fin k → ℝ) P]
  [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ P]

theorem schemeMap_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin k → ℝ) ∞ g) :
    schemeMap (g ∘ f) (hg.comp hf) = schemeMap f hf ≫ schemeMap g hg := rfl

end ProjectAInos.SmoothGeometry.Manifold
