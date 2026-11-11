/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.LocallyRingedSpace
public import ProjectAInos.SmoothGeometry.SmoothPresheaf
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Diffeomorphisms, open submanifolds and smooth coordinate charts -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.Manifold

open CategoryTheory TopologicalSpace IsManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type} [TopologicalSpace N] [ChartedSpace H' N]

/-- Diffeomorphic manifolds have isomorphic smooth locally ringed spaces. -/
def isoOfDiffeomorph (e : M ≃ₘ⟮I, I'⟯ N) : locallyRingedSpace I M ≅ locallyRingedSpace I' N where
  hom := map e e.contMDiff
  inv := map e.symm e.symm.contMDiff
  hom_inv_id := by
    rw [← map_comp]
    have h : (e.symm : N → M) ∘ e = id := funext e.symm_apply_apply
    simp only [h, map_id]
  inv_hom_id := by
    rw [← map_comp]
    have h : (e : M → N) ∘ e.symm = id := funext e.apply_symm_apply
    simp only [h, map_id]

instance subtypeMap_isOpenImmersion (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion (map (I := I) (Subtype.val : U → M) contMDiff_subtype_val) :=
  inferInstanceAs (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
    (ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) (contMDiff_subtype_val (I := I))))

/-- The manifold construction commutes with open restriction, retaining C∞ operations. -/
def restrictIso (U : Opens M) :
    (locallyRingedSpace I M).restrict U.isOpenEmbedding ≅ locallyRingedSpace I U :=
  LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq
    ((locallyRingedSpace I M).ofRestrict U.isOpenEmbedding)
    (map (I := I) (Subtype.val : U → M) contMDiff_subtype_val) rfl

variable {n : ℕ} {P : Type} [TopologicalSpace P] [ChartedSpace (Fin n → ℝ) P]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ P]

/-- The source of a coordinate chart as an open set. -/
def chartSource (x : P) : Opens P := ⟨(chartAt (Fin n → ℝ) x).source, (chartAt _ x).open_source⟩

/-- The target of a coordinate chart as an open Euclidean set. -/
def chartTarget (x : P) : Opens (Fin n → ℝ) :=
  ⟨(chartAt (Fin n → ℝ) x).target, (chartAt _ x).open_target⟩

/-- A chart restricts to an actual diffeomorphism between open submanifolds. -/
def chartDiffeomorph (x : P) :
    chartSource (n := n) x ≃ₘ⟮𝓘(ℝ, Fin n → ℝ), 𝓘(ℝ, Fin n → ℝ)⟯ chartTarget (n := n) x where
  toEquiv := (chartAt (Fin n → ℝ) x).toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartTarget (n := n) x) _).mp
    intro y
    exact (contMDiffAt_of_mem_maximalAtlas
      (chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) x) y.property).comp y
        contMDiff_subtype_val.contMDiffAt
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (chartSource (n := n) x) _).mp
    intro y
    exact (contMDiffAt_symm_of_mem_maximalAtlas
      (chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) x) y.property).comp y
        contMDiff_subtype_val.contMDiffAt

end ProjectAInos.SmoothGeometry.Manifold
