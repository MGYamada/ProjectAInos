/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.CurveFamily

/-!
# Tangent fields on an open set of the model space

The tangent bundle of an open set `U` of the model space is trivialized by the inclusion. A
tangent field along a map into `U` is therefore exactly as regular as its coordinates
(`contMDiffAt_tangent_iff`), a map into `U` is as regular as its coordinates
(`contMDiffAt_iff_contDiffAt_val`), and the native velocities of a curve and of a
two-parameter family in `U` are the ordinary derivatives of their coordinates
(`curveVelocity_val`, `familyVelocity_val`). For the Minkowski coordinate metric the native
raising of a covector is that of the model (`minkowski_sharp`).
-/

@[expose] public section

noncomputable section

open Bundle Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-- The trivialization of the tangent bundle of `U` at any point is the identity on fibres. -/
theorem trivializationAt_snd (x y : U) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) y) :
    (trivializationAt (MinkowskiModel d) (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x ⟨y, v⟩).2 =
      v := by
  have hy : y ∈ (trivializationAt (MinkowskiModel d)
      (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    change y ∈ (physicalChart x).source
    simp
  have h := (trivializationAt (MinkowskiModel d)
    (TangentSpace 𝓘(ℝ, MinkowskiModel d)) x).symm_apply_apply_mk hy v
  rw [← Trivialization.symmL_apply (R := ℝ) _ hy, physicalChart_symmL] at h
  exact h

/-- A tangent field along a map into `U`, given by its coordinates, is `Cⁿ` exactly when the
map and the coordinates are. -/
theorem contMDiffAt_tangent_iff {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {f : F → U} {X : F → MinkowskiModel d} {p₀ : F} :
    ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) n
        (fun p => TotalSpace.mk' (MinkowskiModel d)
          (E := TangentSpace 𝓘(ℝ, MinkowskiModel d)) (f p) (X p)) p₀ ↔
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀ ∧ ContDiffAt ℝ n X p₀ := by
  rw [contMDiffAt_totalSpace]
  have h : (fun p => (trivializationAt (MinkowskiModel d) (TangentSpace 𝓘(ℝ, MinkowskiModel d))
      (f p₀) (⟨f p, X p⟩ : TangentBundle 𝓘(ℝ, MinkowskiModel d) U)).2) = X :=
    funext fun p => trivializationAt_snd (f p₀) (f p) (X p)
  change ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀ ∧
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n
        (fun p => (trivializationAt (MinkowskiModel d) (TangentSpace 𝓘(ℝ, MinkowskiModel d))
          (f p₀) (⟨f p, X p⟩ : TangentBundle 𝓘(ℝ, MinkowskiModel d) U)).2) p₀ ↔ _
  rw [h, contMDiffAt_iff_contDiffAt]

/-- The coordinates of a `Cⁿ` map into `U` are `Cⁿ`. -/
theorem contDiffAt_val {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    {f : F → U} {p₀ : F} (hf : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀) :
    ContDiffAt ℝ n (fun p => (f p : MinkowskiModel d)) p₀ :=
  contMDiffAt_iff_contDiffAt.mp ((contMDiff_subtype_val (U := U)).contMDiffAt.comp p₀ hf)

/-- A map into `U` is `Cⁿ` exactly when its coordinates are. -/
theorem contMDiffAt_iff_contDiffAt_val {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ∞ω} {f : F → U} {p₀ : F} :
    ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, MinkowskiModel d) n f p₀ ↔
      ContDiffAt ℝ n (fun p => (f p : MinkowskiModel d)) p₀ := by
  refine ⟨contDiffAt_val, fun h => ?_⟩
  rw [contMDiffAt_iff_target]
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr h.continuousAt, ?_⟩
  have he : (extChartAt 𝓘(ℝ, MinkowskiModel d) (f p₀) ∘ f) =
      fun p => (f p : MinkowskiModel d) := by
    funext p
    rw [Function.comp_apply, extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply]
    exact physicalChart_apply (f p₀) (f p)
  rw [he, contMDiffAt_iff_contDiffAt]
  exact h

/-- The native velocity of a curve in `U` is the derivative of its coordinates. -/
theorem curveVelocity_val {γ : ℝ → U} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, MinkowskiModel d) γ t) :
    (curveVelocity γ t : MinkowskiModel d) = deriv (fun s => (γ s : MinkowskiModel d)) t := by
  have h := chartTangentMap_curveVelocity (physicalChart_mem (γ t))
    (by simp : γ t ∈ (physicalChart (γ t)).source) hγ
  have he : (physicalChart (γ t) ∘ γ) = fun s => (γ s : MinkowskiModel d) :=
    funext fun s => physicalChart_apply (γ t) (γ s)
  rw [physicalChart_tangentMap, he] at h
  exact h

/-- The native parameter velocity of a family in `U` is the derivative of its coordinates. -/
theorem familyVelocity_val {Γ : ℝ × ℝ → U} {z : ℝ × ℝ} (v : ℝ × ℝ)
    (hΓ : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, MinkowskiModel d) Γ z) :
    (familyVelocity Γ v z : MinkowskiModel d) =
      fderiv ℝ (fun q => (Γ q : MinkowskiModel d)) z v := by
  have h := chartTangentMap_familyVelocity v (physicalChart_mem (Γ z))
    (by simp : Γ z ∈ (physicalChart (Γ z)).source) hΓ
  have he : (physicalChart (Γ z) ∘ Γ) = fun q => (Γ q : MinkowskiModel d) :=
    funext fun q => physicalChart_apply (Γ z) (Γ q)
  rw [physicalChart_tangentMap, he] at h
  exact h

/-- For the Minkowski coordinate metric the native raising of a covector is that of the
model. -/
theorem minkowski_sharp (x : U) (α : MinkowskiModel d →L[ℝ] ℝ) :
    ((minkowski (σ := σ) (U := U)).toLorentzMetric.sharp x α : MinkowskiModel d) =
      Minkowski.sharp σ α := by
  apply ((minkowski (σ := σ) (U := U)).toLorentzMetric.flat x).injective
  refine (LorentzMetric.flat_sharp _ x α).trans ?_
  have h : Minkowski.flat σ (Minkowski.sharp σ α) = α := (Minkowski.flat σ).apply_symm_apply α
  ext w
  change α w = minkowskiForm σ d (Minkowski.sharp σ α) w
  rw [← Minkowski.flat_apply, h]

end ProjectAinos.SmoothGeometry.CoordinateMetric
