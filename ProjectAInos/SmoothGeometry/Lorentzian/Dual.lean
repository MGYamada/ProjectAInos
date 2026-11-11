/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian
public import ProjectAInos.SmoothGeometry.Minkowski.Dual

/-! # Metric duality on Lorentz manifolds

The metric identifies each actual tangent space with its continuous dual.
Pointwise signature witnesses prove invertibility; no smooth or global frame
is chosen as part of the public metric-duality interface.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

theorem form_bijective (x : M) : Function.Bijective (g.form x) := by
  obtain ⟨e, he⟩ := g.signature x
  let f := (e.trans (Minkowski.flat σ)).trans
    (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
  have hf : (f : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) = g.form x := by
    funext v
    ext w
    simp [f, he]
  rw [← hf]
  exact f.bijective

/-- Lower a tangent vector with the metric, as a continuous linear equivalence. -/
def flat (x : M) : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ]
    (TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective (g.form x).toLinearMap (g.form_bijective x)).toContinuousLinearEquiv

/-- Raise a cotangent vector with the inverse metric. -/
def sharp (x : M) : (TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) ≃L[ℝ]
    TangentSpace 𝓘(ℝ, MinkowskiModel d) x := (g.flat x).symm

@[simp] theorem flat_apply (x : M) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.flat x v w = g.form x v w := rfl

@[simp] theorem flat_toContinuousLinearMap (x : M) :
    (g.flat x).toContinuousLinearMap = g.form x := rfl

/-- The metric dual is a smooth bundle map. -/
theorem flat_smooth : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod
      𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)) ∞
    (fun x => TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
      x (g.flat x).toContinuousLinearMap) := g.smooth

@[simp] theorem sharp_flat (x : M) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.sharp x (g.flat x v) = v := (g.flat x).symm_apply_apply v

@[simp] theorem flat_sharp (x : M) (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.flat x (g.sharp x α) = α := (g.flat x).apply_symm_apply α

@[simp] theorem form_sharp_left (x : M)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.form x (g.sharp x α) v = α v :=
  congrArg (fun β => β v) (g.flat_sharp x α)

@[simp] theorem form_sharp_right (x : M)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.form x v (g.sharp x α) = α v := by
  rw [g.symmetric, g.form_sharp_left]

theorem sharp_eq_iff (x : M)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.sharp x α = v ↔ ∀ w, g.form x v w = α w := by
  constructor
  · rintro rfl w
    exact g.form_sharp_left x α w
  · intro h
    apply (g.flat x).injective
    rw [g.flat_sharp]
    ext w
    exact (h w).symm

/-- Lowering a smooth vector field gives a smooth cotangent section. -/
def lower
    (v : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x)⟯) :
    Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯ :=
  ⟨fun x => g.flat x (v x), g.smooth.clm_bundle_apply v.contMDiff⟩

@[simp] theorem lower_apply
    (v : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x)⟯)
    (x : M) (w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.lower v x w = g.form x (v x) w := rfl

/-- The inverse metric is a smooth section of the hom bundle. In local bundle
coordinates this is smooth inversion of a family of invertible linear maps. -/
theorem sharp_smooth : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod
      𝓘(ℝ, (MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)) ∞
    (fun x => TotalSpace.mk' ((MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)
      x (g.sharp x).toContinuousLinearMap) := by
  let T := fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x
  let C := fun x : M => T x →L[ℝ] ℝ
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hg := (contMDiffAt_hom_bundle _).mp (g.smooth x₀)
  have hi : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      𝓘(ℝ, (MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d) ∞
      (fun x => (inCoordinates (MinkowskiModel d) T (MinkowskiModel d →L[ℝ] ℝ) C
        x₀ x x₀ x (g.form x)).inverse) x₀ := by
    apply ContMDiffAt.comp (g := ContinuousLinearMap.inverse) x₀ _ hg.2
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    exact isInvertible_equiv.comp
      ((show (g.form x₀).IsInvertible from ⟨g.flat x₀, rfl⟩).comp isInvertible_equiv)
  apply hi.congr_of_eventuallyEq
  have hT : (trivializationAt (MinkowskiModel d) T x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  have hC : (trivializationAt (MinkowskiModel d →L[ℝ] ℝ) C x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [hT, hC] with x hx hx'
  rw [inCoordinates_eq hx hx', inCoordinates_eq hx' hx]
  rw [← g.flat_toContinuousLinearMap x]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm,
    inverse_equiv, sharp, ContinuousLinearMap.comp_assoc]

/-- Raising a smooth cotangent section gives a smooth tangent section. -/
def raise
    (α : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯) :
    Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x)⟯ :=
  ⟨fun x => g.sharp x (α x), g.sharp_smooth.clm_bundle_apply α.contMDiff⟩

@[simp] theorem raise_apply
    (α : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯) (x : M) :
    g.raise α x = g.sharp x (α x) := rfl

@[simp] theorem raise_lower
    (v : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x)⟯) :
    g.raise (g.lower v) = v := by
  ext x
  exact g.sharp_flat x (v x)

@[simp] theorem lower_raise
    (α : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯) :
    g.lower (g.raise α) = α := by
  ext x w
  exact g.form_sharp_left x (α x) w

/-- The inverse-metric pairing of smooth one-forms is a smooth scalar. -/
def inversePairing
    (α β : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯) :
    C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ :=
  g.pairing (g.raise α) (g.raise β)

@[simp] theorem inversePairing_apply
    (α β : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ)⟯) (x : M) :
    g.inversePairing α β x = α x (g.sharp x (β x)) :=
  g.form_sharp_left x (α x) (g.sharp x (β x))

section Naturality

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (h : LorentzMetric σ d N) (x : M) (y : N)
  (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ]
    TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
  (he : ∀ v w, g.form x v w = h.form y (e v) (e w))

include he

/-- Lowering commutes with a metric-preserving change of tangent coordinates.
The covector transforms by pullback, in the opposite direction to vectors. -/
theorem flat_naturality (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.flat x v = (h.flat y (e v)).comp e.toContinuousLinearMap := by
  ext w
  exact he v w

/-- Raising a pulled-back covector transforms by the inverse tangent map. -/
theorem sharp_naturality (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ) :
    g.sharp x (α.comp e.toContinuousLinearMap) = e.symm (h.sharp y α) := by
  apply (g.sharp_eq_iff x _ _).mpr
  intro w
  rw [he]
  simp

end Naturality

@[simp] theorem opposite_flat_apply (x : M)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.opposite.flat x v = -g.flat x v := rfl

@[simp] theorem opposite_sharp_apply (x : M)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.opposite.sharp x α = -g.sharp x α := by
  apply (g.opposite.sharp_eq_iff x α _).mpr
  intro w
  simp

@[simp] theorem minkowskiMetric_flat (σ : LorentzConvention) (d : ℕ)
    (x : MinkowskiModel d) : (minkowskiMetric σ d).flat x = Minkowski.flat σ := by
  ext v w
  rfl

@[simp] theorem minkowskiMetric_sharp (σ : LorentzConvention) (d : ℕ)
    (x : MinkowskiModel d) : (minkowskiMetric σ d).sharp x = Minkowski.sharp σ := by
  simp only [sharp, minkowskiMetric_flat, Minkowski.sharp]

end ProjectAInos.SmoothGeometry.LorentzMetric
