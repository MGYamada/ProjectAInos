/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.Scheme
public import ProjectAInos.SmoothGeometry.Minkowski.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Lorentz manifolds on the common C∞ scheme foundation

The metric is extra smooth bilinear data on the actual tangent bundle. Its
Lorentz signature is a pointwise condition; no global frame is required.
Both time-positive and time-negative conventions are explicit parameters.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Manifold ContDiff BigOperators

namespace ProjectAInos.SmoothGeometry

open Bundle ContinuousLinearMap

/-- A smooth Lorentz metric of signature `(1,d)` on a manifold with `d+1` dimensional charts. -/
structure LorentzMetric (σ : LorentzConvention) (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] where
  form : ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
    TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ
  smooth : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)) ∞
    (fun x => TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ) x (form x))
  signature : ∀ x, ∃ e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d,
    ∀ v w, form x v w = minkowskiForm σ d (e v) (e w)

namespace LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] (g : LorentzMetric σ d M)

theorem symmetric (x : M) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.form x v w = g.form x w v := by
  obtain ⟨e, he⟩ := g.signature x
  rw [he, he, minkowskiForm_symmetric]

theorem nondegenerate (x : M) (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x)
    (h : ∀ w, g.form x v w = 0) : v = 0 := by
  obtain ⟨e, he⟩ := g.signature x
  apply e.injective
  rw [map_zero]
  apply minkowskiForm_nondegenerate σ
  intro w
  obtain ⟨w, rfl⟩ := e.surjective w
  rw [← he]
  exact h w

/-- Pairing smooth vector fields gives a smooth real function, hence an element
of the same C∞ function algebra used by the structure sheaf. -/
def pairing
    (v w : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
      (fun x : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) x)⟯) :
    C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ :=
  ⟨fun x => g.form x (v x) (w x), by
    intro x
    have h : ContMDiffAt 𝓘(ℝ, MinkowskiModel d) (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ)) ∞
        (fun y => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y (g.form y (v y) (w y))) x :=
      (g.smooth x).clm_bundle_apply₂ (v.contMDiff x) (w.contMDiff x)
    rw [contMDiffAt_totalSpace] at h
    exact h.2⟩

/-- Flatness as the existence of local inertial coordinates: locally the metric
is the pullback of the Minkowski form by a smooth coordinate diffeomorphism. -/
def IsLocallyMinkowski : Prop :=
  ∀ x : M, ∃ (U : TopologicalSpace.Opens M), x ∈ U ∧
    ∃ (V : TopologicalSpace.Opens (MinkowskiModel d))
      (e : U ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ V),
      ∀ (y : U) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) y.val),
        g.form y.val v w = minkowskiForm σ d
          (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) e y v)
          (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) e y w)

/-- Reverse metric convention without changing the manifold or tangent bundle. -/
def opposite : LorentzMetric σ.opposite d M where
  form x := -g.form x
  smooth := g.smooth.neg_section
  signature x := by
    obtain ⟨e, he⟩ := g.signature x
    refine ⟨e, fun v w => ?_⟩
    simp [he]

@[simp] theorem opposite_form (x : M) : g.opposite.form x = -g.form x := rfl

 theorem isLocallyMinkowski_opposite_iff :
    g.opposite.IsLocallyMinkowski ↔ g.IsLocallyMinkowski := by
  constructor <;> intro h x <;> obtain ⟨U, hx, V, e, he⟩ := h x
  · refine ⟨U, hx, V, e, fun y v w => ?_⟩
    simpa using he y v w
  · refine ⟨U, hx, V, e, fun y v w => ?_⟩
    simpa using congrArg Neg.neg (he y v w)

end LorentzMetric

/-- A Lorentz manifold carries a metric on a smooth manifold. Its scheme is
derived uniformly from the smooth-function sheaf. -/
structure LorentzManifold (σ : LorentzConvention) (d : ℕ) where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace (MinkowskiModel d) carrier]
  [manifold : IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ carrier]
  metric : LorentzMetric σ d carrier

attribute [instance] LorentzManifold.topology LorentzManifold.chartedSpace LorentzManifold.manifold

namespace LorentzManifold

instance {σ d} : CoeSort (LorentzManifold σ d) Type := ⟨carrier⟩

/-- The shared scheme used for both special and general relativity. -/
def toScheme {σ : LorentzConvention} {d : ℕ} (X : LorentzManifold σ d) : Scheme := Manifold.scheme (d + 1) X.carrier

def opposite {σ : LorentzConvention} {d : ℕ} (X : LorentzManifold σ d) :
    LorentzManifold σ.opposite d where
  carrier := X.carrier
  metric := X.metric.opposite

@[simp] theorem opposite_toScheme {σ : LorentzConvention} {d : ℕ}
    (X : LorentzManifold σ d) : X.opposite.toScheme = X.toScheme := rfl

end LorentzManifold

/-- The constant Lorentz metric on Minkowski space. -/
def minkowskiMetric (σ : LorentzConvention) (d : ℕ) : LorentzMetric σ d (MinkowskiModel d) where
  form _ := minkowskiForm σ d
  smooth := by
    intro x
    rw [contMDiffAt_section]
    convert contMDiffAt_const (c := minkowskiForm σ d) using 1
    funext y
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
    rfl
  signature _ := ⟨ContinuousLinearEquiv.refl ℝ _, fun _ _ => rfl⟩

/-- Minkowski space is one instance of the same Lorentz-manifold interface. -/
def minkowski (σ : LorentzConvention) (d : ℕ) : LorentzManifold σ d where
  carrier := MinkowskiModel d
  metric := minkowskiMetric σ d

/-- The metric in the canonical tangent-space identification of a vector space. -/
def minkowskiCoefficients (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  (minkowskiMetric σ d).form x

/-- Its metric coefficients are constant in the canonical inertial chart. -/
theorem minkowskiMetric_fderiv (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    fderiv ℝ (minkowskiCoefficients σ d) x = 0 :=
  fderiv_const_apply (minkowskiForm σ d)

/-- Minkowski space has global inertial coordinates, hence is locally Minkowski. -/
theorem minkowski_isLocallyMinkowski (σ : LorentzConvention) (d : ℕ) : (minkowskiMetric σ d).IsLocallyMinkowski := by
  intro x
  refine ⟨⊤, trivial, ⊤, Diffeomorph.refl _ _ ∞, ?_⟩
  intro y v w
  change minkowskiForm σ d v w = minkowskiForm σ d
    (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) id y v)
    (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) id y w)
  rw [mfderiv_id]
  rfl

/-- The scheme of Minkowski space uses the manifold construction and is affine. -/
def minkowskiSchemeIso (σ : LorentzConvention) (d : ℕ) :
    (minkowski σ d).toScheme ≅ Scheme.specObj (SmoothAlgebra.SmoothRingCat.of
      (SmoothAlgebra.SmoothOperation (d + 1))) where
  hom := ⟨(Manifold.euclideanIso (d + 1)).hom⟩
  inv := ⟨(Manifold.euclideanIso (d + 1)).inv⟩
  hom_inv_id := Scheme.Hom.ext (Manifold.euclideanIso (d + 1)).hom_inv_id
  inv_hom_id := Scheme.Hom.ext (Manifold.euclideanIso (d + 1)).inv_hom_id

end ProjectAInos.SmoothGeometry
