/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.Gluing
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeCoordinates
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeGluing
import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExteriorExamples

/-! External API regressions: use the public definitions with default elaborator
options, without unfolding morphism wrappers or adding local instances. -/

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ProjectAInos.SmoothGeometry

noncomputable section

universe u

section OpenImmersions

variable {X Y Z : Scheme.{u}}

example : Scheme.IsOpenImmersion (𝟙 X) := inferInstance

example (f : X ⟶ Y) [IsIso f] : Scheme.IsOpenImmersion f := inferInstance

example (f : X ⟶ Y) (g : Y ⟶ Z) [Scheme.IsOpenImmersion f] [Scheme.IsOpenImmersion g] :
    Scheme.IsOpenImmersion (f ≫ g) := inferInstance

example (U : Opens X.carrier) : Scheme.IsOpenImmersion (X.ofRestrict U.isOpenEmbedding) :=
  inferInstance

example (U : Opens X.carrier) (f : Y ⟶ X) :
    HasPullback (X.ofRestrict U.isOpenEmbedding) f := inferInstance

example (U : Opens X.carrier) (e : X ≅ Y) (f : Z ⟶ Y) :
    HasPullback (X.ofRestrict U.isOpenEmbedding ≫ e.hom) f := inferInstance

end OpenImmersions

section LocallyRingedGluing

variable (D : LocallyRingedSpace.GlueData.{u})

example : HasMulticoequalizer D.toGlueData.diagram := inferInstance

example : D.glued = D.toGlueData.glued := rfl

example (i : D.J) : D.ι i = Multicoequalizer.π D.toGlueData.diagram i := rfl

example (i : D.J) : LocallyRingedSpace.IsOpenImmersion (D.toGlueData.ι i) := inferInstance

example (i j : D.J) : PullbackCone (D.ι i) (D.ι j) := D.toGlueData.vPullbackCone i j

example (X : LocallyRingedSpace.{u}) (f : ∀ i, D.U i ⟶ X)
    (h : ∀ p, D.toGlueData.diagram.fst p ≫ f p.1 = D.toGlueData.diagram.snd p ≫ f p.2)
    (i : D.J) : D.ι i ≫ Multicoequalizer.desc D.toGlueData.diagram X f h = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f h i

end LocallyRingedGluing

section SchemeGluing

variable (D : Scheme.GlueData.{u})

example : HasMulticoequalizer D.toGlueData.diagram := inferInstance

example : D.glued = D.toGlueData.glued := rfl

example (i : D.J) : D.ι i = Multicoequalizer.π D.toGlueData.diagram i := rfl

example (i : D.J) : Scheme.IsOpenImmersion (D.toGlueData.ι i) := inferInstance

example (i j : D.J) : PullbackCone (D.ι i) (D.ι j) := D.toGlueData.vPullbackCone i j

example (X : Scheme.{u}) (f : ∀ i, D.U i ⟶ X)
    (h : ∀ p, D.toGlueData.diagram.fst p ≫ f p.1 = D.toGlueData.diagram.snd p ≫ f p.2)
    (i : D.J) : D.ι i ≫ Multicoequalizer.desc D.toGlueData.diagram X f h = f i :=
  Multicoequalizer.π_desc D.toGlueData.diagram X f h i

end SchemeGluing


section NativeDifferentialForms

open Bundle DifferentialForm
open scoped Manifold ContDiff

variable {E H M F H' N G H'' P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  (J : ModelWithCorners ℝ F H') [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
  (K : ModelWithCorners ℝ G H'') [TopologicalSpace P] [ChartedSpace H'' P]
  [IsManifold K ∞ P]

example (k : ℕ) : ContMDiffVectorBundle ∞ (E [⋀^Fin k]→L[ℝ] ℝ)
    (fun x : M => TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) I := inferInstance

example {k : ℕ} (f : C^∞⟮I, M; J, N⟯) (α : SmoothForm J N k)
    (x : M) (v : Fin k → TangentSpace I x) :
    smoothPullback I J f α x v = α (f x) (fun i => mfderiv I J f x (v i)) :=
  smoothPullback_apply I J f α x v

example {k : ℕ} (α : SmoothForm I M k) :
    smoothPullback I I (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) α = α := smoothPullback_id I α

example {k : ℕ} (f : C^∞⟮I, M; J, N⟯) (g : C^∞⟮J, N; K, P⟯)
    (α : SmoothForm K P k) :
    smoothPullback I K (g.comp f) α = smoothPullback I J f (smoothPullback J K g α) :=
  smoothPullback_comp I J K f g α

example (k : ℕ) (y : N) (α : SmoothForm J N (k + 1)) :
    smoothPullback I J (ContMDiffMap.const y : C^∞⟮I, M; J, N⟯) α = 0 :=
  smoothPullback_const I J k y α

example {k : ℕ} (e e' : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] (α : NativeForm I M k)
    {x : M} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    coefficients I e' α x = (coefficients I e α x).compContinuousLinearMap
      (e'.coordChangeL ℝ e x).toContinuousLinearMap := coefficients_change I e e' α hx hx'

example {k : ℕ} (α : SmoothForm I M k)
    (e : Trivialization E (π E (fun x : M => TangentSpace I x)))
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞
      (coefficients I e (fun y => α y)) x := α.contMDiffAt_coefficients I e hx

example {k : ℕ} {ι : Type*} (U : ι → Set M) (hopen : ∀ i, IsOpen (U i))
    (hU : ∀ x, ∃ i, x ∈ U i) (α : ι → NativeForm I M k)
    (hsmooth : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x (α i x)) (U i))
    (hα : ∀ i j x, x ∈ U i ∩ U j → α i x = α j x) {i : ι} {x : M} (hx : x ∈ U i) :
    smoothGlue I U hopen hU α hsmooth hα x = α i x :=
  smoothGlue_apply I U hopen hU α hsmooth hα hx

example {k : ℕ} (f : E → F) (α : Form F k) :
    nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α = pullback f α := nativePullback_flat f α

example (p v : LorentzianCharts.Plane) :
    smoothPullback 𝓘(ℝ, LorentzianCharts.Plane) 𝓘(ℝ, LorentzianCharts.Plane)
      LorentzianCharts.shearDiffeomorph.toContMDiffMap NativeExamples.spatial p ![v] =
        v 1 + 2 * p 0 * v 0 := NativeExamples.spatial_shear p v

end NativeDifferentialForms


section NativeExteriorCalculus

open Bundle DifferentialForm
open scoped Manifold ContDiff Topology

variable {E M F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] {k : ℕ}

example {f : M → N} {α : NativeForm 𝓘(ℝ, F) N k} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hα : ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (F [⋀^Fin k]→L[ℝ] ℝ) y (α y)) (f x)) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y
        (nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α y)) x :=
  contMDiffAt_nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) hf hα

example (α : SmoothForm 𝓘(ℝ, E) M k) :
    smoothExteriorDerivative (smoothExteriorDerivative α) = 0 := smoothExteriorDerivative_squared α

example (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯) (α : SmoothForm 𝓘(ℝ, F) N k) :
    smoothExteriorDerivative (smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α) =
      smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f (smoothExteriorDerivative α) :=
  smoothExteriorDerivative_pullback f α

example (α : SmoothForm 𝓘(ℝ, E) M k) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : M} (hx : x ∈ e.source) :
    nativeExteriorDerivative (fun y => α y) x =
      chartLift e (extDeriv (chartCoefficients e (fun y => α y))) x :=
  nativeExteriorDerivative_eq_chart α he hx

example (α : SmoothForm 𝓘(ℝ, E) M k) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E} (hy : y ∈ e.target) :
    chartCoefficients e (fun x => smoothExteriorDerivative α x) y =
      extDeriv (chartCoefficients e (fun x => α x)) y :=
  chartCoefficients_smoothExteriorDerivative α he hy

example : SmoothForm 𝓘(ℝ, E) M k →ₗ[ℝ] SmoothForm 𝓘(ℝ, E) M (k + 1) :=
  smoothExteriorDerivativeLinear

example {α β : SmoothForm 𝓘(ℝ, E) M k} {x : M} (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    smoothExteriorDerivative α x = smoothExteriorDerivative β x := smoothExteriorDerivative_local h

example (α : Form E k) (hα : ContDiff ℝ ∞ α) :
    (fun x => smoothExteriorDerivative (ofFlat α hα) x) = exteriorDerivative α :=
  smoothExteriorDerivative_flat α hα

example : smoothExteriorDerivative NativeExamples.potential = NativeExamples.area :=
  NativeExamples.potential_exteriorDerivative

example : smoothExteriorDerivative NativeExamples.area = 0 := NativeExamples.area_closed

end NativeExteriorCalculus
