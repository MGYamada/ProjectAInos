/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.Lorentzian.Dual
import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples
import ProjectAInos.SmoothGeometry.Lorentzian.ChartConnection
import ProjectAInos.SmoothGeometry.Lorentzian.ConnectionExamples
import ProjectAInos.SmoothGeometry.Lorentzian.Regularity
import ProjectAInos.SmoothGeometry.Lorentzian.Restriction
import ProjectAInos.SmoothGeometry.Tensor.Bundle

/-! Typed contracts for GR 5.1's shared metric and connection foundation. These examples use
default elaborator options and do not assume a global frame or flatness. -/

open ProjectAInos.SmoothGeometry
open scoped Manifold ContDiff

noncomputable section

section Connection

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)
  {X Y Z : ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x} {x : M}

example : CovariantDerivative 𝓘(ℝ, MinkowskiModel d) (MinkowskiModel d)
    (TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)) := g.leviCivita

example : g.IsLeviCivita g.leviCivita := g.isLeviCivita_leviCivita

example : g.leviCivita.torsion = 0 := g.leviCivita_torsion

example
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Z) x)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (Y y) (Z y)) x v =
      g.form x (g.leviCivita Y x v) (Z x) + g.form x (Y x) (g.leviCivita Z x v) :=
  g.leviCivita_metricCompatible v hY hZ

example
    (hX : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% X) x)
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Z) x) :
    g.form x (g.leviCivita Y x (X x)) (Z x) =
      (mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (Y y) (Z y)) x (X x) +
       mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (Z y) (X y)) x (Y x) -
       mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (X y) (Y y)) x (Z x) -
       g.form x (Y x) (VectorField.mlieBracket 𝓘(ℝ, MinkowskiModel d) X Z x) -
       g.form x (Z x) (VectorField.mlieBracket 𝓘(ℝ, MinkowskiModel d) Y X x) +
       g.form x (X x) (VectorField.mlieBracket 𝓘(ℝ, MinkowskiModel d) Z Y x)) / 2 :=
  g.leviCivita_pairing hX hY hZ

example
    (cov cov' : CovariantDerivative 𝓘(ℝ, MinkowskiModel d) (MinkowskiModel d)
      (TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)))
    (h : g.IsLeviCivita cov) (h' : g.IsLeviCivita cov')
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) : cov Y x v = cov' Y x v :=
  h.uniqueness g h' hY v

example : g.opposite.leviCivita = g.leviCivita := g.leviCivita_opposite

example : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita ∞ := inferInstance

example (n : ℕ∞) : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita n :=
  inferInstance

example (n : ℕ∞) (hY : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (n + 1) (T% Y) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) n
      (fun y => Bundle.TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := g.contMDiffAt_leviCivita hY

example (hY : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) 2 (T% Y) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) 1
      (fun y => Bundle.TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := g.contMDiffAt_leviCivita hY

example (hY : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) ∞ (T% Y) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) ∞
      (fun y => Bundle.TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := g.contMDiffAt_leviCivita hY

end Connection

section ConnectionNaturality

variable {σ : LorentzConvention} {d : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (g : LorentzMetric σ d M) (h : LorentzMetric σ d N)

example (x : M) (y : N)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (hL : ∀ v w, g.form x v w = h.form y (L v) (L w)) : L.IsInvertible :=
  g.isInvertible_of_metric h x y L hL

example {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hmetric : ∀ y v w, g.form y v w = h.form (f y)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w))
    {Y : ∀ y : N, TangentSpace 𝓘(ℝ, MinkowskiModel d) y} {x : M}
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) (f x))
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x
      (g.leviCivita (VectorField.mpullback 𝓘(ℝ, MinkowskiModel d)
        𝓘(ℝ, MinkowskiModel d) f Y) x v) =
      h.leviCivita Y (f x)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v) :=
  g.leviCivita_naturality_of_metric h hf hmetric hY v

example (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hinv : ∀ x, (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x).IsInvertible)
    (x : M) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    (h.pullback f hf hinv).form x v w = h.form (f x)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x w) :=
  h.pullback_form f hf hinv x v w

example (U : TopologicalSpace.Opens M) : LorentzMetric σ d U := g.restrict U

example (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞
      (Subtype.val : U → M) := Manifold.isLocalDiffeomorph_subtype_val _ U

example (U : TopologicalSpace.Opens M) {x : U}
    {Y : ∀ y : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) y}
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x.val)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (Subtype.val : U → M) x
      ((g.restrict U).leviCivita
        (VectorField.mpullback 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
          (Subtype.val : U → M) Y) x v) =
      g.leviCivita Y x.val
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (Subtype.val : U → M) x v) :=
  g.leviCivita_restrict U hY v

end ConnectionNaturality

section CoordinateConnection

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} (g : LorentzMetric σ d (MinkowskiModel d))

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.christoffel x k i j = ∑ l,
      g.inverseComponent x (NormedSpace.fromTangentSpace x) k l *
        (fderiv ℝ (fun y => g.modelComponent y j l) x (Pi.single i 1) +
         fderiv ℝ (fun y => g.modelComponent y l i) x (Pi.single j 1) -
         fderiv ℝ (fun y => g.modelComponent y i j) x (Pi.single l 1)) / 2 :=
  g.christoffel_eq x k i j

example (k i j : Fin (d + 1)) : ContDiff ℝ ∞ (fun x => g.christoffel x k i j) :=
  g.christoffel_contDiff k i j

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.christoffel x k i j = g.christoffel x k j i := g.christoffel_symmetric x k i j

example {Y : MinkowskiModel d → MinkowskiModel d} {x : MinkowskiModel d}
    (hY : DifferentiableAt ℝ Y x) (v : MinkowskiModel d) (k : Fin (d + 1)) :
    NormedSpace.fromTangentSpace x
      (g.leviCivita (fun y => modelField (Y y) y) x (modelField v x)) k =
        fderiv ℝ Y x v k + ∑ i, ∑ j, g.christoffel x k i j * v i * Y x j :=
  g.leviCivita_model_coordinates hY v k

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.opposite.christoffel x k i j = g.christoffel x k i j :=
  g.christoffel_opposite x k i j

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    (minkowskiMetric σ d).christoffel x k i j = 0 := minkowski_christoffel σ d x k i j

end CoordinateConnection

section Duality

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) (x : M)

example (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.flat x v w = g.form x v w := g.flat_apply x v w

example (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.sharp x (g.flat x v) = v := g.sharp_flat x v

example (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.flat x (g.sharp x α) = α := g.flat_sharp x α

example : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod
      𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)) ∞
    (fun y => Bundle.TotalSpace.mk'
      (MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
      y (g.flat y).toContinuousLinearMap) := g.flat_smooth

example : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod
      𝓘(ℝ, (MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)) ∞
    (fun y => Bundle.TotalSpace.mk'
      ((MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)
      y (g.sharp y).toContinuousLinearMap) := g.sharp_smooth

example (v : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
    (fun y : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) y)⟯) :
    g.raise (g.lower v) = v := g.raise_lower v

example (α : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
    (fun y : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ)⟯) :
    g.lower (g.raise α) = α := g.lower_raise α

example (α β : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
    (fun y : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ)⟯) :
    g.inversePairing α β x = α x (g.sharp x (β x)) := g.inversePairing_apply α β x

example (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.opposite.sharp x α = -g.sharp x α := g.opposite_sharp_apply x α

example (p : MinkowskiModel d) :
    (minkowskiMetric σ d).sharp p = Minkowski.sharp σ :=
  LorentzMetric.minkowskiMetric_sharp σ d p

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (h : LorentzMetric σ d N) (y : N)
  (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ]
    TangentSpace 𝓘(ℝ, MinkowskiModel d) y)

example (he : ∀ v w, g.form x v w = h.form y (e v) (e w))
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.flat x v = (h.flat y (e v)).comp e.toContinuousLinearMap :=
  g.flat_naturality h x y e he v

example (he : ∀ v w, g.form x v w = h.form y (e v) (e w))
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ) :
    g.sharp x (α.comp e.toContinuousLinearMap) = e.symm (h.sharp y α) :=
  g.sharp_naturality h x y e he α

end Duality

section Bilinear

variable {E F G X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

example (B : G →L[ℝ] G →L[ℝ] ℝ) (A : F →L[ℝ] G) (C : E →L[ℝ] F) :
    BilinearTensor.pullback B (A.comp C) =
      BilinearTensor.pullback (BilinearTensor.pullback B A) C :=
  BilinearTensor.pullback_comp B A C

example {B : X → F →L[ℝ] F →L[ℝ] ℝ} {A : X → E →L[ℝ] F}
    (hB : ContDiff ℝ ∞ B) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => BilinearTensor.pullback (B x) (A x)) :=
  BilinearTensor.contDiff_pullback hB hA

example {B : X → E →L[ℝ] E →L[ℝ] ℝ} {v w : X → E}
    (hB : ContDiff ℝ ∞ B) (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => B x (v x) (w x)) :=
  BilinearTensor.contDiff_contract hB hv hw

end Bilinear

section TensorBundles

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

open Tensor

example (r s : ℕ) :
    ContMDiffVectorBundle ∞
      ((Shape.mixed r s).bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Model
      ((Shape.mixed r s).bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Fiber
      𝓘(ℝ, MinkowskiModel d) := inferInstance

example {σ : LorentzConvention} (g : LorentzMetric σ d M) :
    ((Shape.mixed 0 2).bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Section 𝓘(ℝ, MinkowskiModel d) :=
  g.toTensor

example (A : SmoothBundle 𝓘(ℝ, MinkowskiModel d) (M := M))
    (L : (SmoothBundle.hom 𝓘(ℝ, MinkowskiModel d) A A).Section 𝓘(ℝ, MinkowskiModel d)) :
    C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ := A.contract 𝓘(ℝ, MinkowskiModel d) L

example (A B : SmoothBundle 𝓘(ℝ, MinkowskiModel d) (M := M))
    (L : (SmoothBundle.hom 𝓘(ℝ, MinkowskiModel d) A
      (SmoothBundle.hom 𝓘(ℝ, MinkowskiModel d) B B)).Section 𝓘(ℝ, MinkowskiModel d))
    (x : M) (v : A.Fiber x) :
    SmoothBundle.partialContract 𝓘(ℝ, MinkowskiModel d) A B L x v =
      LinearMap.trace ℝ (B.Fiber x) (L x v).toLinearMap :=
  SmoothBundle.partialContract_apply 𝓘(ℝ, MinkowskiModel d) A B L x v

example (A : SmoothBundle 𝓘(ℝ, MinkowskiModel d) (M := M))
    (e : Bundle.Trivialization A.Model
      (Bundle.TotalSpace.proj : Bundle.TotalSpace A.Model A.Fiber → M))
    [MemTrivializationAtlas e] (T : A.Section 𝓘(ℝ, MinkowskiModel d)) :
    ContMDiffOn 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, A.Model) ∞
      (A.coefficients 𝓘(ℝ, MinkowskiModel d) e T) e.baseSet :=
  A.coefficients_contMDiffOn 𝓘(ℝ, MinkowskiModel d) e T

example (s : Shape) {x y z : M}
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (f : TangentSpace 𝓘(ℝ, MinkowskiModel d) y ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) z) :
    s.pullback 𝓘(ℝ, MinkowskiModel d) (e.trans f) =
      (s.pullback 𝓘(ℝ, MinkowskiModel d) f).trans (s.pullback 𝓘(ℝ, MinkowskiModel d) e) :=
  s.pullback_trans 𝓘(ℝ, MinkowskiModel d) e f

example (a b : Shape) {x y : M}
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (L : (a.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x →L[ℝ]
      (b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x →L[ℝ]
        (b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x)
    (v : (a.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber y) :
    LinearMap.trace ℝ ((b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber y)
        ((Shape.map 𝓘(ℝ, MinkowskiModel d) (.hom a (.hom b b)) e L) v).toLinearMap =
      LinearMap.trace ℝ ((b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x)
        (L ((a.map 𝓘(ℝ, MinkowskiModel d) e).symm v)).toLinearMap :=
  Shape.partialTrace_map 𝓘(ℝ, MinkowskiModel d) a b e L v

variable {σ : LorentzConvention} (g : LorentzMetric σ d M)

example (B : CovariantTwoTensor d M) : g.lowerIndex (g.raiseIndex B) = B :=
  g.lowerIndex_raiseIndex B

example (A : TangentEndomorphism d M) : g.raiseIndex (g.lowerIndex A) = A :=
  g.raiseIndex_lowerIndex A

example (B : CovariantTwoTensor d M) : C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ :=
  g.contractField B

example (x : M) : g.contract x (g.form x) = d + 1 := g.contract_metric x

example (x : M)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.opposite.contract x B = -g.contract x B := g.contract_opposite x B

example (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x B = ∑ i, ∑ j,
      B (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) * g.inverseComponent x e i j :=
  g.contract_eq_sum_components x e B

end TensorBundles

section FieldPullback

open Tensor

variable {d : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  [TopologicalSpace P] [ChartedSpace (MinkowskiModel d) P]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ P]

example (s : Shape) (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := N)).Section 𝓘(ℝ, MinkowskiModel d)) :
    (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Section 𝓘(ℝ, MinkowskiModel d) :=
  s.pullbackField 𝓘(ℝ, MinkowskiModel d) f T

example (s : Shape) (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (g : N ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ P)
    (T : (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := P)).Section 𝓘(ℝ, MinkowskiModel d)) :
    s.pullbackField 𝓘(ℝ, MinkowskiModel d) (f.trans g) T =
      s.pullbackField 𝓘(ℝ, MinkowskiModel d) f (s.pullbackField 𝓘(ℝ, MinkowskiModel d) g T) :=
  s.pullbackField_trans 𝓘(ℝ, MinkowskiModel d) f g T

example (s : Shape) (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Section 𝓘(ℝ, MinkowskiModel d)) :
    s.pullbackField 𝓘(ℝ, MinkowskiModel d) f
      (s.pullbackField 𝓘(ℝ, MinkowskiModel d) f.symm T) = T :=
  s.pullbackField_symm 𝓘(ℝ, MinkowskiModel d) f T

example (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : CovariantTwoTensor d N) (x : M)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    Shape.pullbackField 𝓘(ℝ, MinkowskiModel d) (Shape.mixed 0 2) f T x v w =
      T (f x) (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x w) :=
  Shape.pullbackField_covariantTwo_apply 𝓘(ℝ, MinkowskiModel d) f T x v w

example (s t : Shape)
    (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : ((Shape.hom s (Shape.hom t t)).bundle 𝓘(ℝ, MinkowskiModel d) (M := N)).Section
      𝓘(ℝ, MinkowskiModel d)) :
    SmoothBundle.partialContract 𝓘(ℝ, MinkowskiModel d)
      (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := M))
      (t.bundle 𝓘(ℝ, MinkowskiModel d) (M := M))
      (Shape.pullbackField 𝓘(ℝ, MinkowskiModel d) (Shape.hom s (Shape.hom t t)) f T) =
    Shape.pullbackField 𝓘(ℝ, MinkowskiModel d) (Shape.hom s Shape.scalar) f
      (SmoothBundle.partialContract 𝓘(ℝ, MinkowskiModel d)
        (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := N))
        (t.bundle 𝓘(ℝ, MinkowskiModel d) (M := N)) T) :=
  Shape.partialContract_pullbackField 𝓘(ℝ, MinkowskiModel d) s t f T

end FieldPullback

section ManifoldChartConnection

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) {e e' : OpenPartialHomeomorph M (MinkowskiModel d)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
  (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
  {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source)

example (v : MinkowskiModel d) : chartTangentMap e x (chartField e v x) = v :=
  chartTangentMap_field he hx v

example (k i j : Fin (d + 1)) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ) ∞
      (fun y => g.chartChristoffel e y k i j) x :=
  g.chartChristoffel_contMDiffAt he hx k i j

example (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = ∑ l,
      g.inverseComponent x (chartTangentEquiv he hx) k l *
        (mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.chartComponent e y j l) x
          (chartField e (Pi.single i 1) x) +
         mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.chartComponent e y l i) x
          (chartField e (Pi.single j 1) x) -
         mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.chartComponent e y i j) x
          (chartField e (Pi.single l 1) x)) / 2 :=
  g.chartChristoffel_eq he hx k i j

example {V : M → MinkowskiModel d}
    (hV : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) V x)
    (v : MinkowskiModel d) (k : Fin (d + 1)) :
    chartTangentMap e x
      (g.leviCivita (fun y => chartField e (V y) y) x (chartField e v x)) k =
      mvfderiv 𝓘(ℝ, MinkowskiModel d) V x (chartField e v x) k +
        ∑ i, ∑ j, g.chartChristoffel e x k i j * v i * V x j :=
  g.leviCivita_chart_coordinates he hx hV v k

example (k i j : Fin (d + 1)) :
    (∑ l, fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single l 1) k *
      g.chartChristoffel e x l i j) =
      fderiv ℝ (fun z => fderiv ℝ (e' ∘ e.symm) z (Pi.single j 1))
        (e x) (Pi.single i 1) k +
      ∑ a, ∑ b, g.chartChristoffel e' x k a b *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single i 1) a *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) b :=
  g.chartChristoffel_transformation he he' hx hx' k i j

example (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = g.chartChristoffel e x k j i :=
  g.chartChristoffel_symmetric he hx k i j

example (k i j : Fin (d + 1)) :
    g.opposite.chartChristoffel e x k i j = g.chartChristoffel e x k i j :=
  g.chartChristoffel_opposite e x k i j

end ManifoldChartConnection

section Charts

open LorentzianCharts

example : spacetime.toScheme = (minkowski .timeNegative 1).toScheme := spacetime_toScheme

example : standardChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
  standardChart_mem_maximalAtlas

example : inertialChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
  inertialChart_mem_maximalAtlas

example : standardChart.source ∩ inertialChart.source = Set.univ := chart_overlap

example (p : Plane) : (standardChart.symm.trans inertialChart) p = shear p :=
  transition_apply p

example (p v w : Plane) :
    metric.form p v w = (minkowskiMetric .timeNegative 1).form (shear p)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w) := metric_covariance p v w

example (p v : Plane) :
    metric.flat p v = (Minkowski.flat .timeNegative (shearLinear (2 * p 0) v)).comp
      (shearLinear (2 * p 0)).toContinuousLinearMap := flat_covariance p v

example (p : Plane) (α : Plane →L[ℝ] ℝ) :
    metric.sharp p (α.comp (shearLinear (2 * p 0)).toContinuousLinearMap) =
      (shearLinear (2 * p 0)).symm (Minkowski.sharp .timeNegative α) :=
  sharp_covariance p α

example (p : Plane) :
    metric.form p (Pi.single 0 1) (Pi.single 0 1) = -1 + 4 * (p 0)^2 :=
  metric_time_time p

example (p : Plane) : metric.form p (Pi.single 0 1) (Pi.single 1 1) = 2 * p 0 :=
  metric_time_space p

example : metric.form ![0, 0] ≠ metric.form ![1, 0] := metric_nonconstant

example : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![0, 0] ≠
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![1, 0] := jacobian_nonconstant

example (p v w : Plane) :
    metric.opposite.form p v w = (minkowskiMetric .timePositive 1).form (shear p)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w) := opposite_metric_covariance p v w

example (p : Plane) : metric.contractField spatialTensor p = 1 := spatialTensor_contract p

example : metric.toTensor = CovariantTwoTensor.pullback (d := 1)
    shearDiffeomorph (minkowskiMetric .timeNegative 1).toTensor := metric_tensor_pullback

example (p : Plane) (k i j : Fin 2) :
    metric.christoffel p k i j = if k = 1 ∧ i = 0 ∧ j = 0 then 2 else 0 :=
  christoffel_shear p k i j

example (p : Plane) : metric.christoffel p 1 0 0 = 2 := by
  simp [christoffel_shear]

example (p : Plane) (k i j : Fin 2) :
    metric.chartChristoffel standardChart p k i j =
      if k = 1 ∧ i = 0 ∧ j = 0 then 2 else 0 := chartChristoffel_standard p k i j

example (p : Plane) (k i j : Fin 2) :
    metric.chartChristoffel inertialChart p k i j = 0 := chartChristoffel_inertial p k i j

example (p : Plane) (k i j : Fin 2) :
    (∑ l, fderiv ℝ shear p (Pi.single l 1) k * metric.christoffel p l i j) =
      fderiv ℝ (fun z => fderiv ℝ shear z (Pi.single j 1)) p (Pi.single i 1) k :=
  chart_transformation_shear p k i j

example (p v w : Plane) :
    fderiv ℝ shear p
      (NormedSpace.fromTangentSpace p
        (metric.leviCivita (LorentzMetric.modelField w) p (LorentzMetric.modelField v p))) =
      fderiv ℝ (fun q => fderiv ℝ shear q w) p v := connection_shear_transformation p v w

example : metric = (minkowskiMetric .timeNegative 1).pullback shearDiffeomorph
    shearDiffeomorph.contMDiff (fun x =>
      shearDiffeomorph.isInvertible_mfderiv (x := x) (by simp)) :=
  metric_eq_pullback

example {Y : ∀ y : Plane, TangentSpace 𝓘(ℝ, Plane) y} {p : Plane}
    (hY : MDifferentiableAt 𝓘(ℝ, Plane) (𝓘(ℝ, Plane).prod 𝓘(ℝ, Plane))
      (T% Y) (shear p)) (v : TangentSpace 𝓘(ℝ, Plane) p) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p
      (metric.leviCivita (VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear Y) p v) =
      (minkowskiMetric .timeNegative 1).leviCivita Y (shear p)
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v) := leviCivita_shear_naturality hY v

end Charts
