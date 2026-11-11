/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.Lorentzian.Dual
import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples
import ProjectAInos.SmoothGeometry.Tensor.Bundle

/-! Typed contracts for GR 5.1's shared metric foundation. These examples use
default elaborator options and do not assume a global frame or flatness. -/

open ProjectAInos.SmoothGeometry
open scoped Manifold ContDiff

noncomputable section

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

end Charts
