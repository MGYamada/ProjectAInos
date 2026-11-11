/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.Lorentzian.Dual
import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples

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

end Charts
