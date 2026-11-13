/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormDerivative
public import ProjectAInos.SmoothGeometry.Lorentzian.Tensor

/-! # Intrinsic covariant divergence of a two-form

Contract the first form slot with the derivative direction using the inverse
metric, then raise the remaining covector. This constructs the vector with
components `∇ᵢFⁱʲ`, without choosing coordinates or an orientation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

local instance (x : M) : T2Space (TM x) := FiberBundle.t2Space E TM x
local instance (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Contract the first form slot with the derivative index. -/
def twoFormDivergenceCovector (F : SmoothForm I M 2) (x : M) : TM x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun v := g.contract x ((g.twoFormDerivative F x).flip v)
    map_add' v w := by rw [map_add, g.contract_add]
    map_smul' r v := by rw [map_smul, g.contract_smul]; rfl }

@[simp] theorem twoFormDivergenceCovector_apply (F : SmoothForm I M 2)
    (x : M) (v : TM x) :
    g.twoFormDivergenceCovector F x v = g.contract x ((g.twoFormDerivative F x).flip v) := rfl

/-- Metric contraction of the smooth native derivative is a smooth covector. -/
theorem twoFormDivergenceCovector_contMDiffAt (F : SmoothForm I M 2) (x : M) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (g.twoFormDivergenceCovector F y)) x := by
  let T := Tensor.SmoothBundle.tangent I (M := M)
  let S := Tensor.SmoothBundle.scalar I (M := M)
  apply Tensor.SmoothBundle.contMDiffAt_of_apply T S
  intro V hV
  have hA : ContMDiffAt I ((I).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E) y
        ((g.sharp y).toContinuousLinearMap.comp ((g.twoFormDerivative F y).flip (V y)))) x := by
    apply Tensor.SmoothBundle.contMDiffAt_of_apply T T
    intro U hU
    apply (g.sharp_smooth x).clm_bundle_apply
    apply Tensor.SmoothBundle.contMDiffAt_of_apply T S
    intro W hW
    exact (((g.twoFormDerivative_contMDiffAt F x).clm_bundle_apply hU).clm_bundle_apply hV).clm_bundle_apply hW
  have h := (Tensor.contMDiff_fiberTrace E (V := TM) («I» := I) x).clm_bundle_apply hA
  change ContMDiffAt I ((I).prod 𝓘(ℝ)) ∞
    (fun y => TotalSpace.mk' ℝ («E» := Bundle.Trivial M ℝ) y
      (g.twoFormDivergenceCovector F y (V y))) x
  simpa only [Tensor.fiberTrace_apply, twoFormDivergenceCovector_apply, contract] using h

def smoothTwoFormDivergenceCovector (F : SmoothForm I M 2) :
    Cₛ^∞⟮I; E →L[ℝ] ℝ, (fun x : M => TM x →L[ℝ] ℝ)⟯ :=
  ⟨g.twoFormDivergenceCovector F, g.twoFormDivergenceCovector_contMDiffAt F⟩

/-- The actual smooth vector obtained by contracting and raising `∇F`. -/
def twoFormDivergence (F : SmoothForm I M 2) : Cₛ^∞⟮I; E, TM⟯ :=
  g.raise (g.smoothTwoFormDivergenceCovector F)

@[simp] theorem twoFormDivergence_apply (F : SmoothForm I M 2) (x : M) :
    g.twoFormDivergence F x = g.sharp x (g.twoFormDivergenceCovector F x) := rfl

@[simp] theorem twoFormDivergence_pairing (F : SmoothForm I M 2) (x : M) (v : TM x) :
    g.form x (g.twoFormDivergence F x) v = g.contract x ((g.twoFormDerivative F x).flip v) :=
  g.form_sharp_left x _ v

/-- Contraction is evaluated in any pointwise tangent basis. -/
theorem twoFormDivergenceCovector_components (F : SmoothForm I M 2) (x : M)
    (e : TM x ≃L[ℝ] E) (v : TM x) :
    g.twoFormDivergenceCovector F x v = ∑ a, ∑ i,
      g.twoFormDerivative F x (e.symm (Pi.single a 1)) v (e.symm (Pi.single i 1)) *
        g.inverseComponent x e a i :=
  g.contract_eq_sum_components x e _

/-- Both raised indices in the divergence are the actual inverse metric. -/
theorem twoFormDivergence_components (F : SmoothForm I M 2) (x : M)
    (e : TM x ≃L[ℝ] E) (j : Fin (d + 1)) :
    e (g.twoFormDivergence F x) j = ∑ b, ∑ a, ∑ i,
      g.twoFormDerivative F x (e.symm (Pi.single a 1)) (e.symm (Pi.single b 1))
        (e.symm (Pi.single i 1)) * g.inverseComponent x e a i * g.inverseComponent x e j b := by
  rw [twoFormDivergence_apply, Tensor.covector_eq_sum x e (g.twoFormDivergenceCovector F x)]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [g.twoFormDivergenceCovector_components F x e, Finset.sum_mul, inverseComponent]

/-- The chart components are `gᵃⁱ gʲᵇ ∇ᵢFₐᵦ`, derived from the intrinsic trace. -/
theorem twoFormDivergence_chart (F : SmoothForm I M 2)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (j : Fin (d + 1)) :
    chartTangentMap e x (g.twoFormDivergence F x) j = ∑ b, ∑ a, ∑ i,
      g.twoFormCovariantComponent F e x i a b *
        g.inverseComponent x (chartTangentEquiv he hx) a i *
        g.inverseComponent x (chartTangentEquiv he hx) j b := by
  simpa only [chartTangentEquiv_apply, chartTangentEquiv_symm, twoFormCovariantComponent] using
    g.twoFormDivergence_components F x (chartTangentEquiv he hx) j

end ProjectAInos.SmoothGeometry.LorentzMetric
