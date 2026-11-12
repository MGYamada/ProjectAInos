/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.FiniteDual
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeWedge

/-! # Intrinsic finite-fibre wedge and its native-chart comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]
  {k l : ℕ}

/-- Exterior product on a finite topological fibre, without choosing a norm or basis. -/
def finiteWedge (α : V [⋀^Fin k]→L[ℝ] ℝ) (β : V [⋀^Fin l]→L[ℝ] ℝ) :
    V [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  finiteToExterior.symm
    (exteriorPower.wedge ℝ (Dual ℝ V) k l (finiteToExterior α) (finiteToExterior β))

@[simp] theorem finiteToExterior_wedge (α : V [⋀^Fin k]→L[ℝ] ℝ)
    (β : V [⋀^Fin l]→L[ℝ] ℝ) :
    finiteToExterior (finiteWedge α β) =
      exteriorPower.wedge ℝ (Dual ℝ V) k l (finiteToExterior α) (finiteToExterior β) :=
  finiteToExterior.apply_symm_apply _

theorem finiteWedge_model {n : ℕ} (α : (Fin n → ℝ) [⋀^Fin k]→L[ℝ] ℝ)
    (β : (Fin n → ℝ) [⋀^Fin l]→L[ℝ] ℝ) : finiteWedge α β = wedgeFiber α β := rfl

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W]

theorem finiteWedge_comp (L : V →L[ℝ] W) (α : W [⋀^Fin k]→L[ℝ] ℝ)
    (β : W [⋀^Fin l]→L[ℝ] ℝ) :
    finiteWedge (α.compContinuousLinearMap L) (β.compContinuousLinearMap L) =
      (finiteWedge α β).compContinuousLinearMap L := by
  apply finiteToExterior.injective
  rw [finiteToExterior_wedge, finiteToExterior_comp, finiteToExterior_comp,
    finiteToExterior_comp, finiteToExterior_wedge, wedge_map]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- Chart coefficients of the intrinsic fibre product are the established coordinate wedge. -/
theorem chartCoefficients_finiteWedge (e : OpenPartialHomeomorph M (Fin n → ℝ))
    (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k) (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l)
    (y : Fin n → ℝ) :
    chartCoefficients e (fun x => finiteWedge (α x) (β x)) y =
      wedgeFiber (chartCoefficients e α y) (chartCoefficients e β y) := by
  change (finiteWedge (α (e.symm y)) (β (e.symm y))).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) e.symm y) = _
  rw [← finiteWedge_comp, finiteWedge_model]
  rfl

/-- The chart construction is exactly the intrinsic wedge on each actual tangent fibre. -/
theorem nativeWedge_eq_finiteWedge (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l) (x : M) :
    nativeWedge α β x = finiteWedge (α x) (β x) := by
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx := mem_chart_source (Fin n → ℝ) x
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_nativeWedge α β he ((chartAt (Fin n → ℝ) x).map_source hx),
    chartCoefficients_finiteWedge]
  rfl

end ProjectAInos.SmoothGeometry.DifferentialForm
