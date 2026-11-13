/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeWedge
public import ProjectAInos.SmoothGeometry.DifferentialForm.WedgeAlgebra

/-! # Algebra and graded differentiation of native forms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

/-- Transport a smooth form along an equality of degrees. -/
def smoothDegreeCast {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {k l : ℕ} (h : k = l) (α : SmoothForm 𝓘(ℝ, E) M k) : SmoothForm 𝓘(ℝ, E) M l := h ▸ α

variable {n k l q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The constant scalar one, as a native smooth form of degree zero. -/
def smoothOne : SmoothForm 𝓘(ℝ, Fin n → ℝ) M 0 := by
  refine ⟨fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ
    (TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (Fin 0) (1 : ℝ), ?_⟩
  intro x
  apply (contMDiffAt_form_iff 𝓘(ℝ, Fin n → ℝ)).mpr
  have h : trivializationCoefficients 𝓘(ℝ, Fin n → ℝ)
      (fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ
        (TangentSpace 𝓘(ℝ, Fin n → ℝ) y) (Fin 0) (1 : ℝ)) x =
      fun _ => coordinateForm (n := n) ![] := by
    funext y
    ext v
    simp [trivializationCoefficients, coordinateForm_apply]
  rw [h]
  exact contMDiffAt_const

@[simp] theorem chartCoefficients_smoothOne (e : OpenPartialHomeomorph M (Fin n → ℝ)) :
    chartCoefficients e (fun x => (smoothOne : SmoothForm 𝓘(ℝ, Fin n → ℝ) M 0) x) =
      fun _ => coordinateForm ![] := by
  funext y
  ext v
  change (1 : ℝ) = coordinateForm ![] v
  simp

@[simp] theorem chartCoefficients_smoothDegreeCast (h : k = l)
    (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) (e : OpenPartialHomeomorph M (Fin n → ℝ))
    (y : Fin n → ℝ) :
    chartCoefficients e (fun x => smoothDegreeCast h α x) y =
      covectorDegreeCast h (chartCoefficients e (fun x => α x) y) := by cases h; rfl

@[simp] theorem chartCoefficients_smoothAdd (α β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (e : OpenPartialHomeomorph M (Fin n → ℝ)) (y : Fin n → ℝ) :
    chartCoefficients e (fun x => (α + β) x) y =
      chartCoefficients e (fun x => α x) y + chartCoefficients e (fun x => β x) y := rfl

@[simp] theorem chartCoefficients_smoothSmul (r : ℝ) (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (e : OpenPartialHomeomorph M (Fin n → ℝ)) (y : Fin n → ℝ) :
    chartCoefficients e (fun x => (r • α) x) y = r • chartCoefficients e (fun x => α x) y := rfl

/-- Native exterior product is associative, with the degree equality explicit. -/
theorem smoothWedge_assoc (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) (γ : SmoothForm 𝓘(ℝ, Fin n → ℝ) M q) :
    smoothDegreeCast (Nat.add_assoc k l q) (smoothWedge (smoothWedge α β) γ) =
      smoothWedge α (smoothWedge β γ) := by
  ext x : 1
  let e := chartAt (Fin n → ℝ) x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Fin n → ℝ) x
  have hy := e.map_source hx
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothDegreeCast,
    chartCoefficients_smoothWedge (smoothWedge α β) γ he hy,
    chartCoefficients_smoothWedge α (smoothWedge β γ) he hy]
  dsimp only [wedge]
  rw [chartCoefficients_smoothWedge α β he hy, chartCoefficients_smoothWedge β γ he hy]
  exact wedgeFiber_assoc _ _ _

/-- Native forms obey graded commutativity with sign `(-1)^(k*l)`. -/
theorem smoothWedge_comm (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothWedge α β = (-1 : ℝ) ^ (k * l) •
      smoothDegreeCast (Nat.add_comm l k) (smoothWedge β α) := by
  ext x : 1
  let e := chartAt (Fin n → ℝ) x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Fin n → ℝ) x
  have hy := e.map_source hx
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothSmul, chartCoefficients_smoothDegreeCast,
    chartCoefficients_smoothWedge α β he hy, chartCoefficients_smoothWedge β α he hy]
  exact wedgeFiber_comm _ _

/-- Scalar one is a left unit, with the degree equality explicit. -/
theorem smoothWedge_one_left (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) :
    smoothDegreeCast (Nat.zero_add k) (smoothWedge smoothOne α) = α := by
  ext x : 1
  let e := chartAt (Fin n → ℝ) x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Fin n → ℝ) x
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothDegreeCast,
    chartCoefficients_smoothWedge smoothOne α he (e.map_source hx), chartCoefficients_smoothOne]
  exact wedgeFiber_one_left _

/-- Scalar one is a right unit. -/
theorem smoothWedge_one_right (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k) :
    smoothWedge α smoothOne = α := by
  ext x : 1
  let e := chartAt (Fin n → ℝ) x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Fin n → ℝ) x
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothWedge α smoothOne he (e.map_source hx), chartCoefficients_smoothOne]
  exact wedgeFiber_one_right _

@[simp] theorem smoothExteriorDerivative_one :
    smoothExteriorDerivative (smoothOne : SmoothForm 𝓘(ℝ, Fin n → ℝ) M 0) = 0 := by
  ext x v
  change chartLift (chartAt (Fin n → ℝ) x)
    (extDeriv (chartCoefficients (chartAt (Fin n → ℝ) x) (fun y => smoothOne y))) x v = 0
  rw [chartCoefficients_smoothOne]
  simp [chartLift, nativePullback, extDeriv]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 0) ℝ (Fin n → ℝ) ℝ 0) _ = 0
  rw [map_zero]
  rfl

/-- The native exterior derivative satisfies the graded Leibniz rule as a section equality. -/
theorem smoothExteriorDerivative_wedge (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothExteriorDerivative (smoothWedge α β) =
      smoothDegreeCast (by omega : (k + 1) + l = (k + l) + 1)
        (smoothWedge (smoothExteriorDerivative α) β) +
      (-1 : ℝ) ^ k • smoothDegreeCast (Nat.add_assoc k l 1).symm
        (smoothWedge α (smoothExteriorDerivative β)) := by
  ext x : 1
  let e := chartAt (Fin n → ℝ) x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx : x ∈ e.source := mem_chart_source (Fin n → ℝ) x
  have hy := e.map_source hx
  have heq : chartCoefficients e (fun y => smoothWedge α β y) =ᶠ[𝓝 (e x)]
      wedge (chartCoefficients e (fun y => α y)) (chartCoefficients e (fun y => β y)) := by
    filter_upwards [e.open_target.mem_nhds hy] with y hy'
    exact chartCoefficients_smoothWedge α β he hy'
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothExteriorDerivative _ he hy, heq.extDeriv_eq]
  rw [chartCoefficients_smoothAdd, chartCoefficients_smoothSmul,
    chartCoefficients_smoothDegreeCast, chartCoefficients_smoothDegreeCast,
    chartCoefficients_smoothWedge (smoothExteriorDerivative α) β he hy,
    chartCoefficients_smoothWedge α (smoothExteriorDerivative β) he hy]
  dsimp only [wedge]
  rw [chartCoefficients_smoothExteriorDerivative α he hy,
    chartCoefficients_smoothExteriorDerivative β he hy]
  exact exteriorDerivative_wedge_cast _ _
    ((α.chartCoefficients_contDiffAt he hy).differentiableAt (by simp))
    ((β.chartCoefficients_contDiffAt he hy).differentiableAt (by simp))

end ProjectAInos.SmoothGeometry.DifferentialForm
