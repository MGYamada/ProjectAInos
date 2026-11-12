/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurve
public import ProjectAInos.SmoothGeometry.Tensor.Contraction

/-! # Intrinsic divergence of a Lorentz vector field

Divergence is the trace of the actual Levi-Civita covariant derivative.
Its coordinate expression is derived from the connection, without an
orientation or a global frame.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "E" => MinkowskiModel d
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- Intrinsic contraction of the derivative index with the vector index. -/
def divergence (V : ∀ x, TM x) (x : M) : ℝ :=
  LinearMap.trace ℝ (TM x) (g.leviCivita V x).toLinearMap

/-- A smooth vector field has smooth divergence. -/
def smoothDivergence (V : Cₛ^∞⟮I; E, TM⟯) : C^∞⟮I, M; ℝ⟯ :=
  Tensor.trace E ⟨g.leviCivita V, fun x =>
    g.contMDiffAt_leviCivita (n := ⊤) (by simpa using V.contMDiff x)⟩

@[simp] theorem smoothDivergence_apply (V : Cₛ^∞⟮I; E, TM⟯) (x : M) :
    g.smoothDivergence V x = g.divergence V x := rfl

/-- Overall metric sign reversal leaves the connection and divergence unchanged. -/
@[simp] theorem divergence_opposite (V : ∀ x, TM x) (x : M) :
    g.opposite.divergence V x = g.divergence V x := by
  simp [divergence]

/-- The intrinsic trace can be evaluated in any pointwise tangent coordinates. -/
theorem divergence_eq_sum (V : ∀ x, TM x) (x : M) (e : TM x ≃L[ℝ] E) :
    g.divergence V x = ∑ i, e (g.leviCivita V x (e.symm (Pi.single i 1))) i := by
  have h := Tensor.traceL_eq_sum E (Pi.basisFun ℝ (Fin (d + 1)))
    (e.toContinuousLinearMap.comp ((g.leviCivita V x).comp e.symm.toContinuousLinearMap))
  have hc : Tensor.traceL E
      (e.toContinuousLinearMap.comp ((g.leviCivita V x).comp e.symm.toContinuousLinearMap)) =
      g.divergence V x :=
    LinearMap.trace_conj' (g.leviCivita V x).toLinearMap e.toLinearEquiv
  rw [hc] at h
  simpa using h

/-- In an actual smooth chart, divergence is `∂ᵢ Vⁱ + Γⁱᵢⱼ Vʲ`.
The derivative still uses the intrinsic tangent direction of the coordinate field. -/
theorem divergence_chart {V : ∀ x, TM x} {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (hV : MDifferentiableAt I ((I).prod I) (T% V) x) :
    g.divergence V x =
      (∑ i, mvfderiv I (fun y => chartTangentMap e y (V y)) x
        (chartField e (Pi.single i 1) x) i) +
      ∑ i, ∑ j, g.chartChristoffel e x i i j * chartTangentMap e x (V x) j := by
  rw [g.divergence_eq_sum V x (chartTangentEquiv he hx), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [chartTangentEquiv_apply, chartTangentEquiv_symm]
  rw [g.leviCivita_chart_decomposition he hx hV,
    map_add, Pi.add_apply, chartTangentMap_field he hx]
  have hc := g.leviCivita_chart_coordinates he hx
    (V := fun _ => chartTangentMap e x (V x)) mdifferentiableAt_const (Pi.single i 1) i
  simpa [mvfderiv, Pi.single_apply] using congrArg
    (fun r => mvfderiv I (fun y => chartTangentMap e y (V y)) x
      (chartField e (Pi.single i 1) x) i + r) hc

end ProjectAInos.SmoothGeometry.LorentzMetric
