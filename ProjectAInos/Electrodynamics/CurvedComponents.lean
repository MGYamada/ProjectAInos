/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.ExcitationChart
public import ProjectAInos.Electrodynamics.Current
public import ProjectAInos.Electrodynamics.Homogeneous

/-! # Native Maxwell forms and covariant component equations

The actual excitation derivative is the volume dual of the intrinsic
two-form divergence. Thus the sourced equation and its coordinate form
are equivalent, with the sign of the public source convention
`∇_μ F^{μν} = j^ν` and no flatness premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.Electrodynamics.Curved
open SmoothGeometry SmoothGeometry.DifferentialForm SmoothGeometry.LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)

local notation "E" => MinkowskiModel 3
local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

/-- The source from `dH` is exactly the native covariant divergence of `F`. -/
theorem exteriorDerivative_excitation (F : Field (M := M)) :
    smoothExteriorDerivative (excitation g o F) = currentForm g o (g.twoFormDivergence F) := by
  ext x : 1
  let e := o.chart x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := o.mem_atlas x
  have hx : x ∈ e.source := o.mem_source x
  let W : M → Fin 4 → Fin 4 → ℝ := fun y i j =>
    g.chartDensity e y * g.raisedTwoFormComponent F e y i j
  have hW : ContMDiffAt I 𝓘(ℝ, Fin 4 → Fin 4 → ℝ) ∞ W x := by
    apply contMDiffAt_pi_module_iff.mpr
    intro i
    apply contMDiffAt_pi_module_iff.mpr
    intro j
    exact (g.chartDensity_contMDiffAt he hx).mul (g.raisedTwoFormComponent_contMDiffAt F he hx i j)
  have hPhi : DifferentiableAt ℝ (W ∘ e.symm) (e x) :=
    ((hW.mdifferentiableAt (by simp)).comp_of_eq (e x)
      ((contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).mdifferentiableAt (by simp))
      (e.left_inv hx)).differentiableAt
  have hskew : ∀ᶠ y in 𝓝 (e x), ∀ i j, (W ∘ e.symm) y i j = -(W ∘ e.symm) y j i := by
    apply Filter.Eventually.of_forall
    intro y i j
    change g.chartDensity e (e.symm y) * g.raisedTwoFormComponent F e (e.symm y) i j =
      -(g.chartDensity e (e.symm y) * g.raisedTwoFormComponent F e (e.symm y) j i)
    rw [g.raisedTwoFormComponent_skew F e (e.symm y) i j]
    ring
  have htrace : (fun j => ∑ i : Fin 4, fderiv ℝ (W ∘ e.symm) (e x) (Pi.single i 1) i j) =
      g.chartDensity e x • chartTangentMap e x (g.twoFormDivergence F x) := by
    ext j
    change _ = g.chartDensity e x * chartTangentMap e x (g.twoFormDivergence F x) j
    rw [g.chartDensity_mul_twoFormDivergence F he hx]
    apply Finset.sum_congr rfl
    intro i _
    rw [← fderiv_matrix_apply hPhi i j (Pi.single i 1)]
    exact (mvfderiv_chartField he hx
      (((g.chartDensity_contMDiffAt he hx).mul
        (g.raisedTwoFormComponent_contMDiffAt F he hx i j)).mdifferentiableAt (by simp))
      (Pi.single i 1)).symm
  have hcoeff : chartCoefficients e (fun y => excitation g o F y) =ᶠ[𝓝 (e x)]
      fun y => o.sign x • bivectorVolume ((W ∘ e.symm) y) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    have h := excitation_chart g o F x (e.map_target hy)
    change chartCoefficients e (fun y => excitation g o F y) (e (e.symm y)) = _ at h
    rwa [e.right_inv hy] at h
  apply nativeForm_eq_of_chartCoefficients he hx
    (α := fun y => smoothExteriorDerivative (excitation g o F) y)
    (β := fun y => currentForm g o (g.twoFormDivergence F) y)
  rw [chartCoefficients_smoothExteriorDerivative _ he (e.map_source hx), hcoeff.extDeriv_eq]
  change extDeriv (o.sign x • (fun y => bivectorVolume ((W ∘ e.symm) y))) (e x) = _
  rw [extDeriv_smul, extDeriv_bivectorVolume hPhi hskew, htrace,
    currentForm_chart g o (g.twoFormDivergence F) x (e.map_source hx)]
  change o.sign x • interior (g.chartDensity e x • chartTangentMap e x (g.twoFormDivergence F x))
      (coordinateForm id) = (o.sign x * g.chartDensity e (e.symm (e x))) •
        interior (chartTangentMap e (e.symm (e x)) (g.twoFormDivergence F (e.symm (e x))))
          (coordinateForm id)
  rw [e.left_inv hx, interior_smul_vector, smul_smul]

theorem source_eq_twoFormDivergence (F : Field (M := M)) :
    source g o F = g.twoFormDivergence F := by
  apply (currentEquiv g o).injective
  exact (source_spec g o F).trans (exteriorDerivative_excitation g o F)

/-- The sourced form equation and native vector equation are equivalent. -/
theorem sourced_iff_divergence (F : Field (M := M)) (j : CurrentVector (M := M)) :
    smoothExteriorDerivative (excitation g o F) = currentForm g o j ↔
      g.twoFormDivergence F = j := by
  rw [exteriorDerivative_excitation]
  exact (currentEquiv g o).injective.eq_iff

theorem Maxwell.twoFormDivergence {F : Field (M := M)} {j : CurrentVector (M := M)}
    (h : Maxwell g o F j) : g.twoFormDivergence F = j :=
  (sourced_iff_divergence g o F j).mp h.2

/-- The source vector has the positive-volume-density expression in every smooth chart. -/
theorem source_density (F : Field (M := M)) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (j : Fin 4) :
    chartTangentMap e x (source g o F x) j = (g.chartDensity e x)⁻¹ *
      ∑ i, mvfderiv I (fun y => g.chartDensity e y * g.raisedTwoFormComponent F e y i j) x
        (chartField e (Pi.single i 1) x) := by
  rw [source_eq_twoFormDivergence, g.twoFormDivergence_density F he hx]

/-- Both Maxwell equations, expressed entirely in native covariant derivatives. -/
theorem maxwell_iff_covariant (F : Field (M := M)) (j : CurrentVector (M := M)) :
    Maxwell g o F j ↔
      (∀ x (u v w : TangentSpace I x), g.twoFormDerivative F x v w u +
        g.twoFormDerivative F x w u v + g.twoFormDerivative F x u v w = 0) ∧
      g.twoFormDivergence F = j := by
  rw [Maxwell, g.exteriorDerivative_zero_iff_covariant, sourced_iff_divergence]

/-- The source vector is independent of the two choices of orientation. -/
theorem source_reverse (F : Field (M := M)) : source g o.reverse F = source g o F := by
  rw [source_eq_twoFormDivergence, source_eq_twoFormDivergence]

include o in
/-- Every two-form divergence is a conserved native vector current. -/
theorem divergence_twoFormDivergence (F : Field (M := M)) (x : M) :
    g.divergence (g.twoFormDivergence F) x = 0 :=
  divergence_zero_of_source g o F (g.twoFormDivergence F) (exteriorDerivative_excitation g o F) x

/-- The sourced equation is equivalent to `∇ᵢFⁱʲ = jʲ` in every smooth chart. -/
theorem sourced_iff_components (F : Field (M := M)) (j : CurrentVector (M := M)) :
    smoothExteriorDerivative (excitation g o F) = currentForm g o j ↔
      ∀ (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas I ∞ M),
        ∀ (x : M) (hx : x ∈ e.source), ∀ k : Fin 4,
          (∑ b, ∑ a, ∑ i, g.twoFormCovariantComponent F e x i a b *
            g.inverseComponent x (chartTangentEquiv he hx) a i *
            g.inverseComponent x (chartTangentEquiv he hx) k b) = chartTangentMap e x (j x) k := by
  rw [sourced_iff_divergence]
  constructor
  · intro h e he x hx k
    rw [← g.twoFormDivergence_chart F he hx, h]
  · intro h
    ext x : 1
    let e := chartAt E x
    have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas x
    have hx : x ∈ e.source := mem_chart_source E x
    apply (chartTangentEquiv he hx).injective
    ext k
    rw [chartTangentEquiv_apply, g.twoFormDivergence_chart F he hx]
    exact h e he x hx k

/-- The premetric equations are equivalent to the two covariant coordinate equations. -/
theorem maxwell_iff_components (F : Field (M := M)) (j : CurrentVector (M := M)) :
    Maxwell g o F j ↔
      (∀ (e : OpenPartialHomeomorph M E), e ∈ IsManifold.maximalAtlas I ∞ M →
        ∀ x ∈ e.source, ∀ i k l : Fin 4,
          g.twoFormCovariantComponent F e x i k l +
          g.twoFormCovariantComponent F e x k l i +
          g.twoFormCovariantComponent F e x l i k = 0) ∧
      (∀ (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas I ∞ M),
        ∀ (x : M) (hx : x ∈ e.source), ∀ k : Fin 4,
          (∑ b, ∑ a, ∑ i, g.twoFormCovariantComponent F e x i a b *
            g.inverseComponent x (chartTangentEquiv he hx) a i *
            g.inverseComponent x (chartTangentEquiv he hx) k b) = chartTangentMap e x (j x) k) := by
  rw [Maxwell, g.exteriorDerivative_zero_iff_components, sourced_iff_components]

end ProjectAInos.Electrodynamics.Curved
