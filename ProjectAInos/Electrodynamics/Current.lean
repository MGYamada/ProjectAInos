/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Curved
public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeCurrent
public import ProjectAInos.SmoothGeometry.Lorentzian.DensityDerivative
public import ProjectAInos.SmoothGeometry.DifferentialForm.InteriorDerivative

/-! # Current forms, volume contraction and intrinsic divergence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology

namespace ProjectAInos.Electrodynamics.Curved
open SmoothGeometry SmoothGeometry.DifferentialForm SmoothGeometry.LorentzMetric

variable {M : Type} [TopologicalSpace M] [ChartedSpace (MinkowskiModel 3) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel 3) ∞ M]
  (g : LorentzMetric .timeNegative 3 M) (o : OrientedAtlas 4 M)

local notation "I" => 𝓘(ℝ, MinkowskiModel 3)
local notation "E" => MinkowskiModel 3

/-- The physical current is contraction of the actual oriented volume with the vector current. -/
theorem currentForm_volume (j : CurrentVector (M := M)) (x : M) :
    currentForm g o j x = interior (j x) (g.volumeForm o x) := g.hodge_flat_one o x (j x)

/-- Current coefficients use the positive density and the selected chart's orientation sign. -/
theorem currentForm_chart (j : CurrentVector (M := M)) (p : M) {y : E}
    (hy : y ∈ (o.chart p).target) :
    chartCoefficients (o.chart p) (fun x => currentForm g o j x) y =
      (o.sign p * g.chartDensity (o.chart p) ((o.chart p).symm y)) •
        interior (chartTangentMap (o.chart p) ((o.chart p).symm y) (j ((o.chart p).symm y)))
          (coordinateForm id) := by
  let e := o.chart p
  have hx : e.symm y ∈ e.source := e.map_target hy
  have hi : mfderiv I I e.symm y (chartTangentMap e (e.symm y) (j (e.symm y))) =
      j (e.symm y) := by
    have h := ((chart_mdifferentiable (o.mem_atlas p)).mfderiv hx).symm_apply_apply (j (e.symm y))
    change mfderiv I I e.symm (e (e.symm y)) (mfderiv I I e (e.symm y) (j (e.symm y))) = _ at h
    rw [e.right_inv hy] at h
    exact h
  have hv := g.chartCoefficients_volumeForm o p hy
  have hc := interior_comp (mfderiv I I e.symm y)
    (chartTangentMap e (e.symm y) (j (e.symm y))) (g.volumeForm o (e.symm y))
  rw [hi] at hc
  change interior (chartTangentMap e (e.symm y) (j (e.symm y)))
    (chartCoefficients e (fun x => g.volumeForm o x) y) = _ at hc
  rw [hv, DifferentialForm.interior_smul] at hc
  change (currentForm g o j (e.symm y)).compContinuousLinearMap (mfderiv I I e.symm y) = _
  rw [currentForm_volume]
  exact hc.symm

/-- Exterior differentiation of the physical current is intrinsic divergence times volume. -/
theorem exteriorDerivative_currentForm (j : CurrentVector (M := M)) (x : M) :
    smoothExteriorDerivative (currentForm g o j) x =
      g.divergence j x • g.volumeForm o x := by
  let e := o.chart x
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := o.mem_atlas x
  have hx : x ∈ e.source := o.mem_source x
  let W : M → E := fun y => g.chartDensity e y • chartTangentMap e y (j y)
  have hj := (j.contMDiff x).mdifferentiableAt (by simp)
  have hW : MDifferentiableAt I I W x :=
    ((g.chartDensity_contMDiffAt he hx).mdifferentiableAt (by simp)).smul
      (chartTangentMap_mdifferentiableAt he hx hj)
  have hPhi : DifferentiableAt ℝ (W ∘ e.symm) (e x) :=
    (hW.comp_of_eq (e x)
      ((contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).mdifferentiableAt (by simp))
      (e.left_inv hx)).differentiableAt
  have htrace : (∑ i : Fin 4, fderiv ℝ (W ∘ e.symm) (e x) (Pi.single i 1) i) =
      g.chartDensity e x * g.divergence j x := by
    rw [g.chartDensity_mul_divergence he hx hj]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun v : E => v i) (mvfderiv_chartField he hx hW (Pi.single i 1)).symm
  have hcoeff : chartCoefficients e (fun y => currentForm g o j y) =ᶠ[𝓝 (e x)]
      fun y => o.sign x • interior ((W ∘ e.symm) y) (coordinateForm id) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    rw [currentForm_chart g o j x hy]
    simp only [W, e, Function.comp_apply, interior_smul_vector, smul_smul]
  apply nativeForm_eq_of_chartCoefficients he hx
    (α := fun y => smoothExteriorDerivative (currentForm g o j) y)
    (β := fun y => g.divergence j y • g.volumeForm o y)
  rw [chartCoefficients_smoothExteriorDerivative _ he (e.map_source hx),
    hcoeff.extDeriv_eq]
  change extDeriv (o.sign x • (fun y => interior ((W ∘ e.symm) y) (coordinateForm id))) (e x) = _
  rw [extDeriv_smul, extDeriv_interior_volume_four hPhi, htrace]
  change o.sign x • ((g.chartDensity e x * g.divergence j x) • coordinateForm id) =
    g.divergence j (e.symm (e x)) • chartCoefficients e (fun y => g.volumeForm o y) (e x)
  rw [g.chartCoefficients_volumeForm o x (e.map_source hx)]
  change o.sign x • ((g.chartDensity e x * g.divergence j x) • coordinateForm id) =
    g.divergence j (e.symm (e x)) •
      ((o.sign x * g.chartDensity e (e.symm (e x))) • coordinateForm id)
  simp only [e.left_inv hx, smul_smul]
  congr 1
  ring

/-- Closedness of the current form is exactly vanishing intrinsic vector divergence. -/
theorem current_closed_iff_divergence (j : CurrentVector (M := M)) :
    smoothExteriorDerivative (currentForm g o j) = 0 ↔ ∀ x, g.divergence j x = 0 := by
  constructor
  · intro h x
    have hx := congrArg (fun α : SmoothForm I M 4 => α x) h
    change smoothExteriorDerivative (currentForm g o j) x = 0 at hx
    rw [exteriorDerivative_currentForm] at hx
    exact (smul_eq_zero.mp hx).resolve_right (g.volumeForm_ne_zero o x)
  · intro h
    ext x : 1
    rw [exteriorDerivative_currentForm, h x, zero_smul]
    rfl

/-- The sourced Maxwell equation implies covariant vector-current conservation. -/
theorem divergence_zero_of_source (F : Field (M := M)) (j : CurrentVector (M := M))
    (h : smoothExteriorDerivative (excitation g o F) = currentForm g o j) :
    ∀ x, g.divergence j x = 0 :=
  (current_closed_iff_divergence g o j).mp (current_closed_of_source g o F j h)

theorem Maxwell.divergence_zero {F : Field (M := M)} {j : CurrentVector (M := M)}
    (h : Maxwell g o F j) (x : M) : g.divergence j x = 0 :=
  divergence_zero_of_source g o F j h.2 x

end ProjectAInos.Electrodynamics.Curved
