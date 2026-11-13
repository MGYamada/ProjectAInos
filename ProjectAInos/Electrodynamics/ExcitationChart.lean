/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Electrodynamics.Curved
public import ProjectAInos.SmoothGeometry.DifferentialForm.BivectorVolume
public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormRaised
public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormExterior
public import ProjectAInos.SmoothGeometry.Minkowski.TwoForm

/-! # The excitation in oriented coordinates

The native Hodge formula identifies the physical excitation with volume
duality of the density-weighted raised field. All coordinate quantities
come from actual tangent maps and metric raising.
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
  (g : LorentzMetric .timeNegative 3 M)

local notation "E" => MinkowskiModel 3
local notation "I" => 𝓘(ℝ, MinkowskiModel 3)

theorem hodgeChartMap_field_basis {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) (i : Fin 4) :
    chartField e (g.hodgeChartMap e x (Pi.single i 1)) x =
      lorentzSign .timeNegative i • g.chartRaisedCovector e x i := by
  have hf : Minkowski.flat .timeNegative (Pi.single i 1 : E) =
      lorentzSign .timeNegative i • (proj i : E →L[ℝ] ℝ) := by
    ext v
    fin_cases i <;> simp [Minkowski.flat_apply, minkowskiForm_apply,
      lorentzSign, Pi.single_apply]
  rw [← chartTangentEquiv_symm he hx]
  simp only [hodgeChartMap, comp_apply, ContinuousLinearEquiv.coe_coe, hf, map_smul]
  rw [g.chartSharp_apply he hx, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem hodgePreprocessed_component (F : Field (M := M))
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (i j : Fin 4) :
    Minkowski.component
      ((chartCoefficients e (fun y => F y) (e x)).compContinuousLinearMap (g.hodgeChartMap e x)) i j =
      lorentzSign .timeNegative i * lorentzSign .timeNegative j *
        g.raisedTwoFormComponent F e x i j := by
  change chartCoefficients e (fun y => F y) (e x)
    (fun k => g.hodgeChartMap e x (![Pi.single i 1, Pi.single j 1] k)) = _
  have ht : (fun k : Fin 2 => g.hodgeChartMap e x (![Pi.single i 1, Pi.single j 1] k)) =
      ![g.hodgeChartMap e x (Pi.single i 1), g.hodgeChartMap e x (Pi.single j 1)] := by
    ext k
    fin_cases k <;> rfl
  rw [ht, chartCoefficients_chartFields _ he hx]
  have hv : (fun k : Fin 2 => chartField e
      (![g.hodgeChartMap e x (Pi.single i 1), g.hodgeChartMap e x (Pi.single j 1)] k) x) =
      ![chartField e (g.hodgeChartMap e x (Pi.single i 1)) x,
        chartField e (g.hodgeChartMap e x (Pi.single j 1)) x] := by
    ext k
    fin_cases k <;> rfl
  rw [hv, hodgeChartMap_field_basis g he hx, hodgeChartMap_field_basis g he hx]
  simp only [← twoFormBilinear_apply]
  simp only [map_smul, smul_apply, smul_eq_mul,
    twoFormBilinear_apply, raisedTwoFormComponent]
  ring

/-- The actual excitation is volume duality of `ρ Fⁱʲ` in each signed smooth chart. -/
theorem excitation_chart (o : OrientedAtlas 4 M) (F : Field (M := M)) (p : M)
    {x : M} (hx : x ∈ (o.chart p).source) :
    chartCoefficients (o.chart p) (fun y => excitation g o F y) (o.chart p x) =
      o.sign p • bivectorVolume (fun i j =>
        g.chartDensity (o.chart p) x * g.raisedTwoFormComponent F (o.chart p) x i j) := by
  let e := o.chart p
  have hc : chartCoefficients e (fun y => excitation g o F y) (e x) =
      -chartCoefficients e (g.nativeHodge o (by decide : 2 + 2 = 3 + 1) (fun y => F y)) (e x) := by
    ext v
    rfl
  rw [hc, g.chartCoefficients_nativeHodge o p _ _ (e.map_source hx)]
  simp only [hodgeChart]
  dsimp only [e]
  rw [(o.chart p).left_inv hx]
  rw [Minkowski.hodgeTwo_expansion, bivectorVolume_apply]
  simp only [hodgePreprocessed_component g F (o.mem_atlas p) hx]
  ext v
  norm_num [lorentzSign, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

end ProjectAInos.Electrodynamics.Curved
