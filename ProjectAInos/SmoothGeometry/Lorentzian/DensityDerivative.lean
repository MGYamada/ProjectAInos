/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.MetricDensityDerivative
public import ProjectAInos.SmoothGeometry.Lorentzian.VolumeDensity
public import ProjectAInos.SmoothGeometry.Lorentzian.Divergence

/-! # The Lorentz density derivative and divergence formula

Metric compatibility determines the derivative of the positive density.
All formulas hold in each smooth chart on its source, without an orientation.
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

theorem chartComponent_contMDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(ℝ, Fin (d + 1) → Fin (d + 1) → ℝ) ∞ (g.chartComponent e) x := by
  apply contMDiffAt_pi_module_iff.mpr
  intro i
  apply contMDiffAt_pi_module_iff.mpr
  intro j
  exact g.contMDiffAt_pairing (chartField_contMDiffAt he hx (Pi.single i 1))
    (chartField_contMDiffAt he hx (Pi.single j 1))

/-- Metric compatibility expressed in the actual coordinate frame. -/
theorem chartComponent_derivative {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (k i j : Fin (d + 1)) :
    mvfderiv I (fun y => g.chartComponent e y i j) x (chartField e (Pi.single k 1) x) =
      (∑ l, g.chartChristoffel e x l k i * g.chartComponent e x l j) +
      ∑ l, g.chartComponent e x i l * g.chartChristoffel e x l k j := by
  have h := g.leviCivita_metricCompatible (chartField e (Pi.single k 1) x)
    (chartField_mdifferentiableAt he hx (Pi.single i 1))
    (chartField_mdifferentiableAt he hx (Pi.single j 1))
  have hc (a : Fin (d + 1)) :
      g.leviCivita (chartField e (Pi.single a 1)) x (chartField e (Pi.single k 1) x) =
        ∑ l, g.chartChristoffel e x l k a • chartField e (Pi.single l 1) x := by
    calc
      _ = chartField e (chartTangentMap e x
          (g.leviCivita (chartField e (Pi.single a 1)) x (chartField e (Pi.single k 1) x))) x :=
        (chartField_tangentMap he hx _).symm
      _ = _ := chartField_eq_sum e x _
  change mvfderiv I (fun y => g.chartComponent e y i j) x _ = _ at h
  rw [hc i, hc j] at h
  simpa only [map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul, chartComponent, mul_comm] using h

/-- Differentiation of the full coefficient matrix has the compatible matrix form. -/
theorem chartComponent_matrix_derivative {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (k : Fin (d + 1)) :
    mvfderiv I (g.chartComponent e) x (chartField e (Pi.single k 1) x) =
      (Matrix.of fun i l => g.chartChristoffel e x l k i) * Matrix.of (g.chartComponent e x) +
        Matrix.of (g.chartComponent e x) *
          (Matrix.of fun i l => g.chartChristoffel e x l k i).transpose := by
  have hG := (g.chartComponent_contMDiffAt he hx).mdifferentiableAt (by simp)
  ext i j
  let P : (Fin (d + 1) → Fin (d + 1) → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : E →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin (d + 1) → Fin (d + 1) → ℝ) →L[ℝ] E)
  have hp := congrArg (fun L => L (chartField e (Pi.single k 1) x))
    (mvfderiv_comp x P.mdifferentiableAt hG)
  rw [mvfderiv_eq_fderiv, P.fderiv] at hp
  change mvfderiv I (fun y => g.chartComponent e y i j) x _ =
    mvfderiv I (g.chartComponent e) x _ i j at hp
  rw [← hp, g.chartComponent_derivative he hx]
  rfl

/-- The logarithmic density derivative is the contracted Levi-Civita coefficient. -/
theorem chartDensity_derivative {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (k : Fin (d + 1)) :
    mvfderiv I (g.chartDensity e) x (chartField e (Pi.single k 1) x) =
      (∑ i, g.chartChristoffel e x i i k) * g.chartDensity e x := by
  let D : (Fin (d + 1) → Fin (d + 1) → ℝ) → ℝ :=
    fun B => Real.sqrt |Matrix.det (Matrix.of B)|
  have hd := MetricDensity.differentiableAt_density (g.chartComponent e x)
    (g.chartComponent_det_ne_zero he hx)
  have hG := (g.chartComponent_contMDiffAt he hx).mdifferentiableAt (by simp)
  have hc := congrArg (fun L => L (chartField e (Pi.single k 1) x))
    (mvfderiv_comp x hd.mdifferentiableAt hG)
  rw [mvfderiv_eq_fderiv] at hc
  change mvfderiv I (g.chartDensity e) x _ =
    fderiv ℝ D (g.chartComponent e x)
      (mvfderiv I (g.chartComponent e) x (chartField e (Pi.single k 1) x)) at hc
  rw [hc, g.chartComponent_matrix_derivative he hx]
  have hm := MetricDensity.fderiv_density_compatible (g.chartComponent e x)
    (fun i l => g.chartChristoffel e x l k i) (g.chartComponent_det_ne_zero he hx)
  change _ = (∑ i, g.chartChristoffel e x i k i) * g.chartDensity e x at hm
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact g.chartChristoffel_symmetric he hx i k i

/-- The density-weighted coordinate derivative is the intrinsic divergence times density. -/
theorem chartDensity_mul_divergence {V : ∀ x, TM x} {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (hV : MDifferentiableAt I ((I).prod I) (T% V) x) :
    g.chartDensity e x * g.divergence V x =
      ∑ i, mvfderiv I (fun y => g.chartDensity e y • chartTangentMap e y (V y)) x
        (chartField e (Pi.single i 1) x) i := by
  have hρ := (g.chartDensity_contMDiffAt he hx).mdifferentiableAt (by simp)
  have hC := chartTangentMap_mdifferentiableAt he hx hV
  have hp := mvfderiv_smul hρ hC
  change mvfderiv I (fun y => g.chartDensity e y • chartTangentMap e y (V y)) x = _ at hp
  rw [g.divergence_chart he hx hV]
  simp only [hp, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    g.chartDensity_derivative he hx, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- In every chart, `div V = ρ⁻¹ ∂ᵢ(ρ Vⁱ)` with `ρ = sqrt(abs(det g))`. -/
theorem divergence_density {V : ∀ x, TM x} {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source)
    (hV : MDifferentiableAt I ((I).prod I) (T% V) x) :
    g.divergence V x = (g.chartDensity e x)⁻¹ *
      ∑ i, mvfderiv I (fun y => g.chartDensity e y • chartTangentMap e y (V y)) x
        (chartField e (Pi.single i 1) x) i := by
  rw [← g.chartDensity_mul_divergence he hx hV,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (g.chartDensity_pos he hx)), one_mul]

end ProjectAInos.SmoothGeometry.LorentzMetric
