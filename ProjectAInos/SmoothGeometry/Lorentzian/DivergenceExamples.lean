/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.DensityDerivative
public import ProjectAInos.SmoothGeometry.Lorentzian.VolumeExamples

/-! # Nonzero divergence in the curved conformal plane -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianDivergenceExamples
open LorentzMetric LorentzianConformalExample

/-- A coordinate-constant spatial field has nonzero intrinsic divergence. -/
theorem conformal_spatial_divergence (p : Plane) :
    metric.divergence (modelField (Pi.single 1 1)) p = 4 * p 1 := by
  rw [metric.divergence_eq_sum _ p (NormedSpace.fromTangentSpace p)]
  change (∑ i : Fin 2, NormedSpace.fromTangentSpace p
    (metric.leviCivita (modelField (Pi.single 1 1)) p
      (modelField (Pi.single i 1) p)) i) = _
  simp_rw [leviCivita_modelField]
  simp [modelField, Fin.sum_univ_succ, Pi.single_apply]
  ring

/-- A direct density derivative gives the same nonzero divergence. -/
theorem conformal_density_gradient (p : Plane) :
    fderiv ℝ (fun q : Plane => Real.exp (2 * (q 1) ^ 2)) p (Pi.single 1 1) =
      metric.divergence (modelField (Pi.single 1 1)) p *
        metric.chartDensity (OpenPartialHomeomorph.refl Plane) p := by
  have hp := (ContinuousLinearMap.proj 1 : Plane →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hd := ((hp.pow 2).const_mul 2).exp
  change HasFDerivAt (fun q : Plane => Real.exp (2 * (q 1) ^ 2)) _ p at hd
  rw [hd.fderiv,
    conformal_spatial_divergence, LorentzianVolumeExamples.conformal_density]
  simp
  ring

end ProjectAInos.SmoothGeometry.LorentzianDivergenceExamples
