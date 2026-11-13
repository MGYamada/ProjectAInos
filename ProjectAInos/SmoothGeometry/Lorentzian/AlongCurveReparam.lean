/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurve
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Velocity regularity and reparametrization along curves -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- A `C^(n+1)` curve has a `C^n` velocity section along itself. -/
theorem curveVelocity_contMDiffAt {n : ℕ∞ω} {γ : ℝ → M} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I (n + 1) γ t) :
    ContMDiffAt 𝓘(ℝ) ((I).prod I) n
      (fun s => TotalSpace.mk' E (γ s) (curveVelocity (d := d) γ s)) t := by
  let unit : ℝ → TangentBundle 𝓘(ℝ) ℝ :=
    fun s => TotalSpace.mk' ℝ s ((NormedSpace.fromTangentSpace s).symm 1)
  have hu : ContMDiffAt 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) n unit t := by
    rw [contMDiffAt_section]
    simpa [unit, NormedSpace.fromTangentSpace, tangentSpaceCastModel,
      TangentBundle.trivializationAt_apply] using!
      (contMDiffAt_const (c := (1 : ℝ)) : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) n (fun _ : ℝ => (1 : ℝ)) t)
  exact (hγ.contMDiffAt_tangentMap (X := unit t) le_rfl).comp t hu

omit [IsManifold I ∞ M] in
/-- Velocity transforms by the derivative of the parameter change. -/
theorem curveVelocity_comp {γ : ℝ → M} {r : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ (r t)) (hr : DifferentiableAt ℝ r t) :
    curveVelocity (d := d) (γ ∘ r) t = deriv r t • curveVelocity (d := d) γ (r t) := by
  have hv : mfderiv 𝓘(ℝ) 𝓘(ℝ) r t ((NormedSpace.fromTangentSpace t).symm 1) =
      deriv r t • (NormedSpace.fromTangentSpace (r t)).symm 1 := by
    rw [mfderiv_eq_fderiv]
    simp only [comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    change (NormedSpace.fromTangentSpace (r t)).symm (deriv r t) = _
    rw [← map_smul]
    simp
  simp only [curveVelocity, mfderiv_comp t hγ hr.mdifferentiableAt]
  change mfderiv 𝓘(ℝ) I γ (r t)
    (mfderiv 𝓘(ℝ) 𝓘(ℝ) r t ((NormedSpace.fromTangentSpace t).symm 1)) = _
  rw [hv, map_smul]

/-- Covariant differentiation transforms with the parameter speed, including
at zeros of that speed; no invertibility of the parameter map is needed. -/
theorem covariantAlong_reparam (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {r : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ (r t)) (hr : DifferentiableAt ℝ r t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) (r t)) :
    g.covariantAlong (γ := γ ∘ r) (fun s => V (r s)) t =
      deriv r t • g.covariantAlong V (r t) := by
  let e := chartAt E (γ (r t))
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ (r t))
  have hx : γ (r t) ∈ e.source := mem_chart_source E (γ (r t))
  have hC := alongComponents_mdifferentiableAt he hx hV
  have hd := (hC.hasDerivAt.scomp t hr.hasDerivAt).deriv
  change deriv (alongComponents e (γ := γ ∘ r) (fun s => V (r s))) t = _ at hd
  change g.chartCovariantAlong e (γ := γ ∘ r) (fun s => V (r s)) t =
    deriv r t • g.chartCovariantAlong e V (r t)
  simp only [chartCovariantAlong, hd, curveVelocity_comp hγ hr, chartField_smul, map_smul,
    smul_add]
  rfl

/-- Covariant acceleration includes the second derivative of a parameter
change. The formula also holds when its first derivative vanishes. -/
theorem covariantAcceleration_reparam (g : LorentzMetric σ d M)
    {γ : ℝ → M} {r : ℝ → ℝ} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (r t)) (hr : ContDiffAt ℝ 2 r t) :
    g.covariantAlong (curveVelocity (d := d) (γ ∘ r)) t =
      deriv (deriv r) t • curveVelocity (d := d) γ (r t) +
        (deriv r t)^2 • g.covariantAlong (curveVelocity (d := d) γ) (r t) := by
  have hγd := hγ.mdifferentiableAt (by norm_num)
  have hrd := hr.differentiableAt (by norm_num)
  have hγn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hγ.of_le (by norm_num))
  have hrn := hr.eventually (by norm_num)
  have hv : ∀ᶠ s in 𝓝 t, curveVelocity (d := d) (γ ∘ r) s =
      deriv r s • curveVelocity (d := d) γ (r s) := by
    filter_upwards [hr.continuousAt hγn, hrn] with s hγs hrs
    exact curveVelocity_comp (hγs.mdifferentiableAt (by norm_num))
      (hrs.differentiableAt (by norm_num))
  have hV := (curveVelocity_contMDiffAt (n := 1) hγ).mdifferentiableAt (by norm_num)
  have hr' := (hr.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [g.covariantAlong_congr hv, g.covariantAlong_smul hr' (hV.comp t hrd.mdifferentiableAt),
    g.covariantAlong_reparam hγd hrd hV, smul_smul, pow_two]

end ProjectAInos.SmoothGeometry.LorentzMetric
