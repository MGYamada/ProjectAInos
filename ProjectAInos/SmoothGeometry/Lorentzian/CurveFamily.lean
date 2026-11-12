/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveMetric
public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveReparam
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Native derivatives of two-parameter curve families

Parameter velocities are actual tangent vectors obtained from the manifold
derivative. C² regularity and zero torsion give the interchange law needed
for curve variations, without an immersion or a global chart assumption.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "P" => ℝ × ℝ
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- A directional velocity of a two-parameter family, in its actual tangent fibre. -/
def familyVelocity (Γ : P → M) (v : P) (z : P) : TangentSpace I (Γ z) :=
  mfderiv J I Γ z ((NormedSpace.fromTangentSpace z).symm v)

theorem familyVelocity_contMDiffAt {Γ : P → M} {z : P} (v : P)
    (hΓ : ContMDiffAt J I 2 Γ z) :
    ContMDiffAt J ((I).prod I) 1
      (fun q => TotalSpace.mk' E (Γ q) (familyVelocity (d := d) Γ v q)) z := by
  let unit : P → TangentBundle J P :=
    fun q => TotalSpace.mk' P q ((NormedSpace.fromTangentSpace q).symm v)
  have hu : ContMDiffAt J ((J).prod J) 1 unit z := by
    rw [contMDiffAt_section]
    simpa [unit, NormedSpace.fromTangentSpace, tangentSpaceCastModel,
      TangentBundle.trivializationAt_apply] using!
      (contMDiffAt_const (c := v) : ContMDiffAt J J 1 (fun _ : P => v) z)
  exact (hΓ.contMDiffAt_tangentMap (X := unit z) (by norm_num)).comp z hu

omit [IsManifold I ∞ M] in
theorem chartTangentMap_familyVelocity {Γ : P → M} {z : P} (v : P)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : Γ z ∈ e.source) (hΓ : MDifferentiableAt J I Γ z) :
    chartTangentMap e (Γ z) (familyVelocity Γ v z) = fderiv ℝ (e ∘ Γ) z v := by
  have hd := mfderiv_comp z ((contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt
    (by simp)) hΓ
  have h := congrArg (fun L => L ((NormedSpace.fromTangentSpace z).symm v)) hd
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (e ∘ Γ) z v = chartTangentMap e (Γ z) (familyVelocity Γ v z) at h
  exact h.symm

omit [IsManifold I ∞ M] in
/-- The native family velocity agrees with differentiation of any regular
parameter path, including the two coordinate slices. -/
theorem curveVelocity_family {Γ : P → M} {ρ : ℝ → P} {t : ℝ} {v : P}
    (hΓ : MDifferentiableAt J I Γ (ρ t)) (hρ : HasDerivAt ρ v t) :
    curveVelocity (d := d) (Γ ∘ ρ) t = familyVelocity (d := d) Γ v (ρ t) := by
  unfold curveVelocity familyVelocity
  rw [mfderiv_comp t hΓ hρ.differentiableAt.mdifferentiableAt]
  change mfderiv J I Γ (ρ t)
    (mfderiv 𝓘(ℝ) J ρ t ((NormedSpace.fromTangentSpace t).symm 1)) = _
  congr 1
  rw [mfderiv_eq_fderiv]
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  change (NormedSpace.fromTangentSpace (ρ t)).symm (deriv ρ t) = _
  rw [hρ.deriv]

/-- Coordinate derivatives of a native parameter velocity are the ordinary
second derivatives of the coordinate representative. -/
theorem familyVelocity_components_hasDerivAt {Γ : P → M} {ρ : ℝ → P} {t : ℝ}
    (v w : P) {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (hx : Γ (ρ t) ∈ e.source)
    (hΓ : ContMDiffAt J I 2 Γ (ρ t)) (hρ : HasDerivAt ρ w t) :
    HasDerivAt (fun s => chartTangentMap e (Γ (ρ s)) (familyVelocity Γ v (ρ s)))
      (fderiv ℝ (fderiv ℝ (e ∘ Γ)) (ρ t) w v) t := by
  have hF : ContDiffAt ℝ 2 (e ∘ Γ) (ρ t) :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by simp)).comp (ρ t) hΓ).contDiffAt
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hΓ.of_le (by norm_num))
  have heq : (fun q => chartTangentMap e (Γ q) (familyVelocity Γ v q)) =ᶠ[𝓝 (ρ t)]
      (fun q => fderiv ℝ (e ∘ Γ) q v) := by
    filter_upwards [hn, hΓ.continuousAt (e.open_source.mem_nhds hx)] with q hq hsource
    exact chartTangentMap_familyVelocity v he hsource (hq.mdifferentiableAt (by norm_num))
  have hd := ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hρ
  have hv := hd.clm_apply (hasDerivAt_const t v)
  simpa only [map_zero, add_zero, Function.comp_apply] using!
    hv.congr_of_eventuallyEq (heq.comp_tendsto hρ.continuousAt)

/-- Mixed covariant derivatives of a C² curve family commute because the
Levi-Civita connection has zero torsion. Parameter velocities may vanish. -/
theorem covariantAlong_family_interchange (g : LorentzMetric σ d M)
    {Γ : P → M} {a b : ℝ} (hΓ : ContMDiffAt J I 2 Γ (a, b)) :
    g.covariantAlong (γ := fun s => Γ (s, b))
      (fun s => familyVelocity Γ (0, 1) (s, b)) a =
    g.covariantAlong (γ := fun t => Γ (a, t))
      (fun t => familyVelocity Γ (1, 0) (a, t)) b := by
  let e := chartAt E (Γ (a, b))
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hx : Γ (a, b) ∈ e.source := mem_chart_source E _
  have hF : ContDiffAt ℝ 2 (e ∘ Γ) (a, b) :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by simp)).comp (a, b) hΓ).contDiffAt
  have h₁ : HasDerivAt (fun s : ℝ => (s, b)) (1, 0) a :=
    (hasDerivAt_id a).prodMk (hasDerivAt_const a b)
  have h₂ : HasDerivAt (fun t : ℝ => (a, t)) (0, 1) b :=
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have hAB := familyVelocity_components_hasDerivAt (ρ := fun s => (s, b)) (t := a)
    (0, 1) (1, 0) he hx hΓ h₁
  have hBA := familyVelocity_components_hasDerivAt (ρ := fun t => (a, t)) (t := b)
    (1, 0) (0, 1) he hx hΓ h₂
  have hderAB : deriv (alongComponents e (γ := fun s => Γ (s, b))
      (fun s => familyVelocity Γ (0, 1) (s, b))) a =
      fderiv ℝ (fderiv ℝ (e ∘ Γ)) (a, b) (1, 0) (0, 1) := hAB.deriv
  have hderBA : deriv (alongComponents e (γ := fun t => Γ (a, t))
      (fun t => familyVelocity Γ (1, 0) (a, t))) b =
      fderiv ℝ (fderiv ℝ (e ∘ Γ)) (a, b) (0, 1) (1, 0) := hBA.deriv
  have hd := hΓ.mdifferentiableAt (by norm_num)
  have hvelA : curveVelocity (d := d) (fun s => Γ (s, b)) a =
      familyVelocity (d := d) Γ (1, 0) (a, b) := by
    simpa only [Function.comp_def] using!
      (curveVelocity_family (ρ := fun s => (s, b)) hd h₁)
  have hvelB : curveVelocity (d := d) (fun t => Γ (a, t)) b =
      familyVelocity (d := d) Γ (0, 1) (a, b) := by
    simpa only [Function.comp_def] using!
      (curveVelocity_family (ρ := fun t => (a, t)) hd h₂)
  have hA := chartField_tangentMap he hx (familyVelocity Γ (1, 0) (a, b))
  have hB := chartField_tangentMap he hx (familyVelocity Γ (0, 1) (a, b))
  rw [chartTangentMap_familyVelocity (1, 0) he hx hd] at hA
  rw [chartTangentMap_familyVelocity (0, 1) he hx hd] at hB
  have hconn := (CovariantDerivative.torsion_eq_zero_iff g.leviCivita).mp g.leviCivita_torsion
    (chartField_mdifferentiableAt he hx (fderiv ℝ (e ∘ Γ) (a, b) (1, 0)))
    (chartField_mdifferentiableAt he hx (fderiv ℝ (e ∘ Γ) (a, b) (0, 1)))
  rw [chartField_bracket he hx, sub_eq_zero] at hconn
  change g.chartCovariantAlong e (fun s => familyVelocity Γ (0, 1) (s, b)) a =
    g.chartCovariantAlong e (fun t => familyVelocity Γ (1, 0) (a, t)) b
  simp only [chartCovariantAlong, alongComponents]
  rw [hderAB, hderBA, hvelA, hvelB,
    chartTangentMap_familyVelocity (0, 1) he hx hd,
    chartTangentMap_familyVelocity (1, 0) he hx hd, ← hA, ← hB,
    (hF.isSymmSndFDerivAt (by norm_num)).eq (1, 0) (0, 1), hconn]

end ProjectAInos.SmoothGeometry.LorentzMetric
