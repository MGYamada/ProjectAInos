/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Variational.ManifoldCurve
public import ProjectAInos.SmoothGeometry.Lorentzian.CurveFamily

/-! # Native velocity of localized chart variations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open Variational

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The variation vector, transported along the proved reference equality
to the tangent fibre of the specified curve. -/
def variationField {γ : ℝ → M} {a b : ℝ}
    (V : ManifoldCurveVariation («E» := E) γ a b) : AlongField (d := d) γ :=
  fun t => tangentSpaceCast I (V.family (0, t)) (γ t)
    (familyVelocity V.family (1, 0) (0, t))

omit [IsManifold I ∞ M] in
/-- An actual localized chart variation realizes its prescribed tangent test
field. The identity includes times outside the coordinate patch. -/
theorem chartCurveFamily_velocity {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} {η : ℝ → E} {t : ℝ}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (hU : IsOpen U)
    (hstay : MapsTo γ U e.source) (hsupport : tsupport η ⊆ U)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) (hη : ContDiff ℝ 2 η) :
    familyVelocity (chartCurveFamily e U γ η) (1, 0) (0, t) =
      chartField e (η t) (chartCurveFamily e U γ η (0, t)) := by
  let Γ := chartCurveFamily e U γ η
  have hΓ := (chartCurveFamily_contMDiffAt he hU hstay hsupport hγ hη).mdifferentiableAt
    (by norm_num)
  by_cases ht : t ∈ U
  · have hx : Γ (0, t) ∈ e.source := by
      rw [show Γ (0, t) = γ t from chartCurveFamily_reference hstay η t]
      exact hstay ht
    apply (chartTangentEquiv he hx).injective
    change chartTangentMap e (Γ (0, t)) (familyVelocity Γ (1, 0) (0, t)) =
      chartTangentMap e (Γ (0, t)) (chartField e (η t) (Γ (0, t)))
    rw [chartTangentMap_field he hx]
    have hp : HasDerivAt (fun ε : ℝ => (ε, t)) (1, 0) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t)
    have hc := chartTangentMap_curveVelocity he hx
      (hΓ.comp 0 hp.differentiableAt.mdifferentiableAt)
    rw [curveVelocity_family (ρ := fun ε => (ε, t)) hΓ hp] at hc
    exact hc.trans (chartCurveFamily_coordinate_hasDerivAt η hstay ht).deriv
  · have hzero : η t = 0 := image_eq_zero_of_notMem_tsupport (fun hs => ht (hsupport hs))
    rw [hzero, chartField_zero]
    apply familyVelocity_fst_eq_zero_of_eventually_const hΓ
    apply Eventually.of_forall
    intro ε
    rw [chartCurveFamily_of_zero hstay hzero ε, chartCurveFamily_reference hstay η t]

omit [IsManifold I ∞ M] in
/-- The native test field of the constructed fixed-endpoint variation. -/
theorem variationField_chart {e : OpenPartialHomeomorph M E} {U : Set ℝ}
    {γ : ℝ → M} {η : ℝ → E} {a b : ℝ}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (hU : IsOpen U)
    (hUI : U ⊆ Ioo a b) (hstay : MapsTo γ U e.source) (hsupport : tsupport η ⊆ U)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) (hη : ContDiff ℝ 2 η)
    {t : ℝ} (ht : t ∈ uIcc a b) :
    variationField (chartCurveVariation he hU hUI hstay hsupport hγ hη) t =
      chartField e (η t) (γ t) := by
  change tangentSpaceCast I (chartCurveFamily e U γ η (0, t)) (γ t)
    (familyVelocity (chartCurveFamily e U γ η) (1, 0) (0, t)) = _
  rw [chartCurveFamily_velocity he hU hstay hsupport (hγ t ht) hη,
    chartCurveFamily_reference hstay η t]
  rfl

end ProjectAInos.SmoothGeometry.LorentzMetric
