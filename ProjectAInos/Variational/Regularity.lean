module

public import ProjectAInos.Variational.Action
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.NormNum

/-!
# Compactly supported variations of smooth actions

Joint regularity and compact support supply the measurability and domination
needed to differentiate an action. The unperturbed density must be integrable,
including on an unbounded region.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace ProjectAInos.Variational

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A twice continuously differentiable field has a continuously differentiable jet. -/
theorem contDiff_jet {u : E → F} (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (jet u) :=
  (hu.of_le (by norm_num)).prodMk (hu.fderiv_right (by norm_num))

/-- Both parts of a variation's jet vanish off its topological support. -/
theorem jet_eq_zero_of_notMem_tsupport {η : E → F} {x : E} (hx : x ∉ tsupport η) :
    jet η x = 0 := by
  simp [jet, image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx]

/-- Joint regularity implies differentiability in each jet fibre. -/
theorem differentiable_lagrangian_fiber {L : Lagrangian E F}
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (x : E) : Differentiable ℝ (L x) :=
  (hL.differentiable (by norm_num)).comp
    ((differentiable_const (c := x)).prodMk differentiable_id)

/-- The fibre differential evaluated along a field is continuously differentiable. -/
theorem contDiff_fiberDerivative {L : Lagrangian E F} {u : E → F}
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (fun x => fderiv ℝ (L x) (jet u x)) :=
  hL.fderiv (contDiff_jet hu) (by norm_num)

/-- The variation derivative depends continuously on the parameter and base point. -/
theorem continuous_variedFirstVariation {L : Lagrangian E F} {u η : E → F}
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u)
    (hη : ContDiff ℝ 2 η) :
    Continuous (fun p : ℝ × E => firstVariationDensity L (perturb u η p.1) η p.2) := by
  let M : (ℝ × E) → JetFiber E F → ℝ := fun p => L p.2
  let J : ℝ × E → JetFiber E F := fun p => jet u p.2 + p.1 • jet η p.2
  have hM : ContDiff ℝ 2 (Function.uncurry M) := by
    exact hL.comp (contDiff_snd.comp contDiff_fst |>.prodMk contDiff_snd)
  have hJ : ContDiff ℝ 1 J :=
    ((contDiff_jet hu).comp contDiff_snd).add
      (contDiff_fst.smul ((contDiff_jet hη).comp contDiff_snd))
  have hc := (hM.fderiv hJ (by norm_num)).clm_apply
    ((contDiff_jet hη).comp contDiff_snd)
  simpa only [M, J, firstVariationDensity, Function.comp_def,
    jet_perturb ((hu.differentiable (by norm_num)) _)
      ((hη.differentiable (by norm_num)) _)] using hc.continuous

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsLocallyFiniteMeasure μ]
  {L : Lagrangian E F} {u η : E → F}

/-- Every perturbed density remains integrable if the base density is integrable.
Only the change in density has compact support. -/
theorem integrable_density_perturb_of_compactSupport
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u)
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hint : Integrable (density L u) μ) (ε : ℝ) :
    Integrable (density L (perturb u η ε)) μ := by
  have hcont {v : E → F} (hv : ContDiff ℝ 2 v) : Continuous (density L v) :=
    hL.continuous.comp (continuous_id.prodMk (contDiff_jet hv).continuous)
  have hdiff := (hcont (hu.add (hη.const_smul ε))).sub (hcont hu)
  have hsupp : HasCompactSupport (fun x => density L (perturb u η ε) x - density L u x) := by
    refine hc.mono' ?_
    intro x hx
    by_contra h
    exact hx (by simp [density,
      jet_perturb (hu.differentiable (by norm_num) x) (hη.differentiable (by norm_num) x) ε,
      jet_eq_zero_of_notMem_tsupport h])
  convert (hdiff.integrable_of_hasCompactSupport hsupp).add hint using 1
  funext x
  exact (sub_add_cancel _ _).symm

/-- Differentiate a smooth action along a compactly supported variation. -/
theorem hasDerivAt_action_of_compactSupport
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u)
    (hη : ContDiff ℝ 2 η) (hc : HasCompactSupport η)
    (hint : Integrable (density L u) μ) :
    Integrable (firstVariationDensity L u η) μ ∧
      HasDerivAt (fun ε => action μ L (perturb u η ε)) (firstVariation μ L u η) 0 := by
  classical
  have hdu := hu.differentiable (by norm_num)
  have hdη := hη.differentiable (by norm_num)
  have hD := continuous_variedFirstVariation hL hu hη
  have hK : IsCompact (tsupport η) := hc
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK :
    IsCompact (Icc (-1 : ℝ) 1 ×ˢ tsupport η)).exists_bound_of_continuousOn hD.continuousOn
  refine hasDerivAt_action (s := Icc (-1) 1)
    (bound := (tsupport η).indicator fun _ => C)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (.of_forall hdu) (.of_forall hdη) (.of_forall fun x _ _ =>
      differentiable_lagrangian_fiber hL x _) ?_ hint ?_ ?_ ?_
  · exact .of_forall fun ε =>
      (hL.continuous.comp (continuous_id.prodMk
        (contDiff_jet (hu.add (hη.const_smul ε))).continuous)).aestronglyMeasurable
  · have h0 : Continuous (fun x => firstVariationDensity L (perturb u η 0) η x) :=
      hD.comp (continuous_const (y := (0 : ℝ)) |>.prodMk continuous_id)
    exact (by simpa only [perturb_zero] using h0 :
      Continuous (firstVariationDensity L u η)).aestronglyMeasurable
  · exact .of_forall fun x ε hε => by
      by_cases hx : x ∈ tsupport η
      · simpa only [indicator_of_mem hx] using hC (ε, x) ⟨hε, hx⟩
      · simp [indicator_of_notMem hx, firstVariationDensity, jet_eq_zero_of_notMem_tsupport hx]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (continuousOn_const.integrableOn_compact hK)

end ProjectAInos.Variational
