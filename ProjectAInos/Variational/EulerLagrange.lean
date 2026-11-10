module

public import ProjectAInos.Variational.IntegrationByParts
public import ProjectAInos.Variational.Regularity
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.NormNum

/-!
# Euler–Lagrange equations in a fixed trivialization

The base has finitely many real coordinates. The fibre can be any real normed
space. The residual takes values in its continuous dual. Compactly supported
interior variations allow integration by parts with the ambient Haar measure.
-/

@[expose] public section

open MeasureTheory Set ContinuousLinearMap
open scoped ContDiff

namespace ProjectAInos.Variational

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate direction corresponding to index `i`. -/
noncomputable def coordinateDirection (i : Fin n) : Coordinates n := Pi.single i 1

/-- Insert a fibre vector into the derivative slot for one base coordinate. -/
noncomputable def insertDirection (i : Fin n) : F →L[ℝ] (Coordinates n →L[ℝ] F) :=
  smulRightL ℝ (Coordinates n) F (proj i)

@[simp] theorem insertDirection_apply (i : Fin n) (v : F) (x : Coordinates n) :
    insertDirection i v x = x i • v := rfl

private theorem sum_insertDirection (p : Coordinates n →L[ℝ] F) :
    ∑ i, insertDirection i (p (coordinateDirection i)) = p := by
  ext x
  change (∑ i, insertDirection i (p (coordinateDirection i))) x = p x
  simp only [sum_apply, insertDirection_apply, coordinateDirection]
  simp_rw [← map_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
  rw [← map_sum, Finset.univ_sum_single]

/-- The derivative of the Lagrangian in the field value. -/
noncomputable def valueCovector (L : Lagrangian (Coordinates n) F)
    (u : Coordinates n → F) (x : Coordinates n) : F →L[ℝ] ℝ :=
  (fderiv ℝ (L x) (jet u x)).comp (inl ℝ F (Coordinates n →L[ℝ] F))

/-- The derivative of the Lagrangian in the `i`th field derivative. -/
noncomputable def momentumCovector (L : Lagrangian (Coordinates n) F)
    (u : Coordinates n → F) (i : Fin n) (x : Coordinates n) : F →L[ℝ] ℝ :=
  (fderiv ℝ (L x) (jet u x)).comp
    ((inr ℝ F (Coordinates n →L[ℝ] F)).comp (insertDirection i))

/-- The field derivative of the Lagrangian minus the divergence of its momentum. -/
noncomputable def eulerLagrange (L : Lagrangian (Coordinates n) F)
    (u : Coordinates n → F) (x : Coordinates n) : F →L[ℝ] ℝ :=
  valueCovector L u x -
    ∑ i, fderiv ℝ (momentumCovector L u i) x (coordinateDirection i)

/-- The fibre chain rule decomposes into the value and each derivative direction. -/
theorem firstVariationDensity_eq_covectors (L : Lagrangian (Coordinates n) F)
    (u η : Coordinates n → F) (x : Coordinates n) :
    firstVariationDensity L u η x = valueCovector L u x (η x) +
      ∑ i, momentumCovector L u i x (fderiv ℝ η x (coordinateDirection i)) := by
  rw [firstVariationDensity_split]
  congr 1
  change (fderiv ℝ (L x) (jet u x)) (inr ℝ F _ (fderiv ℝ η x)) = _
  calc
    _ = (fderiv ℝ (L x) (jet u x)) (inr ℝ F _
        (∑ i, insertDirection i (fderiv ℝ η x (coordinateDirection i)))) :=
      congrArg (fun p => (fderiv ℝ (L x) (jet u x)) (inr ℝ F _ p))
        (sum_insertDirection (fderiv ℝ η x)).symm
    _ = _ := by rw [map_sum, map_sum]; rfl

variable {L : Lagrangian (Coordinates n) F} {u : Coordinates n → F}

theorem contDiff_valueCovector (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (valueCovector L u) :=
  (contDiff_fiberDerivative hL hu).clm_comp contDiff_const

theorem contDiff_momentumCovector (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hu : ContDiff ℝ 2 u) (i : Fin n) : ContDiff ℝ 1 (momentumCovector L u i) :=
  (contDiff_fiberDerivative hL hu).clm_comp contDiff_const

theorem continuous_eulerLagrange (hL : ContDiff ℝ 2 (Function.uncurry L))
    (hu : ContDiff ℝ 2 u) : Continuous (eulerLagrange L u) :=
  (contDiff_valueCovector hL hu).continuous.sub
    (continuous_finsetSum _ fun i _ =>
      ((contDiff_momentumCovector hL hu i).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply
        continuous_const)

/-- Smooth variations whose topological support is compact and lies in the region. -/
structure InteriorVariation (Ω : Set (Coordinates n)) (η : Coordinates n → F) : Prop where
  smooth : ContDiff ℝ ∞ η
  compact : HasCompactSupport η
  interior : tsupport η ⊆ Ω

/-- The actual action derivative vanishes for each smooth interior variation. -/
def Stationary (μ : Measure (Coordinates n)) (Ω : Set (Coordinates n))
    (L : Lagrangian (Coordinates n) F) (u : Coordinates n → F) : Prop :=
  ∀ η : Coordinates n → F, InteriorVariation Ω η →
    HasDerivAt (fun ε => action (μ.restrict Ω) L (perturb u η ε)) 0 0

variable {μ : Measure (Coordinates n)} [μ.IsAddHaarMeasure]
  {Ω : Set (Coordinates n)} {η : Coordinates n → F}

private theorem integrable_pairing {a : Coordinates n → F →L[ℝ] ℝ}
    {v : Coordinates n → F} (ha : Continuous a) (hv : Continuous v)
    (hK : HasCompactSupport v) : Integrable (fun x => a x (v x)) μ := by
  refine (ha.clm_apply hv).integrable_of_hasCompactSupport (hK.mono ?_)
  intro x hx hvx
  exact hx (by simp [hvx])

/-- Integration by parts identifies the first variation with the residual pairing.
The products vanish off the variation's support, so the whole-space Haar
identity applies before restricting the resulting integral to the region. -/
theorem firstVariation_eq_integral_eulerLagrange
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u)
    (hη : InteriorVariation Ω η) :
    firstVariation (μ.restrict Ω) L u η = ∫ x in Ω, eulerLagrange L u x (η x) ∂μ := by
  let A := valueCovector L u
  let P := momentumCovector L u
  let d := coordinateDirection (n := n)
  have hP i := contDiff_momentumCovector hL hu i
  have hη₂ : ContDiff ℝ 2 η := hη.smooth.of_le (by norm_num)
  have hDη : Continuous (fderiv ℝ η) :=
    (hη₂.fderiv_right (m := 0) (by norm_num)).continuous
  have hDP i : Continuous (fderiv ℝ (P i)) :=
    ((hP i).fderiv_right (m := 0) (by norm_num)).continuous
  have hA : Integrable (fun x => A x (η x)) μ :=
    integrable_pairing (contDiff_valueCovector hL hu).continuous hη.smooth.continuous hη.compact
  have hleft (i : Fin n) : Integrable (fun x => P i x (fderiv ℝ η x (d i))) μ :=
    integrable_pairing (hP i).continuous (hDη.clm_apply continuous_const)
      (hη.compact.fderiv_apply ℝ (d i))
  have hright (i : Fin n) : Integrable (fun x => fderiv ℝ (P i) x (d i) (η x)) μ :=
    integrable_pairing ((hDP i).clm_apply continuous_const) hη.smooth.continuous hη.compact
  have hparts (i : Fin n) : (∫ x, P i x (fderiv ℝ η x (d i)) ∂μ) =
      -∫ x, fderiv ℝ (P i) x (d i) (η x) ∂μ :=
    integral_bilinear_fderiv_right_eq_neg_left_of_integrable
      (B := (ContinuousLinearMap.apply ℝ ℝ (E' := F)).flip)
      (hright i) (hleft i)
      (integrable_pairing (hP i).continuous hη.smooth.continuous hη.compact)
      (fun x _ => (hP i).differentiable one_ne_zero x)
      (fun x _ => hη₂.differentiable (by norm_num) x)
  have hsum : (∫ x, ∑ i, P i x (fderiv ℝ η x (d i)) ∂μ) =
      -(∫ x, ∑ i, fderiv ℝ (P i) x (d i) (η x) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hleft i), integral_finsetSum _ (fun i _ => hright i)]
    simp only [hparts, Finset.sum_neg_distrib]
  have hzero₁ : ∀ x ∉ Ω, firstVariationDensity L u η x = 0 := fun x hx => by
    simp [firstVariationDensity, jet_eq_zero_of_notMem_tsupport (fun h => hx (hη.interior h))]
  have hzero₂ : ∀ x ∉ Ω, eulerLagrange L u x (η x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hη.interior h)), map_zero]
  rw [firstVariation, setIntegral_eq_integral_of_forall_compl_eq_zero hzero₁,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero₂]
  simp_rw [firstVariationDensity_eq_covectors]
  change (∫ x, A x (η x) + ∑ i, P i x (fderiv ℝ η x (d i)) ∂μ) = _
  rw [integral_add hA (integrable_finsetSum _ fun i _ => hleft i), hsum,
    ← sub_eq_add_neg, ← integral_sub hA (integrable_finsetSum _ fun i _ => hright i)]
  simp [eulerLagrange, A, P, d]

/-- The derivative of the restricted action is the Euler–Lagrange pairing. -/
theorem hasDerivAt_action_eulerLagrange
    (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u)
    (hint : Integrable (density L u) (μ.restrict Ω)) (hη : InteriorVariation Ω η) :
    HasDerivAt (fun ε => action (μ.restrict Ω) L (perturb u η ε))
      (∫ x in Ω, eulerLagrange L u x (η x) ∂μ) 0 := by
  rw [← firstVariation_eq_integral_eulerLagrange hL hu hη]
  exact (hasDerivAt_action_of_compactSupport hL hu
    (hη.smooth.of_le (by norm_num)) hη.compact hint).2

/-- The classical Euler–Lagrange equations are equivalent to stationarity
under every smooth compactly supported interior variation. -/
theorem stationary_iff_eulerLagrange
    (hΩ : IsOpen Ω) (hL : ContDiff ℝ 2 (Function.uncurry L)) (hu : ContDiff ℝ 2 u)
    (hint : Integrable (density L u) (μ.restrict Ω)) :
    Stationary μ Ω L u ↔ ∀ x ∈ Ω, eulerLagrange L u x = 0 := by
  refine ⟨?_, fun h η hη => ?_⟩
  · intro hs x hx
    ext v
    let R : Coordinates n → ℝ := fun y => eulerLagrange L u y v
    have hR : Continuous R := (continuous_eulerLagrange hL hu).clm_apply continuous_const
    have ha := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hR.continuousOn.locallyIntegrableOn (μ := μ) hΩ.measurableSet)
      (fun g hg hgK hgΩ => by
        let ζ : Coordinates n → F := fun y => g y • v
        have hsupp : tsupport ζ ⊆ tsupport g :=
          tsupport_comp_subset (g := fun a : ℝ => a • v) (zero_smul ℝ v) g
        have hζ : InteriorVariation Ω ζ :=
          ⟨hg.smul contDiff_const, hgK.of_isClosed_subset (isClosed_tsupport _) hsupp,
            hsupp.trans hgΩ⟩
        have hz := (hasDerivAt_action_eulerLagrange hL hu hint hζ).unique (hs ζ hζ)
        have heq : (∫ y in Ω, eulerLagrange L u y (ζ y) ∂μ) =
            ∫ y, g y • R y ∂μ := by
          simp only [ζ, R, map_smul]
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hgΩ h)), zero_smul]
        exact heq.symm.trans hz)
    have hr : R =ᵐ[μ.restrict Ω] (fun _ => 0) :=
      (ae_restrict_iff' hΩ.measurableSet).2 ha
    exact Measure.eqOn_open_of_ae_eq hr hΩ hR.continuousOn continuous_const.continuousOn hx
  · have hz : (∫ x in Ω, eulerLagrange L u x (η x) ∂μ) = 0 :=
      setIntegral_eq_zero_of_ae_eq_zero (.of_forall fun x hx => by simp [h x hx])
    simpa only [hz] using hasDerivAt_action_eulerLagrange hL hu hint hη

end ProjectAInos.Variational
