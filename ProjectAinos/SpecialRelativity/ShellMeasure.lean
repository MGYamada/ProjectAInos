/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialRelativity.FutureShell
public import ProjectAinos.SpecialRelativity.Factorization
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The invariant measure on the mass shell

In the chart of the future mass shell by the space momenta `π`, the measure

`FutureShell.measure d m = dᵈπ / E(π)`, `E(π) = √(m² + Σ πᵢ²)`,

on the domain `m² + Σ πᵢ² > 0` is invariant under the orthochronous Lorentz group
(`map_action_measure`): for the transformation `L` in the chart,
`Measure.map (action m L) (measure d m) = measure d m` (Landau–Lifshitz, *The Classical Theory
of Fields*, §10). The normalization is `1/E`; the convention `1/(2E)` differs by the constant
factor `1/2`.

The proof uses the factorization of `L` into a rotation after a boost.

* A rotation acts in the chart by a linear map that preserves `Σ πᵢ²`
  (`action_rotation_eq`, `sum_mul_spaceLinear`). Its determinant is `±1`, so it preserves the
  volume, the domain and the energy (`map_action_measure_rotation`).
* A boost acts by `π ↦ π + (γ²/(1 + γ) ⟨β, π⟩ − γ E) β`. Its derivative is the identity plus a
  map of rank one, with the determinant `E′/E` (`det_boostDeriv`), and the formula for the
  change of variables gives the invariance (`map_action_measure_boost`).

Two general statements on a measure with a density carry the argument:
`map_withDensity_of_comp_eq` for a map that preserves the measure and the density, and
`map_withDensity_of_jacobian` for a differentiable injective map whose Jacobian compensates
the change of the density.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace ProjectAinos.SpecialRelativity.FutureShell

open SmoothGeometry SmoothGeometry.Minkowski

/-! ### Two statements on measures with a density -/

/-- A measurable map that preserves a measure and a density preserves the measure with that
density. -/
theorem map_withDensity_of_comp_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → α}
    (hφ : Measurable φ) (hμ : Measure.map φ μ = μ) {h : α → ℝ≥0∞} (hh : Measurable h)
    (hcomp : ∀ x, h (φ x) = h x) :
    Measure.map φ (μ.withDensity h) = μ.withDensity h := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hφ hS, withDensity_apply _ (hφ hS), withDensity_apply _ hS,
    ← lintegral_indicator (hφ hS), ← lintegral_indicator hS]
  have hfun : (fun x => (φ ⁻¹' S).indicator h x) = fun x => S.indicator h (φ x) := by
    funext x
    by_cases hx : φ x ∈ S
    · rw [indicator_of_mem (show x ∈ φ ⁻¹' S from hx), indicator_of_mem hx, hcomp]
    · rw [indicator_of_notMem (show x ∉ φ ⁻¹' S from hx), indicator_of_notMem hx]
  rw [hfun, ← lintegral_map (hh.indicator hS) hφ, hμ]

/-- A differentiable injective map of a measurable set onto itself preserves the Lebesgue
measure with a density, if its Jacobian compensates the change of the density. -/
theorem map_withDensity_of_jacobian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {s : Set E} (hs : MeasurableSet s) {φ : E → E}
    {φ' : E → E →L[ℝ] E} (hφ : Measurable φ)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : InjOn φ s) (himg : φ '' s = s)
    {h : E → ℝ≥0∞} (hjac : ∀ x ∈ s, ENNReal.ofReal |(φ' x).det| * h (φ x) = h x) :
    Measure.map φ ((μ.restrict s).withDensity h) = (μ.restrict s).withDensity h := by
  refine Measure.ext fun S hS => ?_
  rw [Measure.map_apply hφ hS, withDensity_apply _ (hφ hS), withDensity_apply _ hS,
    Measure.restrict_restrict (hφ hS), Measure.restrict_restrict hS,
    ← setLIntegral_indicator (hφ hS), ← setLIntegral_indicator hS]
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hφ' hinj (S.indicator h)
  rw [himg] at hchange
  rw [hchange]
  refine setLIntegral_congr_fun hs fun x hx => ?_
  by_cases hxS : φ x ∈ S
  · rw [indicator_of_mem (show x ∈ φ ⁻¹' S from hxS), indicator_of_mem hxS, hjac x hx]
  · rw [indicator_of_notMem (show x ∉ φ ⁻¹' S from hxS), indicator_of_notMem hxS, mul_zero]

/-! ### The measure -/

variable {d : ℕ} {m : ℝ}

/-- The invariant measure `dᵈπ/E` on the domain of the space momenta of the shell. -/
def measure (d : ℕ) (m : ℝ) : Measure (Fin d → ℝ) :=
  (volume.restrict (domain d m)).withDensity fun π => ENNReal.ofReal (energy m π)⁻¹

theorem continuous_energy : Continuous (energy (d := d) m) :=
  Real.continuous_sqrt.comp
    (continuous_const.add (FreeParticle.contDiff_sum_sq (n := 0)).continuous)

theorem continuous_point : Continuous (point (d := d) m) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_energy
  · exact continuous_apply j

theorem continuous_action (L : orthochronousLorentzGroup d) : Continuous (action m L) :=
  contDiff_spaceMomentum.continuous.comp
    ((LorentzGroup.toContinuousLinearEquiv L.val).continuous.comp continuous_point)

theorem measurableSet_domain : MeasurableSet (domain d m) := isOpen_domain.measurableSet

theorem measurable_density :
    Measurable fun π : Fin d → ℝ => ENNReal.ofReal (energy m π)⁻¹ :=
  continuous_energy.measurable.inv.ennreal_ofReal

/-! ### Rotations -/

/-- The pairing of two vectors given by their time and space parts. -/
theorem pair_cons (s t : ℝ) (x y : Fin d → ℝ) :
    pair (Fin.cons s x : MinkowskiModel d) (Fin.cons t y) = s * t - ∑ i, x i * y i := by
  rw [pair, minkowskiForm_apply, Fin.sum_univ_succ]
  simp only [lorentzSign, LorentzConvention.timeSign_timePositive, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_ne_zero, ↓reduceIte, one_mul, mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The vector with the time zero and the space part `x`, as a linear map of `x`. -/
def consZero (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] MinkowskiModel d where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' r x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The space momentum, as a linear map. -/
def spaceMomentumLinear (d : ℕ) : MinkowskiModel d →ₗ[ℝ] (Fin d → ℝ) where
  toFun := spaceMomentum
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The space block of a Lorentz transformation, as a linear map of the space momenta. -/
def spaceLinear (R : LorentzGroup d) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  (spaceMomentumLinear d).comp (R.val.toLinearMap.comp (consZero d))

theorem spaceLinear_apply (R : LorentzGroup d) (x : Fin d → ℝ) :
    spaceLinear R x = spaceMomentum (R.val (Fin.cons 0 x)) := rfl

/-- A rotation maps a vector with the time zero to a vector with the time zero. -/
theorem rotation_consZero {R : LorentzGroup d} (hR : R ∈ rotationGroup d) (x : Fin d → ℝ) :
    R.val (Fin.cons 0 x) = (Fin.cons 0 (spaceLinear R x) : MinkowskiModel d) := by
  have ht : time (R.val (Fin.cons 0 x)) = 0 := time_rotation hR _
  have h := cons_time_spaceMomentum (R.val (Fin.cons 0 x))
  rw [ht] at h
  exact h.symm

/-- The point of the shell is its energy along the time axis plus its space momentum. -/
theorem point_eq (m : ℝ) (π : Fin d → ℝ) :
    point m π = energy m π • timeAxis d + (Fin.cons 0 π : MinkowskiModel d) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [point, timeAxis]
  · simp [point, timeAxis]

/-- A rotation acts in the chart of the shell by its space block, for every mass. -/
theorem action_rotation_eq (m : ℝ) {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (π : Fin d → ℝ) :
    action m ⟨R, rotationGroup_le_orthochronous hR⟩ π = spaceLinear R π := by
  change spaceMomentum (R.val (point m π)) = _
  rw [point_eq, map_add, map_smul, (mem_rotationGroup_iff R).mp hR, rotation_consZero hR]
  funext i
  simp [spaceMomentum, timeAxis]

/-- The space block of a rotation preserves the scalar product of the space momenta. -/
theorem sum_mul_spaceLinear {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (x y : Fin d → ℝ) :
    ∑ i, spaceLinear R x i * spaceLinear R y i = ∑ i, x i * y i := by
  have h := LorentzGroup.preserves_pair R (Fin.cons 0 x : MinkowskiModel d) (Fin.cons 0 y)
  rw [rotation_consZero hR, rotation_consZero hR, pair_cons, pair_cons] at h
  linarith

theorem energy_spaceLinear {R : LorentzGroup d} (hR : R ∈ rotationGroup d) (π : Fin d → ℝ) :
    energy m (spaceLinear R π) = energy m π := by
  have h := sum_mul_spaceLinear hR π π
  simp only [← pow_two] at h
  rw [energy, energy, h]

theorem spaceLinear_mem_domain_iff {R : LorentzGroup d} (hR : R ∈ rotationGroup d)
    (π : Fin d → ℝ) : spaceLinear R π ∈ domain d m ↔ π ∈ domain d m := by
  have h := sum_mul_spaceLinear hR π π
  simp only [← pow_two] at h
  change 0 < m ^ 2 + ∑ i, spaceLinear R π i ^ 2 ↔ 0 < m ^ 2 + ∑ i, π i ^ 2
  rw [h]

/-- The determinant of the space block of a rotation is `±1`. -/
theorem det_spaceLinear_sq {R : LorentzGroup d} (hR : R ∈ rotationGroup d) :
    LinearMap.det (spaceLinear R) ^ 2 = 1 := by
  have hM : (LinearMap.toMatrix' (spaceLinear R)).transpose *
      LinearMap.toMatrix' (spaceLinear R) = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, LinearMap.toMatrix'_apply]
    rw [sum_mul_spaceLinear hR, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_mul, Pi.single_apply]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, LinearMap.det_toMatrix'] at hdet
  rw [pow_two]
  exact hdet

/-- The space block of a rotation preserves the volume. -/
theorem map_spaceLinear_volume {R : LorentzGroup d} (hR : R ∈ rotationGroup d) :
    Measure.map (spaceLinear R) (volume : Measure (Fin d → ℝ)) = volume := by
  have hsq := det_spaceLinear_sq hR
  have hne : LinearMap.det (spaceLinear R) ≠ 0 := fun h0 => by
    rw [h0] at hsq
    norm_num at hsq
  have habs : |(LinearMap.det (spaceLinear R))⁻¹| = 1 := by
    have h1 : |LinearMap.det (spaceLinear R)| ^ 2 = 1 ^ 2 := by rw [sq_abs, hsq, one_pow]
    rw [abs_inv, (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp h1, inv_one]
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, habs, ENNReal.ofReal_one,
    one_smul]

/-- The measure of the shell is invariant under the rotations. -/
theorem map_action_measure_rotation {R : LorentzGroup d} (hR : R ∈ rotationGroup d) :
    Measure.map (action m ⟨R, rotationGroup_le_orthochronous hR⟩) (measure d m) =
      measure d m := by
  have hfun : action m ⟨R, rotationGroup_le_orthochronous hR⟩ = spaceLinear R :=
    funext (action_rotation_eq m hR)
  rw [hfun, measure, ← withDensity_indicator measurableSet_domain]
  refine map_withDensity_of_comp_eq
    (spaceLinear R).continuous_of_finiteDimensional.measurable (map_spaceLinear_volume hR)
    (measurable_density.indicator measurableSet_domain) fun π => ?_
  by_cases hπ : π ∈ domain d m
  · rw [indicator_of_mem ((spaceLinear_mem_domain_iff hR π).mpr hπ), indicator_of_mem hπ,
      energy_spaceLinear hR]
  · rw [indicator_of_notMem fun h => hπ ((spaceLinear_mem_domain_iff hR π).mp h),
      indicator_of_notMem hπ]

/-! ### Boosts -/

/-- The derivative of the energy: `dE = Σ (πᵢ/E) dπᵢ`. -/
theorem hasFDerivAt_energy {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    HasFDerivAt (energy (d := d) m) ((energy m π)⁻¹ • FreeParticle.dotCovector π) π := by
  have hj (j : Fin d) : HasFDerivAt (fun w : Fin d → ℝ => w j ^ 2)
      ((2 * π j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) π := by
    simpa using ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt
      (x := π)).pow 2
  have hg : HasFDerivAt (fun w : Fin d → ℝ => m ^ 2 + ∑ j, w j ^ 2)
      (∑ j, (2 * π j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) π :=
    (HasFDerivAt.fun_sum fun j _ => hj j).const_add (m ^ 2)
  have hs := hg.sqrt (ne_of_gt hπ)
  have hpos : 0 < Real.sqrt (m ^ 2 + ∑ i, π i ^ 2) := Real.sqrt_pos.mpr hπ
  refine hs.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [smul_apply, _root_.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    FreeParticle.dotCovector_apply, energy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

/-- The determinant of the identity plus a map of rank one: `det (1 + ℓ ⊗ b) = 1 + ℓ(b)`. -/
theorem det_id_add_smulRight (c b : Fin d → ℝ) :
    (ContinuousLinearMap.id ℝ (Fin d → ℝ) + (FreeParticle.dotCovector c).smulRight b).det =
      1 + ∑ i, c i * b i := by
  change LinearMap.det ((ContinuousLinearMap.id ℝ (Fin d → ℝ) +
    (FreeParticle.dotCovector c).smulRight b : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = _
  rw [← LinearMap.det_toMatrix']
  have hM : LinearMap.toMatrix' ((ContinuousLinearMap.id ℝ (Fin d → ℝ) +
      (FreeParticle.dotCovector c).smulRight b : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
        (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) =
      1 + Matrix.replicateCol Unit b * Matrix.replicateRow Unit c := by
    ext i j
    have hdot : FreeParticle.dotCovector c (Pi.single j 1) = c j := by
      rw [FreeParticle.dotCovector_apply, Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, mul_one]
      · intro k _ hk
        rw [Pi.single_eq_of_ne hk, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [LinearMap.toMatrix'_apply]
    simp only [ContinuousLinearMap.coe_coe, add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton]
    rw [hdot, Pi.single_apply, mul_comm]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  rfl

/-- The co-ordinates of a velocity. -/
def velocityCoord (β : Velocity d) : Fin d → ℝ := fun i => β.val i

theorem inner_velocity_space (β : Velocity d) (v : MinkowskiModel d) :
    inner ℝ β.val (space v) = ∑ i, velocityCoord β i * spaceMomentum v i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [velocityCoord, spaceMomentum, mul_comm]

theorem sum_velocityCoord_mul_self (β : Velocity d) :
    ∑ i, velocityCoord β i * velocityCoord β i = ‖β.val‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ => (pow_two _).symm

/-- The boost with the velocity `β` in the chart of the shell:
`π ↦ π + (γ²/(1 + γ) ⟨β, π⟩ − γ E(π)) β`. -/
def boostMap (m : ℝ) (β : Velocity d) (π : Fin d → ℝ) : Fin d → ℝ :=
  π + (β.gamma ^ 2 / (1 + β.gamma) * (∑ j, velocityCoord β j * π j) -
    β.gamma * energy m π) • velocityCoord β

theorem action_boost_eq (m : ℝ) (β : Velocity d) (π : Fin d → ℝ) :
    action m (boostOrthochronous β) π = boostMap m β π := by
  funext i
  change space ((boost β).val (point m π)) i = _
  rw [boost_space, inner_velocity_space, spaceMomentum_point, time_point]
  rfl

theorem boostMap_mem (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    boostMap m β π ∈ domain d m := by
  rw [← action_boost_eq]
  exact action_mem _ hπ

/-- The energy after the boost: `E′ = γ (E − ⟨β, π⟩)`. -/
theorem energy_boostMap (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    energy m (boostMap m β π) = β.gamma * (energy m π - ∑ j, velocityCoord β j * π j) := by
  have h := congrArg time (point_action (boostOrthochronous β) hπ)
  rw [time_point, action_boost_eq] at h
  rw [h]
  change time ((boost β).val (point m π)) = _
  rw [boost_time, inner_velocity_space, spaceMomentum_point, time_point]

theorem injOn_boostMap (β : Velocity d) : InjOn (boostMap m β) (domain d m) := by
  intro π hπ π' hπ' h
  have h1 : action m (boostOrthochronous β)⁻¹ (boostMap m β π) = π := by
    rw [← action_boost_eq, ← action_mul _ _ hπ, inv_mul_cancel, action_one]
  have h2 : action m (boostOrthochronous β)⁻¹ (boostMap m β π') = π' := by
    rw [← action_boost_eq, ← action_mul _ _ hπ', inv_mul_cancel, action_one]
  rw [← h1, ← h2, h]

theorem image_boostMap (β : Velocity d) : boostMap m β '' domain d m = domain d m := by
  apply Subset.antisymm
  · rintro _ ⟨π, hπ, rfl⟩
    exact boostMap_mem β hπ
  · intro π hπ
    refine ⟨action m (boostOrthochronous β)⁻¹ π, action_mem _ hπ, ?_⟩
    rw [← action_boost_eq, ← action_mul _ _ hπ, mul_inv_cancel, action_one]

/-- The coefficients of the linear form in the derivative of the boost. -/
def boostCoeff (m : ℝ) (β : Velocity d) (π : Fin d → ℝ) : Fin d → ℝ :=
  (β.gamma ^ 2 / (1 + β.gamma)) • velocityCoord β - (β.gamma * (energy m π)⁻¹) • π

/-- The derivative of the boost in the chart: the identity plus a map of rank one. -/
def boostDeriv (m : ℝ) (β : Velocity d) (π : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.id ℝ (Fin d → ℝ) +
    (FreeParticle.dotCovector (boostCoeff m β π)).smulRight (velocityCoord β)

theorem hasFDerivAt_boostMap (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    HasFDerivAt (boostMap m β) (boostDeriv m β π) π := by
  have hdot : HasFDerivAt (fun π : Fin d → ℝ => ∑ j, velocityCoord β j * π j)
      (FreeParticle.dotCovector (velocityCoord β)) π := by
    have hfun : (fun π : Fin d → ℝ => ∑ j, velocityCoord β j * π j) =
        ⇑(FreeParticle.dotCovector (velocityCoord β)) :=
      funext fun π => (FreeParticle.dotCovector_apply _ _).symm
    rw [hfun]
    exact (FreeParticle.dotCovector (velocityCoord β)).hasFDerivAt
  have hE := hasFDerivAt_energy hπ
  have h := (hasFDerivAt_id π).add (((hdot.const_mul (β.gamma ^ 2 / (1 + β.gamma))).sub
    (hE.const_mul β.gamma)).smul_const (velocityCoord β))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
  simp only [boostDeriv, boostCoeff, add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, sub_apply, smul_apply, smul_eq_mul,
    FreeParticle.dotCovector_apply, Pi.sub_apply, Pi.smul_apply]
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Jacobian of the boost in the chart is `E′/E`. -/
theorem det_boostDeriv (β : Velocity d) {π : Fin d → ℝ} (hπ : π ∈ domain d m) :
    (boostDeriv m β π).det = energy m (boostMap m β π) / energy m π := by
  have hg := β.gamma_identity
  have hgp := β.gamma_pos
  have hE := energy_pos hπ
  have hsum : ∑ i, boostCoeff m β π i * velocityCoord β i =
      β.gamma ^ 2 / (1 + β.gamma) * ‖β.val‖ ^ 2 -
        β.gamma * (energy m π)⁻¹ * ∑ j, velocityCoord β j * π j := by
    rw [← sum_velocityCoord_mul_self, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [boostCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [boostDeriv, det_id_add_smulRight, hsum, energy_boostMap β hπ]
  field_simp
  linear_combination (-(energy m π)) * hg

/-- The measure of the shell is invariant under the boosts. -/
theorem map_action_measure_boost (β : Velocity d) :
    Measure.map (action m (boostOrthochronous β)) (measure d m) = measure d m := by
  have hfun : action m (boostOrthochronous β) = boostMap m β := funext (action_boost_eq m β)
  have hmeas : Measurable (boostMap m β) := hfun ▸ (continuous_action _).measurable
  rw [hfun, measure]
  refine map_withDensity_of_jacobian volume measurableSet_domain hmeas
    (fun π hπ => (hasFDerivAt_boostMap β hπ).hasFDerivWithinAt) (injOn_boostMap β)
    (image_boostMap β) fun π hπ => ?_
  have hE := energy_pos hπ
  have hE' := energy_pos (boostMap_mem β hπ)
  rw [det_boostDeriv β hπ, abs_of_pos (div_pos hE' hE),
    ← ENNReal.ofReal_mul (div_pos hE' hE).le]
  congr 1
  field_simp

/-! ### The invariance -/

/-- The measure of the shell is carried by the domain. -/
theorem ae_mem_domain : ∀ᵐ π ∂(measure d m), π ∈ domain d m :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_domain)

/-- The measure `dᵈπ/E` of the mass shell is invariant under the orthochronous Lorentz
group. -/
theorem map_action_measure (L : orthochronousLorentzGroup d) :
    Measure.map (action m L) (measure d m) = measure d m := by
  have hL : L = ⟨rotationPart L, rotationGroup_le_orthochronous (rotationPart_mem L)⟩ *
      boostOrthochronous (boostPart L) := Subtype.ext (rotationPart_mul_boost L).symm
  have hae : action m L =ᵐ[measure d m]
      action m ⟨rotationPart L, rotationGroup_le_orthochronous (rotationPart_mem L)⟩ ∘
        action m (boostOrthochronous (boostPart L)) := by
    filter_upwards [ae_mem_domain] with π hπ
    conv_lhs => rw [hL]
    exact action_mul _ _ hπ
  rw [Measure.map_congr hae,
    ← Measure.map_map (continuous_action _).measurable (continuous_action _).measurable,
    map_action_measure_boost, map_action_measure_rotation (rotationPart_mem L)]

/-- A Lorentz transformation in the chart preserves the measure of the shell. -/
theorem measurePreserving_action (L : orthochronousLorentzGroup d) :
    MeasurePreserving (action m L) (measure d m) (measure d m) :=
  ⟨(continuous_action L).measurable, map_action_measure L⟩

/-- The integral of a function over the shell does not change under a Lorentz
transformation. -/
theorem integral_comp_action {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : orthochronousLorentzGroup d) (f : (Fin d → ℝ) → G)
    (hf : AEStronglyMeasurable f (measure d m)) :
    ∫ π, f (action m L π) ∂(measure d m) = ∫ π, f π ∂(measure d m) := by
  have h := integral_map (continuous_action (m := m) L).measurable.aemeasurable
    (by rw [map_action_measure]; exact hf)
  rw [map_action_measure] at h
  exact h.symm

end ProjectAinos.SpecialRelativity.FutureShell
