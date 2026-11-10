module

public import ProjectAInos.Thermodynamics.Entropy
public import ProjectAInos.Thermodynamics.SectorModel
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Concrete realizations of thermodynamic completions

The nonnegative real model recovers the ordinary real entropy coordinate.
The sector model separates its entropy direction from one conserved amount.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics

open Completion

/-- Completing a real vector space viewed as an additive monoid recovers the
same real vector space. -/
noncomputable def completionEquivSelf (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Completion V ≃ₗ[ℝ] V :=
  LinearEquiv.ofBijective (liftLinear (LinearMap.id : V →ₗ[ℝ≥0] V))
    ⟨liftLinear_injective _ Function.injective_id,
      liftLinear_surjective _ (fun v => ⟨v, 0, by simp⟩)⟩

@[simp]
theorem completionEquivSelf_of {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    completionEquivSelf V (of v) = v := by
  exact liftLinear_of (LinearMap.id : V →ₗ[ℝ≥0] V) v

/-- Nonnegative real entropy values as an extensive state function. -/
def nnrealToRealLinear : ℝ≥0 →ₗ[ℝ≥0] ℝ where
  __ := NNReal.toRealHom.toAddMonoidHom
  map_smul' _ _ := rfl

@[simp]
theorem nnrealToRealLinear_apply (x : ℝ≥0) : nnrealToRealLinear x = (x : ℝ) := rfl

/-- The Grothendieck completion of nonnegative real states is the real line. -/
noncomputable def nnrealCompletionEquiv : Completion ℝ≥0 ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (liftLinear nnrealToRealLinear)
    ⟨liftLinear_injective _ NNReal.coe_injective,
      liftLinear_surjective _ (fun r => ⟨r.toNNReal, (-r).toNNReal, by
        simp only [nnrealToRealLinear_apply, Real.coe_toNNReal']
        exact (max_zero_sub_max_neg_zero_eq_self r).symm⟩)⟩

@[simp]
theorem nnrealCompletionEquiv_of (x : ℝ≥0) :
    nnrealCompletionEquiv (of x) = (x : ℝ) :=
  liftLinear_of nnrealToRealLinear x

/-- The process cone becomes the ordinary nonnegative real half-line. -/
theorem nnreal_mem_processCone_iff (v : Completion ℝ≥0) :
    v ∈ processCone ℝ≥0 ↔ 0 ≤ nnrealCompletionEquiv v := by
  obtain ⟨y, x, rfl⟩ := exists_sub_of v
  rw [processCone_reflects nnreal_stability, map_sub,
    nnrealCompletionEquiv_of, nnrealCompletionEquiv_of, sub_nonneg]
  exact NNReal.coe_le_coe.symm

/-- Every real formal difference lies in the process span of the rank-one model. -/
theorem nnreal_processSpan_eq_top : processSpan ℝ≥0 = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨y, x, rfl⟩ := exists_sub_of v
  have hmem (a : ℝ≥0) : of a ∈ processCone ℝ≥0 :=
    (nnreal_mem_processCone_iff _).mpr (by rw [nnrealCompletionEquiv_of]; exact a.coe_nonneg)
  exact Submodule.sub_mem _ (Submodule.subset_span (hmem y))
    (Submodule.subset_span (hmem x))

theorem nnreal_unit_mem_processCone : (of 1 : Completion ℝ≥0) ∈ processCone ℝ≥0 :=
  (nnreal_mem_processCone_iff _).mpr (by rw [nnrealCompletionEquiv_of]; exact zero_le_one)

theorem nnreal_unit_ne_zero : (of 1 : Completion ℝ≥0) ≠ 0 := by
  intro h
  have hbad : (1 : ℝ) = 0 := by
    simpa only [nnrealCompletionEquiv_of, map_zero, NNReal.coe_one]
      using congrArg nnrealCompletionEquiv h
  exact one_ne_zero hbad

/-- The supremum construction normalized at one is the ordinary real coordinate. -/
theorem nnreal_entropyCoordinate_eq (w : processSpan ℝ≥0) :
    entropyCoordinate nnreal_stability nnreal_exchangeComparison (of 1)
      nnreal_unit_mem_processCone nnreal_unit_ne_zero w = nnrealCompletionEquiv w := by
  have hrepr := entropyCut_sSup_smul (processCone ℝ≥0)
    (processCone_sequentialOrderClosed nnreal_stability)
    (processCone_salient nnreal_stability)
    ((exchangeComparison_iff_coneTotal nnreal_stability).mp nnreal_exchangeComparison)
    nnreal_unit_mem_processCone nnreal_unit_ne_zero w.property
  have h := congrArg nnrealCompletionEquiv hrepr
  change sSup (entropyCut (processCone ℝ≥0) (of 1) w) = nnrealCompletionEquiv w
  simpa only [map_smul, nnrealCompletionEquiv_of, NNReal.coe_one, smul_eq_mul, mul_one]
    using h

/-- The normalized extension in the rank-one model. -/
noncomputable def nnrealEntropyExtension :
    EntropyExtension (entropyCoordinate nnreal_stability nnreal_exchangeComparison (of 1)
      nnreal_unit_mem_processCone nnreal_unit_ne_zero) :=
  ⟨nnrealCompletionEquiv.toLinearMap, by
    ext w
    exact (nnreal_entropyCoordinate_eq w).symm⟩

@[simp]
theorem nnrealEntropyExtension_state (x : ℝ≥0) :
    nnrealEntropyExtension.state x = (x : ℝ) :=
  nnrealCompletionEquiv_of x

/-- There are no independent conserved directions in the rank-one model. -/
theorem nnreal_conservation_subsingleton :
    Subsingleton (Completion ℝ≥0 ⧸ processSpan ℝ≥0) := by
  rw [nnreal_processSpan_eq_top]
  infer_instance

/-- Entropy on formal differences in the conserved-coordinate model. -/
noncomputable def sectorCompletionEntropy : Completion SectorState →ₗ[ℝ] ℝ :=
  ({ toFun := SectorState.entropy
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : SectorState →ₗ[ℝ] ℝ).comp
    (completionEquivSelf SectorState).toLinearMap

/-- Conserved amount on formal differences in the sector model. -/
noncomputable def sectorCompletionAmount : Completion SectorState →ₗ[ℝ] ℝ :=
  ({ toFun := SectorState.amount
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : SectorState →ₗ[ℝ] ℝ).comp
    (completionEquivSelf SectorState).toLinearMap

@[simp]
theorem sectorCompletionEntropy_of (x : SectorState) :
    sectorCompletionEntropy (of x) = SectorState.entropy x := by
  change SectorState.entropy (completionEquivSelf SectorState (of x)) = _
  rw [completionEquivSelf_of]

@[simp]
theorem sectorCompletionAmount_of (x : SectorState) :
    sectorCompletionAmount (of x) = SectorState.amount x := by
  change SectorState.amount (completionEquivSelf SectorState (of x)) = _
  rw [completionEquivSelf_of]

/-- Accessible sector processes preserve the amount and increase entropy. -/
theorem sector_mem_processCone_iff (v : Completion SectorState) :
    v ∈ processCone SectorState ↔
      sectorCompletionAmount v = 0 ∧ 0 ≤ sectorCompletionEntropy v := by
  obtain ⟨y, x, rfl⟩ := exists_sub_of v
  rw [processCone_reflects SectorState.stability]
  simp only [map_sub, sectorCompletionAmount_of, sectorCompletionEntropy_of,
    sub_eq_zero, sub_nonneg]
  change (SectorState.amount x = SectorState.amount y ∧
      SectorState.entropy x ≤ SectorState.entropy y) ↔ _
  exact and_congr eq_comm Iff.rfl

/-- The process span is exactly the kernel of the conserved amount. -/
theorem sector_processSpan_eq_ker :
    processSpan SectorState = LinearMap.ker sectorCompletionAmount := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    exact (sector_mem_processCone_iff v).mp hv |>.1
  · intro v hv
    change sectorCompletionAmount v = 0 at hv
    rcases le_total 0 (sectorCompletionEntropy v) with h | h
    · exact Submodule.subset_span ((sector_mem_processCone_iff v).mpr ⟨hv, h⟩)
    · have hn : -v ∈ processCone SectorState :=
        (sector_mem_processCone_iff (-v)).mpr (by
          constructor
          · simp only [map_neg, hv, neg_zero]
          · simpa only [map_neg] using neg_nonneg.mpr h)
      simpa using (processSpan SectorState).neg_mem (Submodule.subset_span hn)

theorem sectorCompletionAmount_surjective : Function.Surjective sectorCompletionAmount := by
  intro r
  exact ⟨of (show SectorState from (0, r)), sectorCompletionAmount_of _⟩

/-- The universal conserved-quantity space in the sector model is one real
amount coordinate. -/
noncomputable def sectorConservationEquiv :
    (Completion SectorState ⧸ processSpan SectorState) ≃ₗ[ℝ] ℝ :=
  (Submodule.quotEquivOfEq _ _ sector_processSpan_eq_ker).trans
    (sectorCompletionAmount.quotKerEquivOfSurjective sectorCompletionAmount_surjective)

@[simp]
theorem sectorConservationEquiv_mk (v : Completion SectorState) :
    sectorConservationEquiv ((processSpan SectorState).mkQ v) =
      sectorCompletionAmount v := by
  simp only [sectorConservationEquiv, Submodule.mkQ_apply, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The entropy axis identifies the process span of the sector model with ℝ. -/
noncomputable def sectorEntropyEquiv : processSpan SectorState ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (sectorCompletionEntropy.domRestrict (processSpan SectorState)) ⟨by
    intro x y h
    apply Subtype.ext
    apply (completionEquivSelf SectorState).injective
    apply Prod.ext
    · exact h
    · have hx : sectorCompletionAmount x = 0 := by
        exact (show (x : Completion SectorState) ∈ LinearMap.ker sectorCompletionAmount from
          sector_processSpan_eq_ker ▸ x.property)
      have hy : sectorCompletionAmount y = 0 := by
        exact (show (y : Completion SectorState) ∈ LinearMap.ker sectorCompletionAmount from
          sector_processSpan_eq_ker ▸ y.property)
      exact hx.trans hy.symm, by
    intro r
    have hr : of (show SectorState from (r, 0)) ∈ processSpan SectorState := by
      rw [sector_processSpan_eq_ker]
      change sectorCompletionAmount (of (show SectorState from (r, 0))) = 0
      exact sectorCompletionAmount_of _
    exact ⟨⟨of (show SectorState from (r, 0)), hr⟩, sectorCompletionEntropy_of _⟩⟩

theorem sectorEntropyEquiv_nonneg_iff (w : processSpan SectorState) :
    0 ≤ sectorEntropyEquiv w ↔ (w : Completion SectorState) ∈ processCone SectorState := by
  rw [sector_mem_processCone_iff]
  have hw : sectorCompletionAmount w = 0 := by
    exact (show (w : Completion SectorState) ∈ LinearMap.ker sectorCompletionAmount from
      sector_processSpan_eq_ker ▸ w.property)
  simp only [hw, true_and]
  rfl

theorem sector_unit_mem_processCone :
    (of (show SectorState from (1, 0))) ∈ processCone SectorState := by
  rw [sector_mem_processCone_iff, sectorCompletionAmount_of, sectorCompletionEntropy_of]
  exact ⟨rfl, zero_le_one⟩

theorem sector_unit_ne_zero : (of (show SectorState from (1, 0))) ≠ 0 := by
  intro h
  have hval : sectorCompletionEntropy (of (show SectorState from (1, 0))) = 0 :=
    (congrArg sectorCompletionEntropy h).trans sectorCompletionEntropy.map_zero
  have hbad : (1 : ℝ) = 0 :=
    (sectorCompletionEntropy_of (show SectorState from (1, 0))).symm.trans hval
  exact one_ne_zero hbad

/-- The abstract supremum construction recovers the entropy axis when the unit
is fixed by the process `(1, 0)`. -/
theorem sector_entropyCoordinate_eq (w : processSpan SectorState) :
    entropyCoordinate SectorState.stability SectorState.exchangeComparison
      (of (show SectorState from (1, 0))) sector_unit_mem_processCone sector_unit_ne_zero w =
      sectorEntropyEquiv w := by
  have h := linearMap_eq_generator_mul_coneEntropyEquiv (processCone SectorState)
    (processCone_sequentialOrderClosed SectorState.stability)
    (processCone_salient SectorState.stability)
    ((exchangeComparison_iff_coneTotal SectorState.stability).mp SectorState.exchangeComparison)
    (of (show SectorState from (1, 0))) sector_unit_mem_processCone sector_unit_ne_zero
    sectorEntropyEquiv.toLinearMap w
  have hunit : sectorEntropyEquiv
      ⟨of (show SectorState from (1, 0)), Submodule.subset_span sector_unit_mem_processCone⟩ = 1 :=
    sectorCompletionEntropy_of _
  change sectorEntropyEquiv w = sectorEntropyEquiv
      ⟨of (show SectorState from (1, 0)), Submodule.subset_span sector_unit_mem_processCone⟩ *
      entropyCoordinate SectorState.stability SectorState.exchangeComparison
        (of (show SectorState from (1, 0))) sector_unit_mem_processCone sector_unit_ne_zero w at h
  rw [hunit, one_mul] at h
  exact h.symm

/-- Adding any multiple of the conserved amount gives a normalized extension. -/
noncomputable def sectorEntropyExtension (b : ℝ) : EntropyExtension sectorEntropyEquiv :=
  ⟨sectorCompletionEntropy + b • sectorCompletionAmount, by
    ext w
    have hw : sectorCompletionAmount w = 0 := by
      exact (show (w : Completion SectorState) ∈ LinearMap.ker sectorCompletionAmount from
        sector_processSpan_eq_ker ▸ w.property)
    change sectorCompletionEntropy w + b * sectorCompletionAmount w = sectorCompletionEntropy w
    rw [hw, mul_zero, add_zero]⟩

@[simp]
theorem sectorEntropyExtension_state (b : ℝ) (x : SectorState) :
    (sectorEntropyExtension b).state x = SectorState.entropy x + b * SectorState.amount x := by
  change sectorCompletionEntropy (of x) + b * sectorCompletionAmount (of x) = _
  rw [sectorCompletionEntropy_of, sectorCompletionAmount_of]

/-- Every normalized entropy extension in the sector model has exactly one
coefficient multiplying the conserved amount. -/
theorem sectorEntropyExtension_classification (S : EntropyExtension sectorEntropyEquiv) :
    ∃! b : ℝ, S = sectorEntropyExtension b := by
  obtain ⟨φ, hφ, _⟩ := (sectorEntropyExtension 0).existsUnique_difference S
  let b := φ (sectorConservationEquiv.symm 1)
  have hφv (v : Completion SectorState) :
      φ ((processSpan SectorState).mkQ v) = b * sectorCompletionAmount v := by
    have hq : (processSpan SectorState).mkQ v =
        sectorCompletionAmount v • sectorConservationEquiv.symm 1 := by
      apply sectorConservationEquiv.injective
      rw [sectorConservationEquiv_mk, map_smul, sectorConservationEquiv.apply_symm_apply]
      simp only [smul_eq_mul, mul_one]
    rw [hq, map_smul]
    exact mul_comm _ _
  have hS : S = sectorEntropyExtension b := by
    apply Subtype.ext
    ext v
    have heq := LinearMap.congr_fun hφ v
    change S.val v = sectorCompletionEntropy v + b * sectorCompletionAmount v
    simpa only [sectorEntropyExtension, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, smul_eq_mul, zero_mul, add_zero, hφv] using heq
  refine ⟨b, hS, ?_⟩
  intro a ha
  have hstate := congrArg (fun T : EntropyExtension sectorEntropyEquiv =>
    T.val (of (show SectorState from (0, 1)))) (ha.symm.trans hS)
  change sectorCompletionEntropy (of (show SectorState from (0, 1))) +
      a * sectorCompletionAmount (of (show SectorState from (0, 1))) =
    sectorCompletionEntropy (of (show SectorState from (0, 1))) +
      b * sectorCompletionAmount (of (show SectorState from (0, 1))) at hstate
  rw [sectorCompletionEntropy_of, sectorCompletionAmount_of] at hstate
  change (0 : ℝ) + a * 1 = 0 + b * 1 at hstate
  simpa only [mul_one, zero_add] using hstate

end ProjectAInos.Thermodynamics
