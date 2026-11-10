module

public import ProjectAInos.Thermodynamics.ComparableCuts
public import ProjectAInos.Thermodynamics.PhysicalComparison

/-!
# Calibrators and comparison of finite scaled products

Crossed adiabatic equivalence identifies the reference directions of two
systems in the completed state space. If every component has an affine-line
representation along a common positive direction, matching reference amounts
cancel and comparison reduces to a real scalar inequality. The coefficients
may be negative: only the physical composition weights are nonnegative.

This is the algebraic calibration step behind LY Theorem 4.5. Existence of the
crossed calibrators and the single-system affine representations are separate
physical obligations; product comparison is proved from those premises here.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical.Accessibility

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
variable (P : Accessibility X)

/-- A raw state mapped first to its adiabatic class, then to the real completion. -/
noncomputable def completedState : X →+ Completion P.StateSpace :=
  Completion.of.comp P.stateClassHom

@[simp] theorem completedState_apply (x : X) :
    P.completedState x = Completion.of (P.stateClass x) := rfl

@[simp] theorem completedState_smul (a : ℝ≥0) (x : X) :
    P.completedState (a • x) = (a : ℝ) • P.completedState x := by
  simp only [completedState_apply, stateClass_scale, Completion.of_nnreal_smul,
    NNReal.smul_def]

/-- Equality in the completion is precisely adiabatic equivalence of raw states. -/
theorem completedState_eq_iff (x y : X) :
    P.completedState x = P.completedState y ↔ P.relation x y ∧ P.relation y x := by
  rw [completedState_apply, completedState_apply,
    (Completion.of_injective P.stability).eq_iff, stateClass_eq]

/-- Completion differences reflect physical accessibility. -/
theorem completedState_sub_mem_iff (x y : X) :
    P.completedState y - P.completedState x ∈ processCone P.StateSpace ↔
      P.relation x y :=
  processCone_reflects P.stability (P.stateClass x) (P.stateClass y)

/-- Crossed adiabatic equivalence exactly identifies the two reference directions. -/
theorem crossed_equivalence_iff_directions_eq (x₀ x₁ y₀ y₁ : X) :
    (P.relation (x₀ + y₁) (x₁ + y₀) ∧ P.relation (x₁ + y₀) (x₀ + y₁)) ↔
      P.completedState x₁ - P.completedState x₀ =
        P.completedState y₁ - P.completedState y₀ := by
  rw [← P.completedState_eq_iff, map_add, map_add, sub_eq_sub_iff_add_eq_add]
  constructor <;> intro h <;> simpa only [add_comm] using h.symm

/-- A strict reference pair gives a nonzero positive completed direction. -/
theorem strict_reference_direction {x₀ x₁ : X}
    (hstrict : P.relation x₀ x₁ ∧ ¬ P.relation x₁ x₀) :
    P.completedState x₁ - P.completedState x₀ ∈ processCone P.StateSpace ∧
      P.completedState x₁ - P.completedState x₀ ≠ 0 := by
  refine ⟨(P.completedState_sub_mem_iff x₀ x₁).mpr hstrict.1, ?_⟩
  intro hzero
  exact hstrict.2 ((P.completedState_eq_iff x₁ x₀).mp (sub_eq_zero.mp hzero)).1

/-- A crossed calibrator transports strictness as well as its entropy direction. -/
theorem strict_reference_of_crossed {x₀ x₁ y₀ y₁ : X}
    (hstrict : P.relation x₀ x₁ ∧ ¬ P.relation x₁ x₀)
    (hcross : P.relation (x₀ + y₁) (x₁ + y₀) ∧
      P.relation (x₁ + y₀) (x₀ + y₁)) :
    P.relation y₀ y₁ ∧ ¬ P.relation y₁ y₀ := by
  have heq := (P.crossed_equivalence_iff_directions_eq x₀ x₁ y₀ y₁).mp hcross
  obtain ⟨he, hne⟩ := P.strict_reference_direction hstrict
  rw [heq] at he hne
  refine ⟨(P.completedState_sub_mem_iff y₀ y₁).mp he, ?_⟩
  intro hback
  have hneg := (P.completedState_sub_mem_iff y₁ y₀).mpr hback
  apply (processCone_salient P.stability) _ he hne
  change -(P.completedState y₁ - P.completedState y₀) ∈ processCone P.StateSpace
  simpa only [neg_sub] using hneg

/-- Along a nonzero positive reference direction, physical accessibility is
exactly the order of its real coefficient. -/
theorem relation_iff_nonneg_of_completed_difference
    {e : Completion P.StateSpace} (he : e ∈ processCone P.StateSpace) (hne : e ≠ 0)
    (x y : X) (r : ℝ)
    (hdiff : P.completedState y - P.completedState x = r • e) :
    P.relation x y ↔ 0 ≤ r := by
  rw [← P.completedState_sub_mem_iff, hdiff]
  exact smul_mem_cone_iff_nonneg (processCone P.StateSpace)
    (processCone_salient P.stability) he hne r

/-- Extensive physical weights multiply unrestricted real affine coordinates. -/
theorem completed_sum_smul_affine {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (x reference : ι → X) (coordinate : ι → ℝ)
    (e : Completion P.StateSpace)
    (haffine : ∀ i, P.completedState (x i) - P.completedState (reference i) =
      coordinate i • e) :
    P.completedState (∑ i, weight i • x i) =
      (∑ i, (weight i : ℝ) • P.completedState (reference i)) +
        (∑ i, (weight i : ℝ) * coordinate i) • e := by
  simp only [map_sum, completedState_smul]
  calc
    ∑ i, (weight i : ℝ) • P.completedState (x i) =
        ∑ i, ((weight i : ℝ) • P.completedState (reference i) +
          ((weight i : ℝ) * coordinate i) • e) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := (sub_eq_iff_eq_add).mp (haffine i)
      rw [h, smul_add, ← mul_smul, add_comm]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_smul]

/-- Weighted reference balance leaves only the total affine-coordinate
difference, even when the two finite products use different index types. -/
theorem completed_products_difference {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (x reference₁ : ι → X) (y reference₂ : κ → X)
    (u : ι → ℝ) (v : κ → ℝ) (e : Completion P.StateSpace)
    (hx : ∀ i, P.completedState (x i) - P.completedState (reference₁ i) = u i • e)
    (hy : ∀ j, P.completedState (y j) - P.completedState (reference₂ j) = v j • e)
    (hbalance : (∑ i, (a i : ℝ) • P.completedState (reference₁ i)) =
      ∑ j, (b j : ℝ) • P.completedState (reference₂ j)) :
    P.completedState (∑ j, b j • y j) - P.completedState (∑ i, a i • x i) =
      ((∑ j, (b j : ℝ) * v j) - ∑ i, (a i : ℝ) * u i) • e := by
  rw [P.completed_sum_smul_affine a x reference₁ u e hx,
    P.completed_sum_smul_affine b y reference₂ v e hy, hbalance, sub_smul]
  abel

/-- The entropy criterion for finite products follows from affine-line
representations and balanced references, without assuming product comparison. -/
theorem finite_products_relation_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (x reference₁ : ι → X) (y reference₂ : κ → X)
    (u : ι → ℝ) (v : κ → ℝ) {e : Completion P.StateSpace}
    (he : e ∈ processCone P.StateSpace) (hne : e ≠ 0)
    (hx : ∀ i, P.completedState (x i) - P.completedState (reference₁ i) = u i • e)
    (hy : ∀ j, P.completedState (y j) - P.completedState (reference₂ j) = v j • e)
    (hbalance : (∑ i, (a i : ℝ) • P.completedState (reference₁ i)) =
      ∑ j, (b j : ℝ) • P.completedState (reference₂ j)) :
    P.relation (∑ i, a i • x i) (∑ j, b j • y j) ↔
      (∑ i, (a i : ℝ) * u i) ≤ ∑ j, (b j : ℝ) * v j := by
  rw [P.relation_iff_nonneg_of_completed_difference he hne _ _ _
    (P.completed_products_difference a b x reference₁ y reference₂ u v e hx hy hbalance)]
  exact sub_nonneg

/-- Any two balanced finite products along one positive direction are comparable. -/
theorem finite_products_comparable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ≥0) (b : κ → ℝ≥0) (x reference₁ : ι → X) (y reference₂ : κ → X)
    (u : ι → ℝ) (v : κ → ℝ) {e : Completion P.StateSpace}
    (he : e ∈ processCone P.StateSpace) (hne : e ≠ 0)
    (hx : ∀ i, P.completedState (x i) - P.completedState (reference₁ i) = u i • e)
    (hy : ∀ j, P.completedState (y j) - P.completedState (reference₂ j) = v j • e)
    (hbalance : (∑ i, (a i : ℝ) • P.completedState (reference₁ i)) =
      ∑ j, (b j : ℝ) • P.completedState (reference₂ j)) :
    P.relation (∑ i, a i • x i) (∑ j, b j • y j) ∨
      P.relation (∑ j, b j • y j) (∑ i, a i • x i) := by
  rcases le_total (∑ i, (a i : ℝ) * u i) (∑ j, (b j : ℝ) * v j) with h | h
  · exact Or.inl ((P.finite_products_relation_iff a b x reference₁ y reference₂
      u v he hne hx hy hbalance).mpr h)
  · exact Or.inr ((P.finite_products_relation_iff b a y reference₂ x reference₁
      v u he hne hy hx hbalance.symm).mpr h)

/-- With the same composition weights, reference balance is automatic. -/
theorem scaled_product_relation_iff {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (x y reference : ι → X) (u v : ι → ℝ)
    {e : Completion P.StateSpace} (he : e ∈ processCone P.StateSpace) (hne : e ≠ 0)
    (hx : ∀ i, P.completedState (x i) - P.completedState (reference i) = u i • e)
    (hy : ∀ i, P.completedState (y i) - P.completedState (reference i) = v i • e) :
    P.relation (∑ i, weight i • x i) (∑ i, weight i • y i) ↔
      (∑ i, (weight i : ℝ) * u i) ≤ ∑ i, (weight i : ℝ) * v i :=
  P.finite_products_relation_iff weight weight x reference y reference u v he hne hx hy rfl

/-- Comparison for an arbitrary finite scaled product of a typed system family.
The only system-level input is an affine-line representation along one common
positive direction; neither product comparison nor ECH is a premise. Zero
physical weights are allowed. -/
theorem scaled_product_comparison_of_affine_lines {Γ : Type*} {State : Γ → Type*}
    (represent : ∀ g, State g → X) (reference : ∀ g, State g)
    {e : Completion P.StateSpace} (he : e ∈ processCone P.StateSpace) (hne : e ≠ 0)
    (haffine : ∀ g (z : State g), ∃ r : ℝ,
      P.completedState (represent g z) - P.completedState (represent g (reference g)) = r • e)
    {ι : Type*} [Fintype ι] (system : ι → Γ) (weight : ι → ℝ≥0)
    (x y : ∀ i, State (system i)) :
    P.relation (∑ i, weight i • represent (system i) (x i))
        (∑ i, weight i • represent (system i) (y i)) ∨
      P.relation (∑ i, weight i • represent (system i) (y i))
        (∑ i, weight i • represent (system i) (x i)) := by
  classical
  let u i := (haffine (system i) (x i)).choose
  let v i := (haffine (system i) (y i)).choose
  apply P.finite_products_comparable weight weight
    (fun i => represent (system i) (x i)) (fun i => represent (system i) (reference (system i)))
    (fun i => represent (system i) (y i)) (fun i => represent (system i) (reference (system i)))
    u v he hne
  · exact fun i => (haffine (system i) (x i)).choose_spec
  · exact fun i => (haffine (system i) (y i)).choose_spec
  · rfl

/-- A finite family of crossed calibrators and single-system affine-line
representations gives comparison on every scaled product of those systems. -/
theorem scaled_products_comparable_of_calibrators {ι : Type*} [Fintype ι]
    (weight : ι → ℝ≥0) (x y lower upper : ι → X) (u v : ι → ℝ) (anchor : ι)
    (hstrict : P.relation (lower anchor) (upper anchor) ∧
      ¬ P.relation (upper anchor) (lower anchor))
    (hcalibrated : ∀ i,
      P.relation (lower i + upper anchor) (upper i + lower anchor) ∧
        P.relation (upper i + lower anchor) (lower i + upper anchor))
    (hx : ∀ i, P.completedState (x i) - P.completedState (lower i) =
      u i • (P.completedState (upper i) - P.completedState (lower i)))
    (hy : ∀ i, P.completedState (y i) - P.completedState (lower i) =
      v i • (P.completedState (upper i) - P.completedState (lower i))) :
    P.relation (∑ i, weight i • x i) (∑ i, weight i • y i) ∨
      P.relation (∑ i, weight i • y i) (∑ i, weight i • x i) := by
  obtain ⟨he, hne⟩ := P.strict_reference_direction hstrict
  have hdir i := (P.crossed_equivalence_iff_directions_eq
    (lower i) (upper i) (lower anchor) (upper anchor)).mp (hcalibrated i)
  apply P.finite_products_comparable weight weight x lower y lower u v he hne
  · intro i
    simpa only [hdir i] using hx i
  · intro i
    simpa only [hdir i] using hy i
  · rfl

end ProjectAInos.Thermodynamics.Physical.Accessibility
