module

public import ProjectAInos.Thermodynamics.FamilyCalibration
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Additive calibrated entropy on composite states

A linear functional taking value one on the common process direction gives
an additive extensive entropy on all raw composites. Equal composition labels
cancel the reference contributions, so entropy characterizes accessibility in
each label fiber. Accessibility is allowed to include reactions between labels:
this theorem does not claim monotonicity across different labels.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

namespace Accessibility

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    (P : Accessibility X)

/-- Evaluate a completed-state observable on raw physical states. -/
noncomputable def completedEntropy (L : Completion P.StateSpace →ₗ[ℝ] ℝ) : X →+ ℝ :=
  L.toAddMonoidHom.comp P.completedState

theorem completedEntropy_scale (L : Completion P.StateSpace →ₗ[ℝ] ℝ)
    (r : ℝ≥0) (x : X) :
    P.completedEntropy L (r • x) = (r : ℝ) * P.completedEntropy L x := by
  change L (P.completedState (r • x)) = (r : ℝ) * L (P.completedState x)
  rw [P.completedState_smul, map_smul, smul_eq_mul]

/-- Normalization on a positive direction suffices for the entropy criterion
for every physical difference lying on that line. -/
theorem relation_iff_completedEntropy_le
    (L : Completion P.StateSpace →ₗ[ℝ] ℝ)
    {e : Completion P.StateSpace} (he : e ∈ processCone P.StateSpace) (hne : e ≠ 0)
    (hL : L e = 1) (x y : X) (r : ℝ)
    (hdiff : P.completedState y - P.completedState x = r • e) :
    P.relation x y ↔ P.completedEntropy L x ≤ P.completedEntropy L y := by
  have hs : P.completedEntropy L y - P.completedEntropy L x = r := by
    change L (P.completedState y) - L (P.completedState x) = r
    rw [← map_sub, hdiff, map_smul, hL, smul_eq_mul, mul_one]
  rw [P.relation_iff_nonneg_of_completed_difference he hne x y r hdiff, ← hs]
  exact sub_nonneg

end Accessibility

namespace ThermalFamily

variable {Γ : Type*} {State : Γ → Type*}
    {P : Accessibility (CompositeState (Σ g, State g))} (F : ThermalFamily P)

/-- A family of nonempty simple systems with pairwise calibrators supplies an
additive extensive entropy on formal composites, characterizing all processes
with matching composition labels. No label-conservation premise is required:
the accessibility relation may also contain reactions. -/
theorem exists_calibrated_entropy (hcal : F.HasCalibrators)
    (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (hnonempty : ∀ g, (S g).domain.Nonempty)
    (chart : ∀ g, State g → (S g).domain)
    (hrepresent : ∀ g z, (S g).represent (chart g z) = CompositeState.mk (.atom ⟨g, z⟩)) :
    ∃ entropy : CompositeState (Σ g, State g) →+ ℝ,
      (∀ (r : ℝ≥0) x, entropy (r • x) = (r : ℝ) * entropy x) ∧
      ∀ x y, Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y →
        (P.relation x y ↔ entropy x ≤ entropy y) := by
  classical
  rcases isEmpty_or_nonempty Γ with hempty | hΓ
  · let := hempty
    refine ⟨0, by simp, ?_⟩
    intro x y _
    have hz (z : CompositeState (Σ g, State g)) : P.stateClass z = 0 := by
      simpa using Nonreactive.atom_normal_form State P z
    change P.stateClass x ≤ P.stateClass y ↔ (0 : ℝ) ≤ 0
    rw [hz x, hz y]
    exact iff_of_true le_rfl le_rfl
  let := hΓ
  let anchor : Γ := Classical.choice hΓ
  obtain ⟨e, he, hne, reference, coordinate, hcoordinate⟩ :=
    F.exists_common_coordinates hcal n S hS hnonempty anchor
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℝ hne
  let entropy := P.completedEntropy L
  have hproduct (p : Nonreactive.ScaledProduct (Γ := Γ)) (u v : p.States State) :
      P.relation (p.realize State u) (p.realize State v) ↔
        entropy (p.realize State u) ≤ entropy (p.realize State v) := by
    have hu (i : Fin p.count) := hcoordinate (p.system i) (chart (p.system i) (u i))
    have hv (i : Fin p.count) := hcoordinate (p.system i) (chart (p.system i) (v i))
    simp only [hrepresent] at hu hv
    let r := (∑ i, (p.amount i : ℝ) * coordinate (p.system i) (chart (p.system i) (v i))) -
      ∑ i, (p.amount i : ℝ) * coordinate (p.system i) (chart (p.system i) (u i))
    have hdiff : P.completedState (p.realize State v) - P.completedState (p.realize State u) =
        r • e :=
      P.completed_products_difference p.amount p.amount
        (fun i => CompositeState.mk (.atom ⟨p.system i, u i⟩))
        (fun i => (S (p.system i)).represent (reference (p.system i)))
        (fun i => CompositeState.mk (.atom ⟨p.system i, v i⟩))
        (fun i => (S (p.system i)).represent (reference (p.system i)))
        (fun i => coordinate (p.system i) (chart (p.system i) (u i)))
        (fun i => coordinate (p.system i) (chart (p.system i) (v i))) e hu hv rfl
    exact P.relation_iff_completedEntropy_le L he hne hL _ _ r hdiff
  refine ⟨entropy, P.completedEntropy_scale L, ?_⟩
  intro x y hlabel
  obtain ⟨p, u, v, hx, hy⟩ := Nonreactive.common_product_of_equal_label State P x y hlabel
  have hsx : entropy x = entropy (p.realize State u) :=
    congrArg (fun z => L (Completion.of z)) hx
  have hsy : entropy y = entropy (p.realize State v) :=
    congrArg (fun z => L (Completion.of z)) hy
  rw [hsx, hsy]
  change P.stateClass x ≤ P.stateClass y ↔ _
  rw [hx, hy]
  exact hproduct p u v

/-- With nonreactive conservation, the calibrated entropy criterion supplies
the exchange-comparison hypothesis of the algebraic entropy theorem. -/
theorem exchangeComparison_of_calibrators (hcal : F.HasCalibrators)
    (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (chart : ∀ g, State g → (S g).domain)
    (hrepresent : ∀ g z, (S g).represent (chart g z) = CompositeState.mk (.atom ⟨g, z⟩))
    (hpreserved : ∀ {x y}, P.relation x y →
      Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y) :
    ExchangeComparison P.StateSpace := by
  apply Nonreactive.exchangeComparison_of_productComparison State P hpreserved
  intro p u v
  have h := F.scaled_products_comparable hcal (fun i => n (p.system i))
    (fun i => S (p.system i)) (fun i => hS (p.system i)) p.amount
    (fun i => chart (p.system i) (u i)) (fun i => chart (p.system i) (v i))
  simpa only [hrepresent, Nonreactive.ScaledProduct.realize] using h

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
