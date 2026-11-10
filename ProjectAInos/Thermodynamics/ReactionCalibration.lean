module

public import ProjectAInos.Thermodynamics.CalibratedEntropy
public import ProjectAInos.Thermodynamics.PhysicalReactions

/-!
# Physical calibration and the no-sinks premise

Absence of sinks is stated using actual transitions between composition labels,
before choosing entropy or transition costs. Pairwise thermal calibrators give
the additive equal-label entropy criterion. The reaction theorem then selects
extensive constants and returns entropy monotone for all transitions.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics

namespace Reactions

variable {X Γ : Type*} [AddCommMonoid X] [AddCommMonoid Γ]

/-- A transition between labels is witnessed by physical representatives. -/
def LabelTransition (label : X →+ Γ) (accessible : X → X → Prop) (a b : Γ) : Prop :=
  ∃ x y, label x = a ∧ label y = b ∧ accessible x y

/-- Actual finite-chain connectivity, allowing one common ancillary label. -/
def ActualConnected (label : X →+ Γ) (accessible : X → X → Prop) (a b : Γ) : Prop :=
  ∃ z, Relation.ReflTransGen (LabelTransition label accessible) (a + z) (b + z)

/-- Physical absence of sinks, independent of the entropy normalization. -/
def RawNoSinks (label : X →+ Γ) (accessible : X → X → Prop) : Prop :=
  ∀ a b, ActualConnected label accessible a b → ActualConnected label accessible b a

/-- Entropy changes only annotate an actual chain; they do not change which
labels it connects. -/
theorem exists_actualCostChain_iff (label : X →+ Γ) (entropy : X →+ ℝ)
    (accessible : X → X → Prop) (a b : Γ) :
    (∃ r, ActualCostChain label entropy accessible a b r) ↔
      Relation.ReflTransGen (LabelTransition label accessible) a b := by
  constructor
  · rintro ⟨r, h⟩
    induction h with
    | nil => exact Relation.ReflTransGen.refl
    | @step b c r x y _ hx hy hxy ih => exact ih.tail ⟨x, y, hx, hy, hxy⟩
  · intro h
    induction h with
    | refl => exact ⟨0, ActualCostChain.nil⟩
    | @tail b c _ hbc ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨x, y, hx, hy, hxy⟩ := hbc
      exact ⟨_, ActualCostChain.step hr hx hy hxy⟩

/-- The cost-based no-sinks interface is supplied by the physical transition
graph for every choice of additive entropy. -/
theorem RawNoSinks.costChain_reverse {label : X →+ Γ}
    {accessible : X → X → Prop} (hM : RawNoSinks label accessible)
    (entropy : X →+ ℝ) (a b : Γ)
    (h : ∃ z c, ActualCostChain label entropy accessible (a + z) (b + z) c) :
    ∃ z c, ActualCostChain label entropy accessible (b + z) (a + z) c := by
  obtain ⟨z, c, hc⟩ := h
  obtain ⟨w, hw⟩ := hM a b ⟨z, (exists_actualCostChain_iff label entropy accessible _ _).mp ⟨c, hc⟩⟩
  obtain ⟨r, hr⟩ := (exists_actualCostChain_iff label entropy accessible _ _).mpr hw
  exact ⟨w, r, hr⟩

end Reactions

namespace Physical.Nonreactive

/-- Every finite composition label has a representative if each atomic system
has at least one physical state. -/
theorem compositionLabel_surjective {Γ : Type*} (State : Γ → Type*)
    (hstate : ∀ g, Nonempty (State g)) : Function.Surjective (compositionLabel State) := by
  classical
  let base (g : Γ) : State g := (hstate g).some
  intro a
  refine ⟨∑ g ∈ a.support, a g • CompositeState.mk (.atom ⟨g, base g⟩), ?_⟩
  simp only [map_sum, compositionLabel_scale, compositionLabel_atom, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  exact Finsupp.sum_single a

end Physical.Nonreactive

namespace Physical.ThermalFamily

variable {Γ : Type*} {State : Γ → Type*}
    {P : Accessibility (CompositeState (Σ g, State g))} (F : ThermalFamily P)

/-- Thermal calibration and the physical absence of sinks give a weak entropy
for the full reacting state relation. The within-label monotonicity premise of
the cost theorem is derived here, rather than supplied separately. -/
theorem exists_weak_entropy_of_calibrators (hcal : F.HasCalibrators)
    (n : Γ → ℕ) (S : ∀ g, SimpleSystem P (n g))
    (hS : ∀ g, F.admitted (S g)) (hnonempty : ∀ g, (S g).domain.Nonempty)
    (hstate : ∀ g, Nonempty (State g))
    (chart : ∀ g, State g → (S g).domain)
    (hrepresent : ∀ g z, (S g).represent (chart g z) = CompositeState.mk (.atom ⟨g, z⟩))
    (hM : Reactions.RawNoSinks (Nonreactive.compositionLabel State) P.relation) :
    ∃ (entropy totalEntropy : CompositeState (Σ g, State g) →+ ℝ)
      (B : (Γ →₀ ℝ≥0) →ₗ[ℝ≥0] ℝ),
      (∀ x, totalEntropy x = entropy x + B (Nonreactive.compositionLabel State x)) ∧
      (∀ (r : ℝ≥0) x, entropy (r • x) = (r : ℝ) * entropy x) ∧
      (∀ x y, Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y →
        (P.relation x y ↔ entropy x ≤ entropy y)) ∧
      (∀ (r : ℝ≥0) x, totalEntropy (r • x) = (r : ℝ) * totalEntropy x) ∧
      (∀ x y, P.relation x y → totalEntropy x ≤ totalEntropy y) ∧
      (∀ x y, Nonreactive.compositionLabel State x = Nonreactive.compositionLabel State y →
        (P.relation x y ↔ totalEntropy x ≤ totalEntropy y)) := by
  obtain ⟨entropy, hscale, hcriterion⟩ :=
    F.exists_calibrated_entropy hcal n S hS hnonempty chart hrepresent
  have hscaleRelation (r : ℝ≥0) (hr : 0 < r) (x y : CompositeState (Σ g, State g)) :
      P.relation (r • x) (r • y) ↔ P.relation x y := by
    constructor
    · intro h
      simpa only [inv_smul_smul₀ hr.ne'] using P.scale_mono r⁻¹ h
    · exact P.scale_mono r
  obtain ⟨B, totalEntropy, htotal, hext, hmono⟩ :=
    Reactions.exists_weak_entropy_from_raw_states (Nonreactive.compositionLabel State)
      entropy P.relation (Nonreactive.compositionLabel_surjective State hstate)
      (Nonreactive.compositionLabel_scale State) hscale P.refl P.add_mono hscaleRelation
      (fun {x y} hxy hlabel => (hcriterion x y hlabel).mp hxy)
      (hM.costChain_reverse entropy)
  refine ⟨entropy, totalEntropy, B, htotal, hscale, hcriterion, hext, hmono, ?_⟩
  intro x y hlabel
  rw [htotal x, htotal y, hlabel, add_le_add_iff_right]
  exact hcriterion x y hlabel

end Physical.ThermalFamily

end ProjectAInos.Thermodynamics
