module

public import ProjectAInos.Thermodynamics.CalibratorExistence
public import ProjectAInos.Thermodynamics.SimpleComparison
public import ProjectAInos.Thermodynamics.SimpleEntropy
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Realizing calibrators from collinear reference directions

Continuous normalized entropy realizes every value between zero and one on
the actual coordinate segment between strict reference states. Thus positive
collinearity of two completed reference directions yields smaller, unscaled
reference pairs with equal directions, hence a physical entropy calibrator.
Conversely, absence of calibrators makes any two strict reference directions
linearly independent. Negative scalar multiples are excluded by cone salience.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]
    {P : Accessibility X}

namespace SimpleSystem

/-- Every entropy value between normalized references is realized on their
coordinate segment. This concerns actual simple states, not formal mixtures. -/
theorem exists_referenceEntropy_on_segment {n : ℕ} (S : SimpleSystem P n)
    (hlocal : S.LocalMixtureIntervals) (x₀ x₁ : S.domain)
    (hstrict : P.relation (S.represent x₀) (S.represent x₁) ∧
      ¬ P.relation (S.represent x₁) (S.represent x₀))
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∃ x : S.domain, x.val ∈ segment ℝ x₀.val x₁.val ∧
      S.referenceEntropy hlocal x₀ x₁ hstrict x = q := by
  have hsub := S.convex_domain.segment_subset x₀.property x₁.property
  have hcont := (S.referenceEntropy_continuousOn hlocal x₀ x₁ hstrict).mono hsub
  have hnorm := S.referenceEntropy_normalized hlocal x₀ x₁ hstrict
  have hq' : q ∈ Icc (S.referenceEntropy hlocal x₀ x₁ hstrict x₀)
      (S.referenceEntropy hlocal x₀ x₁ hstrict x₁) := by
    simpa only [hnorm.1, hnorm.2] using hq
  obtain ⟨x, hx, hs⟩ := (convex_segment x₀.val x₁.val).isPreconnected.intermediate_value
    (left_mem_segment ℝ x₀.val x₁.val) (right_mem_segment ℝ x₀.val x₁.val) hcont hq'
  exact ⟨⟨x, hsub hx⟩, hx, hs⟩

end SimpleSystem

namespace ThermalFamily

variable (F : ThermalFamily P)

/-- Positive collinearity produces smaller strict pairs with the prescribed
lower endpoints and equal completed differences. Intermediate values are
realized on the original simple-system coordinate segments. -/
theorem calibrator_with_lower_references_of_collinear_directions
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (a₀ a₁ : S.domain) (b₀ b₁ : T.domain)
    (ha : P.relation (S.represent a₀) (S.represent a₁) ∧
      ¬ P.relation (S.represent a₁) (S.represent a₀))
    (hb : P.relation (T.represent b₀) (T.represent b₁) ∧
      ¬ P.relation (T.represent b₁) (T.represent b₀))
    (r : ℝ) (hr : 0 < r)
    (hdir : P.completedState (S.represent a₁) - P.completedState (S.represent a₀) =
      r • (P.completedState (T.represent b₁) - P.completedState (T.represent b₀))) :
    ∃ a : S.domain, ∃ b : T.domain,
      a.val ∈ segment ℝ a₀.val a₁.val ∧ b.val ∈ segment ℝ b₀.val b₁.val ∧
      IsEntropyCalibrator P (S.represent a₀) (S.represent a)
        (T.represent b₀) (T.represent b) := by
  let hlocalS := F.localMixtureIntervals_of_axioms S hS
  let hlocalT := F.localMixtureIntervals_of_axioms T hT
  let q : ℝ := 1 / (1 + r)
  have hd : 0 < 1 + r := by linarith
  have hq : 0 < q := one_div_pos.mpr hd
  have hqle : q ≤ 1 := by
    change 1 / (1 + r) ≤ 1
    exact (div_le_one hd).mpr (by linarith)
  have hqr : 0 < q * r := mul_pos hq hr
  have hqrle : q * r ≤ 1 := by
    dsimp only [q]
    rw [one_div_mul_eq_div]
    exact (div_le_one hd).mpr (by linarith)
  obtain ⟨a, haseg, hsa⟩ := S.exists_referenceEntropy_on_segment hlocalS a₀ a₁ ha ⟨hq.le, hqle⟩
  obtain ⟨b, hbseg, hsb⟩ := T.exists_referenceEntropy_on_segment hlocalT b₀ b₁ hb ⟨hqr.le, hqrle⟩
  have hna := (S.referenceEntropy_normalized hlocalS a₀ a₁ ha).1
  have hnb := (T.referenceEntropy_normalized hlocalT b₀ b₁ hb).1
  have hasa : P.relation (S.represent a₀) (S.represent a) ∧
      ¬ P.relation (S.represent a) (S.represent a₀) := by
    constructor
    · apply (S.referenceEntropy_relation_iff hlocalS a₀ a₁ ha a₀.property a.property).mpr
      simpa only [hna, hsa] using hq.le
    · intro hback
      have h := (S.referenceEntropy_relation_iff hlocalS a₀ a₁ ha a.property a₀.property).mp hback
      rw [hna, hsa] at h
      exact hq.not_ge h
  have hbsb : P.relation (T.represent b₀) (T.represent b) ∧
      ¬ P.relation (T.represent b) (T.represent b₀) := by
    constructor
    · apply (T.referenceEntropy_relation_iff hlocalT b₀ b₁ hb b₀.property b.property).mpr
      simpa only [hnb, hsb] using hqr.le
    · intro hback
      have h := (T.referenceEntropy_relation_iff hlocalT b₀ b₁ hb b.property b₀.property).mp hback
      rw [hnb, hsb] at h
      exact hqr.not_ge h
  refine ⟨a, b, haseg, hbseg, hasa, hbsb, ?_⟩
  apply (P.crossed_equivalence_iff_directions_eq _ _ _ _).mpr
  rw [S.referenceEntropy_repr hlocalS a₀ a₁ ha a.property,
    T.referenceEntropy_repr hlocalT b₀ b₁ hb b.property, hsa, hsb, hdir, mul_smul]

/-- Collinear positive reference directions imply existence of a genuine
crossed calibrator in the two unscaled simple systems. -/
theorem calibrator_of_collinear_reference_directions
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (a₀ a₁ : S.domain) (b₀ b₁ : T.domain)
    (ha : P.relation (S.represent a₀) (S.represent a₁) ∧
      ¬ P.relation (S.represent a₁) (S.represent a₀))
    (hb : P.relation (T.represent b₀) (T.represent b₁) ∧
      ¬ P.relation (T.represent b₁) (T.represent b₀))
    (r : ℝ) (hr : 0 < r)
    (hdir : P.completedState (S.represent a₁) - P.completedState (S.represent a₀) =
      r • (P.completedState (T.represent b₁) - P.completedState (T.represent b₀))) :
    ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d) := by
  obtain ⟨a, b, _, _, hab⟩ :=
    F.calibrator_with_lower_references_of_collinear_directions S T hS hT a₀ a₁ b₀ b₁ ha hb r hr hdir
  exact ⟨a₀, a, b₀, b, hab⟩

/-- In the absence of calibrators, strict reference directions cannot be
scalar multiples. Cone salience excludes negative scalars, and nonzeroness
excludes zero, so positive realization handles every remaining case. -/
theorem reference_direction_ne_smul_of_no_calibrator
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (a₀ a₁ : S.domain) (b₀ b₁ : T.domain)
    (ha : P.relation (S.represent a₀) (S.represent a₁) ∧
      ¬ P.relation (S.represent a₁) (S.represent a₀))
    (hb : P.relation (T.represent b₀) (T.represent b₁) ∧
      ¬ P.relation (T.represent b₁) (T.represent b₀)) (r : ℝ) :
    P.completedState (S.represent a₁) - P.completedState (S.represent a₀) ≠
      r • (P.completedState (T.represent b₁) - P.completedState (T.represent b₀)) := by
  intro hdir
  obtain ⟨hea, hnea⟩ := P.strict_reference_direction ha
  obtain ⟨heb, hneb⟩ := P.strict_reference_direction hb
  have hr : 0 ≤ r := (smul_mem_cone_iff_nonneg (processCone P.StateSpace)
    (processCone_salient P.stability) heb hneb r).mp (hdir ▸ hea)
  have hrne : r ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hdir
    exact hnea hdir
  exact hno (F.calibrator_of_collinear_reference_directions S T hS hT a₀ a₁ b₀ b₁
    ha hb r (lt_of_le_of_ne hr (Ne.symm hrne)) hdir)

/-- Absence of calibrators implies linear independence of arbitrary strict
reference directions in the real completed state space. -/
theorem reference_directions_independent_of_no_calibrator
    {n m : ℕ} (S : SimpleSystem P n) (T : SimpleSystem P m)
    (hS : F.admitted S) (hT : F.admitted T)
    (hno : ¬ ∃ a b : S.domain, ∃ c d : T.domain,
      IsEntropyCalibrator P (S.represent a) (S.represent b) (T.represent c) (T.represent d))
    (a₀ a₁ : S.domain) (b₀ b₁ : T.domain)
    (ha : P.relation (S.represent a₀) (S.represent a₁) ∧
      ¬ P.relation (S.represent a₁) (S.represent a₀))
    (hb : P.relation (T.represent b₀) (T.represent b₁) ∧
      ¬ P.relation (T.represent b₁) (T.represent b₀)) :
    LinearIndependent ℝ ![P.completedState (S.represent a₁) - P.completedState (S.represent a₀),
      P.completedState (T.represent b₁) - P.completedState (T.represent b₀)] := by
  apply linearIndependent_fin2.mpr
  refine ⟨(P.strict_reference_direction hb).2, ?_⟩
  intro r hdir
  exact F.reference_direction_ne_smul_of_no_calibrator S T hS hT hno a₀ a₁ b₀ b₁ ha hb r hdir.symm

end ThermalFamily

end ProjectAInos.Thermodynamics.Physical
