module

public import ProjectAInos.Thermodynamics.Representation
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Tactic.NormNum

/-!
# Degenerate and non-Archimedean cones

The lexicographic cone has a total order but fails sequential order closedness.
The zero cone has zero process span, so it has no nonzero entropy direction.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

/-- The lexicographically nonnegative cone in two real coordinates. -/
def lexicographicCone : PointedCone ℝ (ℝ × ℝ) where
  carrier := {x | 0 < x.1 ∨ x.1 = 0 ∧ 0 ≤ x.2}
  zero_mem' := Or.inr ⟨rfl, le_rfl⟩
  add_mem' := by
    intro x y hx hy
    change 0 < x.1 + y.1 ∨ x.1 + y.1 = 0 ∧ 0 ≤ x.2 + y.2
    rcases hx with hx | ⟨hx, hx'⟩ <;> rcases hy with hy | ⟨hy, hy'⟩
    · exact Or.inl (add_pos hx hy)
    · exact Or.inl (by simpa [hy] using hx)
    · exact Or.inl (by simpa [hx] using hy)
    · exact Or.inr ⟨by simp [hx, hy], add_nonneg hx' hy'⟩
  smul_mem' := by
    intro r x hx
    change 0 < (r : ℝ) * x.1 ∨ (r : ℝ) * x.1 = 0 ∧ 0 ≤ (r : ℝ) * x.2
    rcases eq_or_lt_of_le r.property with hr | hr
    · exact Or.inr ⟨by simp [← hr], by simp [← hr]⟩
    · rcases hx with hx | ⟨hx, hx'⟩
      · exact Or.inl (mul_pos hr hx)
      · exact Or.inr ⟨by simp [hx], mul_nonneg hr.le hx'⟩

/-- Every vector has a nonnegative or nonpositive lexicographic sign. -/
theorem lexicographicCone_total : ConeTotalOnSpan lexicographicCone := by
  intro x _
  change (0 < x.1 ∨ x.1 = 0 ∧ 0 ≤ x.2) ∨
    (0 < -x.1 ∨ -x.1 = 0 ∧ 0 ≤ -x.2)
  rcases lt_trichotomy 0 x.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total 0 x.2 with hy | hy
    · exact Or.inl (Or.inr ⟨h.symm, hy⟩)
    · exact Or.inr (Or.inr ⟨by simp [← h], neg_nonneg.mpr hy⟩)
  · exact Or.inr (Or.inl (neg_pos.mpr h))

/-- Both signs can belong to the lexicographic cone only at zero. -/
theorem lexicographicCone_salient :
    (lexicographicCone : ConvexCone ℝ (ℝ × ℝ)).Salient := by
  intro x hx hne hneg
  change 0 < x.1 ∨ x.1 = 0 ∧ 0 ≤ x.2 at hx
  change 0 < -x.1 ∨ -x.1 = 0 ∧ 0 ≤ -x.2 at hneg
  apply hne
  rcases hx with hx | ⟨hx, hy⟩ <;> rcases hneg with hn | ⟨hn, hny⟩
  · linarith
  · linarith
  · linarith
  · exact Prod.ext hx (show x.2 = 0 from le_antisymm (by linarith) hy)

/-- Positive perturbations of an excluded boundary vector demonstrate failure
of SC even though the cone is salient and total on its span. -/
theorem lexicographicCone_not_sequentialOrderClosed :
    ¬ SequentialOrderClosed lexicographicCone := by
  intro h
  have hbad := h (0, -1) (1, 0) (fun n => 1 / ((n : ℝ≥0) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => by
      apply Or.inl
      change 0 < (0 : ℝ) + (1 / ((n : ℝ≥0) + 1) : ℝ≥0) * 1
      positivity)
  norm_num [lexicographicCone] at hbad

/-- The degenerate cone has zero process span. -/
theorem zeroCone_span (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Submodule.span ℝ ((⊥ : PointedCone ℝ V) : Set V) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simpa using hx
  · exact bot_le

end ProjectAInos.Thermodynamics
