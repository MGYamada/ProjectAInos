module

public import ProjectAInos.Thermodynamics.Conservation

/-!
# The signed reference-state cutoff formula

Negative coefficients in a reference mixture are moved to the other side of
the accessibility relation. This gives a cutoff for every real parameter,
including parameters outside the unit interval. Its value is entropy relative
to the first reference state.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics

variable {M V : Type*} [AddCommMonoid M] [Preorder M] [Module ℝ≥0 M]
  [AddCommGroup V] [Module ℝ V]

/-- Accessibility from a signed mixture of two reference states. Every scalar
acting on a physical state is nonnegative. -/
def signedReferenceLE (x₀ x₁ x : M) (r : ℝ) : Prop :=
  (1 - r).toNNReal • x₀ + r.toNNReal • x₁ ≤
    x + (-(1 - r)).toNNReal • x₀ + (-r).toNNReal • x₁

private theorem positive_part_difference (r : ℝ) :
    (r.toNNReal : ℝ) - ((-r).toNNReal : ℝ) = r := by
  rcases le_total 0 r with hr | hr
  · rw [Real.coe_toNNReal r hr, Real.toNNReal_of_nonpos (neg_nonpos.mpr hr)]
    simp
  · rw [Real.toNNReal_of_nonpos hr, Real.coe_toNNReal (-r) (neg_nonneg.mpr hr)]
    simp

/-- Signed physical mixtures agree with subtraction in the completed space. -/
theorem signedReferenceLE_iff (P : PointedCone ℝ V) (i : M →ₗ[ℝ≥0] V)
    (horder : ∀ x y, x ≤ y ↔ i y - i x ∈ P) (x₀ x₁ x : M) (r : ℝ) :
    signedReferenceLE x₀ x₁ x r ↔
      i x - i x₀ - r • (i x₁ - i x₀) ∈ P := by
  rw [signedReferenceLE, horder]
  simp only [map_add, map_smul, NNReal.smul_def]
  have h₀ : ((-(1 - r)).toNNReal : ℝ) = ((1 - r).toNNReal : ℝ) - (1 - r) := by
    linarith [positive_part_difference (1 - r)]
  have h₁ : ((-r).toNNReal : ℝ) = (r.toNNReal : ℝ) - r := by
    linarith [positive_part_difference r]
  rw [h₀, h₁]
  have hvec : i x + ((↑(1 - r).toNNReal : ℝ) - (1 - r)) • i x₀ +
      ((↑r.toNNReal : ℝ) - r) • i x₁ -
      ((↑(1 - r).toNNReal : ℝ) • i x₀ + (↑r.toNNReal : ℝ) • i x₁) =
      i x - i x₀ - r • (i x₁ - i x₀) := by module
  rw [hvec]

/-- The cutoff inequality in matched sectors, with entropy unit fixed by the
difference of the reference states. -/
theorem signedReferenceLE_iff_entropy_le (P : PointedCone ℝ V)
    (i : M →ₗ[ℝ≥0] V) (horder : ∀ x y, x ≤ y ↔ i y - i x ∈ P)
    {W : Submodule ℝ V} {s : W ≃ₗ[ℝ] ℝ} (S : EntropyExtension s)
    (hs : ∀ w : W, 0 ≤ s w ↔ (w : V) ∈ P)
    (x₀ x₁ x : M) (h₀₁ : i x₁ - i x₀ ∈ W) (hx : i x - i x₀ ∈ W)
    (hnorm : s ⟨i x₁ - i x₀, h₀₁⟩ = 1) (r : ℝ) :
    signedReferenceLE x₀ x₁ x r ↔ r ≤ S.val (i x) - S.val (i x₀) := by
  rw [signedReferenceLE_iff P i horder]
  have hmem : i x - i x₀ - r • (i x₁ - i x₀) ∈ W :=
    W.sub_mem hx (W.smul_mem r h₀₁)
  have he : S.val (i x₁ - i x₀) = 1 := (S.apply_subtype ⟨_, h₀₁⟩).trans hnorm
  rw [← hs ⟨_, hmem⟩, ← S.apply_subtype ⟨_, hmem⟩]
  simp only [map_sub, map_smul, smul_eq_mul]
  rw [show S.val (i x₁) - S.val (i x₀) = 1 by simpa only [map_sub] using he]
  simp only [mul_one, sub_nonneg]

/-- The real supremum of the accessibility cut is the entropy difference from
the first reference state. -/
theorem reference_cutoff_eq_relative_entropy (P : PointedCone ℝ V)
    (i : M →ₗ[ℝ≥0] V) (horder : ∀ x y, x ≤ y ↔ i y - i x ∈ P)
    {W : Submodule ℝ V} {s : W ≃ₗ[ℝ] ℝ} (S : EntropyExtension s)
    (hs : ∀ w : W, 0 ≤ s w ↔ (w : V) ∈ P)
    (x₀ x₁ x : M) (h₀₁ : i x₁ - i x₀ ∈ W) (hx : i x - i x₀ ∈ W)
    (hnorm : s ⟨i x₁ - i x₀, h₀₁⟩ = 1) :
    sSup {r : ℝ | signedReferenceLE x₀ x₁ x r} =
      S.val (i x) - S.val (i x₀) := by
  have hset : {r : ℝ | signedReferenceLE x₀ x₁ x r} =
      Set.Iic (S.val (i x) - S.val (i x₀)) := by
    ext r
    exact signedReferenceLE_iff_entropy_le P i horder S hs x₀ x₁ x h₀₁ hx hnorm r
  rw [hset, csSup_Iic]

@[simp]
theorem signedReferenceLE_zero (x₀ x₁ x : M) :
    signedReferenceLE x₀ x₁ x 0 ↔ x₀ ≤ x := by
  simp [signedReferenceLE, Real.toNNReal_of_nonpos (show (-1 : ℝ) ≤ 0 by linarith)]

@[simp]
theorem signedReferenceLE_one (x₀ x₁ x : M) :
    signedReferenceLE x₀ x₁ x 1 ↔ x₁ ≤ x := by
  simp [signedReferenceLE, Real.toNNReal_of_nonpos (show (-1 : ℝ) ≤ 0 by linarith)]

end ProjectAInos.Thermodynamics
